import json
import random
import pandas as pd
from pathlib import Path

DATA_DIR = Path(__file__).parent / "data"
OUT_PATH = Path(__file__).parent / "jobs.json"

# Take the first NJOBS collections of the first date, we'll assign a slack of (0-10)
NJOBS = 100
SEED = 42
MIN_SLACK, MAX_SLACK = 0, 10
IGNORE_JOBS = ["1925"]
H = 24  # Planning horizon in hours
CLAMP_LATEST_START = True  # Cap each latest start so the job finishes inside the horizon


def build_instance(hourly_cpu, horizon=H, clamp_latest_start=CLAMP_LATEST_START):
    # First NJOBS distinct collection_ids in file order
    ids = [c for c in hourly_cpu["collection_id"].unique() if c not in IGNORE_JOBS]
    rows_by_collection = {
        cid: rows
        for cid, rows in hourly_cpu[hourly_cpu["collection_id"].isin(ids)].groupby("collection_id")
    }
    slack_rng = random.Random(SEED)

    jobs = {}
    count = 0
    for collection_id in ids:
        rows = rows_by_collection[collection_id]
        cpu_by_hour = dict(zip(rows["hour"].astype(int), rows["total_cpus"]))
        first_hour, last_hour = min(cpu_by_hour), max(cpu_by_hour)
        cpu_per_hour = [float(cpu_by_hour.get(hour, 0.0)) for hour in range(first_hour, last_hour + 1)]
        duration = len(cpu_per_hour)

        if duration >= 24:
            continue

        # Always draw the slack so the random sequence (and every other job's latest start) doesn't depend on clamping
        latest_start = first_hour + slack_rng.randint(MIN_SLACK, MAX_SLACK)
        if clamp_latest_start:
            latest_start = min(latest_start, horizon - duration)
            if latest_start < first_hour:
                raise ValueError(
                    f"Job {collection_id} (starts at hour {first_hour}, lasts {duration}h) cannot finish within {horizon}h"
                )
        jobs[collection_id] = {"A": first_hour, "L": latest_start, "U": cpu_per_hour}
        count += 1

        if count == NJOBS:
            break
    return {"jobs": jobs}


def load_instance(path=OUT_PATH):
    if not Path(path).exists():
        raise FileNotFoundError(f"{path} not found; run `python data.py` to generate it")
    return json.loads(Path(path).read_text())


if __name__ == "__main__":
    parquet_path = sorted(DATA_DIR.glob("*.parquet"))[0]
    instance = build_instance(pd.read_parquet(parquet_path))
    OUT_PATH.write_text(json.dumps(instance, indent=2))
    print(f"Read {parquet_path.name}, wrote {len(instance['jobs'])} jobs to {OUT_PATH.name}")
