import signal
import sys
import time
from fractions import Fraction
from functools import reduce
from pathlib import Path

sys.path.insert(0, str(Path(__file__).parent / "solvers" / "optimathsat-1.7.4-linux-64-bit" / "python"))
import optimathsat as msat  

# msat_solve runs in C, so let Ctrl-C kill the process
signal.signal(signal.SIGINT, signal.SIG_DFL)  

 
H = 24 # Planning horizon (all jobs must finish within H)
WIDTH = 0.2
SLOPES = [1.7651, 1.3582, 0.9824, 0.6221, 0.2722]  # m_k from formulation.tex
OBJECTIVES = {"peak power": (1, 0), "total energy": (0, 1)}

# Instances: power cap "a" and jobs with earliest start A, latest start L, per-hour CPU fractions U.
# Used claude to generate this.
SAT_INSTANCE = {"a": 0.8, "jobs": {
    "j0": {"A": 0, "L": 3, "U": [0.30, 0.30, 0.20]},
    "j1": {"A": 1, "L": 5, "U": [0.50, 0.40]},
    "j2": {"A": 4, "L": 7, "U": [0.25, 0.25]},
    "j3": {"A": 5, "L": 13, "U": [0.40, 0.40, 0.40]},
    "j4": {"A": 8, "L": 11, "U": [0.20, 0.30]},
    "j5": {"A": 10, "L": 15, "U": [0.35]},
    "j6": {"A": 12, "L": 15, "U": [0.30, 0.20, 0.10]},
    "j7": {"A": 14, "L": 18, "U": [0.45, 0.25]},
    "j8": {"A": 16, "L": 19, "U": [0.20, 0.20]},
    "j9": {"A": 18, "L": 22, "U": [0.30, 0.30]},
}}

# All 10 jobs are forced into hour 0, so it's guaranteed unsatisfiable
UNSAT_INSTANCE = {"a": 0.8, "jobs": {f"j{i}": {"A": 0, "L": 0, "U": [0.10, 0.10]} for i in range(10)}}

def make_number(env, v):
    return msat.msat_make_number(env, str(Fraction(v).limit_denominator(10**9)))

def add(env, terms):
    return reduce(lambda a, b: msat.msat_make_plus(env, a, b), terms, make_number(env, 0))

def multiply(env, c, term):
    return msat.msat_make_times(env, make_number(env, c), term)

def value_if(env, v, cond):
    """
    The term v if cond holds, else 0.
    """
    return msat.msat_make_term_ite(env, cond, make_number(env, v), make_number(env, 0))

def get_start_hours(instance, job):
    """
    Feasible start hours S_j, dropping those that would run past the horizon.
    """
    d = instance["jobs"][job]
    return range(d["A"], min(d["L"], H - len(d["U"])) + 1)


def declare_variables(env, instance):
    """
    Declare x_js (Bool), u_t, P_t and p_max (Real); returns (x, u, p, p_max).
    """
    var = lambda name, sort: msat.msat_make_constant(env, msat.msat_declare_function(env, name, sort))
    real = msat.msat_get_rational_type(env)
    x = {(j, s): var(f"x_{j}_{s}", msat.msat_get_bool_type(env))
         for j in instance["jobs"] for s in get_start_hours(instance, j)}
    return (x, [var(f"u_{t}", real) for t in range(H)], [var(f"P_{t}", real) for t in range(H)],
            var("p_max", real))


def encode_constraint_start(env, instance, x):
    """
    (12): every job starts exactly once.
    """
    for j in instance["jobs"]:
        count = add(env, [value_if(env, 1, x[j, s]) for s in get_start_hours(instance, j)])
        msat.msat_assert_formula(env, msat.msat_make_equal(env, count, make_number(env, 1)))

def encode_constraint_utilization(env, instance, x, u):
    """
    (13)-(14): u_t is the sum of the running jobs' CPU fractions and is at most 1.
    """
    for t in range(H):
        running = [value_if(env, d["U"][t - s], x[j, s])
                   for j, d in instance["jobs"].items() for s in get_start_hours(instance, j) if s <= t < s + len(d["U"])]
        msat.msat_assert_formula(env, msat.msat_make_equal(env, u[t], add(env, running)))
        msat.msat_assert_formula(env, msat.msat_make_leq(env, u[t], make_number(env, 1)))

def make_power_curve(env, u_t):
    """
    P_t as the 5 linear segments (eq. 7-10), written as an if-then-else chain over u_t.
    """
    base = [sum(m * WIDTH for m in SLOPES[:k]) for k in range(5)]  
    segment = [msat.msat_make_plus(env, multiply(env, SLOPES[k], u_t), make_number(env, base[k] - SLOPES[k] * k * WIDTH))
               for k in range(5)]
    curve = segment[4]
    for k in reversed(range(4)):
        below = msat.msat_make_leq(env, u_t, make_number(env, (k + 1) * WIDTH))
        curve = msat.msat_make_term_ite(env, below, segment[k], curve)
    return curve

def encode_constraint_power(env, instance, u, p, p_max):
    """
    (10), (11), (15): P_t follows the curve, P_t <= p_max, and P_t <= a.
    """
    msat.msat_assert_formula(env, msat.msat_make_leq(env, make_number(env, 0), p_max))
    for u_t, p_t in zip(u, p):
        msat.msat_assert_formula(env, msat.msat_make_equal(env, p_t, make_power_curve(env, u_t)))
        msat.msat_assert_formula(env, msat.msat_make_leq(env, p_t, p_max))
        msat.msat_assert_formula(env, msat.msat_make_leq(env, p_t, make_number(env, instance["a"])))

def solve(instance, w_p, w_e):
    """
    Minimize w_p * p_max + w_e * sum(P_t) subject to (12)-(15); returns a result dict with timings.
    """
    env = msat.msat_create_opt_env({"model_generation": "true"})
    try:
        # Encode the constraints and variables
        t0 = time.perf_counter()
        x, u, p, p_max = declare_variables(env, instance)
        encode_constraint_start(env, instance, x)
        encode_constraint_utilization(env, instance, x, u)
        encode_constraint_power(env, instance, u, p, p_max)
        objective = msat.msat_make_minimize(env, add(env, [multiply(env, w_p, p_max), multiply(env, w_e, add(env, p))]))
        msat.msat_assert_objective(env, objective)
        encode_time = time.perf_counter() - t0

        # Solve
        t0 = time.perf_counter()
        status = msat.msat_solve(env)
        solve_time = time.perf_counter() - t0
        result = {"sat": status == msat.MSAT_SAT, "encode_time": encode_time, "solve_time": solve_time}

        # If satisfiable, load the optimal model and read the start hours, utilization and power from it.
        if result["sat"]:
            msat.msat_load_objective_model(env, objective)
            value = lambda term: float(Fraction(msat.msat_term_repr(msat.msat_get_model_value(env, term))))
            result["starts"] = {j: s for (j, s), term in x.items()
                                if msat.msat_term_is_true(env, msat.msat_get_model_value(env, term))}
            result["u"] = [value(v) for v in u]
            result["p"] = [value(v) for v in p]
        return result
    finally:
        msat.msat_destroy_env(env)


def print_schedule_report(instance, result):
    """
    Print the job hours 
    """
    print("Job hours")
    for j, s in result["starts"].items():
        print(f"  {j}: hours {s}-{s + len(instance['jobs'][j]['U']) - 1}")
    print("Hourly Schedule")
    print("hour  u_t    P_t")
    for t, (u, p) in enumerate(zip(result["u"], result["p"])):
        print(f"  {t:2d}  {u:.3f}  {p:.3f}")


runs = [(SAT_INSTANCE, o) for o in OBJECTIVES] + [(UNSAT_INSTANCE, "peak power")]
for instance, objective in runs:
    result = solve(instance, *OBJECTIVES[objective])
    print(f"=== Minimize {objective}: {'SAT' if result['sat'] else 'UNSAT'} ===")
    if result["sat"]:
        print_schedule_report(instance, result)
        print(f"peak={max(result['p']):.4f}  energy={sum(result['p']):.4f}")
    print(f"encode={result['encode_time']:.3f}s  solve={result['solve_time']:.3f}s\n")
