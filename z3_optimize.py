"""
Notation (equation numbers refer to the spec):
    t in T = {0..H-1}        hours of the planning horizon
    j in J                   jobs
    tau in {0..D_j-1}        hourly step within job j's run
    s in S_j = {A_j..L_j}    feasible start hours, L_j = min(A_j + slack, H - D_j)
    k in K = {1..5}          segments of the piecewise-linear power curve

    U[j][tau]   fraction of CPU capacity job j uses at step tau
    x[j][s]     1 if job j starts in hour s                       (binary)
    z[j][t]     1 if job j is running in hour t                   (5)
    u[t]        total CPU utilization in hour t                   (6)
    sigma[k][t] portion of u[t] in segment k, in [0, 0.2]         (7)
    delta[k][t] 1 if segment k is full in hour t                  (8)-(9)
    P[t]        dynamic power in hour t                           (10)
    p_max       peak power                                        (11)
"""
import math
from dataclasses import dataclass
from enum import Enum

import z3

K = 5  # number of power-curve segments
SEG_WIDTH = 1 / K  # 0.2


def power_curve(u):
    """Dynamic power above idle, normalized to [0, 1]   (1)"""
    return 2 * u - u ** 1.9


# m_k = [P(0.2k) - P(0.2(k-1))] / 0.2  ->  1.7651, 1.3582, 0.9824, 0.6221, 0.2722
m = {k: round((power_curve(SEG_WIDTH * k) - power_curve(SEG_WIDTH * (k - 1))) / SEG_WIDTH, 4)
     for k in range(1, K + 1)}


class Objective(Enum):
    WEIGHTED = "weighted"  # eq (3): w_p * p_max + w_e * sum_t P_t + w_t * sum_{j,s} s * x_js
    SAT = "sat"  # eqs (12)-(15) only: find any feasible schedule
    PEAK = "peak"  # minimize p_max
    ENERGY = "energy"  # minimize E = sum_t P_t


@dataclass
class Job:
    """A job j with arrival A_j and per-step CPU fractions U_{j,tau}; D_j = len(U)."""
    id: str
    A: int  # arrival hour (relative to horizon start)
    U: list  # U[tau] = fraction of CPU capacity used at step tau

    @property
    # job duration
    def D(self):
        return len(self.U)


class Optimize:
    """Schedule jobs J over horizon T = {0..H-1}.

    objective:
        Objective.WEIGHTED - eq (3): w_p * p_max + w_e * sum_t P_t + w_t * sum_{j,s} s * x_js
        Objective.SAT      - eqs (12)-(15) only: find any feasible schedule
        Objective.PEAK / Objective.ENERGY, or a list of them in priority order,
                           e.g. [Objective.PEAK, Objective.ENERGY], solved
                           lexicographically (OMT); the w_t start-time tie-break
                           is always added last.
    a:      optional power cap, P_t <= a for all t                       (15)
    slack:  hours a job may be delayed past its arrival (L_j = A_j + slack)
    """

    def __init__(self, J, H, slack=0, objective=Objective.WEIGHTED, w_p=1.0, w_e=1.0, w_t=1e-4,
                 a=None, timeout_ms=None):
        self.J = list(J)
        self.H = H
        self.T = range(H)
        self.slack = slack
        # normalize to either Objective.WEIGHTED / Objective.SAT or a tuple of PEAK/ENERGY
        if objective in (Objective.PEAK, Objective.ENERGY):
            objective = (objective,)
        if isinstance(objective, Objective):
            if objective not in (Objective.WEIGHTED, Objective.SAT):
                raise ValueError(f"unsupported objective {objective}")
        else:
            objective = tuple(objective)
            if not objective or not all(o in (Objective.PEAK, Objective.ENERGY) for o in objective):
                raise ValueError("priority list may only contain Objective.PEAK and Objective.ENERGY")
        self.objective = objective
        # weights of each objective (min max power, min total energy, tie-breaking)
        self.w_p, self.w_e, self.w_t = w_p, w_e, w_t
        self.a = a
        self.timeout_ms = timeout_ms
        self.t0 = 0  # absolute hour corresponding to t = 0 (set by from_dataframe)

        self.S = {}  # j -> S_j
        for j in self.J:
            # minimum latest slack or deadline
            L = min(j.A + slack, H - j.D)
            if j.A < 0 or L < j.A:
                raise ValueError(f"job {j.id} (A={j.A}, D={j.D}) does not fit in H={H}")
            # possible start times for j
            self.S[j.id] = range(j.A, L + 1)

        self.opt = None
        # one shot bool starts, running statuses, utilizations, piecewise vars for u, power
        self.x, self.u, self.sigma, self.delta, self.P = {}, {}, {}, {}, {}
        self.p_max = None

    # ---- construction -------------------------------------------------

    @classmethod
    def from_dataframe(cls, df, capacity=None, H=24, t0=None, max_jobs=None, **kwargs):
        """Build J from the output of data_processsing.read_data.

        A_j  = first hour the collection appears (relative to t0)
        D_j  = last - first + 1 hours
        U_jt = total_cpus / capacity at each step (0 for hours with no record)

        df:       pandas DataFrame with one row per (collection, hour), as returned by
                  read_data. Columns used:
                      collection_id  str    job id (Borg collection); becomes Job.id
                      t              int    absolute hour since May 1 00:00
                      total_cpus     float  CPUs the collection used in hour t
                  (read_data also returns `day` and `hour`, which are ignored here.)
                  Each (collection_id, t) pair appears at most once.
        H:        horizon length in hours. Default = span of `t` in df.
        t0:       absolute hour mapped to t = 0. Default = min `t` in df.
        capacity: total CPUs of the platform. Default = the observed peak hourly CPU
                  of the selected jobs, so the trace's own schedule satisfies u_t <= 1.
        max_jobs: keep only the largest jobs by total CPU (Z3 won't scale to ~100k+).
        """
        if t0 is None:
            t0 = int(df["t"].min())
        if H is None:
            H = int(df["t"].max()) - t0 + 1
        df = df[(df["t"] >= t0) & (df["t"] < t0 + H)]

        if max_jobs is not None:
            keep = df.groupby("collection_id")["total_cpus"].sum().nlargest(max_jobs).index
            df = df[df["collection_id"].isin(keep)]
        if capacity is None:
            capacity = float(df.groupby("t")["total_cpus"].sum().max())

        J = []
        for cid, g in df.groupby("collection_id"):
            first, last = int(g["t"].min()), int(g["t"].max())
            usage = dict(zip(g["t"].astype(int), g["total_cpus"]))
            # floor to 6 decimals so rounding never pushes the trace's own schedule above u_t = 1
            U = [math.floor(float(usage.get(t, 0.0)) / capacity * 1e6) / 1e6 for t in range(first, last + 1)]
            J.append(Job(id=str(cid), A=first - t0, U=U))

        inst = cls(J, H, **kwargs)
        inst.t0 = t0
        inst.capacity = capacity
        return inst

    def each_job_starts_exactly_once(self, opt):
        """Create x_js binary variables and add sum_{s in S_j} x_js = 1 for every j   (4)/(12)"""
        for j in self.J:
            # propogates each id in x with all possible starts
            self.x[j.id] = {s: z3.Bool(f"x_{j.id}_{s}") for s in self.S[j.id]}
            # PbEq is weighted sum of vars and the value they should equal
            opt.add(z3.PbEq([(x, 1) for x in self.x[j.id].values()], 1))

    def util_t_leq_1(self, opt, t):
        """Define u_t = sum_j sum_s U_{j,t-s} x_js (6)/(13) and add u_t <= 1 (14) for hour t."""
        self.u[t] = z3.Real(f"u_{t}")
        terms = []
        for j in self.J:
            for s in self.S[j.id]:
                # job j started at s is running in hour t
                if s <= t <= s + j.D - 1:
                    tau = t - s  # step of j's run that falls in hour t
                    if j.U[tau] != 0:  # skip zero-usage steps
                        terms.append(z3.If(self.x[j.id][s], z3.RealVal(j.U[tau]), 0))
        opt.add(self.u[t] == (z3.Sum(terms) if terms else z3.RealVal(0)))
        opt.add(self.u[t] <= 1)  # (14)

    def segments_fill_in_order(self, opt, t):
        """Create sigma_kt in [0, 0.2] and delta_kt, and add (8)-(9) for hour t, so that
        segment k+1 can only be used once segment k is full."""
        for k in range(1, K + 1):
            self.sigma[(k, t)] = z3.Real(f"sigma_{k}_{t}")
            # bounds for segment
            opt.add(self.sigma[(k, t)] >= 0, self.sigma[(k, t)] <= SEG_WIDTH)
        for k in range(1, K):
            self.delta[(k, t)] = z3.Bool(f"delta_{k}_{t}")
            d = z3.If(self.delta[(k, t)], SEG_WIDTH, 0)
            opt.add(self.sigma[(k, t)] >= d)  # (8)
            opt.add(self.sigma[(k + 1, t)] <= d)  # (9)

    def build(self):
        opt = z3.Optimize()
        if self.timeout_ms is not None:
            opt.set(timeout=self.timeout_ms)

        self.each_job_starts_exactly_once(opt)

        for t in self.T:
            self.util_t_leq_1(opt, t)
            # piecewise segments   (7)-(9)
            self.segments_fill_in_order(opt, t)
            # segments add to utilization
            opt.add(self.u[t] == z3.Sum([self.sigma[(k, t)] for k in range(1, K + 1)]))  # (7)

            # P_t = sum_k m_k sigma_kt   (10)
            self.P[t] = z3.Real(f"P_{t}")
            opt.add(self.P[t] == z3.Sum([z3.RealVal(m[k]) * self.sigma[(k, t)] for k in range(1, K + 1)]))
            opt.add(self.P[t] >= 0)

            if self.a is not None:
                opt.add(self.P[t] <= self.a)  # (15)

        # P_t <= p_max   (11)
        self.p_max = z3.Real("p_max")
        opt.add(self.p_max >= 0)
        for t in self.T:
            opt.add(self.P[t] <= self.p_max)

        E = z3.Sum([self.P[t] for t in self.T])
        # builds tie-breaker sum 
        start_sum = z3.Sum([z3.If(x, s, 0) for j in self.J for s, x in self.x[j.id].items()])

        if self.objective is Objective.WEIGHTED:  # (3)
            opt.minimize(self.w_p * self.p_max + self.w_e * E + self.w_t * start_sum)
        elif self.objective is not Objective.SAT:  # lexicographic OMT
            terms = {Objective.PEAK: self.p_max, Objective.ENERGY: E}
            for o in self.objective:
                opt.minimize(terms[o])
            opt.minimize(start_sum)

        self.opt = opt
        return self

    # ---- solving -----------------------------------------------------

    def solve(self):
        """Solve and return a result dict, or None if unsat/unknown."""
        if self.opt is None:
            self.build()
        status = self.opt.check()
        if status != z3.sat:
            print(f"solver returned {status}")
            return None

        mdl = self.opt.model()
        start = {jid: next(s for s, x in xs.items() if z3.is_true(mdl.eval(x, model_completion=True)))
                 for jid, xs in self.x.items()}
        u = {t: _to_float(mdl.eval(self.u[t])) for t in self.T}
        P = {t: _to_float(mdl.eval(self.P[t])) for t in self.T}
        return {
            "start": start,  # job id -> chosen s (relative hour; add self.t0 for absolute)
            "u": u,
            "P": P,
            "p_max": max(P.values(), default=0.0),
            "E": sum(P.values()),
        }


def _to_float(v):
    if z3.is_rational_value(v):
        return v.numerator_as_long() / v.denominator_as_long()
    return float(v.as_decimal(12).rstrip("?"))


if __name__ == "__main__":
    demo = [
        Job("a", A=0, U=[0.4, 0.4, 0.3]),
        Job("b", A=0, U=[0.3, 0.3]),
        Job("c", A=1, U=[0.3, 0.2]),
        Job("d", A=2, U=[0.5]),
    ]
    
    res = Optimize(demo, H=6, slack=3, objective=Objective.WEIGHTED, a=0.9).solve()
    print(Objective.WEIGHTED, res)
