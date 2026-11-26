#SMT
import time
import cvc5 #solver engine
from cvc5 import Kind #library for math operations
import compute_mks #slope calculator
import json #raw data
import gurobipy as gp
from gurobipy import GRB

# Initialize cvc5 Solver
slv = cvc5.Solver()
slv.setOption("produce-models", "true") #when sat (true), produce the model of solution
slv.setLogic("QF_LIRA") # What math solver accepts: Quantifier-Free Linear Integer and Real Arithmetic

#defines number types
real = slv.getRealSort() 
integer = slv.getIntegerSort()
boolean = slv.getBooleanSort()

#safety function so cvc5 does not crash when there is 0 or 1 job to add
def cvc5_sum(*terms):
    if not terms: return slv.mkReal("0")
    if len(terms) == 1: return terms[0]
    return slv.mkTerm(Kind.ADD, *terms)

# Set Parameters
T = 24 #planning horizon in hours
a = "0.8" #power cap

with open("jobs.json", "r") as file:
    raw_data = json.load(file)["jobs"]

jobs = {}
for j, data in raw_data.items():
    #filter only jobs whose cpu stays <= 0.1 at every time slot 
    # otherwise it returns unsat bc there are too many jobs that can't shift
    if all(val <= 0.1 for val in data["U"]): 
        # nested dictionary (similar to json)
        jobs[j] = {
            "A": data["A"],
            "L": data["L"],
            "D": len(data["U"]),
            #keep 8 decimal places for cpu, with fixed point type(decimal notation) (0.8f)
            #cvc5 wants string format (f" ")
            "U": [f"{val:.8f}" for val in data["U"]],
        }
        #omt takes too long, option to cut the data to solve in a reasonable time
        if len(jobs) == 10:
            break

# Fetch the slopes dynamically and format them as strings for cvc5
slopes = [f"{m:.4f}" for m in compute_mks.slopes] 

# x_js - Binary start variables for each job
x = {} #initialize dictionary containing all jobs with all possible start times
for j, data in jobs.items(): #to get both key and value for jobs (j) 
    x[j] = {} #nested dictionary
    #loops through possible start times (s) starting at A and ending at L
    #+1 because range does not include last number
    for s in range(data['A'], data['L'] + 1):
        bit = slv.mkConst(boolean, f"x_{j}_{s}")
        #the bit is an boolean variable 
        # There will be one 1 only per job bc of the constraint
        x[j][s] = bit

#example of final dict, where variable <...> \in {0,1}
# x = {
#     'J1': {
#         0: <"x_J1_0">,
#         1: <"x_J1_1">
#     },
#     'J2': {
#         1: <"x_J2_1">,
#         2: <"x_J2_2">
#     }
# }

# Hourly CPU and Power Variables (total for each hour t in T )
u = [slv.mkConst(real, f"u_{t}") for t in range(T)]
P = [slv.mkConst(real, f"P_{t}") for t in range(T)]

# Piecewise Variables
# 5 segments k
# CVC5 variable representing CPU inside bucket k at hour t
sigma = [[slv.mkConst(real, f"sigma_{k}_{t}") for t in range(T)] for k in range(5)]
# 4 segments (last one does not need to be constrained)
# delta (boolean) determines the order in which segments are filled
delta = [[slv.mkConst(boolean, f"delta_{k}_{t}") for t in range(T)] for k in range(4)]

# Constraints

# Each job starts exactly once
for j in jobs:
    #for each job, create a list containing all possible start times
    start_vars = [
        #use IfThenElse to convert boolear to integers
        slv.mkTerm(Kind.ITE, bit, slv.mkInteger(1), slv.mkInteger(0))
        for bit in x[j].values()
    ]
    #list example: [x_J1_0, x_J1_1] where values are binary
    #we don't need the keys because t does not matter here
    #sum all starting time and force the sum == 1
    sum_x = cvc5_sum(*start_vars)
    slv.assertFormula(slv.mkTerm(Kind.EQUAL, sum_x, slv.mkInteger(1)))

for t in range(T):
    # calculate total CPU utilization by hour (u_t) 
    active_cpu_terms = []
    for j, data in jobs.items():
        for s, bit in x[j].items():
            #check if job is active at hour t
            if s <= t <= s + data['D'] - 1:
                # step is the relative h of job runtime {0(t=s),1,2...}
                step = t - s
                #get the job's cpu usage for that step
                cpu_val = slv.mkReal(data['U'][step])
                # if bit 1 = cpu_val, else (0) = 0
                active_cpu_terms.append(
                    slv.mkTerm(Kind.ITE, bit, cpu_val, slv.mkReal("0.0"))
                )
    
    slv.assertFormula(slv.mkTerm(Kind.EQUAL, u[t], cvc5_sum(*active_cpu_terms)))
    #this will have all jobs and possible cpu at time t depending on job's start time
    #u_1 = (0.2 * x_J1_0) + (0.4 * x_J1_1)
    #this is why it's key bit is binary and 1 exactly once

    # CPU Capacity <=1
    slv.assertFormula(slv.mkTerm(Kind.LEQ, u[t], slv.mkReal("1.0")))

    # Power Cap <= a
    slv.assertFormula(slv.mkTerm(Kind.LEQ, P[t], slv.mkReal(a)))

    # Piecewise Constraints
    # u_t = sum(sigma_k)
    # CONSTRAINT: total CPU at t must be equal whatever is inside the 5 buckets at t
    slv.assertFormula(slv.mkTerm(Kind.EQUAL, u[t], cvc5_sum(*[sigma[k][t] for k in range(5)])))
    
    for k in range(5):
        # a bucket holds between 0-0.2 cpu units by design 
        slv.assertFormula(slv.mkTerm(Kind.GEQ, sigma[k][t], slv.mkReal("0.0")))
        slv.assertFormula(slv.mkTerm(Kind.LEQ, sigma[k][t], slv.mkReal("0.2")))
    
    for k in range(4):
        #switch: variable to switch buckets (0-False or 0.2-True)
        switch_kt = slv.mkTerm(Kind.ITE, delta[k][t], slv.mkReal("0.2"), slv.mkReal("0.0"))
        
        #sigma_k >= 0 - ok & keep filling bucket
        #sigma_k >= 0.2 - ok & bucket full
        slv.assertFormula(slv.mkTerm(Kind.GEQ, sigma[k][t], switch_kt))
        
        #sigma_{k+1} <= 0 - can't be : sigma_{k+1} must be 0, next bucket shut
        #sigma_{k+1} <= 0.2 - ok fill next bucket
        slv.assertFormula(slv.mkTerm(Kind.LEQ, sigma[k+1][t], switch_kt))

    # Power Calculation: P_t = sum(m_k * sigma_kt)
    power_terms = []
    for k in range(5):
        power_terms.append(slv.mkTerm(Kind.MULT, slv.mkReal(slopes[k]), sigma[k][t]))
    slv.assertFormula(slv.mkTerm(Kind.EQUAL, P[t], cvc5_sum(*power_terms)))

#OMT

# Adjustable objective weights
w_e = "1.0"     # Weight for total energy: sum(P_t)
w_p  = "0.5"     # Weight for peak power: max(P_t)
w_t   = "0.0001"  # Tie-breaker weight (keep << w_energy and w_peak)

# Select Peak Power:
#Create one constant real solver variable (P_peak)
P_peak = slv.mkConst(real, "P_peak")
# declare possibilities for P_peak
# (P_peak=P[0]) OR (P_peak=P[1]) OR (P_peak=P[2]) ... (P_peak=P[T-1]) 
slv.assertFormula(slv.mkTerm(Kind.OR, *[slv.mkTerm(Kind.EQUAL, P_peak, P[t]) for t in range(T)]))
# P_peak >= P[t] for all t (AND)
slv.assertFormula(slv.mkTerm(Kind.AND, *[slv.mkTerm(Kind.GEQ, P_peak, P[t]) for t in range(T)]))

# Total Energy = sum(P_t)
total_energy = cvc5_sum(*P)

# Tie-breaker penalty = sum(w_tie * s * x_{js})
tie_terms = []
for j in jobs:
    for s, bit in x[j].items():
        if s > 0: #starting at s 0, penalty = 0, so can skip
            penalty = slv.mkTerm(Kind.MULT, slv.mkReal(w_t), slv.mkReal(str(s)))
            tie_terms.append(slv.mkTerm(Kind.ITE, bit, penalty, slv.mkReal("0.0")))
tie_penalty = cvc5_sum(*tie_terms)

# Combined Objective: Z = w_energy * Total_Energy + w_peak * P_peak + Tie_Penalty
Z = slv.mkConst(real, "Z")
obj_expr = cvc5_sum(
    slv.mkTerm(Kind.MULT, slv.mkReal(w_e), total_energy),
    slv.mkTerm(Kind.MULT, slv.mkReal(w_p), P_peak),
    tie_penalty
)
slv.assertFormula(slv.mkTerm(Kind.EQUAL, Z, obj_expr))

# Set variables, Solve and Extract Results
result = slv.checkSat()
print("Satisfiability:", result)

#optimization loop for cvc5
if result.isSat():
    start_time = time.perf_counter()
    #initialize best_Z with Z
    best_Z = slv.getValue(Z).getRealValue()

    while True:
        slv.push() #add solver checkpoint to stack
        # Z must be lower than best_Z
        slv.assertFormula(slv.mkTerm(Kind.LT, Z, slv.mkReal(best_Z)))
        if slv.checkSat().isSat():
            # continue updating best_Z if sat
            best_Z = slv.getValue(Z).getRealValue()
        else: #if unsat
            slv.pop()  # remove the last unsat checkpoint from stack
            break #exit while loop
    
    #set the latest satisfiable best_Z found to be equal to Z
    slv.assertFormula(slv.mkTerm(Kind.EQUAL, Z, slv.mkReal(best_Z)))
    slv.checkSat()  # refresh model with Z = best_Z
    elapsed = time.perf_counter() - start_time

    print("\nSchedule:")
    for j in jobs:
        for s, bit in x[j].items():
            if slv.getValue(bit).getBooleanValue():
                print(f"  Job {j} starts at hour {s}")

    print("\nUtilization & Power:")
    for t in range(T):
        u_val = float(slv.getValue(u[t]).getRealValue())
        p_val = float(slv.getValue(P[t]).getRealValue())
        print(f"  Hour {t}: CPU = {u_val:.2f}, Power = {p_val:.3f}")
        
#Gurobi MILP (mixed-integer-linear-programming)

if result.isSat():
    environment = gp.Env(params={"OutputFlag": 0}) #do not print gurobi flags
    m = gp.Model("dc_milp", env=environment)

    #redefine variables for MILP
    x_g = {}
    for j, data in jobs.items():
        x_g[j] = {}
        for s in range(data["A"], data["L"] + 1):
            x_g[j][s] = m.addVar(vtype=GRB.BINARY)
    # lb = lower bound, ub = upper bound
    u_g = [m.addVar(lb=0.0, ub=1.0) for t in range(T)]
    P_g = [m.addVar(lb=0.0, ub=float(a)) for t in range(T)]
    #sigma = how much cpu falls inside k bucket at each hour t
    sigma_g = [[m.addVar(lb=0.0, ub=0.2) for t in range(T)] for k in range(5)]
    delta_g = [[m.addVar(vtype=GRB.BINARY) for t in range(T)] for k in range(4)]
    # a single global variable for the entire horizon
    P_peak_g = m.addVar(lb=0.0)

    slopes_g = [float(m) for m in slopes]

    #redefine constraints for MILP
    for j in jobs:
        #jobs must start only once
        m.addConstr(gp.quicksum(x_g[j].values()) == 1)
    
    # k buckets constraint
    for t in range(T):
        # Sum CPU usage from all jobs active during hour t
        active_cpu_terms = []
        for j, data in jobs.items():
            for s in x_g[j]:
                job_end = s + data["D"] - 1
                if s <= t <= job_end:
                    cpu = float(data["U"][t - s]) #t-s bc U is indexed [0-(D-1)], so at t=10 if s=10 index=[0] OK
                    active_cpu_terms.append(cpu * x_g[j][s])
        m.addConstr(u_g[t] == gp.quicksum(active_cpu_terms)) #total cpu

        #  total CPU u_g[t] is equal to the 5 buckets cpus sum
        bucket_terms = []
        for k in range(5):
            bucket_terms.append(sigma_g[k][t])
        m.addConstr(u_g[t] == gp.quicksum(bucket_terms))

        # Force bucket k to fill (0.2) before bucket k+1 can unlock
        for k in range(4):
            # sigma = 0.2 max; if delta = 1 -> full; if delta = 0 -> filling
            m.addConstr(sigma_g[k][t] >= 0.2 * delta_g[k][t])
            # if delta = 0 -> sigma k+1 cannot fill; delta =1 -> sigma k+1 can start filling
            m.addConstr(sigma_g[k + 1][t] <= 0.2 * delta_g[k][t])

        # Multiply each bucket's CPU slice by its slope to get hourly power
        power_terms = []
        for k in range(5):
            power_terms.append(slopes_g[k] * sigma_g[k][t])
        m.addConstr(P_g[t] == gp.quicksum(power_terms))

        # Ensure global peak power is at least hour t's power
        m.addConstr(P_peak_g >= P_g[t])

    total_energy_g = gp.quicksum(P_g)
    tie_penalty_g = gp.quicksum(
        #higher s (later start time) gets penalized in minimization
        float(w_t) * s * x_g[j][s] for j in jobs for s in x_g[j]
    )
    m.setObjective(
        float(w_e) * total_energy_g + float(w_p) * P_peak_g + tie_penalty_g,
        GRB.MINIMIZE,
    )

    g_start = time.perf_counter()
    m.optimize()
    g_elapsed = time.perf_counter() - g_start

print(f"Solve Time:        gurobi: {g_elapsed:.4f}s | cvc5: {elapsed:.4f}s")
print(f"Optimal Objective (Z): {m.ObjVal:.5f}")
print(f"Total Energy:      {total_energy_g.getValue():.3f}")
print(f"Peak Power:        {P_peak_g.X:.3f}")