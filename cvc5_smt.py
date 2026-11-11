import cvc5 #solver engine
from cvc5 import Kind #library for math operations
import compute_mks #slope calculator

# Initialize cvc5 Solver
slv = cvc5.Solver()
slv.setOption("produce-models", "true") #when sat (true), produce the model of solution
slv.setLogic("QF_LIRA") # What math solver accepts: Quantifier-Free Linear Integer and Real Arithmetic

#defines number types
real = slv.getRealSort() 
integer = slv.getIntegerSort()

#safety function so cvc5 does not crash when there is 0 or 1 job to add
def cvc5_sum(*terms):
    if not terms: return slv.mkReal("0")
    if len(terms) == 1: return terms[0]
    return slv.mkTerm(Kind.ADD, *terms)

# Set Parameters
T = 4 #planning horizon
a = "0.8" #power cap

# Fetch the slopes dynamically and format them as strings for cvc5
slopes = [f"{m:.4f}" for m in compute_mks.slopes] 

# SAT Dummy Job Data: {Arrival, Latest Start, Duration, CPU_per_hour}. 
jobs = {
    'J1': {'A': 0, 'L': 1, 'D': 2, 'U': ["0.4", "0.4"]},
    'J2': {'A': 1, 'L': 2, 'D': 2, 'U': ["0.5", "0.5"]}
}

# UNSAT Dummy Job Data: {Arrival, Latest Start, Duration, CPU_per_hour}. Uncomment to test
# jobs = {
#    'J1': {'A': 0, 'L': 1, 'D': 2, 'U': ["0.6", "0.6"]},
#    'J2': {'A': 1, 'L': 2, 'D': 2, 'U': ["0.5", "0.5"]}
# }

# x_js - Binary start variables for each job
x = {} #initialize dictionary containing all jobs with all possible start times
for j, data in jobs.items(): #to get both key and value for jobs (j) 
    x[j] = {} #nested dictionary
    #loops through possible start times (s) starting at A and ending at L
    for s in range(data['A'], data['L'] + 1): 
        bit = slv.mkConst(integer, f"x_{j}_{s}")
        # Restrict to {0, 1}
        slv.assertFormula(slv.mkTerm(Kind.GEQ, bit, slv.mkInteger(0))) #bit => 0
        slv.assertFormula(slv.mkTerm(Kind.LEQ, bit, slv.mkInteger(1))) #bit <=1
        #the bit is an integer <=1 and => 0, so eother 0 or 1. 
        # There will be one 1 only per job bc of the constraint below
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
#5 segments k
# CVC5 variable representing CPU inside bucket k at hour t
sigma = [[slv.mkConst(real, f"sigma_{k}_{t}") for t in range(T)] for k in range(5)]
# 4 segments (last one does not need to be constrained)
# delta determines the order in which segmets be filled
delta = [[slv.mkConst(integer, f"delta_{k}_{t}") for t in range(T)] for k in range(4)]

# Constraints

# Each job starts exactly once
for j in jobs:
    #for each job, create a list containing all possible start times
    start_vars = list(x[j].values())
    #list example: [x_J1_0, x_J1_1] where values are binary
    #we don't need the keys because t does not matter here
    #sum all starting time and force the sum == 1
    sum_x = cvc5_sum(*start_vars)
    slv.assertFormula(slv.mkTerm(Kind.EQUAL, sum_x, slv.mkInteger(1)))

for t in range(T):
    # calculate total CPU utilization by hour (u_t) 
    active_cpu_terms = []
    for j, data in jobs.items():
        for s, var_x in x[j].items():
            #check if job is active at hour t
            if s <= t <= s + data['D'] - 1:
                # step is the relative h of job runtime {0(t=s),1,2...}
                step = t - s
                #get the job's cpu usage for that step
                cpu_val = slv.mkReal(data['U'][step])
                # Convert x_{js} to real to multiply with CPU fraction
                x_real = slv.mkTerm(Kind.TO_REAL, var_x)
                active_cpu_terms.append(slv.mkTerm(Kind.MULT, cpu_val, x_real))
    
    slv.assertFormula(slv.mkTerm(Kind.EQUAL, u[t], cvc5_sum(*active_cpu_terms)))
    #this will have all jobs and possible cpu at time t depending on job's start time
    #u_1 = (0.2 * x_J1_0) + (0.4 * x_J1_1)
    #this is why it's key x is binary and 1 exactly once

    # CPU Capacity <=1
    slv.assertFormula(slv.mkTerm(Kind.LEQ, u[t], slv.mkReal("1.0")))

    # Power Cap <= a
    slv.assertFormula(slv.mkTerm(Kind.LEQ, P[t], slv.mkReal(a)))

    # Piecewise Constraints
    # u_t = sum(sigma_k)
    #total CPU at t = whatever is inside the 5 buckets at t
    slv.assertFormula(slv.mkTerm(Kind.EQUAL, u[t], cvc5_sum(*[sigma[k][t] for k in range(5)])))
    
    for k in range(5):
        # a bucket cannot hold more than 0.2 cpu or less than 0
        slv.assertFormula(slv.mkTerm(Kind.GEQ, sigma[k][t], slv.mkReal("0.0")))
        slv.assertFormula(slv.mkTerm(Kind.LEQ, sigma[k][t], slv.mkReal("0.2")))

    for k in range(4):
        # delta_kt in {0, 1}
        slv.assertFormula(slv.mkTerm(Kind.GEQ, delta[k][t], slv.mkInteger(0)))
        slv.assertFormula(slv.mkTerm(Kind.LEQ, delta[k][t], slv.mkInteger(1)))
        
        delta_real = slv.mkTerm(Kind.TO_REAL, delta[k][t])
        #variable to switch buckets (0-no or 0.2-yes)
        switch = slv.mkTerm(Kind.MULT, slv.mkReal("0.2"), delta_real)
        
        #sigma_k >= 0 - ok keep filling bucket
        #sigma_k >= 0.2 - ok bucket full
        slv.assertFormula(slv.mkTerm(Kind.GEQ, sigma[k][t], switch))
        #sigma_{k+1} <= 0 - can't be : sigma_{k+1} must be 0, next bucket shut
        #sigma_{k+1} <= 0.2 - ok fill next bucket
        slv.assertFormula(slv.mkTerm(Kind.LEQ, sigma[k+1][t], switch))

    # Power Calculation: P_t = sum(m_k * sigma_kt)
    power_terms = []
    for k in range(5):
        power_terms.append(slv.mkTerm(Kind.MULT, slv.mkReal(slopes[k]), sigma[k][t]))
    slv.assertFormula(slv.mkTerm(Kind.EQUAL, P[t], cvc5_sum(*power_terms)))

# Solve and Extract Results
result = slv.checkSat()
print("Satisfiability:", result)

if result.isSat():
    print("\n Schedule ")
    for j, data in jobs.items():
        for s, var_x in x[j].items():
            if str(slv.getValue(var_x)) == "1":
                print(f"Job {j} starts at hour {s}")
    
    print("\n Utilization & Power ")
    for t in range(T):
        u_val = float(slv.getValue(u[t]).getRealValue()) 
        p_val = float(slv.getValue(P[t]).getRealValue())
        print(f"Hour {t}: CPU = {u_val:.2f}, Power = {p_val:.3f}")