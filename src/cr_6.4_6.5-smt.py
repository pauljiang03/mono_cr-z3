from z3 import *

N = 5
m = 24 

RNE = RNE()
S32 = FPSort(8, 24)

def ceil_log2(n):
    k, v = 0, 1
    if n <= 1: 
         return 0
    while v < n:
        v <<= 1
        k += 1
    return k

def exp_unbiased_normal(x):
    bv = fpToIEEEBV(x)
    exp = Extract(30, 23, bv) 
    return BV2Int(exp) - 127

s = Solver()

print(f"Proof for N={N} terms")
print("Attempting to Prove => All Intermediate Additions, Lemma 6.3 Hold'")

T = [FP(f"T{i}", S32) for i in range(N)]
e_list = [exp_unbiased_normal(ti) for ti in T]

if N == 0:
    print("N=0, trivial case.")
    growth = 0
    s.add(Bool(True)) 
elif N == 1:
    print("N=1, trivial case.")
    growth = 0
    s.add(0 <= m) 
else:
    e_max, e_min = Ints("e_max e_min")
    for e in e_list:
        s.add(e <= e_max, e >= e_min)
    
    s.add(Or([e == e_max for e in e_list]))
    s.add(Or([e == e_min for e in e_list]))

    growth = ceil_log2(N)
    K_span = e_max - e_min + 2 * growth
    s.add(K_span <= m)
    
    print(f" (e_max - e_min) + 2*ceil_log2({N}) <= {m}")
    print(f" (e_max - e_min) + {2*growth} <= {m}")

s32_intermediate = FPVal(0.0, S32)

step_premise_consequences = []

print("\nIteratively checking 2-term premise at each step:")
for i in range(N):
    operand_A = s32_intermediate 
    operand_B = T[i]
    
    e_A = exp_unbiased_normal(operand_A)
    e_B = e_list[i] 
    step_2term_premise = (Abs(e_A - e_B) + 2 <= m)
    
    step_premise_consequences.append(step_2term_premise)
    
    s32_intermediate = fpAdd(RNE, s32_intermediate, T[i])

consequence_all_steps_hold = And(step_premise_consequences)
negated_consequence = Or([Not(c) for c in step_premise_consequences])
s.add(negated_consequence)

print("running")
result = s.check()
print(f"\nResult: {result}")

if result == unsat:
    print(f"Z3 found no counterexample for N={N}.")
    print("For N terms, IF the global condition holds,")
    print("THEN every intermediate 2-term addition satisfies lemma 6.3.")
elif result == sat:
    print(f"Z3 found a case for N={N} where the global condition holds")
    print("BUT at least one intermediate 2-term addition FAILED to meet lemma 6.3.")
    print("\nModel for counterexample:")
    print(s.model())
else:
     print(f"\nSolver finished with state: {result}")

