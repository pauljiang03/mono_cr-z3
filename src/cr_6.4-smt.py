from z3 import *
import time

'''
N can be set 5, 9, or 16 to verify for any existing tensor core architecture
For N <= 128, can prove in under 1 minute
'''

N = 5
m = 24

RNE = RNE()
fp32 = FPSort(8, 24)

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

T = [FP(f"T{i}", fp32) for i in range(N)]
e_list = []

for i, ti in enumerate(T):
    e_list.append(exp_unbiased_normal(ti))
    not_exceptional = And(Not(fpIsNaN(ti)), Not(fpIsInf(ti)))
    s.add(not_exceptional)


e_min = e_list[0]
e_max = e_list[0]

for i in range(1, N):
    e_current = e_list[i]
    e_min = If(e_current < e_min, e_current, e_min)
    e_max = If(e_current > e_max, e_current, e_max)

growth = ceil_log2(N)
K_span = e_max - (e_min - 24) + growth

print(f"(e_max - e_min) + ceil_log2({N}) <= {m}")
s.add(K_span <= m)

step_premises = []


s32_intermediate_sum = T[0]
for i in range(1, N):
    t_a = s32_intermediate_sum
    t_b = T[i]

    e_a = exp_unbiased_normal(t_a)
    e_b = e_list[i]
    e_max_2 = If(e_a > e_b, e_a, e_b)
    e_min_2 = If(e_a < e_b, e_a, e_b)

    one_span = e_max_2 - (e_min_2 - 24) + 1

    step_premise_holds = (one_span <= m)
    step_premises.append(step_premise_holds)

    s32_intermediate_sum = fpAdd(RNE, s32_intermediate_sum, t_b)



all_steps_hold = And(step_premises)
all_steps_not_hold = Not(all_steps_hold)
s.add(all_steps_not_hold)

print("Running solver...")
start_check_time = time.monotonic()
result = s.check()
end_check_time = time.monotonic()
check_duration = end_check_time - start_check_time
print(f"Result: {result} (found in {check_duration:.4f} seconds)")

if result == sat:
    print("\nsat")
    model = s.model()
    print(model)
else:
    print("\nunsat")


