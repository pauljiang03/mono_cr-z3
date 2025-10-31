from z3 import *
import time

N = 1024
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


T_orig = [FP(f"T_orig{i}", S32) for i in range(N)]
Eps = [FP(f"Eps{i}", S32) for i in range(N)]

e_T_list = []
e_eps_list = []

for i in range(N):
    s.add(And(Not(fpIsNaN(T_orig[i])), Not(fpIsInf(T_orig[i]))))
    s.add(And(Not(fpIsNaN(Eps[i])), Not(fpIsInf(Eps[i]))))
    e_T_list.append(exp_unbiased_normal(T_orig[i]))
    e_eps_list.append(exp_unbiased_normal(Eps[i]))

growth = ceil_log2(N)


e_T_min = e_T_list[0]
e_T_max = e_T_list[0]

for i in range(1, N):
    e_current = e_T_list[i]
    e_T_min = If(e_current < e_T_min, e_current, e_T_min)
    e_T_max = If(e_current > e_T_max, e_current, e_T_max)

    K_span_6_5 = (e_T_max - e_T_min) + 2 * growth
    s.add(K_span_6_5 <= m)

e_eps_max_set_bit = e_T_max - m
e_eps_min_set_bit = e_T_min - m

thm_6_4 = (e_eps_max_set_bit - e_eps_min_set_bit) + growth < m
s.add(Not(thm_6_4))

print("Running solver...")
start_check_time = time.monotonic()
result = s.check()
end_check_time = time.monotonic()
check_duration = end_check_time - start_check_time
print(f"\nResult: {result} (found in {check_duration:.4f} seconds)")

if result == sat:
    print("\nsat")
    model = s.model()
    print(model)
else:
    print("\nunsat")

