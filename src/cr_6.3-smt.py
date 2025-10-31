from z3 import *
import time

'''
Result: unsat (found in 1141.6448 seconds)
'''

m = 24
RNE = RNE()
S32 = FPSort(8, 24)
S64 = FPSort(11, 53)

def exp_unbiased_normal(x):
    bv = fpToIEEEBV(x)
    exp = Extract(30, 23, bv)
    return BV2Int(exp) - 127

s = Solver()

T0 = FP("T0", S32)
T1 = FP("T1", S32)
s.add(T1 < T0)
e0 = exp_unbiased_normal(T0)
e1 = exp_unbiased_normal(T1) - 24
#should be 23?

s.add(Abs(e0 - e1) + 1 <= m)

print(f"Checking: |e0 - e1| + 1 <= {m}")

s32_0 = FPVal(0.0, S32)
s32_1 = fpAdd(RNE, s32_0, T0)
s32 = fpAdd(RNE, s32_1, T1)

s64_0 = FPVal(0.0, S64)
s64_1 = fpAdd(RNE, s64_0, fpToFP(RNE, T0, S64))
s64 = fpAdd(RNE, s64_1, fpToFP(RNE, T1, S64))

s.add(fpToFP(RNE, s64, S32) != s32)

print("\nSearching for counterexample...")
start_check_time = time.monotonic()
result = s.check()
end_check_time = time.monotonic()

check_duration = end_check_time - start_check_time
print(f"Result: {result} (found in {check_duration:.4f} seconds)")

if result == sat:
    print("\nCounterexample found.")
    print(s.model())
else:
    print("\nNo counterexample found.")
