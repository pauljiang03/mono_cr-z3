from z3 import *
import time

m = 24
RNE = RNE()
fp32 = FPSort(8, 24)
fp128 = FPSort(15, 113)

def exp_unbiased_normal(x):
    bv = fpToIEEEBV(x)
    exp = Extract(30, 23, bv)
    return BV2Int(exp) - 127

s = Solver()

T0 = FP("T0", fp32)
T1 = FP("T1", fp32)
s.add(exp_unbiased_normal(T1) <= exp_unbiased_normal(T0))
max_bit = exp_unbiased_normal(T0)
min_bit = exp_unbiased_normal(T1) - 24

s.add(Abs(max_bit - min_bit) + 1 <= m)

print(f"Checking: |e0 - e1| + 1 <= {m}")

s32_0 = FPVal(0.0, fp32)
s32_1 = fpAdd(RNE, s32_0, T0)
s32 = fpAdd(RNE, s32_1, T1)

s128_0 = FPVal(0.0, fp128)
s128_1 = fpAdd(RNE, s128_0, fpToFP(RNE, T0, fp128))
s128 = fpAdd(RNE, s128_1, fpToFP(RNE, T1, fp128))

s.add(s128 != fpToFP(RNE, s32, fp128))

print("\nSearching for counterexample...")
start_check_time = time.monotonic()
result = s.check()
end_check_time = time.monotonic()

check_duration = end_check_time - start_check_time
print(f"Result: {result} (found in {check_duration:.4f} seconds)")

if result == sat:
    print("\nsat")
    print(s.model())
else:
    print("\nunsat")

