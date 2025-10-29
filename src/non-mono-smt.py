from z3 import *

'''
 *
 * Theorem 4.4 states that a system is SUSCEPTIBLE to non-monotonicity if:
 * p <= floor(log2(n-1) - 2)
 *
 * This is equivalent to the proof's inequality:
 * n - 1 >= 2^(p + 2)
 *
 *
 * We will:
 * 1. ASSUME the conditions for MONOTONICITY.
 * 2. MODEL the hardware behavior based on the proof text.
 * 3. ASSERT that non-monotonic behavior is impossible.
 *
'''

# We define the core variables from the proof (Theorem 4.4)
# unsigned int p; // p // Number of padding bits
# unsigned int n; // n // Total number of terms

p = BitVec('p', 32)
n = BitVec('n', 32)

s = Solver()

# We assume n > 1. We need more than 1 term to introduce non-monotoncity.
s.add(ULT(BitVecVal(1, 32), n))

# We assume p >= 0. We cannot have negative padding bits.
# We assume reasonable bounds on p
s.add(p >= 0)
s.add(p < 30)

# We assume the condition for MONOTONICITY is TRUE.
# Monotonicity holds if the system is NOT susceptible.
# Susceptibility condition: n - 1 >= 2^(p + 2)
# Monotonicity condition: n - 1 < 2^(p + 2)

threshold = BitVec('threshold', 32)
s.add(threshold == (BitVecVal(1, 32) << (p + 2)))
s.add(ULT(n - 1, threshold))

# The Theorem 4.4 states:
# 1. Assume a largest term T'
# 2. Assume a bit position k = ulp(T') - p
# 3. Assume a bit position l = ulp(T')
# 4. Non-monotonicity is caused by the sum of n-1 smaller terms that
#    cannot be reflected in the bits of T' without additional shifting.
# 5. The maximum possible value this sum can have is (n - 1) bits at k.
# 6. Non-monotonicity occurs if this sum is large enough to generate a carry bit past l.
# 7. The minimum sum required for this carry is 2^(p + 2) bits at k.

# In our encoding, sum is bounded by its maximum
# possible value, which is given as (n - 1) at k.
sum = BitVec('sum', 32)

s.add(ULE(sum, n - 1))

# non_monotonic is true if this sum
# reaches or exceeds the threshold required for a carry into l.
non_monotonic = Bool('non_monotonic')
s.add(non_monotonic == UGE(sum, threshold))

# Given assumptions:
# 1. n - 1 < threshold
# 2. sum <= n - 1
#
# It must follow that sum < threshold.
# Therefore, non_monotonic_behavior must be 0 (false).
#
# assert(non_monotonic_behavior == 0);

s.add(non_monotonic)
res = s.check()

if res == sat:
    print("Counterexample found (assertion violated):")
    m = s.model()
    print(f"p = {m[p]}")
    print(f"n = {m[n]}")
    print(f"threshold = {m[threshold]}")
    print(f"sum = {m[sum]}")
    print(f"non_monotonic = {m[non_monotonic]}")
else:
    print("UNSAT — no counterexample found. non monotonicity not possible.")


def check_arch(name, n_val, p_val):
    solver = Solver()
    n_bv = BitVecVal(n_val, 32)
    p_bv = BitVecVal(p_val, 32)
    lhs = n_bv - BitVecVal(1, 32)
    rhs = (BitVecVal(1, 32) << (p_bv + 2))
    susceptible = UGE(lhs, rhs)
    solver.add(susceptible)
    res = solver.check()
    print(f"\nCorollary 4.5: {name}")
    print(f"n = {n_val}, p = {p_val}")
    if res == sat:
        print(f"(n-1 >= 2^(p+2)) -> SUSCEPTIBLE")
    else:
        print(f"(n-1 < 2^(p+2)) -> MONOTONIC")

check_arch("Volta", 5, 0)
check_arch("Turing", 5, 1)
check_arch("Ampere", 9, 1)
check_arch("Hopper", 17, 2)
