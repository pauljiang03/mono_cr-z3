#include <assert.h>
#include <stdint.h> 

/*
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
 */

unsigned int nondet_uint();

int main() {
    // We define the core variables from the proof (Theorem 4.4)
    unsigned int p; // p // Number of padding bits
    unsigned int n; // n // Total number of addends 

    // Assign non-deterministic values to model all possible hardware configs.
    p = nondet_uint();
    n = nondet_uint();

    // We assume n > 1. We need more than 1 term to introduce non-monotoncity.
    __CPROVER_assume(n > 1);

    // We assume p >= 0. We cannot have negative padding bits. 
    __CPROVER_assume(p >= 0);

    // We assume the condition for MONOTONICITY is TRUE.
    // Monotonicity holds if the system is NOT susceptible.
    // Susceptibility condition: n - 1 >= 2^(p + 2)
    // Monotonicity condition: n - 1 < 2^(p + 2)
    
    unsigned int threshold = 1U << (p + 2); 
    __CPROVER_assume(n - 1 < threshold);

    // The Theorem 4.4 states:
    // 1. Assume a largest term T'
    // 2. Assume a bit position k = ulp(T') - p
    // 3. Assume a bit position l = ulp(T')
    // 4. Non-monotonicity is caused by the sum of n-1 smaller terms that 
    //    canot be reflected in the bits of T' without shifting. 
    // 5. The maximum possible value this sum can have is (n - 1) bits at k. 
    // 6. Non-monotonicity occurs if this sum is large enough to generate a carry bit past l. 
    // 7. The minimum sum required for this carry is 2^(p + 2) bits at k.

    // In our encoding, sum is bounded by its maximum
    // possible value, which the proof gives as (n - 1) at k.
    unsigned int sum = nondet_uint();
    __CPROVER_assume(sum <= (n - 1));

    // 'non_monotonic_behavior' is true if this sum
    // reaches or exceeds the threshold required for a carry into l.
    int non_monotonic_behavior = (sum >= threshold);

    // Given assumptions:
    // 1. n - 1 < threshold
    // 2. sum <= n - 1
    //
    // It must follow that sum < threshold.
    // Therefore, non_monotonic_behavior must be 0 (false).
    //
    assert(non_monotonic_behavior == 0); 
    
    return 0;
}
