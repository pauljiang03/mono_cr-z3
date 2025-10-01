#include <assert.h>
#include <math.h>

void main() {
    float T1;       
    float T1_prime;  
    float T_small_sum; 
    
    float Delta_S_add; 

    __CPROVER_assume(T1 > 1.0e10f);
    __CPROVER_assume(T1 < 1.0e12f);
    __CPROVER_assume(T_small_sum > 1.0f);
    __CPROVER_assume(T_small_sum < 10.0f);

    __CPROVER_assume(T1 > T1_prime);
    
    float D = T1 - T1_prime; 
    

    __CPROVER_assume(Delta_S_add > D);
    __CPROVER_assume(Delta_S_add > 0.0f);
    

    float S = T1; 


    float S_prime = T1_prime + Delta_S_add;

 
    assert(S_prime >= S); 
    
    assert(S_prime <= S); 
}
