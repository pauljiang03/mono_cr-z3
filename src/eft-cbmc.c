#include <assert.h>
#include <stdint.h> 

unsigned long long nondet_ullong();
unsigned int nondet_uint();

unsigned int max(unsigned int a, unsigned int b) {
    return (a > b) ? a : b;
}

unsigned long long pow2(int exp) {
    if (exp < 0 || exp >= 64) {
        return 0; 
    }
    return 1ULL << exp;
}


unsigned long long truncate(unsigned long long val, int exp) {
    unsigned long long mask = ~(pow2(exp) - 1);
    return val & mask;
}


int main() {
    const unsigned int N = 5; 

    unsigned int p;    // p // Number of padding bits
    unsigned long long T[N]; // T[N] // The array of n input terms
    unsigned long long D;    // D // Sum from the hardware computation
    unsigned int e_T_max; // e_T_max // Max exponent among all T
    unsigned int e_D;     // e_D // Exponent of the hardware result D

    unsigned long long S_exact = 0; // The true, unrounded mathematical sum

    p = nondet_uint();
    __CPROVER_assume(p >= 0); 

    e_T_max = nondet_uint();
    e_D = nondet_uint();
    __CPROVER_assume(e_T_max > 0 && e_T_max < 60);
    __CPROVER_assume(e_D > 0 && e_D < 60);

    D = nondet_ullong();

    
    int e_align = max(e_D, e_T_max);
    
    unsigned long long eps[N];
    
    for (int i = 0; i < N; i++) {
        T[i] = nondet_ullong();
        __CPROVER_assume(T[i] > 0 && T[i] < (1ULL << 62));
        
        S_exact += T[i];

  
        unsigned long long T_prime = truncate(T[i], e_align);

        eps[i] = T[i] - T_prime;

        assert(T[i] == T_prime + eps[i]);
    }


    int e_delta = (int)e_D - (int)e_T_max;
    
    int tau = (e_delta > 0 ? e_delta : 0) + (int)p;
    
    unsigned long long sum_window = 0;
    int e_mask_val = (int)e_T_max - tau; 

    for (int i = 0; i < N; i++) {

        unsigned long long eps_window_i = truncate(eps[i], e_mask_val);
        
        sum_window = sum_window + eps_window_i;
    }

    unsigned long long eps_overlap = truncate(sum_window, e_D);


    unsigned long long sum_eps = 0;
    for (int i = 0; i < N; i++) {
        sum_eps += eps[i];
    }
    unsigned long long E_total = sum_eps - eps_overlap;

    unsigned long long S_recovered = D + E_total;


    assert(S_recovered == S_E_exact);

    return 0;
}
