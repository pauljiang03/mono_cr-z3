#include <assert.h>
#include <limits.h> 

void main() {
    int a; 
    int b;
    

    __CPROVER_assume(a > 0 && a > (INT_MAX - 10)); 
    __CPROVER_assume(b > 0 && b < 10);
    int c = a + b;

    assert(c > a); 
}
