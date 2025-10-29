
#include <assert.h>
#include <stdint.h>
#include <stdbool.h>

#ifndef N_MAX
#define N_MAX 5
#endif

static inline uint32_t f2u(float x) {
  union { float f; uint32_t u; } v; v.f = x; return v.u;
}
static inline float u2f(uint32_t u) {
  union { float f; uint32_t u; } v; v.u = u; return v.f;
}

static inline bool fp32_pow2(int k, float *out) {
  if (k < -126 || k > 127) return false;
  uint32_t exp = (uint32_t)(k + 127);
  uint32_t bits = (exp << 23);
  *out = u2f(bits);
  return true;
}

static inline float rtz_align(float x, int eE) {
  uint32_t u = f2u(x);
  uint32_t sign = u >> 31;
  int exp = ((u >> 23) & 0xFF) - 127;
  uint32_t frac = u & 0x7FFFFFu;

  int k = eE - exp;
  if (k <= 0) return x;
  if (k >= 24) {
    uint32_t bits = (sign << 31) | (((uint32_t)(eE+127)) << 23);
    return u2f(bits);
  }
  uint32_t mask = ~((1u << k) - 1u);
  uint32_t bits = (sign << 31) | (((uint32_t)(exp+127)) << 23) | (frac & mask);
  return u2f(bits);
}

extern int  nondet_int(void);
extern float nondet_float(void);

static inline _Bool is_finite32(float x) {
  return (((f2u(x) >> 23) & 0xFFu) != 0xFFu);
}

int main(void) {
  int n = nondet_int();
  __CPROVER_assume(0 <= n && n <= N_MAX);

  int e_D = nondet_int();
  int e_T_max = nondet_int();
  __CPROVER_assume(e_D >= -30 && e_D <= 30);
  __CPROVER_assume(e_T_max >= -30 && e_T_max <= 30);

  int p = nondet_int();
  __CPROVER_assume(p >= 0 && p <= 4);

  float T[N_MAX];
  for (int i = 0; i < n; ++i) {
    T[i] = nondet_float();
    __CPROVER_assume(is_finite32(T[i]));
  }

  float D = nondet_float();
  __CPROVER_assume(is_finite32(D));

  long double S_exact = 0.0L;
  for (int i = 0; i < n; ++i) S_exact += (long double)T[i];

  int eE = (e_D >= e_T_max ? e_D : e_T_max);
  float E32;
  __CPROVER_assume(fp32_pow2(eE, &E32));

  float Tp[N_MAX], eps[N_MAX];
  for (int i = 0; i < n; ++i) {
    Tp[i] = rtz_align(T[i], eE);
    eps[i] = T[i] - Tp[i];
  }

  int tau = ((e_D - e_T_max >= 0) ? (e_D - e_T_max) : 0) + p;

  float mask_win;
  __CPROVER_assume(fp32_pow2(e_T_max - tau, &mask_win));

  float eps_win[N_MAX];
  for (int i = 0; i < n; ++i) {
    eps_win[i] = rtz_align(eps[i], e_T_max - tau);
  }

  float sum_window = 0.0f;
  for (int i = 0; i < n; ++i)
    sum_window += eps_win[i];

  float mask_eD;
  __CPROVER_assume(fp32_pow2(e_D, &mask_eD));

  float eps_overlap = rtz_align(sum_window, e_D);

  float sum_eps = 0.0f;
  for (int i = 0; i < n; ++i)
    sum_eps += eps[i];

  long double Recovery =
      (long double)D - (long double)eps_overlap + (long double)sum_eps;

  assert(S_exact == Recovery);

  return 0;
}
