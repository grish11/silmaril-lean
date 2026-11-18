/* Radix-2 decimation-in-time FFT of 8 complex points (C99 complex). */
#include <complex.h>
#include <math.h>
#include <stdio.h>

#define N 8
#define PI 3.14159265358979323846

static void fft(double complex *x, int n)
{
  /* bit-reversal permutation */
  for (int i = 1, j = 0; i < n; i++) {
    int bit = n >> 1;
    for (; j & bit; bit >>= 1)
      j ^= bit;
    j ^= bit;
    if (i < j) {
      double complex t = x[i];
      x[i] = x[j];
      x[j] = t;
    }
  }
  /* butterflies */
  for (int len = 2; len <= n; len <<= 1) {
    double complex w = cexp(-2.0 * PI * I / len);
    for (int i = 0; i < n; i += len) {
      double complex wk = 1.0;
      for (int k = 0; k < len / 2; k++) {
        double complex u = x[i + k];
        double complex v = x[i + k + len / 2] * wk;
        x[i + k] = u + v;
        x[i + k + len / 2] = u - v;
        wk *= w;
      }
    }
  }
}

int main(void)
{
  double complex x[N] = {1, 1, 1, 1, 0, 0, 0, 0};
  fft(x, N);
  for (int i = 0; i < N; i++)
    printf("%d: %+.3f %+.3fi\n", i, creal(x[i]) + 0.0, cimag(x[i]) + 0.0);
  return 0;
}
