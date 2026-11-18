/* Top-down merge sort of an int array, with a scratch buffer. */
#include <stdio.h>

static void merge(int *a, int *tmp, int lo, int mid, int hi)
{
  int i = lo, j = mid, k = lo;
  while (i < mid && j < hi)
    tmp[k++] = (a[i] <= a[j]) ? a[i++] : a[j++];
  while (i < mid)
    tmp[k++] = a[i++];
  while (j < hi)
    tmp[k++] = a[j++];
  for (k = lo; k < hi; k++)
    a[k] = tmp[k];
}

void msort(int *a, int *tmp, int lo, int hi)
{
  if (hi - lo < 2)
    return;
  int mid = lo + (hi - lo) / 2;
  msort(a, tmp, lo, mid);
  msort(a, tmp, mid, hi);
  merge(a, tmp, lo, mid, hi);
}

int main(void)
{
  int a[8] = {5, 2, 7, 1, 8, 3, 6, 4};
  int tmp[8];
  msort(a, tmp, 0, 8);
  for (int i = 0; i < 8; i++)
    printf("%d%c", a[i], i == 7 ? '\n' : ' ');
  return 0;
}
