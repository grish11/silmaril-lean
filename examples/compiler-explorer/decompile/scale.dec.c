unsigned long long wc_scale(unsigned long long wc_a, unsigned long long wc_b) {
  return ((wc_b + (wc_a * 8ULL)) + 18446744073709551611ULL);
}
