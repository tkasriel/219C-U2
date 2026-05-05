#define main bipbip_reference_main
#include "bipbip.cpp"
#undef main

static void print_vector(const char *label, tweak_word mk[4], tweak_word tweak, block_word input) {
  bool trk[7][53];
  bool t[53];
  bool drk[12][24];
  bool x[24];
  block_word y = input;

  KeySc(mk, trk);
  TwkIn(tweak, t);
  TwkSc(t, trk, drk);
  Word2Bits(y, x);
  BipBipDec(x, drk);
  Bits2Word(y, x);

  printf("%s mk=[%016llx,%016llx,%016llx,%016llx] tweak=%010llx in=%06x out=%06x\n",
         label,
         (unsigned long long)mk[0],
         (unsigned long long)mk[1],
         (unsigned long long)mk[2],
         (unsigned long long)mk[3],
         (unsigned long long)tweak,
         input,
         y);
}

int main() {
  tweak_word mk0[4] = {
    0x0000000000000001ULL,
    0x0000000000000020ULL,
    0x0000000000000300ULL,
    0x0000000000004000ULL
  };

  tweak_word mk1[4] = {
    0x0123456789abcdefULL,
    0x0f1e2d3c4b5a6978ULL,
    0x0011223344556677ULL,
    0x8899aabbccddeeffULL
  };

  print_vector("v0", mk0, 0x0000000000ULL, 0x000000);
  print_vector("v1", mk0, 0x0000000000ULL, 0x000001);
  print_vector("v2", mk0, 0x0000000000ULL, 0xabcdef);
  print_vector("v3", mk0, 0x0000000001ULL, 0x000000);
  print_vector("v4", mk0, 0x123456789aULL, 0x654321);
  print_vector("v5", mk0, 0xffffffffffULL, 0xffffff);
  print_vector("v6", mk1, 0x0000000000ULL, 0x000000);
  print_vector("v7", mk1, 0x0000000001ULL, 0x000001);
  print_vector("v8", mk1, 0x13579bdf24ULL, 0x2468ac);
  print_vector("v9", mk1, 0xffffffffffULL, 0xffffff);

  return 0;
}
