// Reference C++ Code for BipBip Tweakable Block Cipher
// https://tches.iacr.org/index.php/TCHES/article/view/9955

#include "stdio.h"
#include "stdlib.h"
#include "stdint.h"

#define tweak_word uint64_t
#define block_word uint32_t

#define sint uint8_t

const sint BBB[64] = {//BipBipBox
0x00,0x01,0x02,0x03,0x04,0x06,0x3e,0x3c,0x08,0x11,0x0e,0x17,0x2b,0x33,0x35,0x2d,0x19,0x1c,0x09,0x0c,0x15,0x13,0x3d,0x3b,0x31,0x2c,0x25,0x38,0x3a,0x26,0x36,0x2a,
0x34,0x1d,0x37,0x1e,0x30,0x1a,0x0b,0x21,0x2e,0x1f,0x29,0x18,0x0f,0x3f,0x10,0x20,0x28,0x05,0x39,0x14,0x24,0x0a,0x0d,0x23,0x12,0x27,0x07,0x32,0x1b,0x2f,0x16,0x22};

const sint IBBB[64] = {//Inverse of BipBipBox
0x00,0x01,0x02,0x03,0x04,0x31,0x05,0x3a,0x08,0x12,0x35,0x26,0x13,0x36,0x0a,0x2c,0x2e,0x09,0x38,0x15,0x33,0x14,0x3e,0x0b,0x2b,0x10,0x25,0x3c,0x11,0x21,0x23,0x29,
0x2f,0x27,0x3f,0x37,0x34,0x1a,0x1d,0x39,0x30,0x2a,0x1f,0x0c,0x19,0x0f,0x28,0x3d,0x24,0x18,0x3b,0x0d,0x20,0x0e,0x1e,0x22,0x1b,0x32,0x1c,0x17,0x07,0x16,0x06,0x2d};

const sint PI1[24] = {1,7,6,0,2,8,12,18,19,13,14,20,21,15,16,22,23,17,9,3,4,10,11,5};
const sint PI2[24] = {0,1,4,5,8,9,2,3,6,7,10,11,16,12,13,17,20,21,15,14,18,19,22,23};
const sint PI3[24] = {16,22,11,5,2,8,0,6,19,13,12,18,14,15,1,7,21,20,4,3,17,23,10,9};

const sint IPI1[24] = {3,0,4,19,20,23,2,1,5,18,21,22,6,9,10,13,14,17,7,8,11,12,15,16};
const sint IPI2[24] = {0,1,6,7,2,3,8,9,4,5,10,11,13,14,19,18,12,15,20,21,16,17,22,23};
const sint IPI3[24] = {6,14,4,19,18,3,7,15,5,23,22,2,10,9,12,13,0,20,11,8,17,16,1,21};

const sint PI4[53] = {0,13,26,39,52,12,25,38,51,11,24,37,50,10,23,36,49,9,22,35,48,8,21,34,47,7,20,33,46,6,19,32,45,5,18,31,44,4,17,30,43,3,16,29,42,2,15,28,41,1,14,27,40};
const sint PI5[53] = {0,11,22,33,44,2,13,24,35,46,4,15,26,37,48,6,17,28,39,50,8,19,30,41,52,10,21,32,43,1,12,23,34,45,3,14,25,36,47,5,16,27,38,49,7,18,29,40,51,9,20,31,42};
  
////////////////////////////////////////////////////////////////////////////////////////////////////

// S-box Layer S
void SBL(bool x[24]) {
  sint a, i, j;
  for (j = 0; j < 4; j++) {
    i = 6 * j + 5;
    a  = x[i--]; a <<= 1;
    a ^= x[i--]; a <<= 1;
    a ^= x[i--]; a <<= 1;
    a ^= x[i--]; a <<= 1;
    a ^= x[i--]; a <<= 1;
    a ^= x[i--];
    a  = BBB[a];

    i = 6 * j + 5;
    x[i--] = (a >> 5) & 1;
    x[i--] = (a >> 4) & 1;
    x[i--] = (a >> 3) & 1;
    x[i--] = (a >> 2) & 1;
    x[i--] = (a >> 1) & 1;
    x[i--] = a & 1;
  }
}

//Inverse S-box Layer S
void ISBL(bool x[24]) {
  sint a, i, j;
  for (j = 0; j < 4; j++) {
    i = 6 * j + 5;
    a  = x[i--]; a <<= 1;
    a ^= x[i--]; a <<= 1;
    a ^= x[i--]; a <<= 1;
    a ^= x[i--]; a <<= 1;
    a ^= x[i--]; a <<= 1;
    a ^= x[i--];
    a  = IBBB[a];

    i = 6 * j + 5;
    x[i--] = (a >> 5) & 1;
    x[i--] = (a >> 4) & 1;
    x[i--] = (a >> 3) & 1;
    x[i--] = (a >> 2) & 1;
    x[i--] = (a >> 1) & 1;
    x[i--] = a & 1;
  }
}

// Linear Mixing Layer in Data Path: theta_d
void LML1(bool x[24]) {
  bool y[24];
  for (sint i = 0; i < 24; i++)
    y[i] = x[i] ^ x[(i + 2) % 24] ^ x[(i + 12) % 24];
  for (sint i = 0; i < 24; i++)
    x[i] = y[i];
}

// Inverse Linear Mixing Layer in Data Path: inv_theta_d
void ILML1(bool x[24]) {
  bool y[24];
  for (sint i = 0; i < 24; i++)
    y[i] = x[(i + 8) % 24] ^ x[(i + 20) % 24] ^ x[(i + 22) % 24];
  for (sint i = 0; i < 24; i++)
    x[i] = y[i];
  
}

// Bit-Permutation with PI1
void BPL1(bool x[24]) {
  bool y[24];
  for (sint i = 0; i < 24; i++)
    y[i] = x[PI1[i]];
  for (sint i = 0; i < 24; i++)
    x[i] = y[i];
}

// Inverse Bit-Permutation with IPI1
void IBPL1(bool x[24]) {
  bool y[24];
  for (sint i = 0; i < 24; i++)
    y[i] = x[IPI1[i]];
  for (sint i = 0; i < 24; i++)
    x[i] = y[i];
  
}

// Bit-Permutation with PI2
void BPL2(bool x[24]) {
  bool y[24];
  for (sint i = 0; i < 24; i++)
    y[i] = x[PI2[i]];
  for (sint i = 0; i < 24; i++)
    x[i] = y[i];
}

//Inverse Bit-Permutation with PI2
void IBPL2(bool x[24]) {
  bool y[24];
  for (sint i = 0; i < 24; i++)
    y[i] = x[IPI2[i]];
  for (sint i = 0; i < 24; i++)
    x[i] = y[i];
}

// Bit-Permutation with PI3
void BPL3(bool x[24]) {
  bool y[24];
  for (sint i = 0; i < 24; i++)
    y[i] = x[PI3[i]];
  for (sint i = 0; i < 24; i++)
    x[i] = y[i];
}

// Inverse Bit-Permutation with PI3
void IBPL3(bool x[24]) {
  bool y[24];
  for (sint i = 0; i < 24; i++)
    y[i] = x[IPI3[i]];
  for (sint i = 0; i < 24; i++)
    x[i] = y[i];
}

// Key Addition Layer in Data Path
void KAD(bool x[24], bool drk[24]) {
  for (sint i = 0; i < 24; i++)
    x[i] ^= drk[i];
}

// Round Function: Core Round
void RFC(bool x[24]) {
  SBL (x);
  BPL1(x);
  LML1(x);
  BPL2(x);
}

// Round Function: Inverse Core Round
void IRFC(bool x[24]) {
  IBPL2(x);
  ILML1(x);
  IBPL1(x);
  ISBL (x);
}

// Round Function: Shell Round
void RFS(bool x[24]) {
  SBL (x);
  BPL3(x);
}

// Round Function: Inverse Shell Round
void IRFS(bool x[24]) {
  IBPL3(x);
  ISBL (x);
}

// BipBip Decryption
void BipBipDec(bool x[24], bool drk[12][24]) {
  KAD(x, drk[0]); RFS(x);
  KAD(x, drk[1]); RFS(x);
  KAD(x, drk[2]); RFS(x);
  KAD(x, drk[3]); RFC(x);
  KAD(x, drk[4]); RFC(x);
  KAD(x, drk[5]); RFC(x);
  KAD(x, drk[6]); RFC(x);
  KAD(x, drk[7]); RFC(x);
  KAD(x, drk[8]); RFS(x);
  KAD(x, drk[9]); RFS(x);
  KAD(x,drk[10]); RFS(x);
  KAD(x,drk[11]);
}

// BipBip Encryption
void BipBipEnc(bool x[24], bool drk[12][24]) {
  KAD(x,drk[11]); IRFS(x);
  KAD(x,drk[10]); IRFS(x);
  KAD(x, drk[9]); IRFS(x);
  KAD(x, drk[8]); IRFC(x);
  KAD(x, drk[7]); IRFC(x);
  KAD(x, drk[6]); IRFC(x);
  KAD(x, drk[5]); IRFC(x);
  KAD(x, drk[4]); IRFC(x);
  KAD(x, drk[3]); IRFS(x);
  KAD(x, drk[2]); IRFS(x);
  KAD(x, drk[1]); IRFS(x);
  KAD(x, drk[0]); 
}

// transforming 24-bit block to boolean vector
void Word2Bits(block_word X, bool x[24]) {
  for (sint i = 0; i < 24; i++)
    x[i] = (X >> i) & 1;
}

// transforming boolean vector to 24-bit block
void Bits2Word(block_word &X, bool x[24]) {
  X = 0;
  for (sint i = 23; i; i--) {
    X ^= x[i];
    X <<= 1;
  }
  X ^= x[0];
}

////////////////////////////////////////////////////////////////////////////////////////////////////

// Chi Layer 
void CHI(bool x[53]) {
  bool y[53];
  for (sint i = 0; i < 51; i++)
    y[i] = x[i] ^ ((!x[i + 1]) & x[i + 2]);
  y[51] = x[51] ^ ((!x[52]) & x[0]);
  y[52] = x[52] ^ ((!x[ 0]) & x[1]);
  for (sint i = 0; i < 53; i++)
    x[i] = y[i];
}

// Linear Mixing Layer in Tweak Path: theta_t
void LML2(bool x[53]) {
  bool y[53];
  for (sint i = 0; i < 53; i++)
    y[i] = x[i] ^ x[(i + 1) % 53] ^ x[(i + 8) % 53];
  for (sint i = 0; i < 53; i++)
    x[i] = y[i];
}

// Linear Mixing Layer in Tweak Path: theta_p
void LML3(bool x[53]) {
  for (sint i = 0; i < 52; i++)
    x[i] ^= x[i + 1];
}

// Bit-Permutation with PI4
void BPL4(bool x[53]) {
  bool y[53];
  for (sint i = 0; i < 53; i++)
    y[i] = x[PI4[i]];
  for (sint i = 0; i < 53; i++)
    x[i] = y[i];
}

// Bit-Permutation with PI5
void BPL5(bool x[53]) {
  bool y[53];
  for (sint i = 0; i < 53; i++)
    y[i] = x[PI5[i]];
  for (sint i = 0; i < 53; i++)
    x[i] = y[i];
}

// Key Addition Layer in Tweak Path
void KAT(bool x[53], bool trk[53]) {
  for (sint i = 0; i < 53; i++)
    x[i] ^= trk[i];
}

// Round Key Ectraction E0
void RKE0(bool x[53], bool drk[24]) {
  sint j = 0;
  for (sint i = 0; i < 24; i++) {
    drk[i] = x[j++]; j++;
  }
}

// Round Key Ectraction E1
void RKE1(bool x[53], bool drk[24]) {
  sint j = 1;
  for (sint i = 0; i < 24; i++) {
    drk[i] = x[j++]; j++;
  }
}

// Round Function: G Round
void RGC(bool x[53]) {
  BPL4(x);
  LML2(x);
  BPL5(x);
  CHI (x);
}

// Round Function: G' Round
void RGP(bool x[53]) {
  BPL4(x);
  LML3(x);
  BPL5(x);
  CHI (x);
}

// BipBip Tweak Schedule
void TwkSc(bool t[53], bool trk[7][53], bool drk[12][24]) {
  for (sint i = 0; i < 24; i++)
    drk[0][i] = trk[0][i];

  KAT (t, trk[1]);
  CHI (t);
  RKE0(t, drk[1]);
  RKE1(t, drk[2]);
  KAT (t, trk[2]);
  RGC (t);
  RKE0(t, drk[3]);
  RKE1(t, drk[4]);
  KAT (t, trk[3]);
  RGC (t);
  RGP (t);
  RKE0(t, drk[5]);
  KAT (t, trk[4]);
  RGC (t);
  RKE0(t, drk[6]);
  RGP (t);
  RKE0(t, drk[7]);
  KAT (t, trk[5]);
  RGC (t);
  RKE0(t, drk[8]);
  RGP (t);
  RKE0(t, drk[9]);
  KAT (t, trk[6]);
  RGC (t);
  RKE0(t, drk[10]);
  RKE1(t, drk[11]);
}

// Initializing 
void TwkIn(tweak_word T, bool t[53]) {
  sint j = 39;
  for (sint i = 52; i > 12; i--)
    t[i] = ((T >> (j--)) & 1);
  t[12] = 1;
  for (sint i = 0; i < 12; i++)
    t[i] = 0;
}

// BipBip Key Schedule
void KeySc(tweak_word MK[4], bool trk[7][53]) {
  bool mk[256];
  for (sint i = 0; i < 4; i++) {
    sint k = i << 6;
    for (sint j = 0; j < 64; j++)
      mk[k++] = (MK[i] >> j) & 1;
  }
  
  sint k = 1;
  for (sint j = 0; j < 24; j++) {
    k *= 3;
    trk[0][j] = mk[k];
  }

  k = 53;
  for (sint i = 1; i < 7; i++) {
    for (sint j = 0; j < 53; j++)
      trk[i][j] = mk[k++];
  }
}

////////////////////////////////////////////////////////////////////////////////////////////////////

int main() {
  // master key       msb                                                                        lsb
  tweak_word MK[4] = {0x0000000000000001, 0x0000000000000020, 0x0000000000000300, 0x0000000000004000};
  bool trk[7][53];
  KeySc(MK, trk);

  printf("trk[0][0:23] = ");
  for (sint j = 0; j < 24; j++)
    printf("%d", trk[0][j]);
  printf("\n");
  for (sint i = 1; i < 7; i++) {
    printf("trk[%d][0:52] = ", i);
    for (sint j = 0; j < 53; j++)
      printf("%d", trk[i][j]);
    printf("\n");
  }

  tweak_word T = 0x0000000000;
  bool t[53], drk[12][24];
  TwkIn(T, t);

  printf("\ntwkpad[0:52] = ");
  for (sint j = 0; j < 53; j++)
    printf("%d", t[j]);
  printf("\n\n");

  TwkSc(t, trk, drk);

  for (sint i = 0; i < 12; i++) {
    printf("trk[%2d][0:23]= ", i);
    for (sint j = 0; j < 24; j++)
      printf("%d", drk[i][j]);
    printf("\n");
  }

  block_word X = 0; //0x3c52e4;
  bool x[24];
  Word2Bits(X, x);

  printf("\ninput [0:23] = ");
  for (sint j = 0; j < 24; j++)
    printf("%d", x[j]);
  printf(" => %06x\n", X);

  BipBipDec(x, drk);
//BipBipEnc(x, drk);
  Bits2Word(X, x);
 
  printf("output[0:23] = ");
  for (sint j = 0; j < 24; j++)
    printf("%d", x[j]);
  printf(" => %06x\n", X);

  return 0;
}
