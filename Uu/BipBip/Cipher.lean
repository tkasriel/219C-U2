import Uu.BitVecUtils

open BitVec

namespace BipBip

/-
A literal Lean port of the BipBip reference implementation.

Conventions match the C++ reference:
* bit `0` is the least-significant bit
* round-key additions are XORs
* tweak/key-schedule indexing follows the `uint8_t` wraparound behavior from the C++ code
-/

/-- A BipBip data block. -/
abbrev Block := BitVec 24

/-- The public tweak bits used by the C3-style embedding. -/
abbrev Tweak := BitVec 40

/-- Internal 53-bit tweak state used by the reference schedule. -/
abbrev TweakState := BitVec 53

/-- A 24-bit round key for the data path. -/
abbrev DataRoundKey := BitVec 24

/-- A 53-bit round key for the tweak path. -/
abbrev TweakRoundKey := BitVec 53

/-- The 256-bit BipBip master key. -/
abbrev MasterKey := BitVec 256

/-- The reference BipBip 6-bit S-box table. -/
private def bbb : Array (BitVec 6) :=
  #[0x00#6, 0x01#6, 0x02#6, 0x03#6, 0x04#6, 0x06#6, 0x3e#6, 0x3c#6,
    0x08#6, 0x11#6, 0x0e#6, 0x17#6, 0x2b#6, 0x33#6, 0x35#6, 0x2d#6,
    0x19#6, 0x1c#6, 0x09#6, 0x0c#6, 0x15#6, 0x13#6, 0x3d#6, 0x3b#6,
    0x31#6, 0x2c#6, 0x25#6, 0x38#6, 0x3a#6, 0x26#6, 0x36#6, 0x2a#6,
    0x34#6, 0x1d#6, 0x37#6, 0x1e#6, 0x30#6, 0x1a#6, 0x0b#6, 0x21#6,
    0x2e#6, 0x1f#6, 0x29#6, 0x18#6, 0x0f#6, 0x3f#6, 0x10#6, 0x20#6,
    0x28#6, 0x05#6, 0x39#6, 0x14#6, 0x24#6, 0x0a#6, 0x0d#6, 0x23#6,
    0x12#6, 0x27#6, 0x07#6, 0x32#6, 0x1b#6, 0x2f#6, 0x16#6, 0x22#6]

/-- The inverse of `bbb`. -/
private def ibbb : Array (BitVec 6) :=
  #[0x00#6, 0x01#6, 0x02#6, 0x03#6, 0x04#6, 0x31#6, 0x05#6, 0x3a#6,
    0x08#6, 0x12#6, 0x35#6, 0x26#6, 0x13#6, 0x36#6, 0x0a#6, 0x2c#6,
    0x2e#6, 0x09#6, 0x38#6, 0x15#6, 0x33#6, 0x14#6, 0x3e#6, 0x0b#6,
    0x2b#6, 0x10#6, 0x25#6, 0x3c#6, 0x11#6, 0x21#6, 0x23#6, 0x29#6,
    0x2f#6, 0x27#6, 0x3f#6, 0x37#6, 0x34#6, 0x1a#6, 0x1d#6, 0x39#6,
    0x30#6, 0x2a#6, 0x1f#6, 0x0c#6, 0x19#6, 0x0f#6, 0x28#6, 0x3d#6,
    0x24#6, 0x18#6, 0x3b#6, 0x0d#6, 0x20#6, 0x0e#6, 0x1e#6, 0x22#6,
    0x1b#6, 0x32#6, 0x1c#6, 0x17#6, 0x07#6, 0x16#6, 0x06#6, 0x2d#6]

/-- Data-path permutation `π₁` from the reference implementation. -/
private def pi1 : Array Nat := #[1, 7, 6, 0, 2, 8, 12, 18, 19, 13, 14, 20, 21, 15, 16, 22, 23, 17, 9, 3, 4, 10, 11, 5]
/-- Data-path permutation `π₂` from the reference implementation. -/
private def pi2 : Array Nat := #[0, 1, 4, 5, 8, 9, 2, 3, 6, 7, 10, 11, 16, 12, 13, 17, 20, 21, 15, 14, 18, 19, 22, 23]
/-- Data-path permutation `π₃` from the reference implementation. -/
private def pi3 : Array Nat := #[16, 22, 11, 5, 2, 8, 0, 6, 19, 13, 12, 18, 14, 15, 1, 7, 21, 20, 4, 3, 17, 23, 10, 9]

/-- Inverse of `pi1`. -/
private def ipi1 : Array Nat := #[3, 0, 4, 19, 20, 23, 2, 1, 5, 18, 21, 22, 6, 9, 10, 13, 14, 17, 7, 8, 11, 12, 15, 16]
/-- Inverse of `pi2`. -/
private def ipi2 : Array Nat := #[0, 1, 6, 7, 2, 3, 8, 9, 4, 5, 10, 11, 13, 14, 19, 18, 12, 15, 20, 21, 16, 17, 22, 23]
/-- Inverse of `pi3`. -/
private def ipi3 : Array Nat := #[6, 14, 4, 19, 18, 3, 7, 15, 5, 23, 22, 2, 10, 9, 12, 13, 0, 20, 11, 8, 17, 16, 1, 21]

/-- Tweak-path permutation `π₄`. -/
private def pi4 : Array Nat := #[0, 13, 26, 39, 52, 12, 25, 38, 51, 11, 24, 37, 50, 10, 23, 36, 49, 9, 22, 35, 48, 8, 21, 34, 47, 7, 20, 33, 46, 6, 19, 32, 45, 5, 18, 31, 44, 4, 17, 30, 43, 3, 16, 29, 42, 2, 15, 28, 41, 1, 14, 27, 40]
/-- Tweak-path permutation `π₅`. -/
private def pi5 : Array Nat := #[0, 11, 22, 33, 44, 2, 13, 24, 35, 46, 4, 15, 26, 37, 48, 6, 17, 28, 39, 50, 8, 19, 30, 41, 52, 10, 21, 32, 43, 1, 12, 23, 34, 45, 3, 14, 25, 36, 47, 5, 16, 27, 38, 49, 7, 18, 29, 40, 51, 9, 20, 31, 42]

/-- Extract the `j`-th 6-bit word from a 24-bit block, counting from the least-significant side. -/
private def word6 (x : Block) (j : Nat) : BitVec 6 :=
  x.extractLsb' (6 * j) 6

/-- Apply the BipBip S-box to a 6-bit word. -/
private def sbox6 (x : BitVec 6) : BitVec 6 :=
  bbb[x.toNat]!

/-- Apply the inverse BipBip S-box to a 6-bit word. -/
private def invSbox6 (x : BitVec 6) : BitVec 6 :=
  ibbb[x.toNat]!

/-- The S-box layer on the 24-bit data path. -/
private def sbl (x : Block) : Block :=
  sbox6 (word6 x 3) ++ sbox6 (word6 x 2) ++ sbox6 (word6 x 1) ++ sbox6 (word6 x 0)

/-- The inverse S-box layer on the 24-bit data path. -/
private def isbl (x : Block) : Block :=
  invSbox6 (word6 x 3) ++ invSbox6 (word6 x 2) ++ invSbox6 (word6 x 1) ++ invSbox6 (word6 x 0)

/-- The linear mixing layer `θ_d` on the 24-bit data path. -/
private def lml1 (x : Block) : Block :=
  Uu.buildBitVec 24 (fun i => x.getLsbD i ^^ x.getLsbD ((i + 2) % 24) ^^ x.getLsbD ((i + 12) % 24))

/-- The inverse of `lml1`. -/
private def ilml1 (x : Block) : Block :=
  Uu.buildBitVec 24 (fun i => x.getLsbD ((i + 8) % 24) ^^ x.getLsbD ((i + 20) % 24) ^^ x.getLsbD ((i + 22) % 24))

/-- Apply `pi1` to a data block. -/
private def bpl1 (x : Block) : Block := Uu.permuteBits pi1 x
/-- Apply `ipi1` to a data block. -/
private def ibpl1 (x : Block) : Block := Uu.permuteBits ipi1 x
/-- Apply `pi2` to a data block. -/
private def bpl2 (x : Block) : Block := Uu.permuteBits pi2 x
/-- Apply `ipi2` to a data block. -/
private def ibpl2 (x : Block) : Block := Uu.permuteBits ipi2 x
/-- Apply `pi3` to a data block. -/
private def bpl3 (x : Block) : Block := Uu.permuteBits pi3 x
/-- Apply `ipi3` to a data block. -/
private def ibpl3 (x : Block) : Block := Uu.permuteBits ipi3 x

/-- XOR a data block with a data-round key. -/
private def kad (x drk : Block) : Block := x ^^^ drk

/-- The BipBip core round `RFC`. -/
private def rfc (x : Block) : Block := bpl2 (lml1 (bpl1 (sbl x)))

/-- The inverse of the BipBip core round `RFC`. -/
private def irfc (x : Block) : Block := isbl (ibpl1 (ilml1 (ibpl2 x)))

/-- The BipBip shell round `RFS`. -/
private def rfs (x : Block) : Block := bpl3 (sbl x)

/-- The inverse of the BipBip shell round `RFS`. -/
private def irfs (x : Block) : Block := isbl (ibpl3 x)

/-- Run BipBip decryption using a precomputed 12-round-key schedule. -/
private def decryptWithRoundKeys (x : Block) (drk : Array DataRoundKey) : Block :=
  let x := rfs (kad x drk[0]!)
  let x := rfs (kad x drk[1]!)
  let x := rfs (kad x drk[2]!)
  let x := rfc (kad x drk[3]!)
  let x := rfc (kad x drk[4]!)
  let x := rfc (kad x drk[5]!)
  let x := rfc (kad x drk[6]!)
  let x := rfc (kad x drk[7]!)
  let x := rfs (kad x drk[8]!)
  let x := rfs (kad x drk[9]!)
  let x := rfs (kad x drk[10]!)
  kad x drk[11]!

/-- Run BipBip encryption using a precomputed 12-round-key schedule. -/
private def encryptWithRoundKeys (x : Block) (drk : Array DataRoundKey) : Block :=
  let x := irfs (kad x drk[11]!)
  let x := irfs (kad x drk[10]!)
  let x := irfs (kad x drk[9]!)
  let x := irfc (kad x drk[8]!)
  let x := irfc (kad x drk[7]!)
  let x := irfc (kad x drk[6]!)
  let x := irfc (kad x drk[5]!)
  let x := irfc (kad x drk[4]!)
  let x := irfs (kad x drk[3]!)
  let x := irfs (kad x drk[2]!)
  let x := irfs (kad x drk[1]!)
  kad x drk[0]!

/-- The `CHI` step in the tweak schedule. -/
private def chi (x : TweakState) : TweakState :=
  Uu.buildBitVec 53 (fun i => x.getLsbD i ^^ ((!x.getLsbD ((i + 1) % 53)) && x.getLsbD ((i + 2) % 53)))

/-- The tweak-path linear layer `θ_t`. -/
private def lml2 (x : TweakState) : TweakState :=
  Uu.buildBitVec 53 (fun i => x.getLsbD i ^^ x.getLsbD ((i + 1) % 53) ^^ x.getLsbD ((i + 8) % 53))

/-- The tweak-path linear layer `θ_p`. -/
private def lml3 (x : TweakState) : TweakState :=
  Uu.buildBitVec 53 (fun i => if i < 52 then x.getLsbD i ^^ x.getLsbD (i + 1) else x.getLsbD 52)

/-- Apply `pi4` to a tweak state. -/
private def bpl4 (x : TweakState) : TweakState := Uu.permuteBits pi4 x
/-- Apply `pi5` to a tweak state. -/
private def bpl5 (x : TweakState) : TweakState := Uu.permuteBits pi5 x
/-- XOR a tweak state with a tweak-round key. -/
private def kat (x trk : TweakState) : TweakState := x ^^^ trk

/-- Extract the even-positioned data-round key bits. -/
private def rke0 (x : TweakState) : DataRoundKey :=
  Uu.buildBitVec 24 (fun i => x.getLsbD (2 * i))

/-- Extract the odd-positioned data-round key bits. -/
private def rke1 (x : TweakState) : DataRoundKey :=
  Uu.buildBitVec 24 (fun i => x.getLsbD (2 * i + 1))

/-- The `G` round in the tweak schedule. -/
private def rgc (x : TweakState) : TweakState := chi (bpl5 (lml2 (bpl4 x)))

/-- The `G'` round in the tweak schedule. -/
private def rgp (x : TweakState) : TweakState := chi (bpl5 (lml3 (bpl4 x)))

/-- Embed the public 40-bit tweak into the 53-bit tweak state expected by BipBip. -/
private def tweakInit (t : Tweak) : TweakState :=
  t ++ (1#1 ++ 0#12)

/-- Match the byte-sized wraparound indexing from the C++ reference key schedule. -/
private def byteWrap (n : Nat) : Nat := n % 256

/-- Derive the BipBip whitening key from the master key. -/
private def whiteningKey (mk : MasterKey) : DataRoundKey :=
  Uu.buildBitVec 24 (fun j =>
    let idx := Uu.powMod 3 (j + 1) 256
    mk.getLsbD idx)

/-- Derive one 53-bit tweak-round key from the master key. -/
private def tweakRoundKey (mk : MasterKey) (i : Nat) : TweakRoundKey :=
  Uu.buildBitVec 53 (fun j => mk.getLsbD (byteWrap (53 * i + j)))

/-- Derive the six tweak-round keys used by the reference schedule. -/
private def tweakRoundKeys (mk : MasterKey) : Array TweakRoundKey :=
  #[tweakRoundKey mk 1, tweakRoundKey mk 2, tweakRoundKey mk 3,
    tweakRoundKey mk 4, tweakRoundKey mk 5, tweakRoundKey mk 6]

/-- Compute the 12 BipBip data-round keys for a given master key and public tweak. -/
private def dataRoundKeys (mk : MasterKey) (tw : Tweak) : Array DataRoundKey :=
  Id.run do
    let wk := whiteningKey mk
    let trk := tweakRoundKeys mk
    let mut t := tweakInit tw
    let mut drk : Array DataRoundKey := #[wk]
    t := chi (kat t trk[0]!)
    drk := drk.push (rke0 t)
    drk := drk.push (rke1 t)
    t := rgc (kat t trk[1]!)
    drk := drk.push (rke0 t)
    drk := drk.push (rke1 t)
    t := rgp (rgc (kat t trk[2]!))
    drk := drk.push (rke0 t)
    t := rgc (kat t trk[3]!)
    drk := drk.push (rke0 t)
    t := rgp t
    drk := drk.push (rke0 t)
    t := rgc (kat t trk[4]!)
    drk := drk.push (rke0 t)
    t := rgp t
    drk := drk.push (rke0 t)
    t := rgc (kat t trk[5]!)
    drk := drk.push (rke0 t)
    drk := drk.push (rke1 t)
    pure drk

/-- BipBip decryption for a 24-bit block under a master key and public tweak. -/
def decrypt (mk : MasterKey) (tw : Tweak) (x : Block) : Block :=
  decryptWithRoundKeys x (dataRoundKeys mk tw)

/-- BipBip encryption for a 24-bit block under a master key and public tweak. -/
def encrypt (mk : MasterKey) (tw : Tweak) (x : Block) : Block :=
  encryptWithRoundKeys x (dataRoundKeys mk tw)

/-- The sample master key from the reference implementation. -/
def sampleKey : MasterKey :=
  BitVec.ofNat 256 ((1 : Nat) + (0x20 <<< 64) + (0x300 <<< 128) + (0x4000 <<< 192))

/-- The all-zero sample tweak from the reference implementation. -/
private def sampleTweak : Tweak := 0

/-- The all-zero sample input block from the reference implementation. -/
private def sampleInput : Block := 0

/-- The reference output for `sampleKey`, `sampleTweak`, and `sampleInput`. -/
private def sampleOutput : Block := 0x3c52e4#24

example : decrypt sampleKey sampleTweak sampleInput = sampleOutput := by native_decide

/-- An additional nontrivial regression-test key. -/
private def sampleKey2 : MasterKey :=
  BitVec.ofNat 256
    ((0x0123456789abcdef : Nat) +
      (0x0f1e2d3c4b5a6978 <<< 64) +
      (0x0011223344556677 <<< 128) +
      (0x8899aabbccddeeff <<< 192))

example : decrypt sampleKey 0x0000000000#40 0x000000#24 = 0x3c52e4#24 := by native_decide
example : decrypt sampleKey 0x0000000000#40 0x000001#24 = 0x445723#24 := by native_decide
example : decrypt sampleKey 0x0000000000#40 0xabcdef#24 = 0x0ddf9a#24 := by native_decide
example : decrypt sampleKey 0x0000000001#40 0x000000#24 = 0x781232#24 := by native_decide
example : decrypt sampleKey 0x123456789a#40 0x654321#24 = 0x8f1dbe#24 := by native_decide
example : decrypt sampleKey 0xffffffffff#40 0xffffff#24 = 0x3c5d9f#24 := by native_decide

example : decrypt sampleKey2 0x0000000000#40 0x000000#24 = 0x301d3c#24 := by native_decide
example : decrypt sampleKey2 0x0000000001#40 0x000001#24 = 0xa66ab3#24 := by native_decide
example : decrypt sampleKey2 0x13579bdf24#40 0x2468ac#24 = 0x198157#24 := by native_decide
example : decrypt sampleKey2 0xffffffffff#40 0xffffff#24 = 0xd5d302#24 := by native_decide

end BipBip
