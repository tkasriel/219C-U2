import Init.Data.BitVec

open BitVec

namespace Uu

/--
Build a bitvector from its least-significant-bit view.

The function `f` is interpreted as providing bit `i`, where `i = 0` is the least-significant bit.
-/
def buildBitVec : (n : Nat) → (Nat → Bool) → BitVec n
  | 0, _ => 0
  | n + 1, f => (buildBitVec n (fun i => f (i + 1))).concat (f 0)

/--
Compute `base ^ exp mod modulus` using repeated multiplication.

This small helper matches the simple arithmetic used by the BipBip reference key schedule.
-/
def powMod (base exp modulus : Nat) : Nat :=
  let rec go (e acc : Nat) :=
    match e with
    | 0 => acc % modulus
    | e + 1 => go e ((acc * base) % modulus)
  go exp 1

/--
Permute the least-significant-bit indexing of a bitvector.

The array `perm` gives, for each output bit position `i`, which input bit position to read.
-/
def permuteBits (perm : Array Nat) (x : BitVec n) : BitVec n :=
  buildBitVec n (fun i => x.getLsbD (perm[i]!))

@[simp] theorem getLsbD_buildBitVec_zero (f : Nat → Bool) :
    (buildBitVec 0 f).getLsbD i = false := by
  simp [buildBitVec]

@[simp] theorem getLsbD_buildBitVec {n : Nat} (f : Nat → Bool) (i : Nat) :
    (buildBitVec n f).getLsbD i = (decide (i < n) && f i) := by
  induction n generalizing f i with
  | zero =>
      simp [buildBitVec]
  | succ n ih =>
      cases i with
      | zero =>
          simp [buildBitVec]
      | succ i =>
          simp [buildBitVec, ih]

end Uu
