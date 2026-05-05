import Uu.BipBip.Cipher

open BitVec

namespace BipBip.C3

/-- The public radix bits that remain visible in the encoded pointer. -/
abbrev Radix := BitVec 6

/-- The high 20 address bits that are protected inside the BipBip payload. -/
abbrev UpperAddr := BitVec 20

/-- The 4-bit version field protected inside the BipBip payload. -/
abbrev Version := BitVec 4

/-- The low 34 address bits that remain visible and also serve as tweak material. -/
abbrev LowerAddr := BitVec 34

/-- The 64-bit encoded pointer layout used by the C3 model. -/
abbrev EncodedPointer := BitVec 64

/--
A decoded C3-style pointer.

The payload `upper ++ version` is encrypted by BipBip, while `radix` and `lower` remain public.
-/
structure PlainPointer where
  radix : Radix
  upper : UpperAddr
  version : Version
  lower : LowerAddr
deriving DecidableEq

/-- The 24-bit hidden payload carried inside a pointer. -/
def payload (p : PlainPointer) : Block :=
  p.upper ++ p.version

/-- The 40-bit public tweak derived from the visible pointer fields. -/
def tweak (p : PlainPointer) : Tweak :=
  p.radix ++ p.lower

/-- Reassemble a 64-bit encoded pointer from its public and protected pieces. -/
def packEncodedPointer (radix : Radix) (cipherSlice : Block) (lower : LowerAddr) : EncodedPointer :=
  (radix ++ cipherSlice) ++ lower

/-- Read the visible radix field from an encoded pointer. -/
private def encodedRadix (p : EncodedPointer) : Radix :=
  p.extractLsb' 58 6

/-- Read the protected 24-bit BipBip slice from an encoded pointer. -/
private def encodedSlice (p : EncodedPointer) : Block :=
  p.extractLsb' 34 24

/-- Read the visible low address bits from an encoded pointer. -/
private def encodedLower (p : EncodedPointer) : LowerAddr :=
  p.extractLsb' 0 34

/-- Encode a decoded pointer into its C3-style encrypted representation. -/
def encodePointer (mk : MasterKey) (p : PlainPointer) : EncodedPointer :=
  packEncodedPointer p.radix (BipBip.decrypt mk (tweak p) (payload p)) p.lower

/-- Decode a C3-style encrypted pointer back into its structured representation. -/
def decodePointer (mk : MasterKey) (p : EncodedPointer) : PlainPointer :=
  let radix := encodedRadix p
  let lower := encodedLower p
  let plain := BipBip.encrypt mk (radix ++ lower) (encodedSlice p)
  {
    radix := radix
    upper := plain.extractLsb' 4 20
    version := plain.extractLsb' 0 4
    lower := lower
  }

/-- A concrete sample pointer used for executable round-trip checks. -/
private def samplePointer : PlainPointer :=
  { radix := 0x12#6, upper := 0xabcde#20, version := 0x7#4, lower := 0x123456789#34 }

example : payload samplePointer = 0xabcde7#24 := by native_decide

example : decodePointer sampleKey (encodePointer sampleKey samplePointer) = samplePointer := by
  native_decide

example :
    encodePointer sampleKey (decodePointer sampleKey (encodePointer sampleKey samplePointer)) =
      encodePointer sampleKey samplePointer := by
  native_decide

end BipBip.C3
