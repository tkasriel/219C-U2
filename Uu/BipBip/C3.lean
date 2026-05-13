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
deriving DecidableEq, Repr

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
def encodedRadix (p : EncodedPointer) : Radix :=
  p.extractLsb' 58 6

/-- Read the protected 24-bit BipBip slice from an encoded pointer. -/
def encodedSlice (p : EncodedPointer) : Block :=
  p.extractLsb' 34 24

/-- Read the visible low address bits from an encoded pointer. -/
def encodedLower (p : EncodedPointer) : LowerAddr :=
  p.extractLsb' 0 34

/-- Encode a decoded pointer into its C3-style encrypted representation. -/
def encodePointer (mk : MasterKey) (p : PlainPointer) : EncodedPointer :=
  packEncodedPointer p.radix (BipBip.encrypt mk (tweak p) (payload p)) p.lower

/-- Decode a C3-style encrypted pointer back into its structured representation. -/
def decodePointer (mk : MasterKey) (p : EncodedPointer) : PlainPointer :=
  let radix := encodedRadix p
  let lower := encodedLower p
  let plain := BipBip.decrypt mk (radix ++ lower) (encodedSlice p)
  {
    radix := radix
    upper := plain.extractLsb' 4 20
    version := plain.extractLsb' 0 4
    lower := lower
  }

/-- Extracting the radix field from a packed encoded pointer returns the original radix. -/
theorem encodedRadix_packEncodedPointer
    (radix : Radix) (cipherSlice : Block) (lower : LowerAddr) :
    encodedRadix (packEncodedPointer radix cipherSlice lower) = radix := by
  calc
    encodedRadix (packEncodedPointer radix cipherSlice lower)
      = (radix ++ cipherSlice).extractLsb' 24 6 := by
          simpa [encodedRadix, packEncodedPointer, Nat.add_assoc] using
            (BitVec.extractLsb'_append_eq_of_le
              (xhi := radix ++ cipherSlice) (xlo := lower) (start := 58) (len := 6) (by omega))
    _ = radix := by
          simpa using (BitVec.extractLsb'_append_eq_left (a := radix) (b := cipherSlice))

/-- Extracting the protected slice from a packed encoded pointer returns the original slice. -/
theorem encodedSlice_packEncodedPointer
    (radix : Radix) (cipherSlice : Block) (lower : LowerAddr) :
    encodedSlice (packEncodedPointer radix cipherSlice lower) = cipherSlice := by
  calc
    encodedSlice (packEncodedPointer radix cipherSlice lower)
      = (radix ++ cipherSlice).extractLsb' 0 24 := by
          simpa [encodedSlice, packEncodedPointer, Nat.add_assoc] using
            (BitVec.extractLsb'_append_eq_of_le
              (xhi := radix ++ cipherSlice) (xlo := lower) (start := 34) (len := 24) (by omega))
    _ = cipherSlice := by
          simpa using (BitVec.extractLsb'_append_eq_right (a := radix) (b := cipherSlice))

/-- Extracting the low address field from a packed encoded pointer returns the original lower bits. -/
theorem encodedLower_packEncodedPointer
    (radix : Radix) (cipherSlice : Block) (lower : LowerAddr) :
    encodedLower (packEncodedPointer radix cipherSlice lower) = lower := by
  simpa [encodedLower, packEncodedPointer, Nat.add_assoc] using
    (BitVec.extractLsb'_append_eq_right (a := radix ++ cipherSlice) (b := lower))

/-- Repacking the three extracted fields of an encoded pointer yields the original pointer. -/
theorem packEncodedPointer_encoded_fields (p : EncodedPointer) :
    packEncodedPointer (encodedRadix p) (encodedSlice p) (encodedLower p) = p := by
  change ((p.extractLsb' 58 6 ++ p.extractLsb' 34 24) ++ p.extractLsb' 0 34) = p
  have hmid : p.extractLsb' 58 6 ++ p.extractLsb' 34 24 = p.extractLsb' 34 30 := by
    simpa using
      (BitVec.extractLsb'_append_extractLsb'_eq_extractLsb'
        (x := p) (start₁ := 34) (len₁ := 24) (start₂ := 58) (len₂ := 6) rfl)
  rw [hmid]
  simpa using (BitVec.extractLsb'_append_extractLsb' (x := p) (len := 34) (w := 30))

/--
The hidden payload recovered by `decodePointer` is exactly the BipBip decryption of the extracted
slice under the extracted tweak.
-/
theorem payload_decodePointer_eq
    (mk : MasterKey) (p : EncodedPointer) :
    payload (decodePointer mk p) =
      BipBip.decrypt mk (encodedRadix p ++ encodedLower p) (encodedSlice p) := by
  let plain := BipBip.decrypt mk (encodedRadix p ++ encodedLower p) (encodedSlice p)
  have hplain : plain.extractLsb' 4 20 ++ plain.extractLsb' 0 4 = plain := by
    simpa [plain] using (BitVec.extractLsb'_append_extractLsb' (x := plain) (len := 4) (w := 20))
  simpa [decodePointer, payload, plain] using hplain

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
