import Uu.BipBip.PrimitiveAssumptions

namespace BipBip.C3.Security

open OracleComp

/-- A C3 attacker sees prior encoded pointers and a fresh target encoded pointer. -/
abbrev C3MultiPointerAttacker := List EncodedPointer → EncodedPointer → PlainPointer

/-- A tampering function on encoded C3 pointers. -/
abbrev C3Tamperer := List EncodedPointer → EncodedPointer → EncodedPointer

/-- An attacker that tries to predict the hidden payload of a tampered encoded C3 pointer. -/
abbrev C3TamperedPayloadAttacker := List EncodedPointer → EncodedPointer → Block

/--
The attacker `A` cannot recover `target` from the encoder outputs of `history` and `target`
themselves, when the master key is sampled uniformly at random.
-/
def isConfidential
    (enc : MasterKey → PlainPointer → EncodedPointer)
    (A : C3MultiPointerAttacker)
    (history : List PlainPointer)
    (target : PlainPointer) : Prop :=
  (Pr[= true |
      (do
        let mk ← ($ᵗ MasterKey)
        pure (decide (A (history.map (enc mk)) (enc mk target) = target)))]).toReal = 0

/-- Encode the history of a C3 recovery instance under the sampled master key. -/
private def c3EncodedHistory
    (mk : MasterKey) (history : List PlainPointer) : List EncodedPointer :=
  history.map (encodePointer mk)

/--
The C3 multi-pointer plaintext-recovery game.

A random master key is sampled, the attacker receives a history of encoded pointers together with a
fresh target encoded pointer, and succeeds if it reconstructs the full decoded target pointer.
-/
noncomputable def c3RecoveryGame
    (A : C3MultiPointerAttacker)
    (history : List PlainPointer)
    (target : PlainPointer) : ProbComp Bool := by
  classical
  exact do
    let mk ← ($ᵗ MasterKey)
    let seenHistory := c3EncodedHistory mk history
    let targetCipher := encodePointer mk target
    pure (decide (A seenHistory targetCipher = target))

/-- Success probability of a C3 multi-pointer plaintext-recovery attacker. -/
noncomputable def c3RecoverySuccessProbability
    (A : C3MultiPointerAttacker)
    (history : List PlainPointer)
    (target : PlainPointer) : ℝ :=
  (Pr[= true | c3RecoveryGame A history target]).toReal

/-- C3 recovery success probabilities are always nonnegative. -/
theorem c3RecoverySuccessProbability_nonneg
    (A : C3MultiPointerAttacker)
    (history : List PlainPointer)
    (target : PlainPointer) :
    0 ≤ c3RecoverySuccessProbability A history target := by
  unfold c3RecoverySuccessProbability
  exact ENNReal.toReal_nonneg

/--
The encoded target pointer `encodePointer mk target` cannot be used by attacker `A`, together with
the encoded history, to recover the underlying plaintext pointer with nonzero probability.
-/
def encodedPointerPlaintextRecoveryImpossible
    (A : C3MultiPointerAttacker)
    (history : List PlainPointer)
    (target : PlainPointer) : Prop :=
  isConfidential BipBip.C3.encodePointer A history target

/--
The hidden payload carried by a tampered encoded C3 pointer cannot be recovered by attacker `A`
from the encoded history and the tampered pointer with nonzero probability.
-/
def tamperedEncodedPointerPayloadRecoveryImpossible
    (τ : C3Tamperer)
    (A : C3TamperedPayloadAttacker)
    (history : List PlainPointer)
    (target : PlainPointer) : Prop :=
  (Pr[= true |
      (do
        let mk ← ($ᵗ MasterKey)
        let seenHistory := history.map (BipBip.C3.encodePointer mk)
        let seenTarget := BipBip.C3.encodePointer mk target
        let tampered := τ seenHistory seenTarget
        pure (decide (A seenHistory tampered = payload (BipBip.C3.decodePointer mk tampered))))]).toReal = 0

/--
C3 confidentiality in the multi-pointer plaintext-recovery formulation.

No attacker can reconstruct the full decoded target pointer from the observed encoded history and
fresh target encoded pointer with nonzero probability.
-/
def C3RecoveryImpossible : Prop :=
  ∀ (A : C3MultiPointerAttacker)
    (history : List PlainPointer)
    (target : PlainPointer),
    encodedPointerPlaintextRecoveryImpossible A history target

/-- Convert a C3 pointer to the corresponding hidden BipBip sample. -/
private def hiddenSampleOfPointer (p : PlainPointer) : BipBipHiddenSample where
  tweak := tweak p
  plaintext := payload p

/-- Recover the radix bits from a 40-bit C3 tweak. -/
private def tweakRadix (tw : Tweak) : Radix :=
  tw.extractLsb' 34 6

/-- Recover the low address bits from a 40-bit C3 tweak. -/
private def tweakLower (tw : Tweak) : LowerAddr :=
  tw.extractLsb' 0 34

/-- Reconstruct the corresponding C3 pointer from a hidden BipBip sample. -/
private def pointerOfHiddenSample (s : BipBipHiddenSample) : PlainPointer where
  radix := tweakRadix s.tweak
  upper := s.plaintext.extractLsb' 4 20
  version := s.plaintext.extractLsb' 0 4
  lower := tweakLower s.tweak

/-- Recovering the radix bits from the tweak of a pointer yields the original radix. -/
private theorem tweakRadix_tweak (p : PlainPointer) : tweakRadix (tweak p) = p.radix := by
  cases p
  exact BitVec.extractLsb'_append_eq_left

/-- Recovering the low address bits from the tweak of a pointer yields the original lower bits. -/
private theorem tweakLower_tweak (p : PlainPointer) : tweakLower (tweak p) = p.lower := by
  cases p
  exact BitVec.extractLsb'_append_eq_right

/-- Recovering the high address bits from the payload of a pointer yields the original upper bits. -/
private theorem upper_payload (p : PlainPointer) : (payload p).extractLsb' 4 20 = p.upper := by
  cases p
  exact BitVec.extractLsb'_append_eq_left

/-- Recovering the version bits from the payload of a pointer yields the original version. -/
private theorem version_payload (p : PlainPointer) : (payload p).extractLsb' 0 4 = p.version := by
  cases p
  exact BitVec.extractLsb'_append_eq_right

/-- `pointerOfHiddenSample` is a left inverse of `hiddenSampleOfPointer`. -/
private theorem pointerOfHiddenSample_hiddenSampleOfPointer (p : PlainPointer) :
    pointerOfHiddenSample (hiddenSampleOfPointer p) = p := by
  cases p
  simp [pointerOfHiddenSample, hiddenSampleOfPointer, tweakRadix_tweak, tweakLower_tweak,
    upper_payload, version_payload]

/-- Converting a C3 pointer to a hidden BipBip sample is injective. -/
private theorem hiddenSampleOfPointer_injective :
    Function.Injective hiddenSampleOfPointer := by
  intro p q h
  simpa [pointerOfHiddenSample_hiddenSampleOfPointer p, pointerOfHiddenSample_hiddenSampleOfPointer q]
    using congrArg pointerOfHiddenSample h

/-- Translate a C3 history to the corresponding BipBip history. -/
private def bipbipHistoryOfC3 (history : List PlainPointer) : List BipBipHiddenSample :=
  history.map hiddenSampleOfPointer

/-- Translate a C3 target pointer to the corresponding BipBip target sample. -/
private def bipbipTargetOfC3 (target : PlainPointer) : BipBipHiddenSample :=
  hiddenSampleOfPointer target

/-- Rewrap a BipBip seen sample as the corresponding encoded C3 pointer fragment. -/
private def encodeSeenSample (s : BipBipSeenSample) : EncodedPointer :=
  packEncodedPointer (tweakRadix s.tweak) s.ciphertext (tweakLower s.tweak)

/-- Repackage an encoded C3 pointer as the corresponding observed BipBip sample. -/
private def seenSampleOfEncodedPointer (p : EncodedPointer) : BipBipSeenSample where
  tweak := encodedRadix p ++ encodedLower p
  ciphertext := encodedSlice p

/-- Repackaging an observed BipBip sample as an encoded C3 pointer and back is the identity. -/
private theorem seenSampleOfEncodedPointer_encodeSeenSample (s : BipBipSeenSample) :
    seenSampleOfEncodedPointer (encodeSeenSample s) = s := by
  cases s with
  | mk tweak ciphertext =>
      simp [seenSampleOfEncodedPointer, encodeSeenSample, encodedRadix_packEncodedPointer,
        encodedSlice_packEncodedPointer, encodedLower_packEncodedPointer, tweakRadix, tweakLower]
      simpa using (BitVec.extractLsb'_append_extractLsb' (x := tweak) (len := 34) (w := 6))

/-- Repackaging an encoded C3 pointer as an observed BipBip sample and back is the identity. -/
private theorem encodeSeenSample_seenSampleOfEncodedPointer (p : EncodedPointer) :
    encodeSeenSample (seenSampleOfEncodedPointer p) = p := by
  calc
    encodeSeenSample (seenSampleOfEncodedPointer p)
      = packEncodedPointer
          (tweakRadix (encodedRadix p ++ encodedLower p))
          (encodedSlice p)
          (tweakLower (encodedRadix p ++ encodedLower p)) := by
            rfl
    _ = packEncodedPointer (encodedRadix p) (encodedSlice p) (encodedLower p) := by
          rw [show tweakRadix (encodedRadix p ++ encodedLower p) = encodedRadix p by
                exact BitVec.extractLsb'_append_eq_left,
              show tweakLower (encodedRadix p ++ encodedLower p) = encodedLower p by
                exact BitVec.extractLsb'_append_eq_right]
    _ = p := packEncodedPointer_encoded_fields p

/-- Rewrapping observed BipBip samples as encoded pointers is injective. -/
private theorem encodeSeenSample_injective : Function.Injective encodeSeenSample := by
  intro s₁ s₂ h
  simpa [seenSampleOfEncodedPointer_encodeSeenSample s₁, seenSampleOfEncodedPointer_encodeSeenSample s₂]
    using congrArg seenSampleOfEncodedPointer h

/-- Rewrapping an observed hidden sample yields exactly the corresponding encoded C3 pointer. -/
private theorem encodeSeenSample_observe_hiddenSampleOfPointer
    (mk : MasterKey) (p : PlainPointer) :
    encodeSeenSample (BipBipHiddenSample.observe mk (hiddenSampleOfPointer p)) = encodePointer mk p := by
  simp [encodeSeenSample, BipBipHiddenSample.observe, hiddenSampleOfPointer, encodePointer,
    tweakRadix_tweak, tweakLower_tweak]

/-- Wrapping a list of observed hidden samples yields the corresponding encoded C3 history. -/
private theorem wrap_hidden_history_eq_encodedHistory
    (mk : MasterKey) (hs : List PlainPointer) :
    (hs.map hiddenSampleOfPointer |>.map (BipBipHiddenSample.observe mk) |>.map encodeSeenSample) =
      hs.map (encodePointer mk) := by
  induction hs with
  | nil =>
      rfl
  | cons p ps ih =>
      simp [encodeSeenSample_observe_hiddenSampleOfPointer]

/-- The wrapped BipBip history for a translated C3 instance is exactly the encoded C3 history. -/
private theorem observedHistory_wrapped_eq_encodedHistory
    (mk : MasterKey) (history : List PlainPointer) :
    (bipbipObservedHistory mk (bipbipHistoryOfC3 history)).map encodeSeenSample = c3EncodedHistory mk history := by
  simpa [bipbipObservedHistory, c3EncodedHistory, bipbipHistoryOfC3]
    using wrap_hidden_history_eq_encodedHistory mk history

/-- The wrapped BipBip target ciphertext for a translated C3 instance is the encoded C3 target. -/
private theorem wrapped_target_eq_encodedTarget
    (mk : MasterKey) (target : PlainPointer) :
    packEncodedPointer
        (tweakRadix (bipbipTargetOfC3 target).tweak)
        (BipBip.encrypt mk (bipbipTargetOfC3 target).tweak (bipbipTargetOfC3 target).plaintext)
        (tweakLower (bipbipTargetOfC3 target).tweak) =
      encodePointer mk target := by
  simpa [bipbipTargetOfC3] using encodeSeenSample_observe_hiddenSampleOfPointer mk target

/--
Under a fixed master key, successful C3 recovery implies successful BipBip payload recovery on the
translated instance.
-/
private theorem payloadPredictor_success_of_c3_success
    (A : C3MultiPointerAttacker) (history : List PlainPointer) (target : PlainPointer) (mk : MasterKey)
    (hsucc : A (c3EncodedHistory mk history) (encodePointer mk target) = target) :
    payload
        (A ((bipbipObservedHistory mk (bipbipHistoryOfC3 history)).map encodeSeenSample)
          (packEncodedPointer (tweakRadix (bipbipTargetOfC3 target).tweak)
            (BipBip.encrypt mk (bipbipTargetOfC3 target).tweak (bipbipTargetOfC3 target).plaintext)
            (tweakLower (bipbipTargetOfC3 target).tweak))) =
      (bipbipTargetOfC3 target).plaintext := by
  have hPayload : payload (A (c3EncodedHistory mk history) (encodePointer mk target)) = payload target := by
    simpa using congrArg payload hsucc
  calc
    payload
        (A ((bipbipObservedHistory mk (bipbipHistoryOfC3 history)).map encodeSeenSample)
          (packEncodedPointer (tweakRadix (bipbipTargetOfC3 target).tweak)
            (BipBip.encrypt mk (bipbipTargetOfC3 target).tweak (bipbipTargetOfC3 target).plaintext)
            (tweakLower (bipbipTargetOfC3 target).tweak)))
      = payload (A (c3EncodedHistory mk history) (encodePointer mk target)) := by
          rw [observedHistory_wrapped_eq_encodedHistory mk history, wrapped_target_eq_encodedTarget mk target]
    _ = payload target := hPayload
    _ = (bipbipTargetOfC3 target).plaintext := by
          rfl

/--
Extract a BipBip plaintext predictor from a C3 recovery attacker by rewrapping every observed
`(tweak, ciphertext)` pair as an encoded pointer.
-/
private def payloadPredictor
    (A : C3MultiPointerAttacker) : BipBipMultiChosenTweakAttacker :=
  fun history targetTweak targetCipher =>
    payload (A (history.map encodeSeenSample) (packEncodedPointer (tweakRadix targetTweak)
      targetCipher (tweakLower targetTweak)))

/-- Translate a C3 tampering function to the corresponding tampering function on BipBip samples. -/
private def bipbipTampererOfC3 (τ : C3Tamperer) : BipBipTamperer :=
  fun history target =>
    seenSampleOfEncodedPointer (τ (history.map encodeSeenSample) (encodeSeenSample target))

/-- Translate a C3 hidden-payload attacker to the corresponding BipBip attacker. -/
private def bipbipTamperedPayloadAttackerOfC3
    (A : C3TamperedPayloadAttacker) : BipBipTamperedPayloadAttacker :=
  fun history target =>
    A (history.map encodeSeenSample) (encodeSeenSample target)

/-- A modifying C3 tamperer induces a modifying BipBip tamperer after rewrapping. -/
private theorem bipbipTampererOfC3_modifies
    (τ : C3Tamperer)
    (hτ : ∀ (history : List EncodedPointer) (target : EncodedPointer), τ history target ≠ target) :
    ∀ (history : List BipBipSeenSample) (target : BipBipSeenSample),
      bipbipTampererOfC3 τ history target ≠ target := by
  intro history target hEq
  apply hτ (history.map encodeSeenSample) (encodeSeenSample target)
  have h' := congrArg encodeSeenSample hEq
  simpa [bipbipTampererOfC3, seenSampleOfEncodedPointer_encodeSeenSample,
    encodeSeenSample_seenSampleOfEncodedPointer] using h'

/-- Pointwise equivalence between the C3 and BipBip tampered hidden-payload success predicates. -/
private theorem tampered_payload_success_iff
    (τ : C3Tamperer)
    (A : C3TamperedPayloadAttacker)
    (history : List PlainPointer)
    (target : PlainPointer)
    (mk : MasterKey) :
    let seenHistory := history.map (encodePointer mk)
    let seenTarget := encodePointer mk target
    let tampered := τ seenHistory seenTarget
    A seenHistory tampered = payload (decodePointer mk tampered) ↔
      let bipHist := bipbipObservedHistory mk (bipbipHistoryOfC3 history)
      let bipTarget := BipBipHiddenSample.observe mk (bipbipTargetOfC3 target)
      let tamperedSeen := bipbipTampererOfC3 τ bipHist bipTarget
      bipbipTamperedPayloadAttackerOfC3 A bipHist tamperedSeen =
        BipBip.decrypt mk tamperedSeen.tweak tamperedSeen.ciphertext := by
  dsimp
  have hHist :
      (bipbipObservedHistory mk (bipbipHistoryOfC3 history)).map encodeSeenSample =
        history.map (encodePointer mk) :=
    observedHistory_wrapped_eq_encodedHistory mk history
  have hTarget :
      encodeSeenSample (BipBipHiddenSample.observe mk (bipbipTargetOfC3 target)) =
        encodePointer mk target := by
    simpa [bipbipTargetOfC3] using encodeSeenSample_observe_hiddenSampleOfPointer mk target
  let tampered := τ (history.map (encodePointer mk)) (encodePointer mk target)
  have hSeen :
      bipbipTampererOfC3 τ (bipbipObservedHistory mk (bipbipHistoryOfC3 history))
        (BipBipHiddenSample.observe mk (bipbipTargetOfC3 target)) =
          seenSampleOfEncodedPointer tampered := by
    simp [bipbipTampererOfC3, tampered, hHist, hTarget]
  have hPayload :
      payload (decodePointer mk tampered) =
        BipBip.decrypt mk (seenSampleOfEncodedPointer tampered).tweak
          (seenSampleOfEncodedPointer tampered).ciphertext := by
    simpa [seenSampleOfEncodedPointer] using (payload_decodePointer_eq mk tampered)
  constructor <;> intro h
  · rw [hSeen]
    simpa [bipbipTamperedPayloadAttackerOfC3, tampered, hHist, hPayload,
      encodeSeenSample_seenSampleOfEncodedPointer] using h
  · rw [hSeen] at h
    simpa [bipbipTamperedPayloadAttackerOfC3, tampered, hHist, hPayload,
      encodeSeenSample_seenSampleOfEncodedPointer] using h

/--
Success in the C3 recovery game implies success of the induced BipBip multi-chosen-tweak payload
predictor on the translated instance.
-/
theorem c3RecoverySuccessProbability_le_bipbip
    (A : C3MultiPointerAttacker) (history : List PlainPointer) (target : PlainPointer) :
    c3RecoverySuccessProbability A history target ≤
      bipbipObservedCipherPredictionSuccessProbability (payloadPredictor A) (bipbipHistoryOfC3 history) (bipbipTargetOfC3 target) := by
  have hprob : Pr[= true | c3RecoveryGame A history target] ≤
      Pr[= true | bipbipObservedCipherPredictionGame (payloadPredictor A) (bipbipHistoryOfC3 history) (bipbipTargetOfC3 target)] := by
    classical
    have hc3 : Pr[= true | c3RecoveryGame A history target] =
        Pr[fun b => b = true | c3RecoveryGame A history target] := by
      simpa using
        (probOutput_true_eq_probEvent (mx := c3RecoveryGame A history target) (p := fun b => b = true)).symm
    have hbip :
        Pr[= true | bipbipObservedCipherPredictionGame (payloadPredictor A) (bipbipHistoryOfC3 history) (bipbipTargetOfC3 target)] =
          Pr[fun b => b = true |
            bipbipObservedCipherPredictionGame (payloadPredictor A) (bipbipHistoryOfC3 history) (bipbipTargetOfC3 target)] := by
      simpa using
        (probOutput_true_eq_probEvent
          (mx := bipbipObservedCipherPredictionGame (payloadPredictor A) (bipbipHistoryOfC3 history) (bipbipTargetOfC3 target))
          (p := fun b => b = true)).symm
    rw [hc3, hbip]
    unfold c3RecoveryGame bipbipObservedCipherPredictionGame payloadPredictor
    change Pr[fun b => b = true |
      (fun mk => decide (A (history.map (encodePointer mk)) (encodePointer mk target) = target))
        <$> ($ᵗ MasterKey)] ≤
      Pr[fun b => b = true |
        (fun mk =>
          decide (payload
            (A ((bipbipObservedHistory mk (bipbipHistoryOfC3 history)).map encodeSeenSample)
              (packEncodedPointer (tweakRadix (bipbipTargetOfC3 target).tweak)
                (BipBip.encrypt mk (bipbipTargetOfC3 target).tweak
                  (bipbipTargetOfC3 target).plaintext)
                (tweakLower (bipbipTargetOfC3 target).tweak)))
            = (bipbipTargetOfC3 target).plaintext))
          <$> ($ᵗ MasterKey)]
    rw [probEvent_map, probEvent_map]
    apply probEvent_mono
    intro mk _ hsucc
    have hEq : A (history.map (encodePointer mk)) (encodePointer mk target) = target := by
      simpa using hsucc
    have hs : payload
        (A ((bipbipObservedHistory mk (bipbipHistoryOfC3 history)).map encodeSeenSample)
          (packEncodedPointer (tweakRadix (bipbipTargetOfC3 target).tweak)
            (BipBip.encrypt mk (bipbipTargetOfC3 target).tweak (bipbipTargetOfC3 target).plaintext)
            (tweakLower (bipbipTargetOfC3 target).tweak))) =
        (bipbipTargetOfC3 target).plaintext :=
      payloadPredictor_success_of_c3_success A history target mk (by simpa [c3EncodedHistory] using hEq)
    simpa [bipbipTargetOfC3, hiddenSampleOfPointer] using hs
  unfold c3RecoverySuccessProbability bipbipObservedCipherPredictionSuccessProbability
  exact (ENNReal.toReal_le_toReal probOutput_ne_top probOutput_ne_top).mpr hprob

/--
If tampered observed-cipher BipBip plaintext recovery succeeds with probability `0`, then tampered
encoded C3 pointers do not reveal their hidden payloads with nonzero probability either.
-/
theorem tamperedEncodedPointerPayloadRecoveryImpossible_of_bipbipTamperedObservedCipherPredictionImpossible
    (h : BipBipTamperedObservedCipherPredictionImpossible) :
    ∀ (τ : C3Tamperer)
      (hτ : ∀ (history : List EncodedPointer) (target : EncodedPointer), τ history target ≠ target)
      (A : C3TamperedPayloadAttacker)
      (history : List PlainPointer)
      (target : PlainPointer),
      tamperedEncodedPointerPayloadRecoveryImpossible τ A history target := by
  intro τ hτ A history target
  unfold tamperedEncodedPointerPayloadRecoveryImpossible
  have hEq :
      (Pr[= true |
        (do
          let mk ← ($ᵗ MasterKey)
          let seenHistory := history.map (BipBip.C3.encodePointer mk)
          let seenTarget := BipBip.C3.encodePointer mk target
          let tampered := τ seenHistory seenTarget
          pure (decide (A seenHistory tampered = payload (BipBip.C3.decodePointer mk tampered))))]).toReal =
      (Pr[= true |
        bipbipTamperedObservedCipherPredictionGame
          (bipbipTampererOfC3 τ)
          (bipbipTamperedPayloadAttackerOfC3 A)
          (bipbipHistoryOfC3 history)
          (bipbipTargetOfC3 target)]).toReal := by
    apply congrArg ENNReal.toReal
    refine probOutput_bind_congr' ($ᵗ MasterKey) true ?_
    intro mk
    have hiff := tampered_payload_success_iff τ A history target mk
    by_cases hs :
        let seenHistory := history.map (BipBip.C3.encodePointer mk)
        let seenTarget := BipBip.C3.encodePointer mk target
        let tampered := τ seenHistory seenTarget
        A seenHistory tampered = payload (BipBip.C3.decodePointer mk tampered)
    · have hs' :
          let bipHist := bipbipObservedHistory mk (bipbipHistoryOfC3 history)
          let bipTarget := BipBipHiddenSample.observe mk (bipbipTargetOfC3 target)
          let tamperedSeen := bipbipTampererOfC3 τ bipHist bipTarget
          bipbipTamperedPayloadAttackerOfC3 A bipHist tamperedSeen =
            BipBip.decrypt mk tamperedSeen.tweak tamperedSeen.ciphertext := hiff.mp hs
      simp [hs, hs']
    · have hs' :
          ¬
            (let bipHist := bipbipObservedHistory mk (bipbipHistoryOfC3 history)
             let bipTarget := BipBipHiddenSample.observe mk (bipbipTargetOfC3 target)
             let tamperedSeen := bipbipTampererOfC3 τ bipHist bipTarget
             bipbipTamperedPayloadAttackerOfC3 A bipHist tamperedSeen =
               BipBip.decrypt mk tamperedSeen.tweak tamperedSeen.ciphertext) := by
            intro h'
            exact hs (hiff.mpr h')
      simp [hs, hs']
  rw [hEq]
  exact h (bipbipTampererOfC3 τ) (bipbipTampererOfC3_modifies τ hτ)
    (bipbipTamperedPayloadAttackerOfC3 A) (bipbipHistoryOfC3 history) (bipbipTargetOfC3 target)

/--
If multi-chosen-tweak BipBip plaintext recovery succeeds with probability `0`, then
`BipBip.C3.encodePointer` is confidential against full-pointer recovery with probability `0` as
well.
-/
theorem c3RecoveryImpossible_of_bipbipObservedCipherPredictionImpossible
    (h : BipBipObservedCipherPredictionImpossible) :
    ∀ (A : C3MultiPointerAttacker)
      (history : List PlainPointer)
      (target : PlainPointer),
      isConfidential BipBip.C3.encodePointer A history target := by
  intro A history target
  unfold isConfidential
  have hEq : c3RecoverySuccessProbability A history target =
      (Pr[= true |
        (do
          let mk ← ($ᵗ MasterKey)
          pure
            (decide
              (A (history.map (BipBip.C3.encodePointer mk))
                (BipBip.C3.encodePointer mk target) = target)))]).toReal := by
    rfl
  have hle :
      c3RecoverySuccessProbability A history target ≤
        bipbipObservedCipherPredictionSuccessProbability (payloadPredictor A) (bipbipHistoryOfC3 history) (bipbipTargetOfC3 target) :=
    c3RecoverySuccessProbability_le_bipbip A history target
  rw [h (payloadPredictor A) (bipbipHistoryOfC3 history) (bipbipTargetOfC3 target)] at hle
  have hzero : c3RecoverySuccessProbability A history target = 0 :=
    le_antisymm hle (c3RecoverySuccessProbability_nonneg A history target)
  rw [← hEq]
  exact hzero

/-- The explicit confidentiality theorem packaged back into the named C3 security proposition. -/
theorem c3RecoveryImpossible
    (h : BipBipObservedCipherPredictionImpossible) :
    C3RecoveryImpossible :=
  by
    intro A history target
    exact c3RecoveryImpossible_of_bipbipObservedCipherPredictionImpossible h A history target


end BipBip.C3.Security
