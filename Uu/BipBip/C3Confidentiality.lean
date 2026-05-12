import Uu.BipBip.PrimitiveAssumptions

namespace BipBip.C3.Security

open OracleComp

/-- A C3 attacker sees prior encoded pointers and a fresh target encoded pointer. -/
abbrev C3MultiPointerAttacker := List EncodedPointer → EncodedPointer → PlainPointer

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
