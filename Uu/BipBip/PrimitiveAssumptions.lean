import Uu.BipBip.C3
import VCVio.CryptoFoundations.SecExp
import VCVio.OracleComp.Constructions.BitVec

namespace BipBip.C3.Security

open OracleComp

/-- A previously observed BipBip ciphertext under a public tweak. -/
structure BipBipSeenSample where
  tweak : Tweak
  ciphertext : Block
deriving DecidableEq, Repr

/-- A hidden BipBip plaintext sample chosen by the attacker before key sampling. -/
structure BipBipHiddenSample where
  tweak : Tweak
  plaintext : Block
deriving DecidableEq, Repr

/--
An observed-cipher multi-chosen-tweak BipBip attacker.

The attacker receives a history of previously observed `(tweak, ciphertext)` pairs together with
the fresh target `(tweak, ciphertext)` pair, and attempts to recover the hidden target plaintext.
-/
abbrev BipBipMultiChosenTweakAttacker := List BipBipSeenSample → Tweak → Block → Block

/-- Reveal a hidden BipBip sample under the sampled master key. -/
def BipBipHiddenSample.observe (mk : MasterKey) (s : BipBipHiddenSample) : BipBipSeenSample where
  tweak := s.tweak
  ciphertext := BipBip.encrypt mk s.tweak s.plaintext

/-- The visible history exposed to a BipBip attacker under the sampled master key. -/
def bipbipObservedHistory
    (mk : MasterKey) (history : List BipBipHiddenSample) : List BipBipSeenSample :=
  history.map (BipBipHiddenSample.observe mk)

/--
The multi-chosen-tweak BipBip observed-cipher prediction game.

A random master key is sampled, the attacker receives the observed history together with the fresh
target `(tweak, ciphertext)`, and succeeds if it recovers the hidden target plaintext.
-/
noncomputable def bipbipObservedCipherPredictionGame
    (A : BipBipMultiChosenTweakAttacker)
    (history : List BipBipHiddenSample)
    (target : BipBipHiddenSample) : ProbComp Bool := by
  classical
  exact do
    let mk ← ($ᵗ MasterKey)
    let seenHistory := bipbipObservedHistory mk history
    let targetCipher := BipBip.encrypt mk target.tweak target.plaintext
    pure (decide (A seenHistory target.tweak targetCipher = target.plaintext))

/-- Success probability in the multi-chosen-tweak BipBip observed-cipher recovery game. -/
noncomputable def bipbipObservedCipherPredictionSuccessProbability
    (A : BipBipMultiChosenTweakAttacker)
    (history : List BipBipHiddenSample)
    (target : BipBipHiddenSample) : ℝ :=
  (Pr[= true | bipbipObservedCipherPredictionGame A history target]).toReal

/-- BipBip observed-cipher prediction success probabilities are always nonnegative. -/
theorem bipbipObservedCipherPredictionSuccessProbability_nonneg
    (A : BipBipMultiChosenTweakAttacker)
    (history : List BipBipHiddenSample)
    (target : BipBipHiddenSample) :
    0 ≤ bipbipObservedCipherPredictionSuccessProbability A history target := by
  unfold bipbipObservedCipherPredictionSuccessProbability
  exact ENNReal.toReal_nonneg

/--
Symbolic multi-chosen-tweak secrecy assumption for BipBip.

For the current proof direction we assume exact zero success probability, rather than a concrete
`ε(q,qTi,t)` bound.
-/
def BipBipObservedCipherPredictionImpossible : Prop :=
  ∀ (A : BipBipMultiChosenTweakAttacker)
    (history : List BipBipHiddenSample)
    (target : BipBipHiddenSample),
    bipbipObservedCipherPredictionSuccessProbability A history target = 0

/-- A tampering function on observed BipBip `(tweak, ciphertext)` pairs. -/
abbrev BipBipTamperer := List BipBipSeenSample → BipBipSeenSample → BipBipSeenSample

/--
A BipBip attacker that tries to predict the plaintext underlying a tampered observed ciphertext.
-/
abbrev BipBipTamperedPayloadAttacker := List BipBipSeenSample → BipBipSeenSample → Block

/--
The tampered observed-cipher BipBip prediction game.

A random master key is sampled, the attacker sees the observed history and target sample, a
tampering function rewrites the target observation, and the attacker succeeds if it predicts the
plaintext recovered from that tampered `(tweak, ciphertext)` pair.
-/
noncomputable def bipbipTamperedObservedCipherPredictionGame
    (τ : BipBipTamperer)
    (A : BipBipTamperedPayloadAttacker)
    (history : List BipBipHiddenSample)
    (target : BipBipHiddenSample) : ProbComp Bool := by
  classical
  exact do
    let mk ← ($ᵗ MasterKey)
    let seenHistory := bipbipObservedHistory mk history
    let seenTarget := BipBipHiddenSample.observe mk target
    let tampered := τ seenHistory seenTarget
    pure (decide (A seenHistory tampered = BipBip.decrypt mk tampered.tweak tampered.ciphertext))

/-- Success probability in the tampered observed-cipher BipBip prediction game. -/
noncomputable def bipbipTamperedObservedCipherPredictionSuccessProbability
    (τ : BipBipTamperer)
    (A : BipBipTamperedPayloadAttacker)
    (history : List BipBipHiddenSample)
    (target : BipBipHiddenSample) : ℝ :=
  (Pr[= true | bipbipTamperedObservedCipherPredictionGame τ A history target]).toReal

/-- Tampered observed-cipher BipBip prediction success probabilities are always nonnegative. -/
theorem bipbipTamperedObservedCipherPredictionSuccessProbability_nonneg
    (τ : BipBipTamperer)
    (A : BipBipTamperedPayloadAttacker)
    (history : List BipBipHiddenSample)
    (target : BipBipHiddenSample) :
    0 ≤ bipbipTamperedObservedCipherPredictionSuccessProbability τ A history target := by
  unfold bipbipTamperedObservedCipherPredictionSuccessProbability
  exact ENNReal.toReal_nonneg

/--
Symbolic multi-chosen-tweak tamper-resistance assumption for BipBip.

If the observed target `(tweak, ciphertext)` is modified before prediction, then the attacker still
cannot recover the plaintext underlying the tampered pair with nonzero probability.
-/
def BipBipTamperedObservedCipherPredictionImpossible : Prop :=
  ∀ (τ : BipBipTamperer)
    (_hτ : ∀ (history : List BipBipSeenSample) (target : BipBipSeenSample), τ history target ≠ target)
    (A : BipBipTamperedPayloadAttacker)
    (history : List BipBipHiddenSample)
    (target : BipBipHiddenSample),
    bipbipTamperedObservedCipherPredictionSuccessProbability τ A history target = 0

end BipBip.C3.Security
