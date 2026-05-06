import Uu.BipBip.C3
import Mathlib.Data.Real.Sqrt
import VCVio.CryptoFoundations.SecExp
import VCVio.CryptoFoundations.SymmEncAlg
import VCVio.OracleComp.Constructions.BitVec

namespace BipBip.C3.Security

open OracleComp

/-- The observable object in the C3 confidentiality game is an encoded pointer. -/
abbrev Observation := EncodedPointer

/--
A left-right confidentiality challenge for C3 pointers.

The two candidate pointers must agree on all public fields, since `radix` and `lower`
remain visible in the encoded representation.
-/
structure ChallengePair where
  left : PlainPointer
  right : PlainPointer
  samePublic : left.radix = right.radix ∧ left.lower = right.lower

/-- The family of observable C3 encodings indexed by the secret master key. -/
abbrev ObservationFamily := MasterKey → EncodedPointer

/-- A read-only attacker consumes an encoded pointer and returns an observation bit. -/
abbrev ReadOnlyAttacker := Observation → Bool

/-- A read-only attacker on the raw 24-bit BipBip ciphertext slice. -/
abbrev SliceAttacker := Block → Bool

/--
View BipBip at a fixed tweak as a deterministic symmetric encryption scheme whose randomness
comes solely from uniform master-key sampling.
-/
def fixedTweakEncAlg (tw : Tweak) : SymmEncAlg ProbComp Block MasterKey Block where
  keygen := ($ᵗ MasterKey)
  encrypt mk msg := pure (BipBip.decrypt mk tw msg)
  decrypt mk c := pure (some (BipBip.encrypt mk tw c))

/--
The `VCV-io` read-only distinguishing game for a fixed world.

A secret master key is sampled uniformly, the world exposes the corresponding encoded pointer,
and the attacker returns a single distinguishing bit.
-/
def readOnlyGame (A : ReadOnlyAttacker) (world : ObservationFamily) : ProbComp Bool := do
  let mk ← ($ᵗ MasterKey)
  pure (A (world mk))

/--
The corresponding read-only distinguishing game for the raw 24-bit BipBip ciphertext slice.
-/
def sliceGame (A : SliceAttacker) (world : MasterKey → Block) : ProbComp Bool := do
  let mk ← ($ᵗ MasterKey)
  pure (A (world mk))

/-- The observation family corresponding to the left branch of a C3 challenge. -/
def leftWorld (pair : ChallengePair) : ObservationFamily :=
  fun mk => encodePointer mk pair.left

/-- The observation family corresponding to the right branch of a C3 challenge. -/
def rightWorld (pair : ChallengePair) : ObservationFamily :=
  fun mk => encodePointer mk pair.right

/--
Reinterpret a C3 attacker as a Boolean test on the protected 24-bit ciphertext slice while
holding the visible pointer fields fixed.
-/
private def packedCipherAttacker
    (radix : Radix) (lower : LowerAddr) (A : ReadOnlyAttacker) : Block → Bool :=
  fun c => A (packEncodedPointer radix c lower)

/--
Computational indistinguishability of two observation families, expressed using the concrete
`VCV-io` read-only distinguishing game and Boolean distinguishing advantage.
-/
def ComputationallyIndistinguishable (obs₀ obs₁ : ObservationFamily) : Prop :=
  ∀ A : ReadOnlyAttacker,
    (readOnlyGame A obs₀).boolDistAdvantage (readOnlyGame A obs₁) = 0

/--
The concrete read-only distinguishing advantage of an attacker on a C3 challenge.
-/
noncomputable def readOnlyAdvantage (A : ReadOnlyAttacker) (pair : ChallengePair) : ℝ :=
  (readOnlyGame A (leftWorld pair)).boolDistAdvantage (readOnlyGame A (rightWorld pair))

/--
Protocol-level computational confidentiality for C3 in the `VCV-io` read-only game.
-/
def C3ReadOnlySecure : Prop :=
  ∀ pair : ChallengePair, ComputationallyIndistinguishable (leftWorld pair) (rightWorld pair)

/--
Structured `VCV-io` game-based security statement: every read-only attacker has
distinguishing advantage at most `ε` on every valid C3 challenge.
-/
def C3ReadOnlyAdvantageBound (ε : ℝ) : Prop :=
  ∀ (A : ReadOnlyAttacker) (pair : ChallengePair), readOnlyAdvantage A pair ≤ ε

/--
Fixed-tweak read-only security for BipBip: for each public tweak, every Boolean test on the
24-bit ciphertext slice has distinguishing advantage at most `ε` between any two payloads.
-/
def BipBipReadOnlyAdvantageBound (ε : ℝ) : Prop :=
  ∀ (tw : Tweak) (A : Block → Bool) (msg₀ msg₁ : Block),
    ((sliceGame A
      (fun mk => BipBip.decrypt mk tw msg₀)).boolDistAdvantage
      (sliceGame A
        (fun mk => BipBip.decrypt mk tw msg₁))) ≤ ε

/--
The paper's idealized per-tweak prediction space `2^23.5`, written as `2^23 * sqrt 2`.

This matches the discussion in Section 3.5, which explains the target prediction term as
`(2^23.5 - qTi)⁻¹`. The compact OCR rendering of Section 2.5 is slightly ambiguous, so this
definition follows the prose clarification from Section 3.5.
-/
noncomputable def bipbipPaperPredictionSpace : ℝ :=
  ((2 : ℝ) ^ (23 : Nat)) * Real.sqrt 2

/--
Concrete `ε` induced by the BipBip paper's prediction-security claim as a function of:

* `q`: total number of encryption/decryption queries,
* `qTi`: number of queries under the target tweak,
* `t`: computation time measured in equivalent BipBip evaluations.
-/
noncomputable def bipbipPredictionSuccessEpsilon (q qTi t : ℕ) : ℝ :=
  1 / max (bipbipPaperPredictionSpace - qTi) 1
    + q / ((2 : ℝ) ^ (96 : Nat))
    + t / ((2 : ℝ) ^ (96 : Nat))
    + (q * t) / ((2 : ℝ) ^ (120 : Nat))

/-- Direction of an oracle query in the BipBip prediction game. -/
inductive BipBipQueryDirection
  | plainToCipher
  | cipherToPlain
deriving DecidableEq, Repr

/--
An answered oracle query in the BipBip prediction game.

We store both the plaintext and ciphertext view of the mapping so that freshness and
resource accounting can be phrased uniformly, while `direction` remembers which oracle
interface the adversary actually used.
-/
structure BipBipAnsweredQuery where
  direction : BipBipQueryDirection
  tweak : Tweak
  plaintext : Block
  ciphertext : Block
deriving DecidableEq, Repr

/-- A final fresh `(plaintext, ciphertext, tweak)` prediction target for BipBip. -/
structure BipBipPredictionGoal where
  tweak : Tweak
  plaintext : Block
  ciphertext : Block
deriving DecidableEq, Repr

/-- An offline trace-level model of a BipBip adversary execution. -/
structure BipBipAttackTrace where
  queries : List BipBipAnsweredQuery
  goal : BipBipPredictionGoal
  timeCost : ℕ
deriving Repr

/-- Whether an answered BipBip query is consistent with the concrete cipher under `mk`. -/
def BipBipAnsweredQuery.validUnder (mk : MasterKey) (q : BipBipAnsweredQuery) : Prop :=
  q.ciphertext = BipBip.decrypt mk q.tweak q.plaintext

/-- Whether a prediction goal is correct for the concrete cipher under `mk`. -/
def BipBipPredictionGoal.validUnder (mk : MasterKey) (g : BipBipPredictionGoal) : Prop :=
  g.ciphertext = BipBip.decrypt mk g.tweak g.plaintext

/-- Whether a past query already revealed the final prediction target. -/
def BipBipAnsweredQuery.reveals
    (q : BipBipAnsweredQuery) (g : BipBipPredictionGoal) : Prop :=
  q.tweak = g.tweak ∧ q.plaintext = g.plaintext ∧ q.ciphertext = g.ciphertext

/-- Total number of answered oracle queries in a BipBip attack trace. -/
def BipBipAttackTrace.totalQueries (tr : BipBipAttackTrace) : ℕ :=
  tr.queries.length

/-- Number of answered queries in a BipBip trace that use the target tweak. -/
def BipBipAttackTrace.targetTweakQueries (tr : BipBipAttackTrace) : ℕ :=
  tr.queries.countP (fun q => q.tweak = tr.goal.tweak)

/-- Every recorded query answer is valid for the sampled master key. -/
def BipBipAttackTrace.validTranscript (mk : MasterKey) (tr : BipBipAttackTrace) : Prop :=
  ∀ q ∈ tr.queries, q.validUnder mk

/-- The final target was not already revealed by any previous query. -/
def BipBipAttackTrace.freshGoal (tr : BipBipAttackTrace) : Prop :=
  ∀ q ∈ tr.queries, ¬ q.reveals tr.goal

/-- Success event for a BipBip attack trace under a sampled master key. -/
def BipBipAttackTrace.successUnder (mk : MasterKey) (tr : BipBipAttackTrace) : Prop :=
  tr.validTranscript mk ∧ tr.freshGoal ∧ tr.goal.validUnder mk

/-- The paper-style hidden-key prediction game induced by a fixed BipBip attack trace. -/
noncomputable def bipbipPredictionGame (tr : BipBipAttackTrace) : ProbComp Bool := by
  classical
  exact do
    let mk ← ($ᵗ MasterKey)
    pure (decide (tr.successUnder mk))

/-- Success probability of a BipBip attack trace in the hidden-key prediction game. -/
noncomputable def bipbipPredictionSuccessProbability (tr : BipBipAttackTrace) : ℝ :=
  (Pr[= true | bipbipPredictionGame tr]).toReal

/--
Structured prediction-security bound for BipBip: every attack trace succeeds with probability
at most `ε(q,qTi,t)`.
-/
def BipBipPredictionSuccessBound : Prop :=
  ∀ tr : BipBipAttackTrace,
    bipbipPredictionSuccessProbability tr ≤
      bipbipPredictionSuccessEpsilon tr.totalQueries tr.targetTweakQueries tr.timeCost

/-- The protected 24-bit slice carried inside an encoded C3 pointer. -/
def encodedCipherSlice (p : EncodedPointer) : Block :=
  p.extractLsb' 34 24

/-- Direction of an oracle query in the C3 pointer-level prediction game. -/
inductive C3QueryDirection
  | plainToEncoded
  | encodedToPlain
deriving DecidableEq, Repr

/--
An answered oracle query at the C3 pointer layer.

As with the BipBip trace model, we store both the decoded pointer and its encoded form and
use `direction` only to record which oracle interface was exercised.
-/
structure C3AnsweredQuery where
  direction : C3QueryDirection
  plain : PlainPointer
  encoded : EncodedPointer
deriving DecidableEq, Repr

/-- A final fresh `(plain, encoded)` prediction target for the C3 pointer layer. -/
structure C3PredictionGoal where
  plain : PlainPointer
  encoded : EncodedPointer
deriving DecidableEq, Repr

/-- An offline trace-level model of a C3 pointer adversary execution. -/
structure C3AttackTrace where
  queries : List C3AnsweredQuery
  goal : C3PredictionGoal
  timeCost : ℕ
deriving Repr

/-- Whether a C3 query answer is consistent with the concrete encoding under `mk`. -/
def C3AnsweredQuery.validUnder (mk : MasterKey) (q : C3AnsweredQuery) : Prop :=
  q.encoded = packEncodedPointer q.plain.radix (encodedCipherSlice q.encoded) q.plain.lower ∧
    encodedCipherSlice q.encoded = BipBip.decrypt mk (tweak q.plain) (payload q.plain)

/-- Whether a C3 prediction goal is correct under `mk`. -/
def C3PredictionGoal.validUnder (mk : MasterKey) (g : C3PredictionGoal) : Prop :=
  g.encoded = packEncodedPointer g.plain.radix (encodedCipherSlice g.encoded) g.plain.lower ∧
    encodedCipherSlice g.encoded = BipBip.decrypt mk (tweak g.plain) (payload g.plain)

/-- Whether a past C3 query already revealed the final target mapping. -/
def C3AnsweredQuery.reveals (q : C3AnsweredQuery) (g : C3PredictionGoal) : Prop :=
  tweak q.plain = tweak g.plain ∧
    payload q.plain = payload g.plain ∧
    encodedCipherSlice q.encoded = encodedCipherSlice g.encoded

/-- Total number of answered oracle queries in a C3 attack trace. -/
def C3AttackTrace.totalQueries (tr : C3AttackTrace) : ℕ :=
  tr.queries.length

/-- Number of answered queries in a C3 trace that use the target tweak. -/
def C3AttackTrace.targetTweakQueries (tr : C3AttackTrace) : ℕ :=
  tr.queries.countP (fun q => tweak q.plain = tweak tr.goal.plain)

/-- Every recorded query answer is valid for the sampled master key. -/
def C3AttackTrace.validTranscript (mk : MasterKey) (tr : C3AttackTrace) : Prop :=
  ∀ q ∈ tr.queries, q.validUnder mk

/-- The final target was not already revealed by any previous C3 query. -/
def C3AttackTrace.freshGoal (tr : C3AttackTrace) : Prop :=
  ∀ q ∈ tr.queries, ¬ q.reveals tr.goal

/-- Success event for a C3 pointer attack trace under a sampled master key. -/
def C3AttackTrace.successUnder (mk : MasterKey) (tr : C3AttackTrace) : Prop :=
  tr.validTranscript mk ∧ tr.freshGoal ∧ tr.goal.validUnder mk

/-- The hidden-key prediction game induced by a fixed C3 pointer attack trace. -/
noncomputable def c3PredictionGame (tr : C3AttackTrace) : ProbComp Bool := by
  classical
  exact do
    let mk ← ($ᵗ MasterKey)
    pure (decide (tr.successUnder mk))

/-- Success probability of a C3 attack trace in the hidden-key prediction game. -/
noncomputable def c3PredictionSuccessProbability (tr : C3AttackTrace) : ℝ :=
  (Pr[= true | c3PredictionGame tr]).toReal

/-- Structured prediction-security bound for the C3 pointer layer. -/
def C3PredictionSuccessBound : Prop :=
  ∀ tr : C3AttackTrace,
    c3PredictionSuccessProbability tr ≤
      bipbipPredictionSuccessEpsilon tr.totalQueries tr.targetTweakQueries tr.timeCost

/-- Translate a C3 prediction goal to the corresponding BipBip target mapping. -/
def C3PredictionGoal.toBipBipGoal (g : C3PredictionGoal) : BipBipPredictionGoal where
  tweak := tweak g.plain
  plaintext := payload g.plain
  ciphertext := encodedCipherSlice g.encoded

/-- Translate a C3 answered query to the corresponding BipBip answered query. -/
def C3AnsweredQuery.toBipBipQuery (q : C3AnsweredQuery) : BipBipAnsweredQuery where
  direction := match q.direction with
    | .plainToEncoded => .plainToCipher
    | .encodedToPlain => .cipherToPlain
  tweak := tweak q.plain
  plaintext := payload q.plain
  ciphertext := encodedCipherSlice q.encoded

/-- Translate a C3 attack trace to the corresponding BipBip attack trace. -/
def C3AttackTrace.toBipBipTrace (tr : C3AttackTrace) : BipBipAttackTrace where
  queries := tr.queries.map C3AnsweredQuery.toBipBipQuery
  goal := tr.goal.toBipBipGoal
  timeCost := tr.timeCost

/-- The C3-to-BipBip trace translation preserves the total query count. -/
@[simp] theorem C3AttackTrace.totalQueries_toBipBip (tr : C3AttackTrace) :
    tr.toBipBipTrace.totalQueries = tr.totalQueries := by
  simp [C3AttackTrace.toBipBipTrace, BipBipAttackTrace.totalQueries, C3AttackTrace.totalQueries]

/-- The C3-to-BipBip trace translation preserves the target-tweak query count. -/
@[simp] theorem C3AttackTrace.targetTweakQueries_toBipBip (tr : C3AttackTrace) :
    tr.toBipBipTrace.targetTweakQueries = tr.targetTweakQueries := by
  rcases tr with ⟨queries, goal, timeCost⟩
  unfold BipBipAttackTrace.targetTweakQueries C3AttackTrace.targetTweakQueries
  simp [C3AttackTrace.toBipBipTrace, C3PredictionGoal.toBipBipGoal]
  rfl

/-- Query validity at the C3 layer implies validity of the translated BipBip query. -/
theorem C3AnsweredQuery.toBipBip_validUnder
    {mk : MasterKey} {q : C3AnsweredQuery} (h : q.validUnder mk) :
    q.toBipBipQuery.validUnder mk := by
  exact h.2

/-- Goal validity at the C3 layer implies validity of the translated BipBip goal. -/
theorem C3PredictionGoal.toBipBip_validUnder
    {mk : MasterKey} {g : C3PredictionGoal} (h : g.validUnder mk) :
    g.toBipBipGoal.validUnder mk := by
  exact h.2

/-- Freshness of a C3 goal implies freshness of the translated BipBip goal. -/
theorem C3AttackTrace.freshGoal_toBipBip
    {tr : C3AttackTrace} (h : tr.freshGoal) :
    tr.toBipBipTrace.freshGoal := by
  intro q hq
  rcases List.mem_map.mp hq with ⟨q', hq', rfl⟩
  specialize h q' hq'
  simpa [C3AnsweredQuery.reveals, BipBipAnsweredQuery.reveals, C3AnsweredQuery.toBipBipQuery,
    C3PredictionGoal.toBipBipGoal] using h

/-- Validity of a C3 transcript implies validity of the translated BipBip transcript. -/
theorem C3AttackTrace.validTranscript_toBipBip
    {mk : MasterKey} {tr : C3AttackTrace} (h : tr.validTranscript mk) :
    tr.toBipBipTrace.validTranscript mk := by
  intro q hq
  rcases List.mem_map.mp hq with ⟨q', hq', rfl⟩
  exact C3AnsweredQuery.toBipBip_validUnder (h q' hq')

/-- Success of a C3 trace implies success of the translated BipBip trace. -/
theorem C3AttackTrace.successUnder_toBipBip
    {mk : MasterKey} {tr : C3AttackTrace} (h : tr.successUnder mk) :
    tr.toBipBipTrace.successUnder mk := by
  rcases h with ⟨hvalid, hfresh, hgoal⟩
  exact ⟨tr.validTranscript_toBipBip hvalid, tr.freshGoal_toBipBip hfresh,
    C3PredictionGoal.toBipBip_validUnder hgoal⟩

/--
If fixed-tweak BipBip has read-only advantage bounded by `ε`, then every C3 read-only attacker
also has advantage bounded by `ε`. This reduction only wraps the BipBip ciphertext slice with
shared public pointer fields.
-/
theorem c3ReadOnlyAdvantageBound_of_bipbipBound
    {ε : ℝ}
    (hBound : BipBipReadOnlyAdvantageBound ε) :
    C3ReadOnlyAdvantageBound ε := by
  intro A pair
  rcases pair.samePublic with ⟨hradix, hlower⟩
  have htweak : tweak pair.left = tweak pair.right := by
    simp [tweak, hradix, hlower]
  let test := packedCipherAttacker pair.left.radix pair.left.lower A
  have hleft :
      readOnlyGame A (leftWorld pair) =
        sliceGame test (fun mk => BipBip.decrypt mk (tweak pair.left) (payload pair.left)) := by
    rfl
  have hright :
      readOnlyGame A (rightWorld pair) =
        sliceGame test (fun mk => BipBip.decrypt mk (tweak pair.left) (payload pair.right)) := by
    simp [readOnlyGame, sliceGame, rightWorld, test, packedCipherAttacker, encodePointer, htweak,
      hradix, hlower]
  unfold readOnlyAdvantage
  rw [hleft, hright]
  exact hBound (tweak pair.left) test (payload pair.left) (payload pair.right)

/--
Game-based reduction: zero advantage for every attacker implies computational confidentiality
of the C3 read-only game.
-/
theorem c3ReadOnlySecure_of_advantageZero
    (h : C3ReadOnlyAdvantageBound 0) :
    C3ReadOnlySecure := by
  intro pair A
  exact le_antisymm (h A pair) (by
    unfold ProbComp.boolDistAdvantage
    exact abs_nonneg _)

/--
Auxiliary cipher-level read-only security assumption for BipBip, stated as a concrete
`ε`-advantage bound at the fixed-tweak payload channel boundary.

This path is retained for one-shot confidentiality corollaries, but the primary story of the
development is the structured paper-style prediction game below.
-/
axiom bipbipReadOnlyAdvantageBoundAxiom (ε : ℝ) : BipBipReadOnlyAdvantageBound ε

/--
Auxiliary paper-shaped cipher-side assumption used to connect the older one-shot read-only game
to the paper's concrete bound.

This is intentionally still an assumption here: the current local game does not yet model the
paper's query counters and prediction event directly, so the full cryptanalytic proof is out of
scope for this development as it stands.
-/
axiom bipbipPaperBoundAxiom (q qTi t : ℕ) :
    BipBipReadOnlyAdvantageBound (bipbipPredictionSuccessEpsilon q qTi t)

/--
Structured paper-side assumption over the explicit BipBip adversary model.

This is the primary assumption boundary for the project: once the local formalization is aligned
tightly enough with the published proof, this is the claim we would want to discharge from the
paper's cryptanalysis.
-/
axiom bipbipPredictionSuccessBoundAxiom : BipBipPredictionSuccessBound

/--
Derived C3 confidentiality bound obtained from the BipBip fixed-tweak read-only bound.
-/
theorem c3ReadOnlyAdvantageBound_from_bipbipAxiom (ε : ℝ) :
    C3ReadOnlyAdvantageBound ε := by
  exact c3ReadOnlyAdvantageBound_of_bipbipBound (bipbipReadOnlyAdvantageBoundAxiom ε)

/--
Derived C3 confidentiality bound obtained from the paper-shaped BipBip resource bound.
-/
theorem c3ReadOnlyAdvantageBound_from_bipbipPaperAxiom (q qTi t : ℕ) :
    C3ReadOnlyAdvantageBound (bipbipPredictionSuccessEpsilon q qTi t) := by
  exact c3ReadOnlyAdvantageBound_of_bipbipBound (bipbipPaperBoundAxiom q qTi t)

/--
If BipBip satisfies the structured paper-style prediction claim, then the C3 pointer layer
inherits the same concrete resource-dependent bound.
-/
theorem c3PredictionSuccessBound_of_bipbipPredictionSuccessBound
    (h : BipBipPredictionSuccessBound) :
    ∀ tr : C3AttackTrace,
    c3PredictionSuccessProbability tr ≤
      bipbipPredictionSuccessEpsilon tr.totalQueries tr.targetTweakQueries tr.timeCost := by
  intro tr
  have hprob : Pr[= true | c3PredictionGame tr] ≤
      Pr[= true | bipbipPredictionGame tr.toBipBipTrace] := by
    classical
    have hc3 : Pr[= true | c3PredictionGame tr] =
        Pr[fun b => b = true | c3PredictionGame tr] := by
      simpa using
        (probOutput_true_eq_probEvent (mx := c3PredictionGame tr) (p := fun b => b = true)).symm
    have hbip : Pr[= true | bipbipPredictionGame tr.toBipBipTrace] =
        Pr[fun b => b = true | bipbipPredictionGame tr.toBipBipTrace] := by
      simpa using
        (probOutput_true_eq_probEvent
          (mx := bipbipPredictionGame tr.toBipBipTrace) (p := fun b => b = true)).symm
    rw [hc3, hbip]
    unfold c3PredictionGame bipbipPredictionGame
    change Pr[fun b => b = true |
      (fun mk => decide (tr.successUnder mk)) <$> ($ᵗ MasterKey)] ≤
      Pr[fun b => b = true |
        (fun mk => decide (tr.toBipBipTrace.successUnder mk)) <$> ($ᵗ MasterKey)]
    rw [probEvent_map, probEvent_map]
    apply probEvent_mono
    intro mk _ hsucc
    have hs : tr.toBipBipTrace.successUnder mk :=
      C3AttackTrace.successUnder_toBipBip (by simpa using hsucc)
    simpa using hs
  have hreal : c3PredictionSuccessProbability tr ≤
      (Pr[= true | bipbipPredictionGame tr.toBipBipTrace]).toReal := by
    unfold c3PredictionSuccessProbability
    exact (ENNReal.toReal_le_toReal probOutput_ne_top probOutput_ne_top).mpr hprob
  calc
    c3PredictionSuccessProbability tr
      ≤ (Pr[= true | bipbipPredictionGame tr.toBipBipTrace]).toReal := hreal
    _ ≤ bipbipPredictionSuccessEpsilon tr.toBipBipTrace.totalQueries
          tr.toBipBipTrace.targetTweakQueries tr.toBipBipTrace.timeCost := by
          exact h tr.toBipBipTrace
    _ = bipbipPredictionSuccessEpsilon tr.totalQueries tr.targetTweakQueries tr.timeCost := by
          rw [C3AttackTrace.totalQueries_toBipBip, C3AttackTrace.targetTweakQueries_toBipBip]
          rfl

/-- The C3 pointer layer inherits the structured prediction bound from the BipBip axiom. -/
theorem c3PredictionSuccessBound_from_bipbipPredictionAxiom :
    C3PredictionSuccessBound := by
  exact c3PredictionSuccessBound_of_bipbipPredictionSuccessBound
    bipbipPredictionSuccessBoundAxiom


end BipBip.C3.Security
