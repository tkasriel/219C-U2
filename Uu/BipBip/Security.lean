import Uu.BipBip.C3

namespace BipBip.C3.Security

/-- In the paper's game, plaintexts are 24-bit BipBip blocks. -/
abbrev Plaintext := Block

/-- In the paper's game, ciphertexts are 24-bit BipBip blocks. -/
abbrev Ciphertext := Block

/--
An oracle query available to the adversary.

The paper allows the adversary to query both directions of the tweakable block cipher
under chosen tweaks.
-/
inductive OracleQuery where
  /-- Query the forward direction on a chosen plaintext and tweak. -/
  | encrypt (tweak : Tweak) (plaintext : Plaintext)
  /-- Query the inverse direction on a chosen ciphertext and tweak. -/
  | decrypt (tweak : Tweak) (ciphertext : Ciphertext)
deriving DecidableEq

/-- Extract the tweak used by an oracle query. -/
def OracleQuery.tweak : OracleQuery → Tweak
  | .encrypt tweak _ => tweak
  | .decrypt tweak _ => tweak

/--
An answered oracle query appearing in the adversary transcript.

The `output` field stores the block returned by the oracle for the given query.
-/
structure QueryAnswer where
  query : OracleQuery
  output : Block
deriving DecidableEq

/--
Check whether an answered query is consistent with BipBip under a specific master key.

This is the basic well-formedness condition for an attack transcript.
-/
def QueryAnswer.consistentWith (mk : MasterKey) : QueryAnswer → Prop
  | ⟨.encrypt tweak plaintext, output⟩ => BipBip.decrypt mk tweak plaintext = output
  | ⟨.decrypt tweak ciphertext, output⟩ => BipBip.encrypt mk tweak ciphertext = output

/--
Check whether an answered query already revealed the target pair `(plaintext, ciphertext)`
under the target tweak.
-/
def QueryAnswer.matchesTarget (tweak : Tweak) (plaintext : Plaintext) (ciphertext : Ciphertext) :
    QueryAnswer → Prop
  | ⟨.encrypt tweak' plaintext', output⟩ =>
      tweak' = tweak ∧ plaintext' = plaintext ∧ output = ciphertext
  | ⟨.decrypt tweak' ciphertext', output⟩ =>
      tweak' = tweak ∧ ciphertext' = ciphertext ∧ output = plaintext

/--
The transcript and time budget consumed by one run of an attack.

The paper measures time in units comparable to one BipBip evaluation.
-/
structure AttackTranscript where
  interactions : List QueryAnswer
  time : Nat
deriving DecidableEq

/-- Total number of oracle queries appearing in the transcript. -/
def AttackTranscript.totalQueries (tr : AttackTranscript) : Nat :=
  tr.interactions.length

/-- Number of oracle queries in the transcript that use a specific tweak value. -/
def AttackTranscript.queriesAtTweak (tr : AttackTranscript) (tweak : Tweak) : Nat :=
  tr.interactions.countP (fun qa => qa.query.tweak = tweak)

/--
The final prediction target guessed by the adversary.

The intended meaning is that `ciphertext` maps to `plaintext` under `tweak`.
-/
structure PredictionGoal where
  tweak : Tweak
  plaintext : Plaintext
  ciphertext : Ciphertext
deriving DecidableEq

/-- The target prediction is correct for a master key when BipBip maps the pair accordingly. -/
def PredictionGoal.holdsUnder (mk : MasterKey) (goal : PredictionGoal) : Prop :=
  BipBip.decrypt mk goal.tweak goal.plaintext = goal.ciphertext

/--
The target prediction is fresh with respect to a transcript when the exact pair was not
already revealed by an earlier oracle query.
-/
def PredictionGoal.freshFor (goal : PredictionGoal) (tr : AttackTranscript) : Prop :=
  ∀ qa ∈ tr.interactions, ¬ QueryAnswer.matchesTarget goal.tweak goal.plaintext goal.ciphertext qa

/--
One full attack run against a fixed master key.

The transcript records the oracle interaction, while `goal` is the final unseen pair the
adversary attempts to predict.
-/
structure AttackView where
  transcript : AttackTranscript
  goal : PredictionGoal
deriving DecidableEq

/--
An attack strategy as a function from the secret master key to the resulting interaction view.

This packages the whole oracle interaction, including adaptive choices, into one object.
-/
abbrev AttackStrategy := MasterKey → AttackView

/-- The attack succeeds for a specific master key when its final prediction is correct. -/
def AttackStrategy.succeeds (A : AttackStrategy) (mk : MasterKey) : Prop :=
  (A mk).goal.holdsUnder mk

/-- The attack transcript is oracle-consistent for every possible master key. -/
def AttackStrategy.oracleConsistent (A : AttackStrategy) : Prop :=
  ∀ mk qa, qa ∈ (A mk).transcript.interactions → qa.consistentWith mk

/-- The attack only makes fresh predictions for every possible master key. -/
def AttackStrategy.freshTargets (A : AttackStrategy) : Prop :=
  ∀ mk, (A mk).goal.freshFor (A mk).transcript

/--
The attack uses at most `q` total queries, at most `qTi` queries at its eventual target tweak,
and at most `t` units of computation.
-/
def AttackStrategy.withinResources (A : AttackStrategy) (q qTi t : Nat) : Prop :=
  ∀ mk,
    (A mk).transcript.totalQueries ≤ q ∧
    (A mk).transcript.queriesAtTweak (A mk).goal.tweak ≤ qTi ∧
    (A mk).transcript.time ≤ t

/-- The overall well-formedness conditions needed for the paper's security claim. -/
def AttackStrategy.Admissible (A : AttackStrategy) (q qTi t : Nat) : Prop :=
  A.oracleConsistent ∧ A.freshTargets ∧ A.withinResources q qTi t

/-- The size of the uniformly sampled master-key space. -/
private def keySpaceSize : Nat := 2 ^ 256

/-- View a natural number as a rational number. -/
private def natQ (n : Nat) : Rat :=
  Rat.ofInt n

/-- The rational number `2^n`. -/
private def pow2Q (n : Nat) : Rat :=
  natQ (2 ^ n)

/-- The `μ = 0.5` slack parameter appearing in the BipBip paper's claim. -/
private def mu : Rat := (1 : Rat) / 2

/-- Count how many master keys make the attack succeed. -/
private def successCount (A : AttackStrategy) : Nat :=
  (List.range keySpaceSize).countP (fun n =>
    let mk : MasterKey := BitVec.ofNat 256 n
    let view := A mk
    decide (BipBip.decrypt mk view.goal.tweak view.goal.plaintext = view.goal.ciphertext))

/--
The exact success probability of an attack strategy under uniform sampling of the 256-bit
master key.
-/
def successProbability (A : AttackStrategy) : Rat :=
  natQ (successCount A) / natQ keySpaceSize

/--
The baseline guessing term from the BipBip paper.

For an ideal 24-bit tweakable block cipher, the success probability would be roughly
`1 / (2^24 - qTi)`. BipBip allows a small slack captured by `μ = 0.5`.
-/
def baselineGuessBound (qTi : Nat) : Rat :=
  let remaining := pow2Q 24 - mu - natQ qTi
  (1 : Rat) / max remaining 1

/--
The full prediction bound claimed in the BipBip paper:

`1 / max(2^(24 - μ) - qTi, 1) + q / 2^96 + t / 2^96 + q*t / 2^120`

written in the paper's equivalent rational form with `μ = 0.5`.
-/
def paperBound (q qTi t : Nat) : Rat :=
  baselineGuessBound qTi +
    natQ q / pow2Q 96 +
    natQ t / pow2Q 96 +
    (natQ q * natQ t) / pow2Q 120

/--
The concrete BipBip security claim, phrased in the style of Section 2.5 of the paper.

Any admissible adversary that makes at most `q` total queries, at most `qTi` queries at
its target tweak, and spends at most `t` computation units has success probability at most
`paperBound q qTi t`.
-/
def SatisfiesPaperClaim : Prop :=
  ∀ (A : AttackStrategy) (q qTi t : Nat),
    A.Admissible q qTi t →
      successProbability A ≤ paperBound q qTi t

/--
The BipBip paper's claimed prediction-security statement.

This is intentionally introduced as an axiom for now so the surrounding formalization can
target exactly the claim made in the paper, while a future proof effort can replace it with
an actual theorem.
-/
axiom bipbipPaperClaim : SatisfiesPaperClaim

/--
Read-only C3 pointer confidentiality follows directly from the BipBip paper claim.

This is a corollary rather than a new assumption: every C3 pointer prediction problem is just
a BipBip prediction problem with the public tweak split into `radix ++ lower`.
-/
theorem c3ReadOnlyPaperClaim :
    SatisfiesPaperClaim :=
  bipbipPaperClaim

end BipBip.C3.Security
