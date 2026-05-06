import Uu.BipBip.PrimitiveAssumptions

namespace BipBip.C3.Security

/-- Legacy one-shot read-only confidentiality statement retained as a secondary corollary. -/
def C3ComputationalConfidentiality : Prop :=
  C3ReadOnlySecure

/--
Parameterized C3 read-only confidentiality: every attacker has distinguishing advantage at most
`ε` in the concrete `VCV-io` game.
-/
def C3ComputationalConfidentialityBound (ε : ℝ) : Prop :=
  C3ReadOnlyAdvantageBound ε

/--
The primary C3 security statement follows from the BipBip prediction-success bound through the
structured trace translation in `PrimitiveAssumptions`.
-/
theorem primaryC3SecurityClaim_holds :
    ∀ tr : C3AttackTrace,
      c3PredictionSuccessProbability tr ≤
        bipbipPredictionSuccessEpsilon tr.totalQueries tr.targetTweakQueries tr.timeCost := by
  exact c3PredictionSuccessBound_from_bipbipPredictionAxiom

/--
Computational confidentiality of C3 with exact zero advantage is a secondary corollary of the
older read-only game path.
-/
theorem c3ComputationalConfidentiality_holds :
    C3ComputationalConfidentiality := by
  exact c3ReadOnlySecure_of_advantageZero (c3ReadOnlyAdvantageBound_from_bipbipAxiom 0)

/--
Computational confidentiality of C3 inherits any concrete BipBip read-only advantage bound.
-/
theorem c3ComputationalConfidentialityBound_holds (ε : ℝ) :
    C3ComputationalConfidentialityBound ε := by
  exact c3ReadOnlyAdvantageBound_from_bipbipAxiom ε

/--
Computational confidentiality of C3 under the concrete resource-bounded `ε(q,qTi,t)` induced
by the BipBip paper's prediction-security claim.
-/
theorem c3ComputationalConfidentialityBound_from_bipbipPaper (q qTi t : ℕ) :
    C3ComputationalConfidentialityBound (bipbipPredictionSuccessEpsilon q qTi t) := by
  exact c3ReadOnlyAdvantageBound_from_bipbipPaperAxiom q qTi t

/--
Structured prediction security for the C3 pointer layer follows from the structured
BipBip prediction-success bound.
-/
theorem c3PredictionSuccessBound_holds :
    ∀ tr : C3AttackTrace,
      c3PredictionSuccessProbability tr ≤
        bipbipPredictionSuccessEpsilon tr.totalQueries tr.targetTweakQueries tr.timeCost := by
  exact primaryC3SecurityClaim_holds

/--
Legacy alias for the read-only confidentiality corollary.
-/
theorem strongestC3ReadOnlyConfidentiality :
    C3ComputationalConfidentiality := by
  exact c3ComputationalConfidentiality_holds

end BipBip.C3.Security
