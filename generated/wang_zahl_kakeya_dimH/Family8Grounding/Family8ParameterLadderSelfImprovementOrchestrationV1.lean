import Family8Grounding.Family8ExplicitParameterSelfImprovementOrchestrationV1
import Family8Grounding.Family8Section8FixedPositiveSelfImprovementBudgetV3

open scoped NNReal

namespace Family8ParameterLadderSelfImprovementOrchestrationV1

open Family8KatzTaoFrostmanPropertiesV1
open Family8ParameterLadderV1
open Family8Section8FixedPositiveSelfImprovementBudgetV3
open Family8ExplicitParameterSelfImprovementOrchestrationV1

noncomputable section

set_option autoImplicit false
set_option warningAsError true

/-!
# Parameter-ladder endpoint to Main Lemma 1

The Section 8 numerical work has already selected the decrement
`sectionEightFixedNu P = P.eta 0` from a parameter ladder and proved it
positive.  This file performs the remaining quantifier bookkeeping.

The geometric proof may select `epsilon0` and a compatible ladder `P` after
`beta`, `gamma`, and the two property hypotheses are known.  It must then
prove the fixed-parameter Frostman endpoint for every requested
`targetEpsilon`, while keeping that same `P` fixed.  Everything after this
endpoint, including positivity of the decrement, the infimum bootstrap, the
`beta = 0` limit, and the all-real boundary reduction, is mechanical.
-/

/-- A fixed ladder endpoint supplies the explicit positive pointwise
self-improvement output. -/
theorem exists_positive_explicitParameters_of_parameterLadder
    {epsilon0 beta gamma : Real}
    (P : ParameterLadder epsilon0 beta gamma)
    (hparameters : forall targetEpsilon : Real, 0 < targetEpsilon ->
      exists eta : Real, exists delta0 : NNReal,
        0 < eta /\ 0 < delta0 /\ delta0 <= (2 : NNReal)⁻¹ /\
          FrostmanAtParameters
            (gamma - sectionEightFixedNu P) targetEpsilon eta delta0) :
    exists nu : Real, 0 < nu /\
      forall targetEpsilon : Real, 0 < targetEpsilon ->
        exists eta : Real, exists delta0 : NNReal,
          0 < eta /\ 0 < delta0 /\ delta0 <= (2 : NNReal)⁻¹ /\
            FrostmanAtParameters (gamma - nu) targetEpsilon eta delta0 := by
  exact ⟨sectionEightFixedNu P, sectionEightFixedNu_pos P, hparameters⟩

/-- This is the most concrete current top-level handoff: the sole remaining
input selects one ladder and proves the actual Section 8 endpoint at that
fixed ladder. -/
theorem mainLemmaOne_of_parameterLadderEndpoint
    (hgeometry : forall beta gamma : Real,
      0 < beta -> beta < gamma -> gamma <= 1 ->
      KatzTaoProperty beta -> FrostmanProperty gamma ->
        exists epsilon0 : Real, exists P : ParameterLadder epsilon0 beta gamma,
          forall targetEpsilon : Real, 0 < targetEpsilon ->
            exists eta : Real, exists delta0 : NNReal,
              0 < eta /\ 0 < delta0 /\ delta0 <= (2 : NNReal)⁻¹ /\
                FrostmanAtParameters
                  (gamma - sectionEightFixedNu P)
                  targetEpsilon eta delta0)
    (beta : Real) :
    KatzTaoProperty beta -> FrostmanProperty beta := by
  apply mainLemmaOne_of_positive_explicitParameterSelfImprovement
  intro target source htargetPos htargetSource hsourceOne hKT hFSource
  obtain ⟨epsilon0, P, hparameters⟩ :=
    hgeometry target source htargetPos htargetSource hsourceOne hKT hFSource
  exact exists_positive_explicitParameters_of_parameterLadder P hparameters

#print axioms exists_positive_explicitParameters_of_parameterLadder
#print axioms mainLemmaOne_of_parameterLadderEndpoint

end

end Family8ParameterLadderSelfImprovementOrchestrationV1
