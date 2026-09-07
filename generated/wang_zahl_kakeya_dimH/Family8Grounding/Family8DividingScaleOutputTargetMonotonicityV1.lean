import Family8Grounding.Family8EndpointIdentityDividingScaleOutputOrchestrationV4
import Mathlib.Tactic

/-!
# Target-loss monotonicity for the dividing-scale output

The right branch of `DividingScaleOutput` contains the Frostman
multiplicity RHS at loss `targetEpsilon / 4`.  On an admissible scale,
increasing that loss only enlarges the RHS.  This file records the resulting
monotonicity at the exact DSO interface, so a producer may work with a
smaller effective target loss and then return the requested output.
-/

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory
open scoped ENNReal NNReal

namespace Family8DividingScaleOutputTargetMonotonicityV1

open Submission.Kakeya.ConvexGeometry
open Family8EndpointIdentityDividingScaleOutputOrchestrationV4
open Family8KatzTaoFrostmanPropertiesV1
open Family8ParameterLadderV1

noncomputable section

variable {delta : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {epsilon0 beta gamma epsilonSmall epsilonLarge : Real}

/-- Local clean form of the only scalar monotonicity needed below.  It is
kept here because the older broad relative-scale monotonicity draft contains
unrelated unfinished nontrivial-threshold theorems. -/
theorem frostmanMultiplicityRHS_mono_epsilon_of_scale_le_one
    {actualVolume : ENNReal}
    (hdeltaOne : delta <= 1)
    (hepsilon : epsilonSmall <= epsilonLarge) :
    frostmanMultiplicityRHS delta actualVolume epsilonSmall gamma <=
      frostmanMultiplicityRHS delta actualVolume epsilonLarge gamma := by
  have hdeltaOneENN : (delta : ENNReal) <= 1 := by
    exact_mod_cast hdeltaOne
  have hpower : (delta : ENNReal) ^ (-epsilonSmall) <=
      (delta : ENNReal) ^ (-epsilonLarge) :=
    ENNReal.rpow_le_rpow_of_exponent_ge hdeltaOneENN (by linarith)
  unfold frostmanMultiplicityRHS
  exact mul_le_mul_left (mul_le_mul_left hpower _) _

/-- A DSO proof at a smaller displayed target loss is also a DSO proof at
any larger target loss. -/
theorem dividingScaleOutput_mono_targetEpsilon
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (P : ParameterLadder epsilon0 beta gamma)
    (hepsilon : epsilonSmall <= epsilonLarge)
    (hOutput : DividingScaleOutput D P epsilonSmall) :
    DividingScaleOutput D P epsilonLarge := by
  rcases hOutput with hVolume | hMultiplicity
  · exact Or.inl hVolume
  · rcases hMultiplicity with
      ⟨j, outerLoss, hj, hOuterLoss, hAverage⟩
    right
    refine ⟨j, outerLoss, hj, hOuterLoss, ?_⟩
    have hRHS :
        frostmanMultiplicityRHS
            delta D.actualFamilyVolume (epsilonSmall / 4) gamma <=
          frostmanMultiplicityRHS
            delta D.actualFamilyVolume (epsilonLarge / 4) gamma := by
      apply frostmanMultiplicityRHS_mono_epsilon_of_scale_le_one
        (hD.delta_le_half.trans (by norm_num))
      linarith
    exact hAverage.trans (mul_le_mul' le_rfl hRHS)

/-- Convenient capped-target form used by parameter-budget producers. -/
theorem dividingScaleOutput_of_min_targetEpsilon
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (P : ParameterLadder epsilon0 beta gamma)
    (targetEpsilon cap : Real)
    (hOutput : DividingScaleOutput D P (min targetEpsilon cap)) :
    DividingScaleOutput D P targetEpsilon :=
  dividingScaleOutput_mono_targetEpsilon D hD P
    (min_le_left targetEpsilon cap) hOutput

#print axioms dividingScaleOutput_mono_targetEpsilon
#print axioms dividingScaleOutput_of_min_targetEpsilon
#print axioms frostmanMultiplicityRHS_mono_epsilon_of_scale_le_one

end
end Family8DividingScaleOutputTargetMonotonicityV1
