import Family8Grounding.Family8CommonExactAndRelativeScaleParametersV1
import Family8Grounding.Family8MultiplicityLossMonotonicityV4
import Family8Grounding.Family8NonzeroMassParameterEndpointOrchestrationV3

open scoped ENNReal NNReal

namespace Family8RelativeScaleFixedNuEndpointOrchestrationV1

open Submission.Kakeya.ConvexGeometry
open Family8KatzTaoFrostmanPropertiesV1
open Family8GeneralizedScaleTrivialBranchV1
open Family8ParameterLadderV1
open Family8Section8FixedPositiveSelfImprovementBudgetV3
open Family8CommonExactAndRelativeScaleParametersV1
open Family8MultiplicityLossMonotonicityV4
open Family8NonzeroMassParameterEndpointOrchestrationV3

noncomputable section

set_option autoImplicit false
set_option warningAsError true

/-!
# Relative-scale source parameters to the fixed-decrement endpoint

The parameter ladder, hence its positive decrement, is fixed before the
requested target loss.  For each target loss we request all source properties
once at the smaller of one quarter of that loss and the fixed decrement.
Displayed-loss monotonicity then supplies the paper-shaped inputs:

* exact and full relative-scale Katz--Tao at the fixed decrement;
* exact and full relative-scale Frostman at one quarter of the target loss.

All four estimates use one positive hypothesis exponent and terminal scale.
The final theorem leaves only the datum-level Section 8 improvement as its
geometric input; parameter extraction, zero mass, the fixed positive
decrement, and the global exponent bootstrap are handled by existing lemmas.
-/

/-- One source loss that is simultaneously below the target-loss reserve and
the fixed Section 8 decrement. -/
def sectionEightSourceLoss
    {epsilon0 beta gamma : Real}
    (P : ParameterLadder epsilon0 beta gamma)
    (targetEpsilon : Real) : Real :=
  min (targetEpsilon / 4) (sectionEightFixedNu P)

theorem sectionEightSourceLoss_pos
    {epsilon0 beta gamma targetEpsilon : Real}
    (P : ParameterLadder epsilon0 beta gamma)
    (hTarget : 0 < targetEpsilon) :
    0 < sectionEightSourceLoss P targetEpsilon := by
  unfold sectionEightSourceLoss
  exact lt_min (by linarith) (sectionEightFixedNu_pos P)

theorem sectionEightSourceLoss_le_targetQuarter
    {epsilon0 beta gamma : Real}
    (P : ParameterLadder epsilon0 beta gamma)
    (targetEpsilon : Real) :
    sectionEightSourceLoss P targetEpsilon <= targetEpsilon / 4 := by
  exact min_le_left _ _

theorem sectionEightSourceLoss_le_fixedNu
    {epsilon0 beta gamma : Real}
    (P : ParameterLadder epsilon0 beta gamma)
    (targetEpsilon : Real) :
    sectionEightSourceLoss P targetEpsilon <= sectionEightFixedNu P := by
  exact min_le_right _ _

/-- A single property invocation supplies the four source estimates used by
the fixed-decrement Section 8 argument. -/
theorem exists_sectionEight_common_source_parameters
    {epsilon0 beta gamma targetEpsilon : Real}
    (P : ParameterLadder epsilon0 beta gamma)
    (hKT : KatzTaoProperty beta)
    (hF : FrostmanProperty gamma)
    (hBeta0 : 0 <= beta)
    (hGamma0 : 0 <= gamma)
    (hGamma1 : gamma <= 1)
    (hTarget : 0 < targetEpsilon) :
    exists eta : Real, exists delta0 : NNReal,
      0 < eta /\ 0 < delta0 /\ delta0 <= (2 : NNReal)⁻¹ /\
        KatzTaoAtParameters
          beta (sectionEightFixedNu P) eta delta0 /\
        FrostmanAtParameters gamma (targetEpsilon / 4) eta delta0 /\
        KatzTaoAtRelativeScaleParameters
          beta (sectionEightFixedNu P) eta delta0 /\
        FrostmanAtRelativeScaleParameters
          gamma (targetEpsilon / 4) eta delta0 := by
  have hSource : 0 < sectionEightSourceLoss P targetEpsilon :=
    sectionEightSourceLoss_pos P hTarget
  obtain ⟨eta, delta0, heta, hdelta0, hdelta0Half,
      hKTExact, hFExact, hKTRelative, hFRelative⟩ :=
    exists_common_exactAndRelativeScale_parameters_same_epsilon
      hKT hF hBeta0 hGamma0 hGamma1 hSource
  have hSourceNu :
      sectionEightSourceLoss P targetEpsilon <= sectionEightFixedNu P :=
    sectionEightSourceLoss_le_fixedNu P targetEpsilon
  have hSourceTarget :
      sectionEightSourceLoss P targetEpsilon <= targetEpsilon / 4 :=
    sectionEightSourceLoss_le_targetQuarter P targetEpsilon
  exact ⟨eta, delta0, heta, hdelta0, hdelta0Half,
    katzTaoAtParameters_of_epsilon_le hKTExact hSourceNu,
    frostmanAtParameters_of_epsilon_le hFExact hSourceTarget,
    katzTaoAtRelativeScaleParameters_of_epsilon_le
      hKTRelative hSourceNu,
    frostmanAtRelativeScaleParameters_of_epsilon_le
      hFRelative hSourceTarget⟩

/-- Main Lemma 1 from the remaining Section 8 datum-level endpoint.

The ladder is fixed outside `targetEpsilon`.  The endpoint receives the four
source estimates above and returns a positive output hypothesis exponent, a
positive raw validity scale, and the improved multiplicity bound only for
nonzero-mass admissible data. -/
theorem mainLemmaOne_of_relativeScale_fixedNu_nonzeroMassEndpoint
    (hSectionEight : forall beta gamma : Real,
      0 < beta -> beta < gamma -> gamma <= 1 ->
        exists epsilon0 : Real, exists P : ParameterLadder epsilon0 beta gamma,
          forall targetEpsilon : Real, 0 < targetEpsilon ->
          forall eta : Real, forall delta0 : NNReal,
            0 < eta -> 0 < delta0 -> delta0 <= (2 : NNReal)⁻¹ ->
            KatzTaoAtParameters
              beta (sectionEightFixedNu P) eta delta0 ->
            FrostmanAtParameters gamma (targetEpsilon / 4) eta delta0 ->
            KatzTaoAtRelativeScaleParameters
              beta (sectionEightFixedNu P) eta delta0 ->
            FrostmanAtRelativeScaleParameters
              gamma (targetEpsilon / 4) eta delta0 ->
              exists outputEta : Real, exists rawDelta0 : NNReal,
                0 < outputEta /\ 0 < rawDelta0 /\
                  forall (delta : NNReal) (index : Type)
                    [Fintype index] [DecidableEq index]
                    (D : ActualTubeDatum delta index),
                      D.IsAdmissible ->
                      delta <= rawDelta0 ->
                      FrostmanHypotheses D outputEta ->
                      D.shading.shadingMass ≠ 0 ->
                      D.shading.averageMultiplicity <=
                        frostmanMultiplicityRHS
                          delta D.actualFamilyVolume targetEpsilon
                            (gamma - sectionEightFixedNu P))
    (beta : Real) :
    KatzTaoProperty beta -> FrostmanProperty beta := by
  apply mainLemmaOne_of_parameterLadderNonzeroMassEndpoint
  intro target source hTargetPos hTargetSource hSourceOne hKT hF
  obtain ⟨epsilon0, P, hEndpoint⟩ :=
    hSectionEight target source hTargetPos hTargetSource hSourceOne
  refine ⟨epsilon0, P, ?_⟩
  intro targetEpsilon hTargetEpsilon
  have hSource0 : 0 <= source := by linarith
  obtain ⟨eta, delta0, heta, hdelta0, hdelta0Half,
      hKTExact, hFExact, hKTRelative, hFRelative⟩ :=
    exists_sectionEight_common_source_parameters
      P hKT hF hTargetPos.le hSource0 hSourceOne hTargetEpsilon
  exact hEndpoint targetEpsilon hTargetEpsilon eta delta0
    heta hdelta0 hdelta0Half hKTExact hFExact hKTRelative hFRelative

#print axioms sectionEightSourceLoss_pos
#print axioms sectionEightSourceLoss_le_targetQuarter
#print axioms sectionEightSourceLoss_le_fixedNu
#print axioms exists_sectionEight_common_source_parameters
#print axioms mainLemmaOne_of_relativeScale_fixedNu_nonzeroMassEndpoint

end

end Family8RelativeScaleFixedNuEndpointOrchestrationV1
