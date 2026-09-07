import Family8Grounding.Family8RelativeScaleFixedNuEndpointOrchestrationV1
import Family8Grounding.Family8AllFrostmanStickyUnionProducerV1

open scoped ENNReal NNReal

namespace Family8OuterMiddleFixedNuEndpointOrchestrationV1

open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Family8KatzTaoFrostmanPropertiesV1
open Family8GeneralizedScaleTrivialBranchV1
open Family8ParameterLadderV1
open Family8Section8FixedPositiveSelfImprovementBudgetV3
open Family8AllFrostmanStickyUnionProducerV1
open Family8RelativeScaleFixedNuEndpointOrchestrationV1

noncomputable section

set_option autoImplicit false
set_option warningAsError true

/-!
# Outer-three and middle-ten factorization endpoint

The official Section 8 gain has a factorized form.  The two outside
Frostman estimates contribute an aggregate loss bounded by
`delta ^ (-3 * P.eta j)`, while the middle long interval contributes
`delta ^ (10 * P.eta j)`.  The fixed-positive numerical gate already turns
their product into the exponent decrement `sectionEightFixedNu P`.

This file also derives the gate's source-volume floor from the actual
Frostman hypotheses.  Thus the remaining geometric theorem need only
produce a stage, an outside-loss scalar, its power cap, and the factorized
triple-product multiplicity estimate.  The improved right-hand side is not
an input to that theorem.
-/

/-- A smaller Frostman hypothesis exponent supplies the volume floor at the
fixed decrement. -/
theorem fixedNu_volumeFloor_of_frostman
    {epsilon0 beta gamma outputEta : Real}
    (P : ParameterLadder epsilon0 beta gamma)
    {delta : NNReal} {index : Type}
    [Fintype index] [DecidableEq index]
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (hOutputEta : outputEta <= sectionEightFixedNu P)
    (hF : FrostmanHypotheses D outputEta) :
    (delta : ENNReal) ^ (P.eta 0) <= D.actualFamilyVolume := by
  have hdeltaOne : (delta : ENNReal) <= 1 := by
    exact_mod_cast hD.delta_le_half.trans (by norm_num)
  have hpower :
      (delta : ENNReal) ^ (P.eta 0) <=
        (delta : ENNReal) ^ outputEta := by
    exact ENNReal.rpow_le_rpow_of_exponent_ge hdeltaOne hOutputEta
  exact hpower.trans
    (delta_rpow_eta_le_actualFamilyVolume_of_frostman D hD hF)

/-- The honest outer-loss cap and middle gain imply the improved source
multiplicity estimate. -/
theorem averageMultiplicity_le_fixedNuRHS_of_outerThree_middleTen
    {epsilon0 beta gamma outputEta targetEpsilon : Real}
    (P : ParameterLadder epsilon0 beta gamma)
    (j : Nat) (hStage : j <= P.N)
    (hBeta0 : 0 <= beta) (hGamma1 : gamma <= 1)
    {delta : NNReal} {index : Type}
    [Fintype index] [DecidableEq index]
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (hOutputEta : outputEta <= sectionEightFixedNu P)
    (hF : FrostmanHypotheses D outputEta)
    (hTarget : 0 < targetEpsilon)
    (outerLoss : ENNReal)
    (hOuter : outerLoss <=
      (delta : ENNReal) ^ (-3 * P.eta j))
    (hFactorized :
      D.shading.averageMultiplicity <=
        (outerLoss * (delta : ENNReal) ^ (10 * P.eta j)) *
          frostmanMultiplicityRHS
            delta D.actualFamilyVolume (targetEpsilon / 4) gamma) :
    D.shading.averageMultiplicity <=
      frostmanMultiplicityRHS delta D.actualFamilyVolume targetEpsilon
        (gamma - sectionEightFixedNu P) := by
  have hvolume :
      (delta : ENNReal) ^ (P.eta 0) <= D.actualFamilyVolume :=
    fixedNu_volumeFloor_of_frostman P D hD hOutputEta hF
  have hvolumeTop : D.actualFamilyVolume ≠ (⊤ : ENNReal) := by
    exact familyVolume_ne_top D.family.bodyFamily
  have hSourceTarget : targetEpsilon / 4 <= targetEpsilon := by
    linarith
  exact hFactorized.trans
    (sectionEight_outerThree_middleTen_fixedPositive_improvement
      P j hStage hBeta0 hGamma1 hD.delta_pos
      (hD.delta_le_half.trans (by norm_num)) hvolumeTop hvolume
      hOuter hSourceTarget)

/-- Main Lemma 1 from the factorized long-interval geometric output.

For each datum, geometry may choose its stopping stage and outside-loss
scalar.  Their two displayed inequalities are precisely the non-mechanical
content remaining from the dividing-scale and three-factor argument. -/
theorem mainLemmaOne_of_outerThree_middleTen_factorization
    (hLongInterval : forall beta gamma : Real,
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
                0 < outputEta /\
                outputEta <= sectionEightFixedNu P /\
                0 < rawDelta0 /\
                  forall (delta : NNReal) (index : Type)
                    [Fintype index] [DecidableEq index]
                    (D : ActualTubeDatum delta index),
                      D.IsAdmissible ->
                      delta <= rawDelta0 ->
                      FrostmanHypotheses D outputEta ->
                      D.shading.shadingMass ≠ 0 ->
                        exists j : Nat, exists outerLoss : ENNReal,
                          j <= P.N /\
                          outerLoss <=
                            (delta : ENNReal) ^ (-3 * P.eta j) /\
                          D.shading.averageMultiplicity <=
                            (outerLoss *
                              (delta : ENNReal) ^ (10 * P.eta j)) *
                            frostmanMultiplicityRHS
                              delta D.actualFamilyVolume
                                (targetEpsilon / 4) gamma)
    (beta : Real) :
    KatzTaoProperty beta -> FrostmanProperty beta := by
  apply mainLemmaOne_of_relativeScale_fixedNu_nonzeroMassEndpoint
  intro target source hTargetPos hTargetSource hSourceOne
  obtain ⟨epsilon0, P, hEndpoint⟩ :=
    hLongInterval target source hTargetPos hTargetSource hSourceOne
  refine ⟨epsilon0, P, ?_⟩
  intro targetEpsilon hTargetEpsilon eta delta0 heta hdelta0 hdelta0Half
    hKTExact hFExact hKTRelative hFRelative
  obtain ⟨outputEta, rawDelta0, hOutputEta, hOutputEtaNu,
      hRawDelta0, hFactorized⟩ :=
    hEndpoint targetEpsilon hTargetEpsilon eta delta0
      heta hdelta0 hdelta0Half hKTExact hFExact hKTRelative hFRelative
  refine ⟨outputEta, rawDelta0, hOutputEta, hRawDelta0, ?_⟩
  intro delta index _ _ D hD hdelta hF hmass
  obtain ⟨j, outerLoss, hStage, hOuter, hAverage⟩ :=
    hFactorized delta index D hD hdelta hF hmass
  exact averageMultiplicity_le_fixedNuRHS_of_outerThree_middleTen
    P j hStage hTargetPos.le hSourceOne D hD hOutputEtaNu hF
      hTargetEpsilon outerLoss hOuter hAverage

#print axioms fixedNu_volumeFloor_of_frostman
#print axioms averageMultiplicity_le_fixedNuRHS_of_outerThree_middleTen
#print axioms mainLemmaOne_of_outerThree_middleTen_factorization

end

end Family8OuterMiddleFixedNuEndpointOrchestrationV1
