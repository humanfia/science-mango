import Family8Grounding.Family8FixedJohnSelfImprovementRHSBridgeV17
import Family8Grounding.Family8FrostmanRHSScaleVolumeAlgebraV8
import Family8Grounding.Family8AllFrostmanStickyUnionProducerV1

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5000000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8FixedJohnSelfImprovementRHSBridgeV19

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Family8KatzTaoFrostmanPropertiesV1
open Family8GeneralizedKatzTaoMultiplicityV1
open Family8GeneralizedFrostmanMultiplicityV1
open Family8FiniteRandomRigidMotionIncidenceV1
open Family8FiniteRandomRigidMotionB2NormalizedDatumV1
open Family8FiniteRandomRigidMotionPaperFixedJohnExactMeanSelectorV4
open Family8FiniteRandomRigidMotionPaperFixedJohnBoundedPackingMeanV5
open Family8FiniteRandomRigidMotionPaperFixedJohnAutomaticDensityRepetitionsV2
open Family8FiniteRandomRigidMotionPaperFixedJohnFrostmanCWATailConnectorV5
open Family8FrostmanRHSScaleVolumeAlgebraV4
open Family8FrostmanRHSScaleVolumeAlgebraV8
open Family8AllFrostmanStickyUnionProducerV1
open Family8FixedJohnSelfImprovementRHSBridgeV17

noncomputable section

/-!
# Actual-datum exponent improvement after the fixed-John V5 endpoint

The source Frostman hypotheses themselves produce the required volume floor.
Consequently the only non-mechanical quantitative premise below is the
explicit power cap on the fixed-John transport scalar, together with the
displayed linear exponent budget.
-/

/-- Actual Family8 instance of scalar-power absorption.  This theorem neither
assumes `himprove` nor accepts the desired final RHS as a premise. -/
theorem source_averageMultiplicity_le_improvedRHS_of_fixedJohn_powerCap
    {sourceEpsilon targetEpsilon gamma nu kappa lambda : Real}
    {delta : NNReal}
    {iota : Type} [Fintype iota] [Nonempty iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible)
    (hF : FrostmanHypotheses D lambda)
    (omega : Fin (fixedJohnAutomaticDensityRepetitions D hD) ->
      FixedJohnPackingTranslation D hD)
    (selected : Finset
      (Fin (fixedJohnAutomaticDensityRepetitions D hD) × iota))
    (hgamma : gamma <= 2)
    (hsource :
      D.shading.averageMultiplicity <=
        (fixedJohnAutomaticGreedyLoss D hD : ENNReal) *
          frostmanMultiplicityRHS (delta / 8)
            (restrictActualTubeDatum
              (eighthNormalizedDatum
                (indexedRigidCopyDatum
                  (fun j => translationRigidMotion
                    (fixedJohnPackingGridVector D hD (omega j))) D))
              selected).actualFamilyVolume sourceEpsilon gamma)
    (hscalar :
      fixedJohnFrostmanTransportScalar
          (fixedJohnAutomaticGreedyLoss D hD : ENNReal)
          ((fixedJohnAutomaticDensityRepetitions D hD : ENNReal) *
            (1 / 4 : ENNReal)) sourceEpsilon gamma <=
        (delta : ENNReal) ^ (-kappa))
    (hnu : 0 <= nu)
    (hbudget :
      kappa + 2 * nu + lambda * nu / 2 <=
        targetEpsilon - sourceEpsilon) :
    D.shading.averageMultiplicity <=
      frostmanMultiplicityRHS delta D.actualFamilyVolume
        targetEpsilon (gamma - nu) := by
  have hsourceScalar :=
    source_averageMultiplicity_le_fixedJohnTransportScalar_mul_sourceRHS
      D hD omega selected hgamma hsource
  have hvolume :
      (delta : ENNReal) ^ lambda <= D.actualFamilyVolume :=
    delta_rpow_eta_le_actualFamilyVolume_of_frostman D hD hF
  have hvolumeTop : D.actualFamilyVolume ≠ ∞ := by
    exact familyVolume_ne_top D.family.bodyFamily
  have hnumeric :=
    scalar_mul_frostmanMultiplicityRHS_le_improved_of_power_budgets
      (sourceEpsilon := sourceEpsilon)
      (targetEpsilon := targetEpsilon) (gamma := gamma)
      (nu := nu) (kappa := kappa) (lambda := lambda)
      hD.delta_pos (hD.delta_le_half.trans (by norm_num))
      hvolumeTop hscalar hvolume hnu hbudget
  exact hsourceScalar.trans hnumeric

#print axioms
  source_averageMultiplicity_le_improvedRHS_of_fixedJohn_powerCap

end
end Family8FixedJohnSelfImprovementRHSBridgeV19
