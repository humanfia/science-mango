import Family8Grounding.Family8FixedJohnSelfImprovementRHSBridgeV15
import Family8Grounding.Family8FrostmanRHSScaleVolumeAlgebraV4

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5000000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8FixedJohnSelfImprovementRHSBridgeV17

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
open Family8FixedJohnSelfImprovementRHSBridgeV15
open Family8FrostmanRHSScaleVolumeAlgebraV4

noncomputable section

/-!
# Fixed-John V5 endpoint in source-scale/source-volume normalization

This connector consumes the actual multiplicity conclusion already returned
by V5.  It does not assume the desired improved RHS.  Its conclusion exposes
the one remaining scalar multiplier explicitly.
-/

/-- Substitute the proved selected-volume estimate into the V5 Frostman RHS.
All geometric information still needed for self-improvement is now a power
bound on `fixedJohnFrostmanTransportScalar`; no final-RHS callback appears. -/
theorem source_averageMultiplicity_le_fixedJohnTransportScalar_mul_sourceRHS
    {gamma epsilon : Real} {delta : NNReal}
    {iota : Type} [Fintype iota] [Nonempty iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible)
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
              selected).actualFamilyVolume epsilon gamma) :
    D.shading.averageMultiplicity <=
      fixedJohnFrostmanTransportScalar
          (fixedJohnAutomaticGreedyLoss D hD : ENNReal)
          ((fixedJohnAutomaticDensityRepetitions D hD : ENNReal) *
            (1 / 4 : ENNReal)) epsilon gamma *
        frostmanMultiplicityRHS delta D.actualFamilyVolume epsilon gamma := by
  let v : Fin (fixedJohnAutomaticDensityRepetitions D hD) -> Space :=
    fun j => fixedJohnPackingGridVector D hD (omega j)
  let normalized := eighthNormalizedDatum
    (indexedRigidCopyDatum
      (fun j => translationRigidMotion (v j)) D)
  let selectedVolume :=
    (restrictActualTubeDatum normalized selected).actualFamilyVolume
  have hvolume0 :=
    normalizedIndexedTranslation_restrict_actualFamilyVolume_le
      v D hD.delta_le_half selected
  have hvolume : selectedVolume <=
      ((fixedJohnAutomaticDensityRepetitions D hD : ENNReal) *
        (1 / 4 : ENNReal)) * D.actualFamilyVolume := by
    change
      (restrictActualTubeDatum normalized selected).actualFamilyVolume <= _
    calc
      (restrictActualTubeDatum normalized selected).actualFamilyVolume <=
          (fixedJohnAutomaticDensityRepetitions D hD : ENNReal) *
            ((1 / 4 : ENNReal) * D.actualFamilyVolume) := by
        simpa only [normalized, v, Fintype.card_fin] using hvolume0
      _ = ((fixedJohnAutomaticDensityRepetitions D hD : ENNReal) *
            (1 / 4 : ENNReal)) * D.actualFamilyVolume := by ac_rfl
  have htransport :=
    loss_mul_frostmanMultiplicityRHS_div_eight_le_source
      (delta := delta) (selectedVolume := selectedVolume)
      (sourceVolume := D.actualFamilyVolume)
      (loss := (fixedJohnAutomaticGreedyLoss D hD : ENNReal))
      (copyVolumeFactor :=
        (fixedJohnAutomaticDensityRepetitions D hD : ENNReal) *
          (1 / 4 : ENNReal))
      (epsilon := epsilon) (gamma := gamma) hgamma hvolume
  exact hsource.trans (by
    simpa only [selectedVolume, normalized, v] using htransport)

#print axioms
  source_averageMultiplicity_le_fixedJohnTransportScalar_mul_sourceRHS

end
end Family8FixedJohnSelfImprovementRHSBridgeV17
