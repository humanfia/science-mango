import Family8Grounding.Family8FixedJohnSelfImprovementRHSBridgeV8

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5000000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8FixedJohnSelfImprovementRHSBridgeV15

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Family8KatzTaoFrostmanPropertiesV1
open Family8GeneralizedKatzTaoMultiplicityV1
open Family8GeneralizedFrostmanMultiplicityV1
open Family8RestrictedActualDatumDensityRetentionV1
open Family8FiniteRandomRigidMotionIncidenceV1
open Family8FiniteRandomRigidMotionB2NormalizedDatumV1
open Family8FiniteRandomRigidMotionPaperFixedJohnCopyTransportCoreV1
open Family8FixedJohnSelfImprovementRHSBridgeV8

noncomputable section

/-! ## Selected copied-volume transport -/

/-- Any selected subtype of an eighth-normalized finite translation copy has
at most `card(tau)/4` times the summed source volume. -/
theorem normalizedIndexedTranslation_restrict_actualFamilyVolume_le
    {tau iota : Type} [Fintype tau] [DecidableEq tau]
    [Fintype iota] [DecidableEq iota]
    {delta : NNReal} (v : tau -> Space)
    (D : ActualTubeDatum delta iota)
    (hdeltaHalf : delta <= (2 : NNReal)⁻¹)
    (selected : Finset (tau × iota)) :
    (restrictActualTubeDatum
      (eighthNormalizedDatum
        (indexedRigidCopyDatum
          (fun j => translationRigidMotion (v j)) D))
      selected).actualFamilyVolume <=
        (Fintype.card tau : ENNReal) *
          ((1 / 4 : ENNReal) * D.actualFamilyVolume) := by
  let copied := indexedRigidCopyDatum
    (fun j : tau => translationRigidMotion (v j)) D
  let normalized := eighthNormalizedDatum copied
  let refined := restrictActualTubeDatum normalized selected
  change refined.actualFamilyVolume <=
    (Fintype.card tau : ENNReal) *
      ((1 / 4 : ENNReal) * D.actualFamilyVolume)
  calc
    refined.actualFamilyVolume <= normalized.actualFamilyVolume :=
      restrictActualTubeDatum_actualFamilyVolume_le normalized selected
    _ = (Fintype.card tau : ENNReal) *
        (eighthNormalizedDatum D).actualFamilyVolume := by
      simpa only [normalized, copied] using
        eighthNormalizedIndexedTranslation_actualFamilyVolume v D
    _ <= (Fintype.card tau : ENNReal) *
        ((1 / 4 : ENNReal) * D.actualFamilyVolume) :=
      mul_le_mul_right
        (eighthNormalizedDatum_actualFamilyVolume_le_quarter D hdeltaHalf) _

#print axioms normalizedIndexedTranslation_restrict_actualFamilyVolume_le

end
end Family8FixedJohnSelfImprovementRHSBridgeV15
