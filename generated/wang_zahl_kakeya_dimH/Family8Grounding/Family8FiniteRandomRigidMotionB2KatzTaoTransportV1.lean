import Family8Grounding.Family8FiniteRandomRigidMotionB2NormalizedDatumV1
import Submission.Kakeya.ConvexFactoring.TubeVolumeBounds
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8FiniteRandomRigidMotionB2KatzTaoTransportV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family6AffineConvexVolumeCoreV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8FiniteRandomRigidMotionB2NormalizationCoreV1
open Family8FiniteRandomRigidMotionB2NormalizationCarrierV1
open Family8FiniteRandomRigidMotionB2DilationVolumeV1
open Family8FiniteRandomRigidMotionB2NormalizedDatumV1

noncomputable section

/-!
# Katz--Tao transport through the honest B2 normalization

The central eighth of each moved tube is dilated into a genuine unit tube at
radius `delta/8`.  Extending the axis costs only a fixed volume ratio.  A
normalized tube contained in a convex test body forces the dilated source
tube to be contained there, hence the source tube lies in the affine
preimage.  Combining this with the exact Jacobian gives a global Katz--Tao
constant `128` and no geometric callback.
-/

theorem eighthNormalizedTube_volume_le_quarter
    {delta : NNReal} (T : Tube delta)
    (hdeltaHalf : delta <= (2 : NNReal)⁻¹) :
    volume (eighthNormalizedTube T).carrier <=
      (1 / 4 : ENNReal) * volume T.carrier := by
  have hnormalizedHalf : delta / 8 <= (2 : NNReal)⁻¹ := by
    exact (div_le_self (show 0 <= delta from bot_le) (by norm_num : (1 : NNReal) <= 8)).trans
      hdeltaHalf
  have hupper :=
    (eighthNormalizedTube T).volume_le_eight_mul_sq_of_le_half
      hnormalizedHalf
  have hlower := T.half_sq_le_volume_of_le_half hdeltaHalf
  calc
    volume (eighthNormalizedTube T).carrier <=
        8 * ((delta / 8 : NNReal) : ENNReal) ^ 2 := hupper
    _ = (1 / 4 : ENNReal) * ((delta : ENNReal) ^ 2 / 2) := by
      apply (ENNReal.toReal_eq_toReal_iff'
        (by finiteness) (by finiteness)).mp
      norm_num [ENNReal.toReal_mul, ENNReal.toReal_pow,
        ENNReal.toReal_div, ENNReal.coe_div]
      ring
    _ <= (1 / 4 : ENNReal) * volume T.carrier :=
      mul_le_mul_of_nonneg_left hlower bot_le

theorem normalized_containedIndices_subset_affinePreimage
    {iota : Type} [Fintype iota] [DecidableEq iota]
    {delta : NNReal} (D : ActualTubeDatum delta iota)
    (K : ConvexBody Space) :
    containedIndices (eighthNormalizedDatum D).family.bodyFamily K ⊆
      containedIndices D.family.bodyFamily
        (affinePreimageConvexBody eighthDilationAffineEquiv K) := by
  classical
  intro i hi
  rw [mem_containedIndices] at hi ⊢
  change (eighthNormalizedTube (D.family.tubes i)).carrier ⊆
    (K : Set Space) at hi
  change (D.family.tubes i).carrier ⊆
    eighthDilationAffineEquiv.symm '' (K : Set Space)
  apply (affineImage_subset_iff_subset_preimage
    eighthDilationAffineEquiv (D.family.tubes i).carrier (K : Set Space)).mp
  change eighthDilationPoint '' (D.family.tubes i).carrier ⊆ (K : Set Space)
  exact
    (image_eighthDilation_tube_carrier_subset_normalizedTube
      (D.family.tubes i)).trans hi

theorem containedMass_eighthNormalizedDatum_le_quarter_preimage
    {iota : Type} [Fintype iota] [DecidableEq iota]
    {delta : NNReal} (D : ActualTubeDatum delta iota)
    (hdeltaHalf : delta <= (2 : NNReal)⁻¹)
    (K : ConvexBody Space) :
    containedMass (eighthNormalizedDatum D).family.bodyFamily K <=
      (1 / 4 : ENNReal) *
        containedMass D.family.bodyFamily
          (affinePreimageConvexBody eighthDilationAffineEquiv K) := by
  classical
  unfold containedMass
  let sourceIndices := containedIndices D.family.bodyFamily
    (affinePreimageConvexBody eighthDilationAffineEquiv K)
  let normalizedIndices :=
    containedIndices (eighthNormalizedDatum D).family.bodyFamily K
  have hsubset : normalizedIndices ⊆ sourceIndices := by
    exact normalized_containedIndices_subset_affinePreimage D K
  calc
    (∑ i ∈ normalizedIndices,
        volume ((eighthNormalizedDatum D).family.bodyFamily i : Set Space)) <=
        ∑ i ∈ normalizedIndices,
          (1 / 4 : ENNReal) *
            volume (D.family.bodyFamily i : Set Space) := by
      apply Finset.sum_le_sum
      intro i hi
      change volume (eighthNormalizedTube (D.family.tubes i)).carrier <=
        (1 / 4 : ENNReal) * volume (D.family.tubes i).carrier
      exact eighthNormalizedTube_volume_le_quarter
        (D.family.tubes i) hdeltaHalf
    _ = (1 / 4 : ENNReal) *
        ∑ i ∈ normalizedIndices,
          volume (D.family.bodyFamily i : Set Space) := by
      rw [Finset.mul_sum]
    _ <= (1 / 4 : ENNReal) *
        ∑ i ∈ sourceIndices,
          volume (D.family.bodyFamily i : Set Space) := by
      exact mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum_of_subset hsubset) bot_le

/-- Honest normalization transports global Katz--Tao control with the fixed
constant `128 = (1/4) / (1/512)`. -/
theorem eighthNormalizedDatum_isKatzTao
    {iota : Type} [Fintype iota] [DecidableEq iota]
    {delta : NNReal} (D : ActualTubeDatum delta iota)
    (hdeltaHalf : delta <= (2 : NNReal)⁻¹)
    {C : ENNReal} (hKT : IsKatzTao C D.family.bodyFamily) :
    IsKatzTao (128 * C) (eighthNormalizedDatum D).family.bodyFamily := by
  intro K
  unfold IsKatzTaoAt
  let Kpre := affinePreimageConvexBody eighthDilationAffineEquiv K
  calc
    containedMass (eighthNormalizedDatum D).family.bodyFamily K <=
        (1 / 4 : ENNReal) * containedMass D.family.bodyFamily Kpre :=
      containedMass_eighthNormalizedDatum_le_quarter_preimage
        D hdeltaHalf K
    _ <= (1 / 4 : ENNReal) * (C * volume (Kpre : Set Space)) :=
      mul_le_mul_of_nonneg_left (hKT Kpre) bot_le
    _ = 128 * C * ((1 / 512 : ENNReal) * volume (Kpre : Set Space)) := by
      have hcoeff :
          (128 : ENNReal) * (1 / 512 : ENNReal) = 1 / 4 := by
        apply (ENNReal.toReal_eq_toReal_iff'
          (by finiteness) (by finiteness)).mp
        norm_num [ENNReal.toReal_mul, ENNReal.toReal_div]
      calc
        (1 / 4 : ENNReal) * (C * volume (Kpre : Set Space)) =
            ((128 : ENNReal) * (1 / 512 : ENNReal)) *
              (C * volume (Kpre : Set Space)) := by rw [hcoeff]
        _ = 128 * C *
              ((1 / 512 : ENNReal) * volume (Kpre : Set Space)) := by
            ac_rfl
    _ = 128 * C * volume (K : Set Space) := by
      rw [volume_eq_affineJacobian_mul_preimage
        eighthDilationAffineEquiv K, eighthDilationAffineJacobian]

#print axioms eighthNormalizedTube_volume_le_quarter
#print axioms normalized_containedIndices_subset_affinePreimage
#print axioms containedMass_eighthNormalizedDatum_le_quarter_preimage
#print axioms eighthNormalizedDatum_isKatzTao

end
end Family8FiniteRandomRigidMotionB2KatzTaoTransportV1
