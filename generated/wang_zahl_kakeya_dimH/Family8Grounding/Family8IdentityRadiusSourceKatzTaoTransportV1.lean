import FamilyStickyGrounding.FamilyStickyScaleChainSelectedCanonicalCoverCoordinatesProducerV1
import Submission.Kakeya.ConvexFactoring.TubeVolumeBounds
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8IdentityRadiusSourceKatzTaoTransportV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyScaleChainSelectedCanonicalCoverCoordinatesProducerV1

noncomputable section

/-!
# Source Katz--Tao transport to the identity-radius cover

Changing a source `delta`-tube to radius `rho` increases its area by at most
the explicit ratio `16 * (rho / delta)^2` encoded below.  Since the active
coarse indices of the identity-radius cover embed back into the original
source indices, a source Katz--Tao estimate transports to the actual coarse
family with exactly this geometric loss.  This replaces the crude active-card
bound for this cover and uses no partition or compatibility hypothesis.
-/

universe u

variable {delta rho : NNReal} {iota : Type u}
  [Fintype iota] [DecidableEq iota]
  {fine : UniformTubeFamily delta iota}

/-- The explicit radius-enlargement volume ratio used in the transport. -/
def identityRadiusKatzTaoVolumeRatio (delta rho : NNReal) : ENNReal :=
  (8 * (rho : ENNReal) ^ 2) / ((delta : ENNReal) ^ 2 / 2)

/-- A radius-changed tube has volume at most the explicit radius-enlargement
ratio times the volume of the original tube. -/
theorem changeRadius_volume_le_identityRadiusRatio_mul_source
    (T : Tube delta)
    (hdeltaPos : 0 < delta) (hdeltaHalf : delta <= (2 : NNReal)⁻¹)
    (hrhoHalf : rho <= (2 : NNReal)⁻¹) :
    volume (T.changeRadius rho).carrier <=
      identityRadiusKatzTaoVolumeRatio delta rho * volume T.carrier := by
  let floor : ENNReal := (delta : ENNReal) ^ 2 / 2
  let upper : ENNReal := 8 * (rho : ENNReal) ^ 2
  have hfloor0 : floor ≠ 0 := by
    dsimp only [floor]
    exact ENNReal.div_ne_zero.mpr
      ⟨pow_ne_zero 2 (ENNReal.coe_ne_zero.mpr hdeltaPos.ne'), by norm_num⟩
  have hfloorTop : floor ≠ ∞ := by
    dsimp only [floor]
    exact ENNReal.div_ne_top (ENNReal.pow_ne_top ENNReal.coe_ne_top)
      (by norm_num)
  have hupper : volume (T.changeRadius rho).carrier <= upper :=
    (T.changeRadius rho).volume_le_eight_mul_sq_of_le_half hrhoHalf
  have hlower : floor <= volume T.carrier :=
    T.half_sq_le_volume_of_le_half hdeltaHalf
  calc
    volume (T.changeRadius rho).carrier <= upper := hupper
    _ = (upper / floor) * floor := by
      rw [ENNReal.div_mul_cancel hfloor0 hfloorTop]
    _ <= (upper / floor) * volume T.carrier := by gcongr
    _ = identityRadiusKatzTaoVolumeRatio delta rho * volume T.carrier := by
      rfl

/-- Active coarse occurrences of the identity-radius cover inject into the
original source occurrence type by undoing its canonical finite reindexing. -/
def identityRadiusActiveEmbedding
    (fine : UniformTubeFamily delta iota) (rho : NNReal)
    (hdelta : delta <= rho) :
    {k // k ∈ (identityRadiusScaleCover fine rho hdelta).activeCoarse} ↪ iota where
  toFun k := (Fintype.equivFin iota).symm k.1
  inj' := by
    intro k l hkl
    apply Subtype.ext
    apply (Fintype.equivFin iota).symm.injective
    exact hkl

/-- Every coarse tube in the identity-radius cover is literally the
radius-changed source tube at the embedded source occurrence. -/
@[simp] theorem identityRadius_activeCoarseFamily_eq_changeRadius_source
    (fine : UniformTubeFamily delta iota) (rho : NNReal)
    (hdelta : delta <= rho)
    (k : {k // k ∈ (identityRadiusScaleCover fine rho hdelta).activeCoarse}) :
    (identityRadiusScaleCover fine rho hdelta).activeCoarseFamily k =
      ((fine.tubes (identityRadiusActiveEmbedding fine rho hdelta k)).changeRadius
        rho).body := by
  rfl

/-- An identity-radius cover inherits source Katz--Tao with only the explicit
tube-volume enlargement ratio. -/
theorem identityRadiusScaleCover_isKatzTaoAtScale_of_sourceKatzTao
    (fine : UniformTubeFamily delta iota)
    (rho : NNReal) (hdelta : delta <= rho)
    (hdeltaPos : 0 < delta) (hdeltaHalf : delta <= (2 : NNReal)⁻¹)
    (hrhoHalf : rho <= (2 : NNReal)⁻¹)
    {A : ENNReal} (hKT : IsKatzTao A fine.bodyFamily) :
    (identityRadiusScaleCover fine rho hdelta).IsKatzTaoAtScale
      (identityRadiusKatzTaoVolumeRatio delta rho * A) := by
  classical
  intro K
  apply IsKatzTaoAt.concentration_le
  let S := identityRadiusScaleCover fine rho hdelta
  let e := identityRadiusActiveEmbedding fine rho hdelta
  let ratio := identityRadiusKatzTaoVolumeRatio delta rho
  have hsubset :
      (containedIndices S.activeCoarseFamily K).image e ⊆
        containedIndices fine.bodyFamily K := by
    intro i hi
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hi
    rw [mem_containedIndices] at hk ⊢
    have hsmall : (fine.tubes (e k)).carrier ⊆
        ((fine.tubes (e k)).changeRadius rho).carrier :=
      (fine.tubes (e k)).carrier_subset_changeRadius hdelta
    exact hsmall.trans (by simpa [S, e] using hk)
  unfold IsKatzTaoAt containedMass
  calc
    (∑ k ∈ containedIndices S.activeCoarseFamily K,
        volume (S.activeCoarseFamily k : Set Space)) <=
      ∑ k ∈ containedIndices S.activeCoarseFamily K,
        ratio * volume (fine.bodyFamily (e k) : Set Space) := by
          apply Finset.sum_le_sum
          intro k _hk
          exact changeRadius_volume_le_identityRadiusRatio_mul_source
            (fine.tubes (e k)) hdeltaPos hdeltaHalf hrhoHalf
    _ = ratio * ∑ k ∈ containedIndices S.activeCoarseFamily K,
        volume (fine.bodyFamily (e k) : Set Space) := by
          rw [Finset.mul_sum]
    _ = ratio * ∑ i ∈ (containedIndices S.activeCoarseFamily K).image e,
        volume (fine.bodyFamily i : Set Space) := by
          congr 1
          rw [Finset.sum_image]
          intro k _hk l _hl hkl
          exact e.injective hkl
    _ <= ratio * ∑ i ∈ containedIndices fine.bodyFamily K,
        volume (fine.bodyFamily i : Set Space) := by
          exact mul_le_mul_of_nonneg_left
            (Finset.sum_le_sum_of_subset hsubset) bot_le
    _ <= ratio * (A * volume (K : Set Space)) := by
          exact mul_le_mul_of_nonneg_left (hKT K) bot_le
    _ = (identityRadiusKatzTaoVolumeRatio delta rho * A) *
        volume (K : Set Space) := by
          dsimp only [ratio]
          ac_rfl

#print axioms changeRadius_volume_le_identityRadiusRatio_mul_source
#print axioms identityRadiusActiveEmbedding
#print axioms identityRadius_activeCoarseFamily_eq_changeRadius_source
#print axioms identityRadiusScaleCover_isKatzTaoAtScale_of_sourceKatzTao

end

end Family8IdentityRadiusSourceKatzTaoTransportV1
