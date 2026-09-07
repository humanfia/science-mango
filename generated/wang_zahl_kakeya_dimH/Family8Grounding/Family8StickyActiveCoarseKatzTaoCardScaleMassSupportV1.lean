import Family8Grounding.Family8StickyActiveCoarseKatzTaoCardScaleMassUpperV4
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8StickyActiveCoarseKatzTaoCardScaleMassSupportV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family6CanonicalFrostmanConstantCoreV1
open Family8KatzTaoFrostmanPropertiesV1
open FamilyStickyAtEveryScaleCoreV1
open Family8StickyParentHullVolumeBoundV1
open Family8ActiveCoarseCanonicalFrostmanXLowerV3.StickyScaleCover
open Family8ParentAggregatedShadingActiveCoarseXUpperV3.StickyScaleCover

noncomputable section

/-!
# Support-only Katz--Tao control of active coarse card--scale mass

This is the source-family-independent form of the canonical `1024` bound.
It uses only tube volume normalization, native Katz--Tao concentration on the
same sticky cover, and literal containment of its active coarse bodies in the
fixed radius-four body.  In particular, it does not ask for an admissibility
certificate for the fine family underlying the cover.
-/

namespace StickyScaleCover

variable {delta rho : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {fine : UniformTubeFamily delta index}

theorem activeCoarse_card_mul_half_sq_le_familyVolume_of_uniform
    (S : StickyScaleCover fine rho)
    (hrhoHalf : rho <= (2 : NNReal)⁻¹) :
    (S.activeCoarse.card : ENNReal) * ((rho : ENNReal) ^ 2 / 2) <=
      familyVolume S.activeCoarseFamily := by
  unfold familyVolume
    FamilyStickyAtEveryScaleCoreV1.StickyScaleCover.activeCoarseFamily
  simp only [UniformTubeFamily.bodyFamily]
  calc
    (S.activeCoarse.card : ENNReal) * ((rho : ENNReal) ^ 2 / 2) =
        ∑ _k : {k // k ∈ S.activeCoarse},
          ((rho : ENNReal) ^ 2 / 2) := by simp
    _ <= ∑ k : {k // k ∈ S.activeCoarse},
          volume (S.coarse.tubes k.1).carrier := by
      exact Finset.sum_le_sum fun k _ =>
        (S.coarse.tubes k.1).half_sq_le_volume_of_le_half hrhoHalf

theorem activeCoarseFamilyVolume_le_512_mul_of_isKatzTaoAtScale_of_contained
    (S : StickyScaleCover fine rho)
    {A : ENNReal} (hKT : S.IsKatzTaoAtScale A)
    (hcontained : forall k,
      (S.activeCoarseFamily k : Set Space) <=
        (closedBallFourBody : Set Space)) :
    familyVolume S.activeCoarseFamily <= 512 * A := by
  have hmass : containedMass S.activeCoarseFamily closedBallFourBody =
      familyVolume S.activeCoarseFamily :=
    containedMass_eq_familyVolume_of_contained
      S.activeCoarseFamily closedBallFourBody hcontained
  have hquotient := hKT closedBallFourBody
  have hvolume0 : volume (closedBallFourBody : Set Space) ≠ 0 := by
    exact ne_of_gt ((show (0 : ENNReal) < 1 by norm_num).trans_le
      one_le_volume_closedBallFourBody)
  have hvolumeTop : volume (closedBallFourBody : Set Space) ≠ ∞ :=
    closedBallFourBody.isCompact.measure_lt_top.ne
  have hfamily : familyVolume S.activeCoarseFamily <=
      A * volume (closedBallFourBody : Set Space) := by
    apply (ENNReal.div_le_iff hvolume0 hvolumeTop).1
    simpa only [concentration_eq_containedMass_div, hmass] using hquotient
  calc
    familyVolume S.activeCoarseFamily <=
        A * volume (closedBallFourBody : Set Space) := hfamily
    _ <= A * 512 := mul_le_mul' le_rfl volume_closedBall_zero_four_le_512
    _ = 512 * A := by ring

theorem activeCoarseCardScaleMass_le_1024_mul_of_isKatzTaoAtScale_of_contained
    (S : StickyScaleCover fine rho)
    (hrhoHalf : rho <= (2 : NNReal)⁻¹)
    {A : ENNReal} (hKT : S.IsKatzTaoAtScale A)
    (hcontained : forall k,
      (S.activeCoarseFamily k : Set Space) <=
        (closedBallFourBody : Set Space)) :
    (activeCoarseCardScaleMass S : ENNReal) <= 1024 * A := by
  have hlower := activeCoarse_card_mul_half_sq_le_familyVolume_of_uniform
    S hrhoHalf
  have hupper :=
    activeCoarseFamilyVolume_le_512_mul_of_isKatzTaoAtScale_of_contained
      S hKT hcontained
  calc
    (activeCoarseCardScaleMass S : ENNReal) =
        2 * ((S.activeCoarse.card : ENNReal) *
          ((rho : ENNReal) ^ 2 / 2)) := by
      simp only [activeCoarseCardScaleMass, ENNReal.coe_mul,
        ENNReal.coe_natCast, ENNReal.coe_pow]
      symm
      calc
        2 * ((S.activeCoarse.card : ENNReal) *
            ((rho : ENNReal) ^ 2 / 2)) =
            (S.activeCoarse.card : ENNReal) *
              (((rho : ENNReal) ^ 2 / 2) * 2) := by ac_rfl
        _ = (S.activeCoarse.card : ENNReal) * (rho : ENNReal) ^ 2 := by
          rw [ENNReal.div_mul_cancel (by norm_num) (by norm_num)]
    _ <= 2 * familyVolume S.activeCoarseFamily :=
      mul_le_mul' le_rfl hlower
    _ <= 2 * (512 * A) := mul_le_mul' le_rfl hupper
    _ = 1024 * A := by ring

#print axioms activeCoarse_card_mul_half_sq_le_familyVolume_of_uniform
#print axioms activeCoarseFamilyVolume_le_512_mul_of_isKatzTaoAtScale_of_contained
#print axioms activeCoarseCardScaleMass_le_1024_mul_of_isKatzTaoAtScale_of_contained

end StickyScaleCover
end
end Family8StickyActiveCoarseKatzTaoCardScaleMassSupportV1
