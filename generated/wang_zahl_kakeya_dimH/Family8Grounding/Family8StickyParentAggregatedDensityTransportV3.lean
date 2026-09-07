import FamilyStickyGrounding.FamilyStickyHierarchyEndpointPrefixShadingTransportV1
import FamilyStickyGrounding.FamilyStickyScaleChainActualStrictLossWithConstantV1
import Submission.Kakeya.ConvexFactoring.TubeVolumeBounds
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8StickyParentAggregatedDensityTransportV3

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyAdjacentScaleStepV2.StickyScaleCover
open FamilyStickyScaleChainActualStrictLossWithConstantV1.StickyScaleCover
open FamilyStickyHierarchyEndpointPrefixShadingTransportV1.StickyScaleCover

noncomputable section

/-!
# Honest density transport under parent aggregation

Parent aggregation loses at most the literal fibre cardinality in shading
mass.  Standard tube-volume bounds compare the active parent and active fine
denominators.  The resulting density inequality below keeps the full scale
factor explicit.  It makes no claim that an arbitrary active refinement
retains a fixed fraction of an ambient shading.
-/

namespace StickyScaleCover

variable {delta rho : NNReal} {iota : Type*}
  [Fintype iota] [DecidableEq iota]
  {fine : UniformTubeFamily delta iota}
  (S : StickyScaleCover fine rho)

theorem activeCoarseFamilyVolume_le_card_mul_eight_sq
    (hrhoHalf : rho <= (2 : NNReal)⁻¹) :
    familyVolume S.activeCoarseFamily <=
      (S.activeCoarse.card : ENNReal) *
        (8 * (rho : ENNReal) ^ 2) := by
  unfold familyVolume
    FamilyStickyAtEveryScaleCoreV1.StickyScaleCover.activeCoarseFamily
  simp only [UniformTubeFamily.bodyFamily, Tube.coe_body]
  calc
    (∑ k : {k // k ∈ S.activeCoarse},
        volume (S.coarse.tubes k.1).carrier) <=
        ∑ _k : {k // k ∈ S.activeCoarse},
          8 * (rho : ENNReal) ^ 2 := by
      exact Finset.sum_le_sum fun k _ =>
        (S.coarse.tubes k.1).volume_le_eight_mul_sq_of_le_half hrhoHalf
    _ = (S.activeCoarse.card : ENNReal) *
        (8 * (rho : ENNReal) ^ 2) := by
      simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ,
        Fintype.card_coe]

theorem activeCoarse_card_mul_half_sq_le_activeFineFamilyVolume
    (hdeltaHalf : delta <= (2 : NNReal)⁻¹) :
    (S.activeCoarse.card : ENNReal) *
        ((delta : ENNReal) ^ 2 / 2) <=
      familyVolume (activeFineFamily S) := by
  have hcardNat : S.activeCoarse.card <= S.activeFine.card :=
    activeCoarse_card_le_activeFine_card S
  have hcard : (S.activeCoarse.card : ENNReal) <=
      (S.activeFine.card : ENNReal) := by
    exact_mod_cast hcardNat
  calc
    (S.activeCoarse.card : ENNReal) *
        ((delta : ENNReal) ^ 2 / 2) <=
      (S.activeFine.card : ENNReal) *
        ((delta : ENNReal) ^ 2 / 2) :=
      mul_le_mul' hcard le_rfl
    _ = ∑ _i : {i // i ∈ S.activeFine},
        ((delta : ENNReal) ^ 2 / 2) := by
      simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ,
        Fintype.card_coe]
    _ <= familyVolume (activeFineFamily S) := by
      unfold familyVolume activeFineFamily
      simp only [UniformTubeFamily.bodyFamily, Tube.coe_body]
      exact Finset.sum_le_sum fun i _ =>
        (fine.tubes i.1).half_sq_le_volume_of_le_half hdeltaHalf

theorem activeCoarseFamilyVolume_mul_half_sq_le_eight_sq_mul_activeFineFamilyVolume
    (hdeltaHalf : delta <= (2 : NNReal)⁻¹)
    (hrhoHalf : rho <= (2 : NNReal)⁻¹) :
    familyVolume S.activeCoarseFamily *
        ((delta : ENNReal) ^ 2 / 2) <=
      (8 * (rho : ENNReal) ^ 2) *
        familyVolume (activeFineFamily S) := by
  calc
    familyVolume S.activeCoarseFamily *
        ((delta : ENNReal) ^ 2 / 2) <=
      ((S.activeCoarse.card : ENNReal) *
          (8 * (rho : ENNReal) ^ 2)) *
        ((delta : ENNReal) ^ 2 / 2) :=
      mul_le_mul' (activeCoarseFamilyVolume_le_card_mul_eight_sq
        S hrhoHalf) le_rfl
    _ = (8 * (rho : ENNReal) ^ 2) *
        ((S.activeCoarse.card : ENNReal) *
          ((delta : ENNReal) ^ 2 / 2)) := by
      ac_rfl
    _ <= (8 * (rho : ENNReal) ^ 2) *
        familyVolume (activeFineFamily S) :=
      mul_le_mul' le_rfl
        (activeCoarse_card_mul_half_sq_le_activeFineFamilyVolume
          S hdeltaHalf)

theorem activeFineDensity_mul_half_sq_le_fiber_mul_eight_sq_mul_parentDensity
    (Y : Shading fine.bodyFamily)
    (M : Nat)
    (hM : forall k : {k // k ∈ S.activeCoarse},
      ((activeIndexFactorization S).fiber k).card <= M)
    (hactive : S.activeCoarse.Nonempty)
    (hdelta : 0 < delta) (hrho : 0 < rho)
    (hdeltaHalf : delta <= (2 : NNReal)⁻¹)
    (hrhoHalf : rho <= (2 : NNReal)⁻¹) :
    (activeFineShading S Y).shadingDensity *
        ((delta : ENNReal) ^ 2 / 2) <=
      (M : ENNReal) * (8 * (rho : ENNReal) ^ 2) *
        (parentAggregatedShading S Y).shadingDensity := by
  have hmass :
      (activeFineShading S Y).shadingMass <=
        (M : ENNReal) * (parentAggregatedShading S Y).shadingMass := by
    simpa only [nsmul_eq_mul] using
      activeFineShading_shadingMass_le_nsmul_parent_of_fiberCard_le
        S Y M hM
  have hcoarsePos : 0 < familyVolume S.activeCoarseFamily := by
    unfold familyVolume
      FamilyStickyAtEveryScaleCoreV1.StickyScaleCover.activeCoarseFamily
    rw [Finset.sum_pos_iff]
    obtain ⟨k, hk⟩ := hactive
    exact ⟨⟨k, hk⟩, Finset.mem_univ _, by
      simpa only [UniformTubeFamily.bodyFamily, Tube.coe_body] using
        (S.coarse.tubes k).volume_pos hrho⟩
  have hfineNonempty : S.activeFine.Nonempty := by
    obtain ⟨k, hk⟩ := hactive
    obtain ⟨i, hi, _hparent⟩ := S.parent_surjective k hk
    exact ⟨i, hi⟩
  have hfinePos : 0 < familyVolume (activeFineFamily S) := by
    unfold familyVolume activeFineFamily
    rw [Finset.sum_pos_iff]
    obtain ⟨i, hi⟩ := hfineNonempty
    exact ⟨⟨i, hi⟩, Finset.mem_univ _, by
      simpa only [UniformTubeFamily.bodyFamily, Tube.coe_body] using
        (fine.tubes i).volume_pos hdelta⟩
  have hratio :
      ((delta : ENNReal) ^ 2 / 2) /
          familyVolume (activeFineFamily S) <=
        (8 * (rho : ENNReal) ^ 2) /
          familyVolume S.activeCoarseFamily := by
    apply (ENNReal.le_div_iff_mul_le
      (Or.inl hcoarsePos.ne')
      (Or.inl (familyVolume_ne_top S.activeCoarseFamily))).2
    rw [show ((delta : ENNReal) ^ 2 / 2) /
        familyVolume (activeFineFamily S) *
          familyVolume S.activeCoarseFamily =
        (((delta : ENNReal) ^ 2 / 2) *
          familyVolume S.activeCoarseFamily) /
            familyVolume (activeFineFamily S) by
      simp only [div_eq_mul_inv]
      ring]
    apply (ENNReal.div_le_iff_le_mul
      (Or.inl hfinePos.ne')
      (Or.inl (familyVolume_ne_top (activeFineFamily S)))).2
    simpa only [mul_comm] using
      activeCoarseFamilyVolume_mul_half_sq_le_eight_sq_mul_activeFineFamilyVolume
        S hdeltaHalf hrhoHalf
  unfold Shading.shadingDensity
  calc
    ((activeFineShading S Y).shadingMass /
          familyVolume (activeFineFamily S)) *
        ((delta : ENNReal) ^ 2 / 2) =
      (activeFineShading S Y).shadingMass *
        (((delta : ENNReal) ^ 2 / 2) /
          familyVolume (activeFineFamily S)) := by
      simp only [div_eq_mul_inv]
      ring
    _ <= ((M : ENNReal) *
          (parentAggregatedShading S Y).shadingMass) *
        ((8 * (rho : ENNReal) ^ 2) /
          familyVolume S.activeCoarseFamily) :=
      mul_le_mul' hmass hratio
    _ = (M : ENNReal) * (8 * (rho : ENNReal) ^ 2) *
        ((parentAggregatedShading S Y).shadingMass /
          familyVolume S.activeCoarseFamily) := by
      simp only [div_eq_mul_inv]
      ring

#print axioms activeCoarseFamilyVolume_le_card_mul_eight_sq
#print axioms activeCoarse_card_mul_half_sq_le_activeFineFamilyVolume
#print axioms
  activeCoarseFamilyVolume_mul_half_sq_le_eight_sq_mul_activeFineFamilyVolume
#print axioms
  activeFineDensity_mul_half_sq_le_fiber_mul_eight_sq_mul_parentDensity

end StickyScaleCover
end
end Family8StickyParentAggregatedDensityTransportV3
