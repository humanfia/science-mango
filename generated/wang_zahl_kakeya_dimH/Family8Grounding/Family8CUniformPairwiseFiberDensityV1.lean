import Family8Grounding.Family8PairwiseFiberDensityFrostmanInheritanceV1
import Family8Grounding.Family8Def212ConvexWolffAtEveryScaleV2
import FamilyStickyGrounding.FamilyStickyScaleChainHierarchySiblingRigidityProducerV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8CUniformPairwiseFiberDensityV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8Def212ConvexWolffAtEveryScaleV2
open Family8Def212ConvexWolffAtEveryScaleV2.ScaleCover
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyScaleChainHierarchySiblingRigidityProducerV1

noncomputable section

variable {delta rho : NNReal} {iota : Type*}
  [Fintype iota] [DecidableEq iota]
  {fine : UniformTubeFamily delta iota}

/-- Definition 2.12 cardinal uniformity and the fine-tube volume sandwich
give pairwise comparability of the literal assigned fibre masses. -/
theorem fiberFamilyVolume_le_sixteen_mul_of_isCUniform
    (S : StickyScaleCover fine rho)
    (hdeltaHalf : delta ≤ (2 : NNReal)⁻¹)
    {C : ENNReal} (huniform : IsCUniform S C)
    (k : Fin S.coarseCard) (hk : k ∈ S.activeCoarse)
    (l : Fin S.coarseCard) (hl : l ∈ S.activeCoarse) :
    familyVolume (S.fiberFamily l) ≤
      (16 * C) * familyVolume (S.fiberFamily k) := by
  have hcard :
      ((S.fiber l).card : ENNReal) ≤
        C * ((S.fiber k).card : ENNReal) :=
    huniform l hl k hk
  calc
    familyVolume (S.fiberFamily l) ≤
        ((S.fiber l).card : ENNReal) *
          (8 * (delta : ENNReal) ^ 2) :=
      fiberFamilyVolume_le_card_mul_eight_sq hdeltaHalf S l
    _ ≤ (C * ((S.fiber k).card : ENNReal)) *
          (8 * (delta : ENNReal) ^ 2) := by
      gcongr
    _ = (16 * C) *
          (((S.fiber k).card : ENNReal) *
            ((delta : ENNReal) ^ 2 / 2)) := by
      have h16 : (16 : ENNReal) * (2 : ENNReal)⁻¹ = 8 := by
        rw [show (16 : ENNReal) = 8 * 2 by norm_num,
          mul_assoc, ENNReal.mul_inv_cancel] <;> norm_num
      rw [ENNReal.div_eq_inv_mul]
      rw [← h16]
      ac_rfl
    _ ≤ (16 * C) * familyVolume (S.fiberFamily k) := by
      gcongr
      exact card_mul_half_sq_le_fiberFamilyVolume hdeltaHalf S k

/-- At one common coarse radius, the same tube-volume sandwich contributes
one further factor sixteen.  Thus C-uniformity gives the pairwise density
comparison needed by cancellation-based Frostman inheritance, with no
absolute parent-density floor. -/
theorem pairwiseFiberDensity_of_isCUniform
    (S : StickyScaleCover fine rho)
    (hdeltaHalf : delta ≤ (2 : NNReal)⁻¹)
    (hrhoHalf : rho ≤ (2 : NNReal)⁻¹)
    {C : ENNReal} (huniform : IsCUniform S C)
    (k : Fin S.coarseCard) (hk : k ∈ S.activeCoarse)
    (l : Fin S.coarseCard) (hl : l ∈ S.activeCoarse) :
    familyVolume (S.fiberFamily l) *
        volume (S.coarse.tubes k).carrier ≤
      ((16 * C) * 16) *
        familyVolume (S.fiberFamily k) *
          volume (S.coarse.tubes l).carrier := by
  calc
    familyVolume (S.fiberFamily l) *
          volume (S.coarse.tubes k).carrier ≤
        ((16 * C) * familyVolume (S.fiberFamily k)) *
          (8 * (rho : ENNReal) ^ 2) := by
      exact mul_le_mul'
        (fiberFamilyVolume_le_sixteen_mul_of_isCUniform
          S hdeltaHalf huniform k hk l hl)
        ((S.coarse.tubes k).volume_le_eight_mul_sq_of_le_half hrhoHalf)
    _ = ((16 * C) * 16) *
          (familyVolume (S.fiberFamily k) *
            ((rho : ENNReal) ^ 2 / 2)) := by
      have h16 : (16 : ENNReal) * (2 : ENNReal)⁻¹ = 8 := by
        rw [show (16 : ENNReal) = 8 * 2 by norm_num,
          mul_assoc, ENNReal.mul_inv_cancel] <;> norm_num
      rw [ENNReal.div_eq_inv_mul]
      rw [← h16]
      ac_rfl
    _ ≤ ((16 * C) * 16) *
          (familyVolume (S.fiberFamily k) *
            volume (S.coarse.tubes l).carrier) := by
      gcongr
      exact (S.coarse.tubes l).half_sq_le_volume_of_le_half hrhoHalf
    _ = ((16 * C) * 16) *
          familyVolume (S.fiberFamily k) *
            volume (S.coarse.tubes l).carrier := by ac_rfl

#print axioms fiberFamilyVolume_le_sixteen_mul_of_isCUniform
#print axioms pairwiseFiberDensity_of_isCUniform

end
end Family8CUniformPairwiseFiberDensityV1
