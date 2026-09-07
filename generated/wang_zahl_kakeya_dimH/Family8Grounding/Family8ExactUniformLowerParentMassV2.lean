import Family8Grounding.Family8CoarseTubePartitionExactUniformStickyFiberV4
import Family8Grounding.Family8LowerParentMassCoarseKatzTaoV1

/-!
# Exact-uniform branching produces genuine lower parent mass, V2

This is the fresh-build-safe successor of V1.  It is independent of V1 and
marks the positive parent radius which is intentionally not needed for
nonzeroness of an `ENNReal` quotient; positivity is used separately for its
finiteness.
-/

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 3000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8ExactUniformLowerParentMassV2

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.JointTubeFactoring
open Submission.Kakeya.Uniformity
open Family8CoarseTubePartitionExactUniformStickyFiberV4
open Family8JointTubeFactoringExactUniformProp66AProductV4
open Family8LowerParentMassCoarseKatzTaoV1
open FamilyStickyAtEveryScaleCoreV1

noncomputable section

variable {delta rho : NNReal} {iota : Type} {coarseCard : Nat}
  [Fintype iota] [DecidableEq iota]
  {fine : UniformTubeFamily delta iota}
  {coarse : UniformTubeFamily rho (Fin coarseCard)}

def exactBranchingParentMassDensity
    (P : CoarseTubePartition fine coarse) : ENNReal :=
  ((P.branching : Nat) : ENNReal) * ((delta : ENNReal) ^ 2 / 2) /
    (8 * (rho : ENNReal) ^ 2)

theorem branching_mul_half_sq_le_fiberFamilyVolume
    (P : CoarseTubePartition fine coarse)
    (hloss : P.branchingLoss = 1)
    (hdeltaHalf : delta <= (2 : NNReal)⁻¹)
    {k : Fin coarseCard} (hk : k ∈ P.coarseIndices) :
    (P.branching : ENNReal) * ((delta : ENNReal) ^ 2 / 2) <=
      familyVolume ((exactPartitionStickyCover P).fiberFamily k) := by
  unfold familyVolume
  simp only [StickyScaleCover.fiberFamily,
    UniformTubeFamily.bodyFamily, Tube.coe_body]
  calc
    (P.branching : ENNReal) * ((delta : ENNReal) ^ 2 / 2) =
        ∑ _i : {i // i ∈ P.fiber k},
          (delta : ENNReal) ^ 2 / 2 := by
      rw [show P.branching = (P.fiber k).card by
        exact (fiber_card_eq_branching_of_branchingLoss_eq_one
          P hloss hk).symm]
      simp
    _ <= ∑ i : {i // i ∈ P.fiber k},
        volume (fine.tubes i.1).carrier := by
      exact Finset.sum_le_sum fun i _ =>
        (fine.tubes i.1).half_sq_le_volume_of_le_half hdeltaHalf

theorem exactBranchingParentMassDensity_mul_parentVolume_le_fiberFamilyVolume
    (P : CoarseTubePartition fine coarse)
    (hloss : P.branchingLoss = 1)
    (hdeltaHalf : delta <= (2 : NNReal)⁻¹)
    (hdelta : 0 < delta)
    (hrhoHalf : rho <= (2 : NNReal)⁻¹)
    {k : Fin coarseCard} (hk : k ∈ P.coarseIndices) :
    exactBranchingParentMassDensity P *
        volume ((exactPartitionStickyCover P).coarse.tubes k).carrier <=
      familyVolume ((exactPartitionStickyCover P).fiberFamily k) := by
  have hratio : exactBranchingParentMassDensity P <=
      familyVolume ((exactPartitionStickyCover P).fiberFamily k) /
        volume ((exactPartitionStickyCover P).coarse.tubes k).carrier := by
    unfold exactBranchingParentMassDensity
    apply ENNReal.div_le_div
    · exact branching_mul_half_sq_le_fiberFamilyVolume
        P hloss hdeltaHalf hk
    · exact (coarse.tubes k).volume_le_eight_mul_sq_of_le_half hrhoHalf
  have hvol0 :
      volume ((exactPartitionStickyCover P).coarse.tubes k).carrier ≠ 0 := by
    change volume (coarse.tubes k).carrier ≠ 0
    exact (coarse.tubes k).volume_pos (hdelta.trans_le P.scale_le) |>.ne'
  have hvolTop :
      volume ((exactPartitionStickyCover P).coarse.tubes k).carrier ≠ ∞ := by
    change volume (coarse.tubes k).carrier ≠ ∞
    exact (coarse.tubes k).volume_lt_top.ne
  exact (ENNReal.le_div_iff_mul_le
    (Or.inl hvol0) (Or.inl hvolTop)).1 hratio

theorem branching_pos_of_coarseIndices_nonempty
    (P : CoarseTubePartition fine coarse)
    (hloss : P.branchingLoss = 1)
    (hcoarse : P.coarseIndices.Nonempty) :
    0 < P.branching := by
  obtain ⟨k, hk⟩ := hcoarse
  obtain ⟨i, hi, hip⟩ := P.parent_surjective k hk
  have hifiber : i ∈ P.fiber k := by
    exact (P.index.mem_fiber i k).2 ⟨hi, hip⟩
  have hcardPos : 0 < (P.fiber k).card :=
    Finset.card_pos.mpr ⟨i, hifiber⟩
  rwa [fiber_card_eq_branching_of_branchingLoss_eq_one P hloss hk] at hcardPos

theorem exactBranchingParentMassDensity_ne_zero
    (P : CoarseTubePartition fine coarse)
    (hloss : P.branchingLoss = 1)
    (hcoarse : P.coarseIndices.Nonempty)
    (hdelta : 0 < delta) (_hrho : 0 < rho) :
    exactBranchingParentMassDensity P ≠ 0 := by
  have hbranch : 0 < (P.branching : ENNReal) := by
    exact_mod_cast branching_pos_of_coarseIndices_nonempty P hloss hcoarse
  unfold exactBranchingParentMassDensity
  apply ENNReal.div_ne_zero.mpr
  constructor
  · exact mul_ne_zero hbranch.ne'
      (ENNReal.div_ne_zero.mpr
        ⟨pow_ne_zero 2 (ENNReal.coe_ne_zero.mpr hdelta.ne'), by norm_num⟩)
  · exact ENNReal.mul_ne_top (by norm_num)
      (ENNReal.pow_ne_top ENNReal.coe_ne_top)

theorem exactBranchingParentMassDensity_ne_top
    (P : CoarseTubePartition fine coarse) (hrho : 0 < rho) :
    exactBranchingParentMassDensity P ≠ ∞ := by
  unfold exactBranchingParentMassDensity
  apply ENNReal.div_ne_top
  · exact ENNReal.mul_ne_top (by simp)
      (ENNReal.div_ne_top
        (ENNReal.pow_ne_top ENNReal.coe_ne_top) (by norm_num))
  · exact mul_ne_zero (by norm_num)
      (pow_ne_zero 2 (ENNReal.coe_ne_zero.mpr hrho.ne'))

theorem exactPartitionStickyCover_isKatzTaoAtScale_of_source
    (P : CoarseTubePartition fine coarse)
    (hloss : P.branchingLoss = 1)
    (hcoarse : P.coarseIndices.Nonempty)
    (hdelta : 0 < delta) (hrho : 0 < rho)
    (hdeltaHalf : delta <= (2 : NNReal)⁻¹)
    (hrhoHalf : rho <= (2 : NNReal)⁻¹)
    {A : ENNReal} (hfineKT : IsKatzTao A fine.bodyFamily) :
    (exactPartitionStickyCover P).IsKatzTaoAtScale
      (A * (exactBranchingParentMassDensity P)⁻¹) := by
  apply isKatzTaoAtScale_of_lowerParentMass
    (exactPartitionStickyCover P)
    (exactBranchingParentMassDensity_ne_zero
      P hloss hcoarse hdelta hrho)
    (exactBranchingParentMassDensity_ne_top P hrho)
  · intro k hk
    exact
      exactBranchingParentMassDensity_mul_parentVolume_le_fiberFamilyVolume
        P hloss hdeltaHalf hdelta hrhoHalf hk
  · exact hfineKT

#print axioms exactBranchingParentMassDensity
#print axioms branching_mul_half_sq_le_fiberFamilyVolume
#print axioms
  exactBranchingParentMassDensity_mul_parentVolume_le_fiberFamilyVolume
#print axioms branching_pos_of_coarseIndices_nonempty
#print axioms exactBranchingParentMassDensity_ne_zero
#print axioms exactBranchingParentMassDensity_ne_top
#print axioms exactPartitionStickyCover_isKatzTaoAtScale_of_source

end
end Family8ExactUniformLowerParentMassV2
