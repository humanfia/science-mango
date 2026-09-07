import Family8Grounding.Family8CoarseTubePartitionExactUniformStickyFiberV4
import Family8Grounding.Family8LowerParentMassCoarseKatzTaoV1

/-!
# Approximate-uniform branching gives lower parent mass

This is the general-loss analogue of the exact-uniform V2 producer.  Every
`CoarseTubePartition` supplies

`branching / branchingLoss <= fiberCard`.

After the uniform tube-volume bounds this gives a genuine lower parent-mass
density and hence a coarse Katz--Tao certificate.  In particular it applies
to the logarithmic `AlmostCoverTubeFactoring` output, whose branching loss is
two and whose retained-mass loss is polylogarithmic.
-/

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 3000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8GeneralBranchingLowerParentMassV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.JointTubeFactoring
open Submission.Kakeya.Uniformity
open Family8CoarseTubePartitionExactUniformStickyFiberV4
open Family8LowerParentMassCoarseKatzTaoV1
open FamilyStickyAtEveryScaleCoreV1

noncomputable section

variable {delta rho : NNReal} {iota : Type} {coarseCard : Nat}
  [Fintype iota] [DecidableEq iota]
  {fine : UniformTubeFamily delta iota}
  {coarse : UniformTubeFamily rho (Fin coarseCard)}

/-- The branching count guaranteed in each fibre after paying the declared
branching loss. -/
def effectiveBranchingNNReal
    (P : CoarseTubePartition fine coarse) : NNReal :=
  (P.branching : NNReal) / (P.branchingLoss : NNReal)

/-- The lower parent-mass density obtained from approximate uniformity. -/
def branchingLossParentMassDensityNNReal
    (P : CoarseTubePartition fine coarse) : NNReal :=
  effectiveBranchingNNReal P * (delta ^ 2 / 2) / (8 * rho ^ 2)

theorem effectiveBranchingNNReal_pos
    (P : CoarseTubePartition fine coarse) :
    0 < effectiveBranchingNNReal P := by
  have hbranch : 0 < (P.branching : NNReal) := by
    exact_mod_cast P.branching_pos
  have hloss : 0 < (P.branchingLoss : NNReal) := by
    exact_mod_cast P.branchingLoss_pos
  unfold effectiveBranchingNNReal
  positivity

theorem branchingLossParentMassDensityNNReal_pos
    (P : CoarseTubePartition fine coarse)
    (hdelta : 0 < delta) (hrho : 0 < rho) :
    0 < branchingLossParentMassDensityNNReal P := by
  have heffective := effectiveBranchingNNReal_pos P
  unfold branchingLossParentMassDensityNNReal
  positivity

theorem coe_branchingLossParentMassDensityNNReal
    (P : CoarseTubePartition fine coarse) (hrho : 0 < rho) :
    (branchingLossParentMassDensityNNReal P : ENNReal) =
      (effectiveBranchingNNReal P : ENNReal) *
        ((delta : ENNReal) ^ 2 / 2) / (8 * (rho : ENNReal) ^ 2) := by
  unfold branchingLossParentMassDensityNNReal
  rw [ENNReal.coe_div (by positivity : (8 * rho ^ 2 : NNReal) ≠ 0)]
  rw [ENNReal.coe_mul]
  rw [ENNReal.coe_div (by norm_num : (2 : NNReal) ≠ 0)]
  rfl

theorem effectiveBranchingNNReal_le_fiber_card
    (P : CoarseTubePartition fine coarse)
    {k : Fin coarseCard} (hk : k ∈ P.coarseIndices) :
    effectiveBranchingNNReal P <= (P.fiber k).card := by
  have hloss : 0 < (P.branchingLoss : NNReal) := by
    exact_mod_cast P.branchingLoss_pos
  have hbranch :
      (P.branching : NNReal) <=
        (P.branchingLoss : NNReal) * ((P.fiber k).card : NNReal) := by
    exact_mod_cast P.branching_le_loss_mul_fiber k hk
  unfold effectiveBranchingNNReal
  exact (div_le_iff₀ hloss).2 (by simpa [mul_comm] using hbranch)

theorem effectiveBranching_mul_half_sq_le_fiberFamilyVolume
    (P : CoarseTubePartition fine coarse)
    (hdeltaHalf : delta <= (2 : NNReal)⁻¹)
    {k : Fin coarseCard} (hk : k ∈ P.coarseIndices) :
    (effectiveBranchingNNReal P : ENNReal) *
        ((delta : ENNReal) ^ 2 / 2) <=
      familyVolume ((exactPartitionStickyCover P).fiberFamily k) := by
  unfold familyVolume
  simp only [StickyScaleCover.fiberFamily,
    UniformTubeFamily.bodyFamily, Tube.coe_body]
  calc
    (effectiveBranchingNNReal P : ENNReal) *
          ((delta : ENNReal) ^ 2 / 2) <=
        ((P.fiber k).card : ENNReal) *
          ((delta : ENNReal) ^ 2 / 2) := by
      exact mul_le_mul'
        (ENNReal.coe_le_coe.mpr
          (effectiveBranchingNNReal_le_fiber_card P hk)) le_rfl
    _ = ∑ _i : {i // i ∈ P.fiber k},
          (delta : ENNReal) ^ 2 / 2 := by simp
    _ <= ∑ i : {i // i ∈ P.fiber k},
        volume (fine.tubes i.1).carrier := by
      exact Finset.sum_le_sum fun i _ =>
        (fine.tubes i.1).half_sq_le_volume_of_le_half hdeltaHalf

theorem branchingLossParentMassDensity_mul_parentVolume_le_fiberFamilyVolume
    (P : CoarseTubePartition fine coarse)
    (hdeltaHalf : delta <= (2 : NNReal)⁻¹)
    (hdelta : 0 < delta)
    (hrho : 0 < rho)
    (hrhoHalf : rho <= (2 : NNReal)⁻¹)
    {k : Fin coarseCard} (hk : k ∈ P.coarseIndices) :
    (branchingLossParentMassDensityNNReal P : ENNReal) *
        volume ((exactPartitionStickyCover P).coarse.tubes k).carrier <=
      familyVolume ((exactPartitionStickyCover P).fiberFamily k) := by
  have hratio :
      (branchingLossParentMassDensityNNReal P : ENNReal) <=
        familyVolume ((exactPartitionStickyCover P).fiberFamily k) /
          volume ((exactPartitionStickyCover P).coarse.tubes k).carrier := by
    rw [coe_branchingLossParentMassDensityNNReal P hrho]
    apply ENNReal.div_le_div
    · exact effectiveBranching_mul_half_sq_le_fiberFamilyVolume
        P hdeltaHalf hk
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

/-- The coarse Katz--Tao coefficient generated by a general branching-loss
partition, represented in `NNReal`. -/
def branchingLossCoarseKatzTaoNNReal (sourceA : NNReal)
    (P : CoarseTubePartition fine coarse) : NNReal :=
  sourceA / branchingLossParentMassDensityNNReal P

theorem coe_branchingLossCoarseKatzTaoNNReal
    (sourceA : NNReal) (P : CoarseTubePartition fine coarse)
    (hdelta : 0 < delta) (hrho : 0 < rho) :
    (branchingLossCoarseKatzTaoNNReal sourceA P : ENNReal) =
      (sourceA : ENNReal) *
        (branchingLossParentMassDensityNNReal P : ENNReal)⁻¹ := by
  have hlower : 0 < branchingLossParentMassDensityNNReal P :=
    branchingLossParentMassDensityNNReal_pos P hdelta hrho
  unfold branchingLossCoarseKatzTaoNNReal
  rw [ENNReal.coe_div hlower.ne']
  rfl

theorem exactPartitionStickyCover_isKatzTaoAtScale_of_generalBranching
    (P : CoarseTubePartition fine coarse)
    (hdelta : 0 < delta) (hrho : 0 < rho)
    (hdeltaHalf : delta <= (2 : NNReal)⁻¹)
    (hrhoHalf : rho <= (2 : NNReal)⁻¹)
    (sourceA : NNReal)
    (hfineKT : IsKatzTao (sourceA : ENNReal) fine.bodyFamily) :
    (exactPartitionStickyCover P).IsKatzTaoAtScale
      (branchingLossCoarseKatzTaoNNReal sourceA P : ENNReal) := by
  rw [coe_branchingLossCoarseKatzTaoNNReal sourceA P hdelta hrho]
  apply isKatzTaoAtScale_of_lowerParentMass
    (exactPartitionStickyCover P)
    (ENNReal.coe_ne_zero.mpr
      (branchingLossParentMassDensityNNReal_pos P hdelta hrho).ne')
    ENNReal.coe_ne_top
  · intro k hk
    exact
      branchingLossParentMassDensity_mul_parentVolume_le_fiberFamilyVolume
        P hdeltaHalf hdelta hrho hrhoHalf hk
  · exact hfineKT

#print axioms effectiveBranchingNNReal
#print axioms branchingLossParentMassDensityNNReal
#print axioms effectiveBranchingNNReal_pos
#print axioms branchingLossParentMassDensityNNReal_pos
#print axioms coe_branchingLossParentMassDensityNNReal
#print axioms effectiveBranchingNNReal_le_fiber_card
#print axioms effectiveBranching_mul_half_sq_le_fiberFamilyVolume
#print axioms
  branchingLossParentMassDensity_mul_parentVolume_le_fiberFamilyVolume
#print axioms branchingLossCoarseKatzTaoNNReal
#print axioms coe_branchingLossCoarseKatzTaoNNReal
#print axioms
  exactPartitionStickyCover_isKatzTaoAtScale_of_generalBranching

end
end Family8GeneralBranchingLowerParentMassV1
