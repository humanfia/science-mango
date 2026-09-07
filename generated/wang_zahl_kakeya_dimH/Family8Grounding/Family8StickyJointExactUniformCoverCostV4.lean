import Family8Grounding.Family8JointTubeFactoringExactUniformProp66AProductV4
import Family8Grounding.Family8StickyParentAggregatedDensityTransportV3
import Mathlib.Tactic

/-!
# Automatic joint-factor cover cost for a literal Sticky scale cover

A Sticky cover already supplies the actual parent map, parent occupation, and
carrier containment. Uniform tube-volume bounds give a fully explicit global
cover cost `A * 8 rho^2 / (delta^2 / 2)`. This feeds the repository's genuine
exact-cardinality `JointTubeFactoring` producer; no cover-cost callback or
abstract count equality remains.
-/

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8StickyJointExactUniformCoverCostV4

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.JointTubeFactoring
open Submission.Kakeya.Uniformity
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyAdjacentScaleStepV2.StickyScaleCover
open Family8Prop66AFrostmanAspectGainAlgebraV1
open Family8Prop66AOuterInnerProductAlgebraV1
open Family8StickyParentAggregatedDensityTransportV3.StickyScaleCover
open Family8JointTubeFactoringExactUniformProp66AProductV4

noncomputable section

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false

variable {delta rho : NNReal} {iota : Type*}
  [Fintype iota] [DecidableEq iota]
  {fine : UniformTubeFamily delta iota}

/-- The parent image of the actual active fine set is exactly the actual
active coarse set. -/
theorem occupiedParents_activeFine_eq_activeCoarse
    (S : StickyScaleCover fine rho) :
    occupiedParents S.activeFine S.parent = S.activeCoarse := by
  ext k
  constructor
  · intro hk
    obtain ⟨i, hi, hik⟩ := Finset.mem_image.mp hk
    simpa [← hik] using S.parent_mem i hi
  · intro hk
    obtain ⟨i, hi, hik⟩ := S.parent_surjective k hk
    exact Finset.mem_image.mpr ⟨i, hi, hik⟩

/-- The raw parent-volume sum used by `JointTubeFactoring` is the literal
active-coarse family volume. -/
theorem sum_occupiedParentVolume_eq_activeCoarseFamilyVolume
    (S : StickyScaleCover fine rho) :
    (∑ k ∈ occupiedParents S.activeFine S.parent,
        volume (S.coarse.tubes k).carrier) =
      familyVolume S.activeCoarseFamily := by
  rw [occupiedParents_activeFine_eq_activeCoarse S]
  unfold familyVolume
    FamilyStickyAtEveryScaleCoreV1.StickyScaleCover.activeCoarseFamily
  rw [← Finset.attach_eq_univ]
  simpa only [UniformTubeFamily.bodyFamily, Tube.coe_body] using
    (Finset.sum_attach S.activeCoarse
      (fun k => volume (S.coarse.tubes k).carrier)).symm

/-- The raw active-fine body mass used by `JointTubeFactoring` is the literal
active-fine family volume. -/
theorem bodyMassOn_activeFine_eq_activeFineFamilyVolume
    (S : StickyScaleCover fine rho) :
    bodyMassOn fine.bodyFamily S.activeFine =
      familyVolume (activeFineFamily S) := by
  unfold bodyMassOn familyVolume activeFineFamily
  rw [← Finset.attach_eq_univ]
  simpa only [UniformTubeFamily.bodyFamily, Tube.coe_body] using
    (Finset.sum_attach S.activeFine
      (fun i => volume (fine.bodyFamily i : Set Space))).symm

/-- Explicit loss which clears the fine/coarse tube-volume ratio. -/
def stickyJointScaleCoverLoss (A : ENNReal) (delta rho : NNReal) : ENNReal :=
  A * ((8 * (rho : ENNReal) ^ 2) /
    ((delta : ENNReal) ^ 2 / 2))

private theorem halfSquare_ne_zero
    {r : NNReal} (hr : 0 < r) :
    (r : ENNReal) ^ 2 / 2 ≠ 0 := by
  apply ENNReal.div_ne_zero.mpr
  exact ⟨pow_ne_zero 2 (ENNReal.coe_ne_zero.mpr hr.ne'), by norm_num⟩

private theorem halfSquare_ne_top (r : NNReal) :
    (r : ENNReal) ^ 2 / 2 ≠ ∞ := by
  exact ENNReal.div_ne_top
    (ENNReal.pow_ne_top ENNReal.coe_ne_top) (by norm_num)

private theorem eightSquare_ne_zero
    {r : NNReal} (hr : 0 < r) :
    8 * (r : ENNReal) ^ 2 ≠ 0 := by
  exact mul_ne_zero (by norm_num)
    (pow_ne_zero 2 (ENNReal.coe_ne_zero.mpr hr.ne'))

private theorem eightSquare_ne_top (r : NNReal) :
    8 * (r : ENNReal) ^ 2 ≠ ∞ := by
  exact ENNReal.mul_ne_top (by norm_num)
    (ENNReal.pow_ne_top ENNReal.coe_ne_top)

theorem stickyJointScaleCoverLoss_ne_zero
    {A : ENNReal} (hA0 : A ≠ 0)
    (hrho : 0 < rho) :
    stickyJointScaleCoverLoss A delta rho ≠ 0 := by
  unfold stickyJointScaleCoverLoss
  apply mul_ne_zero hA0
  apply ENNReal.div_ne_zero.mpr
  exact ⟨eightSquare_ne_zero hrho, halfSquare_ne_top delta⟩

theorem stickyJointScaleCoverLoss_ne_top
    {A : ENNReal} (hAtop : A ≠ ∞)
    (hdelta : 0 < delta) :
    stickyJointScaleCoverLoss A delta rho ≠ ∞ := by
  unfold stickyJointScaleCoverLoss
  apply ENNReal.mul_ne_top hAtop
  exact ENNReal.div_ne_top (eightSquare_ne_top rho)
    (halfSquare_ne_zero hdelta)

/-- Tube-volume comparability automatically proves the exact global cover
cost required by `JointTubeFactoring`. -/
theorem stickyJointScaleCoverCost
    (S : StickyScaleCover fine rho) (A : ENNReal)
    (hdelta : 0 < delta)
    (hdeltaHalf : delta ≤ (2 : NNReal)⁻¹)
    (hrhoHalf : rho ≤ (2 : NNReal)⁻¹) :
    A * (∑ k ∈ occupiedParents S.activeFine S.parent,
        volume (S.coarse.tubes k).carrier) ≤
      stickyJointScaleCoverLoss A delta rho *
        bodyMassOn fine.bodyFamily S.activeFine := by
  rw [sum_occupiedParentVolume_eq_activeCoarseFamilyVolume,
    bodyMassOn_activeFine_eq_activeFineFamilyVolume]
  have hhalf0 : (delta : ENNReal) ^ 2 / 2 ≠ 0 :=
    halfSquare_ne_zero hdelta
  have hhalfTop : (delta : ENNReal) ^ 2 / 2 ≠ ∞ :=
    halfSquare_ne_top delta
  have hcross :=
    activeCoarseFamilyVolume_mul_half_sq_le_eight_sq_mul_activeFineFamilyVolume
      S hdeltaHalf hrhoHalf
  have hvolume : familyVolume S.activeCoarseFamily ≤
      ((8 * (rho : ENNReal) ^ 2) /
        ((delta : ENNReal) ^ 2 / 2)) *
          familyVolume (activeFineFamily S) := by
    have hdiv : familyVolume S.activeCoarseFamily ≤
        ((8 * (rho : ENNReal) ^ 2) *
          familyVolume (activeFineFamily S)) /
            ((delta : ENNReal) ^ 2 / 2) :=
      (ENNReal.le_div_iff_mul_le (Or.inl hhalf0) (Or.inl hhalfTop)).2 hcross
    calc
      familyVolume S.activeCoarseFamily ≤
          ((8 * (rho : ENNReal) ^ 2) *
            familyVolume (activeFineFamily S)) /
              ((delta : ENNReal) ^ 2 / 2) := hdiv
      _ = ((8 * (rho : ENNReal) ^ 2) /
            ((delta : ENNReal) ^ 2 / 2)) *
              familyVolume (activeFineFamily S) := by
        simp only [div_eq_mul_inv]
        ac_rfl
  calc
    A * familyVolume S.activeCoarseFamily ≤
        A * (((8 * (rho : ENNReal) ^ 2) /
          ((delta : ENNReal) ^ 2 / 2)) *
            familyVolume (activeFineFamily S)) :=
      mul_le_mul' le_rfl hvolume
    _ = stickyJointScaleCoverLoss A delta rho *
        familyVolume (activeFineFamily S) := by
      unfold stickyJointScaleCoverLoss
      ac_rfl

/-- A literal Sticky cover plus source Katz--Tao data produces the same-data
exact-cardinality partition and exact Eq.(45)-times-Eq.(46) product. -/
theorem exists_sticky_jointExactUniform_prop66A_product
    (S : StickyScaleCover fine rho)
    (hdelta : 0 < delta) (hrho : 0 < rho)
    (hscale : delta ≤ rho)
    (hdeltaHalf : delta ≤ (2 : NNReal)⁻¹)
    (hrhoHalf : rho ≤ (2 : NNReal)⁻¹)
    (hactive : S.activeFine.Nonempty)
    (AKT : ENNReal) (hAKT0 : AKT ≠ 0) (hAKTtop : AKT ≠ ∞)
    (hfineKT : IsKatzTaoOn AKT fine.bodyFamily S.activeFine)
    {a b : NNReal} {CF : ENNReal} {epsilon beta : Real}
    (ha : 0 < a) (hb : 0 < b)
    (hbeta : 0 ≤ beta) (hbetaOne : beta ≤ 1) :
    ∃ (level : Fin (Fintype.card iota + 1))
        (selected : Finset (Fin S.coarseCard))
        (selectedFine : Finset iota)
        (fine' : UniformTubeFamily delta iota)
        (coarse' : UniformTubeFamily rho (Fin S.coarseCard))
        (P : CoarseTubePartition fine' coarse'),
      (∀ i, fine'.tubes i = fine.tubes i) ∧
      (∀ k, coarse'.tubes k = S.coarse.tubes k) ∧
      P.index = selectedIndexFactorization S.activeFine S.parent selected ∧
      P.branching = level.1 ∧ P.branchingLoss = 1 ∧
      WithinFactor (2 * (Fintype.card iota + 1))
        (bodyMassOn fine.bodyFamily S.activeFine)
        (bodyMassOn fine'.bodyFamily P.fineIndices) ∧
      selectedFine.Nonempty ∧ selected.Nonempty ∧
      selectedFine ⊆ S.activeFine ∧ selected ⊆ S.activeCoarse ∧
      (∀ k ∈ P.coarseIndices, (P.fiber k).card = level.1) ∧
      IsKatzTaoOn
        (2 * stickyJointScaleCoverLoss AKT delta rho)
        coarse'.bodyFamily P.coarseIndices ∧
      (∀ k ∈ P.coarseIndices,
        IsFrostmanOn (2 * stickyJointScaleCoverLoss AKT delta rho)
          fine'.bodyFamily (P.fiber k) (coarse'.bodyFamily k)) ∧
      proposition66AOuterFactor delta a b P.coarseIndices.card
            CF epsilon beta *
          proposition66AInnerFactor delta a b P.branching epsilon beta =
        proposition66AFrostmanFactor delta a b P.fineIndices.card
          CF epsilon beta := by
  have hactiveRefined : S.activeFine ⊆ fine.refinement.refined := by
    rw [S.activeFine_eq_refined]
  have hcoarseRefined : S.activeCoarse ⊆ S.coarse.refinement.refined := by
    rw [S.activeCoarse_eq_refined]
  exact exists_jointTubeFactoring_with_exactUniform_prop66A_product
    fine S.coarse S.activeFine S.activeCoarse S.parent AKT
      (stickyJointScaleCoverLoss AKT delta rho)
      hdelta hscale hactive hactiveRefined hcoarseRefined
      S.parent_mem S.carrier_subset hAKT0 hAKTtop
      (stickyJointScaleCoverLoss_ne_zero hAKT0 hrho)
      (stickyJointScaleCoverLoss_ne_top hAKTtop hdelta)
      hfineKT
      (stickyJointScaleCoverCost S AKT hdelta hdeltaHalf hrhoHalf)
      ha hb hbeta hbetaOne

#print axioms occupiedParents_activeFine_eq_activeCoarse
#print axioms sum_occupiedParentVolume_eq_activeCoarseFamilyVolume
#print axioms bodyMassOn_activeFine_eq_activeFineFamilyVolume
#print axioms stickyJointScaleCoverLoss_ne_zero
#print axioms stickyJointScaleCoverLoss_ne_top
#print axioms stickyJointScaleCoverCost
#print axioms exists_sticky_jointExactUniform_prop66A_product

end
end Family8StickyJointExactUniformCoverCostV4
