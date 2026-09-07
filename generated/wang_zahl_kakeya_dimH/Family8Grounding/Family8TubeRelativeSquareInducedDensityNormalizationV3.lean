import Family8Grounding.Family8CoarseTubePartitionLowerCountLossV1
import Submission.Kakeya.ConvexFactoring.InducedShadingDensityAlgebra
import Submission.Kakeya.ConvexFactoring.TubeVolumeBounds
import Mathlib.Tactic

/-!
# Relative-square induced-density normalization, V3

V1--V2 are frozen elaboration drafts.  This clean successor keeps the exact
`768 * branchingLoss^2` calculation and performs the ENNReal half-volume
cancellation on one chosen factor rather than by a global rewrite.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000
set_option linter.unusedSectionVars false

open scoped BigOperators ENNReal NNReal
open MeasureTheory

namespace Family8TubeRelativeSquareInducedDensityNormalizationV3

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.InducedShadingDensityAlgebra
open Submission.Kakeya.Uniformity

noncomputable section

variable {delta rho : NNReal} {iota kappa : Type*}
  [Fintype iota] [Fintype kappa]
  [DecidableEq iota] [DecidableEq kappa]
  {fine : UniformTubeFamily delta iota}
  {coarse : UniformTubeFamily rho kappa}

theorem coarseFamilyVolume_le_activeCard_mul_eight_sq
    (P : CoarseTubePartition fine coarse)
    (hcoarse : P.coarseIndices = Finset.univ)
    (hrhoHalf : rho <= (2 : NNReal)⁻¹) :
    familyVolume coarse.bodyFamily <=
      (P.coarseIndices.card : ENNReal) *
        (8 * (rho : ENNReal) ^ 2) := by
  unfold familyVolume
  simp only [UniformTubeFamily.bodyFamily, Tube.coe_body]
  rw [← hcoarse]
  calc
    (∑ k ∈ P.coarseIndices, volume (coarse.tubes k).carrier) <=
        ∑ _k ∈ P.coarseIndices, 8 * (rho : ENNReal) ^ 2 := by
      exact Finset.sum_le_sum fun k _hk =>
        (coarse.tubes k).volume_le_eight_mul_sq_of_le_half hrhoHalf
    _ = (P.coarseIndices.card : ENNReal) *
        (8 * (rho : ENNReal) ^ 2) := by
      simp only [Finset.sum_const, nsmul_eq_mul]

theorem activeFineCard_mul_half_sq_le_fineFamilyVolume
    (P : CoarseTubePartition fine coarse)
    (hfine : P.fineIndices = Finset.univ)
    (hdeltaHalf : delta <= (2 : NNReal)⁻¹) :
    (P.fineIndices.card : ENNReal) *
        ((delta : ENNReal) ^ 2 / 2) <=
      familyVolume fine.bodyFamily := by
  unfold familyVolume
  simp only [UniformTubeFamily.bodyFamily, Tube.coe_body]
  rw [← hfine]
  calc
    (P.fineIndices.card : ENNReal) *
          ((delta : ENNReal) ^ 2 / 2) =
        ∑ _i ∈ P.fineIndices, (delta : ENNReal) ^ 2 / 2 := by
      simp only [Finset.sum_const, nsmul_eq_mul]
    _ <= ∑ i ∈ P.fineIndices, volume (fine.tubes i).carrier := by
      exact Finset.sum_le_sum fun i _hi =>
        (fine.tubes i).half_sq_le_volume_of_le_half hdeltaHalf

theorem relativeSquareGrowth_mul_coarseVolume_mul_density_le
    (P : CoarseTubePartition fine coarse)
    (Y : Shading fine.bodyFamily)
    (hfine : P.fineIndices = Finset.univ)
    (hcoarse : P.coarseIndices = Finset.univ)
    (hdeltaHalf : delta <= (2 : NNReal)⁻¹)
    (hrhoHalf : rho <= (2 : NNReal)⁻¹) :
    ((((P.branchingLoss * P.branching : Nat) : ENNReal) * 48) *
          (delta : ENNReal) ^ 2) *
        familyVolume coarse.bodyFamily * Y.shadingDensity <=
      (768 * (P.branchingLoss : ENNReal) ^ 2) *
        (rho : ENNReal) ^ 2 * familyVolume fine.bodyFamily := by
  have hcoarseVolume :=
    coarseFamilyVolume_le_activeCard_mul_eight_sq
      P hcoarse hrhoHalf
  have hfineVolume :=
    activeFineCard_mul_half_sq_le_fineFamilyVolume
      P hfine hdeltaHalf
  have hcountNat :=
    Family8CoarseTubePartitionLowerCountLossV1.CoarseTubePartition.coarse_card_mul_branching_le_loss_mul_fine_card
      P
  have hcount :
      (P.coarseIndices.card : ENNReal) *
          (P.branching : ENNReal) <=
        (P.branchingLoss : ENNReal) *
          (P.fineIndices.card : ENNReal) := by
    exact_mod_cast hcountNat
  have hd : ((delta : ENNReal) ^ 2 / 2) * 2 =
      (delta : ENNReal) ^ 2 := by
    rw [ENNReal.div_mul_cancel] <;> norm_num
  have hfineScaled :
      (P.fineIndices.card : ENNReal) * (delta : ENNReal) ^ 2 <=
        2 * familyVolume fine.bodyFamily := by
    calc
      (P.fineIndices.card : ENNReal) * (delta : ENNReal) ^ 2 =
          (P.fineIndices.card : ENNReal) *
            (((delta : ENNReal) ^ 2 / 2) * 2) :=
        congrArg (fun z : ENNReal =>
          (P.fineIndices.card : ENNReal) * z) hd.symm
      _ = 2 * ((P.fineIndices.card : ENNReal) *
          ((delta : ENNReal) ^ 2 / 2)) := by
        ac_rfl
      _ <= 2 * familyVolume fine.bodyFamily :=
        mul_le_mul' le_rfl hfineVolume
  calc
    ((((P.branchingLoss * P.branching : Nat) : ENNReal) * 48) *
          (delta : ENNReal) ^ 2) *
        familyVolume coarse.bodyFamily * Y.shadingDensity <=
      ((((P.branchingLoss * P.branching : Nat) : ENNReal) * 48) *
          (delta : ENNReal) ^ 2) *
        ((P.coarseIndices.card : ENNReal) *
          (8 * (rho : ENNReal) ^ 2)) * 1 :=
      mul_le_mul' (mul_le_mul' le_rfl hcoarseVolume)
        Y.shadingDensity_le_one
    _ = 384 * (P.branchingLoss : ENNReal) *
        ((P.coarseIndices.card : ENNReal) *
          (P.branching : ENNReal)) *
        (delta : ENNReal) ^ 2 * (rho : ENNReal) ^ 2 := by
      simp only [Nat.cast_mul]
      ring
    _ <= 384 * (P.branchingLoss : ENNReal) *
        ((P.branchingLoss : ENNReal) *
          (P.fineIndices.card : ENNReal)) *
        (delta : ENNReal) ^ 2 * (rho : ENNReal) ^ 2 := by
      gcongr
    _ = 384 * (P.branchingLoss : ENNReal) ^ 2 *
        (rho : ENNReal) ^ 2 *
          ((P.fineIndices.card : ENNReal) *
            (delta : ENNReal) ^ 2) := by
      ring
    _ <= 384 * (P.branchingLoss : ENNReal) ^ 2 *
        (rho : ENNReal) ^ 2 *
          (2 * familyVolume fine.bodyFamily) := by
      exact mul_le_mul' le_rfl hfineScaled
    _ = (768 * (P.branchingLoss : ENNReal) ^ 2) *
        (rho : ENNReal) ^ 2 * familyVolume fine.bodyFamily := by
      ring

theorem sourceDensity_sq_div_loss_mul_768_branchingLoss_sq_le
    (P : CoarseTubePartition fine coarse)
    (Y : Shading fine.bodyFamily)
    (R : IndexedShadingRefinement Y)
    (loss : Nat)
    (hfine : P.fineIndices = Finset.univ)
    (hcoarse : P.coarseIndices = Finset.univ)
    (hretained : WithinFactor loss
      Y.shadingMass R.shading.shadingMass)
    (hgrowth : HasFiberCoveringGrowth P.asConvexFactorization
      R.shading (rho : Real) ((rho : ENNReal) ^ 2)
      ((((P.branchingLoss * P.branching : Nat) : ENNReal) * 48) *
        (delta : ENNReal) ^ 2))
    (_hdelta : 0 < delta) (hrho : 0 < rho)
    (hrhoHalf : rho <= (2 : NNReal)⁻¹) :
    Y.shadingDensity ^ 2 /
        ((loss : ENNReal) *
          (768 * (P.branchingLoss : ENNReal) ^ 2)) <=
      (P.asConvexFactorization.neighborhoodInducedShading
        R.shading (rho : Real)).shadingDensity := by
  have hcoarseVolume0 : familyVolume coarse.bodyFamily ≠ 0 := by
    apply ne_of_gt
    unfold familyVolume
    rw [Finset.sum_pos_iff]
    obtain ⟨k, hk⟩ := P.coarseIndices_nonempty
    exact ⟨k, Finset.mem_univ _, by
      simpa only [UniformTubeFamily.bodyFamily, Tube.coe_body] using
        (coarse.tubes k).volume_pos hrho⟩
  apply sourceDensity_sq_div_loss_le_inducedDensity
    P.asConvexFactorization Y R
      (by
        intro i _hi
        change i ∈ P.fineIndices
        simpa only [hfine] using Finset.mem_univ i)
      loss (rho : Real) ((rho : ENNReal) ^ 2)
      ((((P.branchingLoss * P.branching : Nat) : ENNReal) * 48) *
        (delta : ENNReal) ^ 2)
      (768 * (P.branchingLoss : ENNReal) ^ 2)
      (pow_ne_zero 2 (ENNReal.coe_ne_zero.mpr hrho.ne'))
      (ENNReal.pow_ne_top ENNReal.coe_ne_top)
      hcoarseVolume0 hretained hgrowth
  exact relativeSquareGrowth_mul_coarseVolume_mul_density_le
    P Y hfine hcoarse (P.scale_le.trans hrhoHalf) hrhoHalf

#print axioms coarseFamilyVolume_le_activeCard_mul_eight_sq
#print axioms activeFineCard_mul_half_sq_le_fineFamilyVolume
#print axioms relativeSquareGrowth_mul_coarseVolume_mul_density_le
#print axioms
  sourceDensity_sq_div_loss_mul_768_branchingLoss_sq_le

end
end Family8TubeRelativeSquareInducedDensityNormalizationV3
