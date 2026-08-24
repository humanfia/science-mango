import Submission.Kakeya.ConvexFactoring.CoarseTubePartition
import Submission.Kakeya.ConvexFactoring.TubeVolumeBounds
import Submission.Kakeya.ConvexFactoring.HeavyParentSelection

open scoped ENNReal NNReal
open MeasureTheory Set

namespace TubeSelectedFamilyRatioPrototype

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.HeavyParentSelection
set_option linter.unusedSectionVars false

noncomputable section

variable {delta rho : NNReal} {ι κ : Type*}
  [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
  {fineFamily : UniformTubeFamily delta ι}
  {coarseFamily : UniformTubeFamily rho κ}

def activeFineBodyFamily
    (P : CoarseTubePartition fineFamily coarseFamily) :=
  selectedCoarseFamily fineFamily.bodyFamily P.fineIndices

def activeCoarseBodyFamily
    (P : CoarseTubePartition fineFamily coarseFamily) :=
  selectedCoarseFamily coarseFamily.bodyFamily P.coarseIndices

theorem activeCoarseVolume_le_card_mul
    (P : CoarseTubePartition fineFamily coarseFamily)
    (hrhoHalf : rho ≤ (2 : ℝ≥0)⁻¹) :
    familyVolume (activeCoarseBodyFamily P) ≤
      (P.coarseIndices.card : ℝ≥0∞) *
        (8 * (rho : ℝ≥0∞) ^ 2) := by
  rw [activeCoarseBodyFamily, selectedCoarseFamily_volume]
  calc
    (∑ k ∈ P.coarseIndices,
        volume (coarseFamily.bodyFamily k : Set Space)) ≤
        ∑ _k ∈ P.coarseIndices, 8 * (rho : ℝ≥0∞) ^ 2 := by
      exact Finset.sum_le_sum fun k _hk => by
        simpa [UniformTubeFamily.bodyFamily, Tube.coe_body] using
          (coarseFamily.tubes k).volume_le_eight_mul_sq_of_le_half hrhoHalf
    _ = (P.coarseIndices.card : ℝ≥0∞) *
        (8 * (rho : ℝ≥0∞) ^ 2) := by
      simp [nsmul_eq_mul]

theorem card_mul_delta_sq_le_two_mul_activeFineVolume
    (P : CoarseTubePartition fineFamily coarseFamily)
    (hdeltaHalf : delta ≤ (2 : ℝ≥0)⁻¹) :
    (P.fineIndices.card : ℝ≥0∞) * (delta : ℝ≥0∞) ^ 2 ≤
      2 * familyVolume (activeFineBodyFamily P) := by
  rw [activeFineBodyFamily, selectedCoarseFamily_volume]
  calc
    (P.fineIndices.card : ℝ≥0∞) * (delta : ℝ≥0∞) ^ 2 =
        ∑ _i ∈ P.fineIndices, (delta : ℝ≥0∞) ^ 2 := by
      simp [nsmul_eq_mul]
    _ ≤ ∑ i ∈ P.fineIndices,
        2 * volume (fineFamily.bodyFamily i : Set Space) := by
      exact Finset.sum_le_sum fun i _hi => by
        have hlow :=
          (fineFamily.tubes i).half_sq_le_volume_of_le_half hdeltaHalf
        have hmul := mul_le_mul_of_nonneg_left hlow
          (show (0 : ℝ≥0∞) ≤ 2 from bot_le)
        calc
          (delta : ℝ≥0∞) ^ 2 =
              (2 * (2 : ℝ≥0∞)⁻¹) * (delta : ℝ≥0∞) ^ 2 := by
            rw [ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_mul]
          _ = 2 * ((delta : ℝ≥0∞) ^ 2 / 2) := by
            rw [ENNReal.div_eq_inv_mul]
            ac_rfl
          _ ≤ 2 * volume (fineFamily.tubes i).carrier := hmul
          _ = 2 * volume (fineFamily.bodyFamily i : Set Space) := by
            rfl
    _ = 2 * ∑ i ∈ P.fineIndices,
        volume (fineFamily.bodyFamily i : Set Space) := by
      rw [Finset.mul_sum]

theorem branching_mul_coarseCard_le_loss_mul_fineCard
    (P : CoarseTubePartition fineFamily coarseFamily) :
    P.branching * P.coarseIndices.card ≤
      P.branchingLoss * P.fineIndices.card := by
  calc
    P.branching * P.coarseIndices.card =
        ∑ _k ∈ P.coarseIndices, P.branching := by simp [mul_comm]
    _ ≤ ∑ k ∈ P.coarseIndices,
        P.branchingLoss * (P.fiber k).card := by
      exact Finset.sum_le_sum fun k hk => P.branching_le_loss_mul_fiber k hk
    _ = P.branchingLoss *
        (∑ k ∈ P.coarseIndices, (P.fiber k).card) := by
      rw [Finset.mul_sum]
    _ = P.branchingLoss * P.fineIndices.card := by
      rw [← P.card_fine_eq_sum_card_fiber]

/-- Division-free selected-family denominator comparison. -/
theorem branching_delta_sq_mul_activeCoarseVolume_le
    (P : CoarseTubePartition fineFamily coarseFamily)
    (hrhoHalf : rho ≤ (2 : ℝ≥0)⁻¹) :
    (P.branching : ℝ≥0∞) * (delta : ℝ≥0∞) ^ 2 *
        familyVolume (activeCoarseBodyFamily P) ≤
      16 * (P.branchingLoss : ℝ≥0∞) * (rho : ℝ≥0∞) ^ 2 *
        familyVolume (activeFineBodyFamily P) := by
  have hdeltaHalf : delta ≤ (2 : ℝ≥0)⁻¹ := P.scale_le.trans hrhoHalf
  have hcoarse := activeCoarseVolume_le_card_mul P hrhoHalf
  have hfine := card_mul_delta_sq_le_two_mul_activeFineVolume P hdeltaHalf
  have hcard :
      (P.branching : ℝ≥0∞) * (P.coarseIndices.card : ℝ≥0∞) ≤
        (P.branchingLoss : ℝ≥0∞) * (P.fineIndices.card : ℝ≥0∞) := by
    exact_mod_cast branching_mul_coarseCard_le_loss_mul_fineCard P
  calc
    (P.branching : ℝ≥0∞) * (delta : ℝ≥0∞) ^ 2 *
        familyVolume (activeCoarseBodyFamily P) ≤
      (P.branching : ℝ≥0∞) * (delta : ℝ≥0∞) ^ 2 *
        ((P.coarseIndices.card : ℝ≥0∞) *
          (8 * (rho : ℝ≥0∞) ^ 2)) := mul_le_mul' le_rfl hcoarse
    _ = 8 * (rho : ℝ≥0∞) ^ 2 * (delta : ℝ≥0∞) ^ 2 *
        ((P.branching : ℝ≥0∞) *
          (P.coarseIndices.card : ℝ≥0∞)) := by ring
    _ ≤ 8 * (rho : ℝ≥0∞) ^ 2 * (delta : ℝ≥0∞) ^ 2 *
        ((P.branchingLoss : ℝ≥0∞) *
          (P.fineIndices.card : ℝ≥0∞)) := mul_le_mul' le_rfl hcard
    _ = 8 * (P.branchingLoss : ℝ≥0∞) * (rho : ℝ≥0∞) ^ 2 *
        ((P.fineIndices.card : ℝ≥0∞) * (delta : ℝ≥0∞) ^ 2) := by ring
    _ ≤ 8 * (P.branchingLoss : ℝ≥0∞) * (rho : ℝ≥0∞) ^ 2 *
        (2 * familyVolume (activeFineBodyFamily P)) :=
      mul_le_mul' le_rfl hfine
    _ = 16 * (P.branchingLoss : ℝ≥0∞) * (rho : ℝ≥0∞) ^ 2 *
        familyVolume (activeFineBodyFamily P) := by ring

def tubeDenominatorLoss
    (P : CoarseTubePartition fineFamily coarseFamily) : ℝ≥0∞ :=
  (16 * (P.branchingLoss : ℝ≥0∞) * (rho : ℝ≥0∞) ^ 2) /
    ((P.branching : ℝ≥0∞) * (delta : ℝ≥0∞) ^ 2)

/-- Quotient form: `C = 16 L_b (rho/delta)^2 / branching`. -/
theorem activeCoarseVolume_le_tubeDenominatorLoss_mul
    (P : CoarseTubePartition fineFamily coarseFamily)
    (hdeltaPos : 0 < delta)
    (hrhoHalf : rho ≤ (2 : ℝ≥0)⁻¹) :
    familyVolume (activeCoarseBodyFamily P) ≤
      tubeDenominatorLoss P * familyVolume (activeFineBodyFamily P) := by
  have hbranch0 : (P.branching : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast P.branching_pos.ne'
  have hdelta0 : (delta : ℝ≥0∞) ^ 2 ≠ 0 :=
    ENNReal.pow_ne_zero (ENNReal.coe_ne_zero.mpr hdeltaPos.ne') 2
  have hden0 :
      (P.branching : ℝ≥0∞) * (delta : ℝ≥0∞) ^ 2 ≠ 0 :=
    mul_ne_zero hbranch0 hdelta0
  have hdenTop :
      (P.branching : ℝ≥0∞) * (delta : ℝ≥0∞) ^ 2 ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.coe_ne_top
      (ENNReal.pow_ne_top ENNReal.coe_ne_top)
  have hcross :
      familyVolume (activeCoarseBodyFamily P) *
          ((P.branching : ℝ≥0∞) * (delta : ℝ≥0∞) ^ 2) ≤
        16 * (P.branchingLoss : ℝ≥0∞) * (rho : ℝ≥0∞) ^ 2 *
          familyVolume (activeFineBodyFamily P) := by
    simpa only [mul_assoc, mul_left_comm, mul_comm] using
      branching_delta_sq_mul_activeCoarseVolume_le P hrhoHalf
  have hle :
      familyVolume (activeCoarseBodyFamily P) ≤
        (16 * (P.branchingLoss : ℝ≥0∞) * (rho : ℝ≥0∞) ^ 2 *
          familyVolume (activeFineBodyFamily P)) /
            ((P.branching : ℝ≥0∞) * (delta : ℝ≥0∞) ^ 2) :=
    (ENNReal.le_div_iff_mul_le
      (Or.inl hden0) (Or.inl hdenTop)).2 hcross
  calc
    familyVolume (activeCoarseBodyFamily P) ≤ _ := hle
    _ = tubeDenominatorLoss P *
        familyVolume (activeFineBodyFamily P) := by
      unfold tubeDenominatorLoss
      simp only [div_eq_mul_inv]
      ac_rfl

end
end TubeSelectedFamilyRatioPrototype

#print axioms TubeSelectedFamilyRatioPrototype.branching_delta_sq_mul_activeCoarseVolume_le
#print axioms TubeSelectedFamilyRatioPrototype.activeCoarseVolume_le_tubeDenominatorLoss_mul
