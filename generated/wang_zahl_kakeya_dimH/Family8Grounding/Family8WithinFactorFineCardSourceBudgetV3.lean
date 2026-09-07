import Submission.Kakeya.ConvexFactoring.AlmostCoverTubeFactoring
import Submission.Kakeya.ConvexFactoring.TubeVolumeBounds
import Mathlib.Tactic

/-!
# Fine-card source budget from retained body mass, V3

Fresh ADD-only successor with explicit `ENNReal` inverse and finiteness
certificates for the retained-loss cancellation.
-/

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8WithinFactorFineCardSourceBudgetV3

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.JointTubeFactoring
open Submission.Kakeya.Uniformity

noncomputable section

variable {delta : NNReal} {iota : Type}
  [Fintype iota] [DecidableEq iota]

/-- Indexed body mass is bounded by cardinality times `8 * delta^2`. -/
theorem bodyMassOn_le_card_mul_eight_sq
    (fine : UniformTubeFamily delta iota) (selected : Finset iota)
    (hdeltaHalf : delta <= (2 : NNReal)⁻¹) :
    bodyMassOn fine.bodyFamily selected <=
      (selected.card : ENNReal) * (8 * (delta : ENNReal) ^ 2) := by
  unfold bodyMassOn UniformTubeFamily.bodyFamily
  simp only [Tube.coe_body]
  calc
    (∑ i ∈ selected, volume (fine.tubes i).carrier) <=
        ∑ _i ∈ selected, 8 * (delta : ENNReal) ^ 2 := by
      exact Finset.sum_le_sum fun i _ =>
        (fine.tubes i).volume_le_eight_mul_sq_of_le_half hdeltaHalf
    _ = (selected.card : ENNReal) * (8 * (delta : ENNReal) ^ 2) := by
      simp only [Finset.sum_const, nsmul_eq_mul]

/-- Retained body mass and one source-mass scalar absorption give the exact
fine-card source budget of the general Family 8 endpoint. -/
theorem fineCard_source_budget_of_withinFactor
    (fine : UniformTubeFamily delta iota) (selected : Finset iota)
    (hdeltaHalf : delta <= (2 : NNReal)⁻¹)
    (sourceMass : ENNReal) (retainLoss q : Nat)
    (sourceA C : NNReal)
    (hretainLoss : 0 < retainLoss)
    (hretain : WithinFactor retainLoss sourceMass
      (bodyMassOn fine.bodyFamily selected))
    (hAbsorb :
      (131072 : ENNReal) * (retainLoss : ENNReal) * (q : ENNReal) ^ 2 *
          (sourceA : ENNReal) <=
        (C : ENNReal) * sourceMass) :
    8192 * (q : NNReal) ^ 2 * sourceA <=
      C * (selected.card : NNReal) * (delta ^ 2 / 2) := by
  have hselectedMass :=
    bodyMassOn_le_card_mul_eight_sq fine selected hdeltaHalf
  have hretainedUpper :
      sourceMass <= (retainLoss : ENNReal) *
        ((selected.card : ENNReal) * (8 * (delta : ENNReal) ^ 2)) := by
    calc
      sourceMass <= retainLoss • bodyMassOn fine.bodyFamily selected := hretain
      _ = (retainLoss : ENNReal) * bodyMassOn fine.bodyFamily selected := by
        simp only [nsmul_eq_mul]
      _ <= (retainLoss : ENNReal) *
          ((selected.card : ENNReal) * (8 * (delta : ENNReal) ^ 2)) :=
        mul_le_mul_of_nonneg_left hselectedMass (by exact bot_le)
  have hcancel : (2 : ENNReal)⁻¹ * 2 = 1 :=
    ENNReal.inv_mul_cancel (by norm_num) (by norm_num)
  have htwoInv : (2 : ENNReal)⁻¹ * 16 = 8 := by
    calc
      (2 : ENNReal)⁻¹ * 16 = ((2 : ENNReal)⁻¹ * 2) * 8 := by ring
      _ = 8 := by rw [hcancel, one_mul]
  have hfactor :
      ((16 : ENNReal) * (retainLoss : ENNReal)) *
          ((8192 : ENNReal) * (q : ENNReal) ^ 2 *
            (sourceA : ENNReal)) <=
        ((16 : ENNReal) * (retainLoss : ENNReal)) *
          ((C : ENNReal) * (selected.card : ENNReal) *
            ((delta : ENNReal) ^ 2 / 2)) := by
    calc
      ((16 : ENNReal) * (retainLoss : ENNReal)) *
          ((8192 : ENNReal) * (q : ENNReal) ^ 2 *
            (sourceA : ENNReal)) =
          (131072 : ENNReal) * (retainLoss : ENNReal) *
            (q : ENNReal) ^ 2 * (sourceA : ENNReal) := by ring
      _ <= (C : ENNReal) * sourceMass := hAbsorb
      _ <= (C : ENNReal) * ((retainLoss : ENNReal) *
          ((selected.card : ENNReal) *
            (8 * (delta : ENNReal) ^ 2))) :=
        mul_le_mul_of_nonneg_left hretainedUpper (by exact bot_le)
      _ = ((16 : ENNReal) * (retainLoss : ENNReal)) *
          ((C : ENNReal) * (selected.card : ENNReal) *
            ((delta : ENNReal) ^ 2 / 2)) := by
        rw [ENNReal.div_eq_inv_mul, ← htwoInv]
        ring
  have hfactorZero :
      (16 : ENNReal) * (retainLoss : ENNReal) ≠ 0 := by
    apply mul_ne_zero
    · norm_num
    · exact_mod_cast hretainLoss.ne'
  have hfactorTop :
      (16 : ENNReal) * (retainLoss : ENNReal) ≠ ∞ :=
    ENNReal.mul_ne_top (by norm_num) (by simp)
  have hbudgetENN :
      (8192 : ENNReal) * (q : ENNReal) ^ 2 * (sourceA : ENNReal) <=
        (C : ENNReal) * (selected.card : ENNReal) *
          ((delta : ENNReal) ^ 2 / 2) :=
    (ENNReal.mul_le_mul_iff_right hfactorZero hfactorTop).mp hfactor
  exact_mod_cast hbudgetENN

end

end Family8WithinFactorFineCardSourceBudgetV3
