import Submission.Kakeya.ConvexFactoring.AlmostCoverTubeFactoring
import Submission.Kakeya.ConvexFactoring.TubeVolumeBounds
import Mathlib.Tactic

/-!
# Efficient selected parents force a branching source budget, V2

Fresh ADD-only successor of V1.  This version performs the scalar algebra in
`NNReal`, after using the paper-facing efficient-parent inequality in
`ENNReal`.
-/

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8EfficientSelectedBranchingSourceBudgetV2

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.JointTubeFactoring
open Submission.Kakeya.Uniformity

noncomputable section

variable {delta rho : NNReal} {iota kappa : Type}
  [Fintype iota] [DecidableEq iota]
  [Fintype kappa] [DecidableEq kappa]

/-- Raw assigned mass is at most raw fibre cardinality times the uniform
fine-tube volume bound. -/
theorem assignedBodyMass_le_card_mul_eight_sq
    (fine : UniformTubeFamily delta iota)
    (active : Finset iota) (parent : iota -> kappa)
    (hdeltaHalf : delta <= (2 : NNReal)⁻¹) (k : kappa) :
    assignedBodyMass fine active parent k <=
      (((rawIndexFactorization active parent).fiber k).card : ENNReal) *
        (8 * (delta : ENNReal) ^ 2) := by
  unfold assignedBodyMass
  calc
    (∑ i ∈ (rawIndexFactorization active parent).fiber k,
        volume (fine.tubes i).carrier) <=
        ∑ _i ∈ (rawIndexFactorization active parent).fiber k,
          8 * (delta : ENNReal) ^ 2 := by
      exact Finset.sum_le_sum fun i _ =>
        (fine.tubes i).volume_le_eight_mul_sq_of_le_half hdeltaHalf
    _ = (((rawIndexFactorization active parent).fiber k).card : ENNReal) *
        (8 * (delta : ENNReal) ^ 2) := by
      simp only [Finset.sum_const, nsmul_eq_mul]

/-- Efficiency plus a raw fibre-cardinality cap forces a geometric lower
bound on the branching scale. -/
theorem efficientParent_geometric_branching_budget
    (fine : UniformTubeFamily delta iota)
    (coarse : UniformTubeFamily rho kappa)
    (active : Finset iota) (parent : iota -> kappa)
    (sourceA coverLoss : ENNReal)
    (hdeltaHalf : delta <= (2 : NNReal)⁻¹)
    (hrhoHalf : rho <= (2 : NNReal)⁻¹)
    (q B : Nat) (k : kappa)
    (hk : k ∈ efficientParents fine coarse active parent sourceA coverLoss)
    (hcard : ((rawIndexFactorization active parent).fiber k).card <= q * B) :
    sourceA * ((rho : ENNReal) ^ 2 / 2) <=
      (2 * coverLoss) * ((q * B : Nat) : ENNReal) *
        (8 * (delta : ENNReal) ^ 2) := by
  have hefficient :
      sourceA * volume (coarse.tubes k).carrier <=
        (2 * coverLoss) * assignedBodyMass fine active parent k :=
    (Finset.mem_filter.mp hk).2
  have hcoarseLower :
      (rho : ENNReal) ^ 2 / 2 <= volume (coarse.tubes k).carrier :=
    (coarse.tubes k).half_sq_le_volume_of_le_half hrhoHalf
  have hmass := assignedBodyMass_le_card_mul_eight_sq
    fine active parent hdeltaHalf k
  have hcardCoe :
      (((rawIndexFactorization active parent).fiber k).card : ENNReal) <=
        ((q * B : Nat) : ENNReal) := by
    exact_mod_cast hcard
  have hcardMass :
      (((rawIndexFactorization active parent).fiber k).card : ENNReal) *
          (8 * (delta : ENNReal) ^ 2) <=
        ((q * B : Nat) : ENNReal) * (8 * (delta : ENNReal) ^ 2) :=
    mul_le_mul_of_nonneg_right hcardCoe (by exact bot_le)
  calc
    sourceA * ((rho : ENNReal) ^ 2 / 2) <=
        sourceA * volume (coarse.tubes k).carrier :=
      mul_le_mul_of_nonneg_left hcoarseLower (by exact bot_le)
    _ <= (2 * coverLoss) * assignedBodyMass fine active parent k := hefficient
    _ <= (2 * coverLoss) *
        ((((rawIndexFactorization active parent).fiber k).card : ENNReal) *
          (8 * (delta : ENNReal) ^ 2)) :=
      mul_le_mul_of_nonneg_left hmass (by exact bot_le)
    _ <= (2 * coverLoss) *
        (((q * B : Nat) : ENNReal) * (8 * (delta : ENNReal) ^ 2)) :=
      mul_le_mul_of_nonneg_left hcardMass (by exact bot_le)
    _ = (2 * coverLoss) * ((q * B : Nat) : ENNReal) *
        (8 * (delta : ENNReal) ^ 2) := by ring

/-- The selected efficient parent supplies the endpoint's second source
budget once the cover loss is absorbed.  In logarithmic bucketing `q = 2`,
so the extra loss is a fixed numerical constant. -/
theorem branching_source_budget_of_efficientParent
    (fine : UniformTubeFamily delta iota)
    (coarse : UniformTubeFamily rho kappa)
    (active : Finset iota) (parent : iota -> kappa)
    (sourceA coverLoss target : NNReal)
    (hdeltaHalf : delta <= (2 : NNReal)⁻¹)
    (hrhoHalf : rho <= (2 : NNReal)⁻¹)
    (q B : Nat) (k : kappa)
    (hk : k ∈ efficientParents fine coarse active parent
      (sourceA : ENNReal) (coverLoss : ENNReal))
    (hcard : ((rawIndexFactorization active parent).fiber k).card <= q * B)
    (hAbsorb : 524288 * coverLoss * (q : NNReal) ^ 2 <= target) :
    8192 * (q : NNReal) * sourceA * rho ^ 2 <=
      target * (B : NNReal) * (delta ^ 2 / 2) := by
  have hgeomENN := efficientParent_geometric_branching_budget
    fine coarse active parent (sourceA : ENNReal) (coverLoss : ENNReal)
      hdeltaHalf hrhoHalf q B k hk hcard
  have hgeom :
      sourceA * (rho ^ 2 / 2) <=
        (2 * coverLoss) * ((q * B : Nat) : NNReal) * (8 * delta ^ 2) := by
    exact_mod_cast hgeomENN
  have hscaled := mul_le_mul_of_nonneg_left hgeom
    (by positivity : (0 : NNReal) <= 16384 * (q : NNReal))
  calc
    8192 * (q : NNReal) * sourceA * rho ^ 2 =
        (16384 * (q : NNReal)) * (sourceA * (rho ^ 2 / 2)) := by
      ring
    _ <= (16384 * (q : NNReal)) *
        ((2 * coverLoss) * ((q * B : Nat) : NNReal) *
          (8 * delta ^ 2)) := hscaled
    _ = (524288 * coverLoss * (q : NNReal) ^ 2) *
        (B : NNReal) * (delta ^ 2 / 2) := by
      norm_num [Nat.cast_mul]
      ring
    _ <= target * (B : NNReal) * (delta ^ 2 / 2) := by
      exact mul_le_mul' (mul_le_mul' hAbsorb le_rfl) le_rfl

end

end Family8EfficientSelectedBranchingSourceBudgetV2
