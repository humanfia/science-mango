import Family8Grounding.Family8CertifiedPlankIntersectingNearParallelRowV1
import Family8Grounding.Family8SelectedParentCertifiedPlankCordobaThresholdedAngleV6
import Mathlib.Tactic

/-!
# Intersection-supported labelled slab L2 summation

This module combines the normalized Appendix-B.2 row container with the
existing certified plank pair-overlap estimate.  The angle buckets are the
literal thresholded buckets already used by Family 8, but every summation row
is restricted to bodies which actually intersect the fixed body.

No individual shading-volume floor is used.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 6000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal InnerProductSpace

namespace Family8CertifiedPlankLabelledSlabL2V1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Family8CertifiedPlankPairOverlapV2
open Family8CertifiedPlankDyadicCordobaV2
open Family8CertifiedPlankIntersectingNearParallelRowV1
open Family8SelectedParentCertifiedPlankCordobaConnectorV4
open Family8SelectedParentCertifiedPlankCordobaThresholdedAngleV6
open FamilyStickyCinematicL32FiniteWeightedBucketV1
open FamilyStickyCinematicL32Lemma57DyadicCeilBucketV1

noncomputable section

local instance (p : Prop) : Decidable p := Classical.propDecidable p

universe u

variable {iota : Type u} [Fintype iota]
variable {F : ConvexFamily iota} {Y : Shading F}
variable {C a b : NNReal}

theorem dyadicCeilUpper_pos (k : Int) : 0 < dyadicCeilUpper k := by
  exact Real.rpow_pos_of_pos (by norm_num) _

/-- The sine upper endpoint associated with the thresholded inverse-sine
bucket.  The exceptional class has endpoint `a / b`; a genuine inverse-sine
bucket with upper endpoint `U` has sine endpoint `2 / U`. -/
def certifiedPlankThresholdedSineUpper (a b : NNReal) :
    Option Int → NNReal
  | none => a / b
  | some k => Real.toNNReal (2 / dyadicCeilUpper k)

theorem le_two_div_dyadicCeilUpper_inv_bucket
    {s : Real} (hs : 0 < s) :
    s ≤ 2 / dyadicCeilUpper (dyadicCeilBucket s⁻¹) := by
  let U := dyadicCeilUpper (dyadicCeilBucket s⁻¹)
  have hU : 0 < U := dyadicCeilUpper_pos _
  have hinv : 0 < s⁻¹ := inv_pos.mpr hs
  have hhalf := (dyadicCeilUpper_half_lt_and_le hinv).1
  change U / 2 < s⁻¹ at hhalf
  have htwo : (0 : Real) < 2 := by norm_num
  have hmul := mul_lt_mul_of_pos_right hhalf (mul_pos htwo hs)
  have hprod : s * U < 2 := by
    calc
      s * U = (U / 2) * (2 * s) := by ring
      _ < s⁻¹ * (2 * s) := hmul
      _ = 2 := by field_simp [ne_of_gt hs]
  change s ≤ 2 / U
  exact le_of_lt ((lt_div_iff₀ hU).2 hprod)

omit [Fintype iota] in
/-- Every actual pair sine is bounded by the endpoint of its canonical
thresholded bucket. -/
theorem certifiedPlankPairSine_le_thresholdedSineUpper
    (cert : ∀ i, PlankDimensionsCertificate C a b (F i))
    (i j : iota) :
    certifiedPlankPairSine cert i j ≤
      (certifiedPlankThresholdedSineUpper a b
        (certifiedPlankThresholdedPairLevel cert i j) : Real) := by
  let s := certifiedPlankPairSine cert i j
  let q : Real := ((a / b : NNReal) : Real)
  by_cases hcut : q ≤ s
  · have hq : 0 < q := certifiedPlankAspectRatio_pos cert i
    have hs : 0 < s := hq.trans_le hcut
    have hupper := le_two_div_dyadicCeilUpper_inv_bucket hs
    unfold certifiedPlankThresholdedPairLevel
    rw [if_pos hcut]
    simp only [certifiedPlankThresholdedSineUpper]
    rw [Real.coe_toNNReal]
    · exact hupper
    · exact (div_nonneg (by norm_num) (dyadicCeilUpper_pos _).le)
  · have hlt : s < q := lt_of_not_ge hcut
    unfold certifiedPlankThresholdedPairLevel
    rw [if_neg hcut]
    simpa [certifiedPlankThresholdedSineUpper, q] using hlt.le

omit [Fintype iota] in
/-- Every thresholded endpoint remains above the shortest plank scale. -/
theorem certifiedPlank_a_le_thresholdedSineUpper
    (cert : ∀ i, PlankDimensionsCertificate C a b (F i))
    (i j : iota) :
    a ≤ certifiedPlankThresholdedSineUpper a b
      (certifiedPlankThresholdedPairLevel cert i j) := by
  have hbpos : 0 < b := (cert i).a_pos.trans_le (cert i).a_le_b
  have hab : a ≤ a / b := by
    apply (le_div_iff₀ hbpos).2
    calc
      a * b ≤ a * 1 := by
        simpa [mul_comm] using mul_le_mul_left (cert i).b_le_one a
      _ = a := mul_one a
  let s := certifiedPlankPairSine cert i j
  let q : Real := ((a / b : NNReal) : Real)
  by_cases hcut : q ≤ s
  · apply NNReal.coe_le_coe.mp
    have haReal : (a : Real) ≤ q := by exact_mod_cast hab
    exact (haReal.trans hcut).trans
      (certifiedPlankPairSine_le_thresholdedSineUpper cert i j)
  · unfold certifiedPlankThresholdedPairLevel
    rw [if_neg hcut]
    simpa [certifiedPlankThresholdedSineUpper] using hab

/-- The actual-intersection subrow of one exact thresholded angle level. -/
def certifiedPlankIntersectingThresholdedLevelRow
    (cert : ∀ i, PlankDimensionsCertificate C a b (F i))
    (i : iota) (k : Option Int) : Finset iota := by
  classical
  exact Finset.univ.filter fun j ↦
    ((F i : Set Space) ∩ (F j : Set Space)).Nonempty ∧
      certifiedPlankThresholdedPairLevel cert i j = k

@[simp] theorem mem_certifiedPlankIntersectingThresholdedLevelRow
    (cert : ∀ i, PlankDimensionsCertificate C a b (F i))
    (i j : iota) (k : Option Int) :
    j ∈ certifiedPlankIntersectingThresholdedLevelRow cert i k ↔
      ((F i : Set Space) ∩ (F j : Set Space)).Nonempty ∧
        certifiedPlankThresholdedPairLevel cert i j = k := by
  classical
  simp [certifiedPlankIntersectingThresholdedLevelRow]

/-- Each exact angle-level row inherits the sharp B.2 Katz--Tao body-mass
bound at its canonical sine endpoint. -/
theorem sum_body_volume_intersectingThresholdedLevelRow_le
    (cert : ∀ i, PlankDimensionsCertificate C a b (F i))
    (hunit : ∀ k, (F k : Set Space) ⊆ Metric.closedBall (0 : Space) 1)
    (D : ENNReal) (hKT : IsKatzTao D F)
    (i : iota) (k : Option Int)
    (_hk : k ∈ plankAngleLevels (certifiedPlankThresholdedLevels cert)) :
    (∑ j ∈ certifiedPlankIntersectingThresholdedLevelRow cert i k,
        volume (F j : Set Space)) ≤
      D * (128 *
        (certifiedPlankThresholdedSineUpper a b k : ENNReal)) := by
  classical
  by_cases hrow :
      (certifiedPlankIntersectingThresholdedLevelRow cert i k).Nonempty
  · obtain ⟨j, hj⟩ := hrow
    have hj' :=
      (mem_certifiedPlankIntersectingThresholdedLevelRow cert i j k).1 hj
    have hkEq := hj'.2
    have ha : a ≤ certifiedPlankThresholdedSineUpper a b k := by
      rw [← hkEq]
      exact certifiedPlank_a_le_thresholdedSineUpper cert i j
    have hsubset : certifiedPlankIntersectingThresholdedLevelRow cert i k ⊆
        certifiedPlankIntersectingNearParallelRow cert i
          (certifiedPlankThresholdedSineUpper a b k) := by
      intro l hl
      have hl' :=
        (mem_certifiedPlankIntersectingThresholdedLevelRow cert i l k).1 hl
      apply (mem_certifiedPlankIntersectingNearParallelRow cert i l _).2
      refine ⟨hl'.1, ?_⟩
      rw [← hl'.2]
      exact certifiedPlankPairSine_le_thresholdedSineUpper cert i l
    calc
      (∑ j ∈ certifiedPlankIntersectingThresholdedLevelRow cert i k,
          volume (F j : Set Space)) ≤
          ∑ j ∈ certifiedPlankIntersectingNearParallelRow cert i
            (certifiedPlankThresholdedSineUpper a b k),
              volume (F j : Set Space) :=
        Finset.sum_le_sum_of_subset hsubset
      _ ≤ D * (128 *
          (certifiedPlankThresholdedSineUpper a b k : ENNReal)) :=
        sum_body_volume_intersectingNearParallelRow_le cert hunit D hKT i _ ha
  · rw [Finset.not_nonempty_iff_eq_empty.mp hrow]
    simp

/-! ## Weighted row payment -/

/-- Uniform scale left after multiplying the certified pair-overlap ratio by
the sharp B.2 angular thickness. -/
def certifiedPlankLabelledSlabAngularRowFactor
    (C a b : NNReal) : ENNReal :=
  max ((a / b : NNReal) : ENNReal)
    (4 * ((a / b : NNReal) : ENNReal) *
      ((((C⁻¹ : NNReal) : ENNReal) ^ 3)⁻¹))

/-- Exact inverse-sine cancellation on each thresholded angle bucket. -/
theorem certifiedPlankAngleScale_mul_thresholdedSineUpper_le
    (cert : ∀ i, PlankDimensionsCertificate C a b (F i))
    (k : Option Int)
    (_hk : k ∈ plankAngleLevels (certifiedPlankThresholdedLevels cert)) :
    certifiedPlankAngleScale C a b
        certifiedPlankDyadicInverseSineWeight k *
      (certifiedPlankThresholdedSineUpper a b k : ENNReal) ≤
        certifiedPlankLabelledSlabAngularRowFactor C a b := by
  cases k with
  | none =>
      simp only [certifiedPlankAngleScale,
        certifiedPlankThresholdedSineUpper, one_mul]
      exact le_max_left _ _
  | some label =>
      let U : Real := dyadicCeilUpper label
      have hU : 0 < U := dyadicCeilUpper_pos label
      have hquot : 0 ≤ 2 / U := div_nonneg (by norm_num) hU.le
      have hthetaReal :
          ((Real.toNNReal (2 / U) : NNReal) : Real) = 2 / U :=
        Real.coe_toNNReal _ hquot
      have htheta :
          ((Real.toNNReal (2 / U) : NNReal) : ENNReal) =
            ENNReal.ofReal (2 / U) := by
        rw [← ENNReal.ofReal_coe_nnreal, hthetaReal]
      have hcancel : ENNReal.ofReal U * ENNReal.ofReal (2 / U) = 2 := by
        rw [← ENNReal.ofReal_mul hU.le]
        have hreal : U * (2 / U) = 2 := by field_simp
        rw [hreal]
        norm_num
      simp only [certifiedPlankAngleScale,
        certifiedPlankDyadicInverseSineWeight,
        certifiedPlankThresholdedSineUpper]
      change
        (ENNReal.ofReal U * 2 * ((a / b : NNReal) : ENNReal) *
            ((((C⁻¹ : NNReal) : ENNReal) ^ 3)⁻¹)) *
              ((Real.toNNReal (2 / U) : NNReal) : ENNReal) ≤
          certifiedPlankLabelledSlabAngularRowFactor C a b
      rw [htheta]
      calc
        (ENNReal.ofReal U * 2 * ((a / b : NNReal) : ENNReal) *
            ((((C⁻¹ : NNReal) : ENNReal) ^ 3)⁻¹)) *
              ENNReal.ofReal (2 / U) =
            4 * ((a / b : NNReal) : ENNReal) *
              ((((C⁻¹ : NNReal) : ENNReal) ^ 3)⁻¹) := by
          calc
            _ = (ENNReal.ofReal U * ENNReal.ofReal (2 / U)) * 2 *
                ((a / b : NNReal) : ENNReal) *
                ((((C⁻¹ : NNReal) : ENNReal) ^ 3)⁻¹) := by ac_rfl
            _ = _ := by rw [hcancel]; norm_num
        _ ≤ certifiedPlankLabelledSlabAngularRowFactor C a b :=
          le_max_right _ _

#print axioms certifiedPlankPairSine_le_thresholdedSineUpper
#print axioms certifiedPlank_a_le_thresholdedSineUpper
#print axioms sum_body_volume_intersectingThresholdedLevelRow_le
#print axioms certifiedPlankAngleScale_mul_thresholdedSineUpper_le

end
end Family8CertifiedPlankLabelledSlabL2V1
