import Family8Grounding.Family8KatzTaoFrostmanPropertiesV1
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8SphereDirectionPackingV1

open LeanEval.Analysis.WangZahlKakeya

noncomputable section

set_option autoImplicit false
set_option warningAsError true

/-!
# Quantitative packing of directions on the two-sphere

This is the finite packing input needed by the common-point tube argument.
The proof does not assume a covering-number estimate.  Around every unit
direction we put an open Euclidean ball of radius `delta / 2`.  Separation
makes these balls disjoint, while unit norm puts their union in the spherical
shell between radii `1 - delta / 2` and `1 + delta / 2`.  Comparing the exact
three-dimensional volumes of the balls and the shell loses one power of
`delta` and gives the dimension-two bound.

The denominator-free conclusion is convenient in `ENNReal` downstream, and
the final theorem gives a literal natural-cardinality ceiling bound.
-/

/-- Open balls of radius `delta / 2` about pairwise `delta`-separated points
are pairwise disjoint. -/
theorem directionSmallBalls_pairwiseDisjoint
    {index : Type} [DecidableEq index]
    (indices : Finset index) (direction : index → Space) (delta : NNReal)
    (hsep : ∀ i ∈ indices, ∀ j ∈ indices, i ≠ j →
      (delta : Real) ≤ dist (direction i) (direction j)) :
    Set.PairwiseDisjoint (↑indices : Set index)
      (fun i => Metric.ball (direction i) ((delta : Real) / 2)) := by
  intro i hi j hj hij
  apply Metric.ball_disjoint_ball
  calc
    (delta : Real) / 2 + (delta : Real) / 2 = (delta : Real) := by ring
    _ ≤ dist (direction i) (direction j) := hsep i hi j hj hij

/-- Small balls around unit directions lie in a shell of thickness `delta`.
This is the geometric reason that the final exponent is `-2`, not `-3`. -/
theorem directionSmallBallUnion_subset_shell
    {index : Type} [DecidableEq index]
    (indices : Finset index) (direction : index → Space) (delta : NNReal)
    (hunit : ∀ i ∈ indices, ‖direction i‖ = 1) :
    (⋃ i ∈ indices, Metric.ball (direction i) ((delta : Real) / 2)) ⊆
      Metric.ball (0 : Space) (1 + (delta : Real) / 2) \
        Metric.closedBall (0 : Space) (1 - (delta : Real) / 2) := by
  intro x hx
  obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp hx
  rw [Metric.mem_ball] at hxi
  constructor
  · rw [Metric.mem_ball]
    calc
      dist x 0 ≤ dist x (direction i) + dist (direction i) 0 :=
        dist_triangle _ _ _
      _ < (delta : Real) / 2 + dist (direction i) 0 :=
        by simpa [add_comm] using
          add_lt_add_right hxi (dist (direction i) 0)
      _ = 1 + (delta : Real) / 2 := by
        rw [dist_zero_right, hunit i hi]
        ring
  · rw [Metric.mem_closedBall]
    have hreverse :
        1 < (delta : Real) / 2 + dist x 0 := by
      calc
        1 = dist (direction i) 0 := by
          rw [dist_zero_right, hunit i hi]
        _ ≤ dist (direction i) x + dist x 0 := dist_triangle _ _ _
        _ < (delta : Real) / 2 + dist x 0 := by
          simpa [add_comm, dist_comm] using
            add_lt_add_right hxi (dist x 0)
    linarith

/-- The inner closed ball is contained in the outer open ball whenever the
shell half-width is positive. -/
theorem closedBall_one_sub_half_subset_ball_one_add_half
    (delta : NNReal) (hdelta : 0 < delta) :
    Metric.closedBall (0 : Space) (1 - (delta : Real) / 2) ⊆
      Metric.ball (0 : Space) (1 + (delta : Real) / 2) := by
  intro x hx
  rw [Metric.mem_closedBall] at hx
  rw [Metric.mem_ball]
  have hdeltaReal : 0 < (delta : Real) := NNReal.coe_pos.mpr hdelta
  linarith

/-- A finite pairwise `delta`-separated family of unit directions has the
denominator-free sphere-packing bound `card * delta^2 ≤ 32`.

The constant `32` is deliberately coarse.  The exact shell computation gives
`6 r + 2 r^3` for `r = delta / 2`; using `delta ≤ 1` bounds this by `8 r`. -/
theorem directionFinset_card_mul_sq_le_thirtyTwo
    {index : Type} [DecidableEq index]
    (indices : Finset index) (direction : index → Space) (delta : NNReal)
    (hdelta : 0 < delta) (hdeltaOne : delta ≤ 1)
    (hunit : ∀ i ∈ indices, ‖direction i‖ = 1)
    (hsep : ∀ i ∈ indices, ∀ j ∈ indices, i ≠ j →
      (delta : Real) ≤ dist (direction i) (direction j)) :
    (indices.card : Real) * (delta : Real) ^ 2 ≤ 32 := by
  let r : Real := (delta : Real) / 2
  let outer : Set Space := Metric.ball (0 : Space) (1 + r)
  let inner : Set Space := Metric.closedBall (0 : Space) (1 - r)
  let packed : Set Space := ⋃ i ∈ indices, Metric.ball (direction i) r
  have hdeltaReal : 0 < (delta : Real) := NNReal.coe_pos.mpr hdelta
  have hdeltaRealOne : (delta : Real) ≤ 1 := by exact_mod_cast hdeltaOne
  have hr : 0 < r := by dsimp only [r]; linarith
  have hrHalf : r ≤ (1 : Real) / 2 := by dsimp only [r]; linarith
  have hinnerRadius : 0 ≤ 1 - r := by linarith
  have houterRadius : 0 ≤ 1 + r := by linarith
  have hdisjoint :
      Set.PairwiseDisjoint (↑indices : Set index)
        (fun i => Metric.ball (direction i) r) := by
    simpa only [r] using
      directionSmallBalls_pairwiseDisjoint indices direction delta hsep
  have hpackedShell : packed ⊆ outer \ inner := by
    simpa only [packed, outer, inner, r] using
      directionSmallBallUnion_subset_shell indices direction delta hunit
  have hinnerOuter : inner ⊆ outer := by
    simpa only [inner, outer, r] using
      closedBall_one_sub_half_subset_ball_one_add_half delta hdelta
  have hpackedVolume :
      volume packed =
        ∑ i ∈ indices, volume (Metric.ball (direction i) r) := by
    simpa only [packed] using
      measure_biUnion_finset hdisjoint (fun _ _ => measurableSet_ball)
  have hshellVolume :
      volume (outer \ inner) = volume outer - volume inner := by
    exact measure_sdiff hinnerOuter measurableSet_closedBall.nullMeasurableSet
      measure_closedBall_lt_top.ne
  have hmeasure : volume packed ≤ volume (outer \ inner) :=
    measure_mono hpackedShell
  have hshellNeTop : volume (outer \ inner) ≠ ∞ := by
    apply ne_of_lt
    exact (measure_mono sdiff_subset).trans_lt measure_ball_lt_top
  have hmeasureReal := ENNReal.toReal_mono hshellNeTop hmeasure
  have hinnerVolumeLe : volume inner ≤ volume outer := measure_mono hinnerOuter
  have hpackedReal :
      (volume packed).toReal =
        (indices.card : Real) * r ^ 3 * (Real.pi * 4 / 3) := by
    rw [hpackedVolume]
    simp only [EuclideanSpace.volume_ball_fin_three, Finset.sum_const,
      nsmul_eq_mul]
    rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_pow]
    · simp only [ENNReal.toReal_natCast, ENNReal.toReal_ofReal hr.le]
      rw [ENNReal.toReal_ofReal]
      · ring
      · positivity
  have hshellReal :
      (volume (outer \ inner)).toReal =
        (1 + r) ^ 3 * (Real.pi * 4 / 3) -
          (1 - r) ^ 3 * (Real.pi * 4 / 3) := by
    rw [hshellVolume,
      ENNReal.toReal_sub_of_le hinnerVolumeLe measure_ball_lt_top.ne]
    simp only [outer, inner, EuclideanSpace.volume_ball_fin_three,
      EuclideanSpace.volume_closedBall_fin_three]
    rw [ENNReal.toReal_mul, ENNReal.toReal_pow,
      ENNReal.toReal_mul, ENNReal.toReal_pow]
    · simp only [ENNReal.toReal_ofReal houterRadius,
        ENNReal.toReal_ofReal hinnerRadius]
      rw [ENNReal.toReal_ofReal (by positivity :
        0 ≤ Real.pi * 4 / 3)]
  rw [hpackedReal, hshellReal] at hmeasureReal
  have hpi : 0 < Real.pi * 4 / 3 := by positivity
  have hcore :
      (indices.card : Real) * r ^ 3 ≤
        (1 + r) ^ 3 - (1 - r) ^ 3 := by
    apply (mul_le_mul_iff_right₀ hpi).mp
    nlinarith
  have hrOne : r ≤ 1 := hrHalf.trans (by norm_num)
  have hrsqOne : r ^ 2 ≤ 1 := by nlinarith [sq_nonneg (1 - r)]
  have hcube : r ^ 3 ≤ r := by
    have := mul_le_mul_of_nonneg_left hrsqOne hr.le
    nlinarith
  have hcoreEight : (indices.card : Real) * r ^ 3 ≤ 8 * r := by
    calc
      (indices.card : Real) * r ^ 3 ≤
          (1 + r) ^ 3 - (1 - r) ^ 3 := hcore
      _ ≤ 8 * r := by nlinarith
  have hcardRSq : (indices.card : Real) * r ^ 2 ≤ 8 := by
    apply (mul_le_mul_iff_right₀ hr).mp
    nlinarith
  dsimp only [r] at hcardRSq
  nlinarith

/-- Literal `C delta^{-2}` form, stated over the reals. -/
theorem directionFinset_card_le_thirtyTwo_mul_inv_sq
    {index : Type} [DecidableEq index]
    (indices : Finset index) (direction : index → Space) (delta : NNReal)
    (hdelta : 0 < delta) (hdeltaOne : delta ≤ 1)
    (hunit : ∀ i ∈ indices, ‖direction i‖ = 1)
    (hsep : ∀ i ∈ indices, ∀ j ∈ indices, i ≠ j →
      (delta : Real) ≤ dist (direction i) (direction j)) :
    (indices.card : Real) ≤ 32 * ((delta : Real)⁻¹) ^ 2 := by
  have hmul := directionFinset_card_mul_sq_le_thirtyTwo
    indices direction delta hdelta hdeltaOne hunit hsep
  have hdeltaReal : 0 < (delta : Real) := NNReal.coe_pos.mpr hdelta
  calc
    (indices.card : Real) =
        ((indices.card : Real) * (delta : Real) ^ 2) /
          (delta : Real) ^ 2 := by field_simp
    _ ≤ 32 / (delta : Real) ^ 2 := by gcongr
    _ = 32 * ((delta : Real)⁻¹) ^ 2 := by field_simp

/-- Natural-cardinality version ready for a point-multiplicity cap. -/
theorem directionFinset_card_le_natCeil_thirtyTwo_mul_inv_sq
    {index : Type} [DecidableEq index]
    (indices : Finset index) (direction : index → Space) (delta : NNReal)
    (hdelta : 0 < delta) (hdeltaOne : delta ≤ 1)
    (hunit : ∀ i ∈ indices, ‖direction i‖ = 1)
    (hsep : ∀ i ∈ indices, ∀ j ∈ indices, i ≠ j →
      (delta : Real) ≤ dist (direction i) (direction j)) :
    indices.card ≤ Nat.ceil (32 * ((delta : Real)⁻¹) ^ 2) := by
  exact_mod_cast
    (directionFinset_card_le_thirtyTwo_mul_inv_sq
      indices direction delta hdelta hdeltaOne hunit hsep).trans
      (Nat.le_ceil _)

#print axioms directionSmallBalls_pairwiseDisjoint
#print axioms directionSmallBallUnion_subset_shell
#print axioms closedBall_one_sub_half_subset_ball_one_add_half
#print axioms directionFinset_card_mul_sq_le_thirtyTwo
#print axioms directionFinset_card_le_thirtyTwo_mul_inv_sq
#print axioms directionFinset_card_le_natCeil_thirtyTwo_mul_inv_sq

end

end Family8SphereDirectionPackingV1
