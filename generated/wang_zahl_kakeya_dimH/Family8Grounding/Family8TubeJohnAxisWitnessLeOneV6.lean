import Family8Grounding.Family8TubeJohnUnitRescalingGeometryV5

set_option autoImplicit false
set_option warningAsError true

open Set
open scoped NNReal InnerProductSpace

namespace Family8TubeJohnAxisWitnessLeOneV6

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Family8Def212ConvexWolffAtEveryScaleV2
open Family8TubeJohnAxisWitnessV1

noncomputable section

/-!
# The explicit tube John witness throughout the full unit-scale window

The witness is unchanged from V1: midpoint center, an axis-aligned
orthonormal frame, and semiaxes `rho, rho, 1/2`.  The sharper outer estimate
uses Parseval jointly across the transverse and longitudinal error
coordinates, rather than maximizing those contributions separately.
-/

/-- Every positive tube of radius at most one has the explicit factor-three
John-axis witness with semiaxes `rho, rho, 1/2`. -/
theorem Tube.johnAxisWitness_of_pos_le_one
    {rho : NNReal} (T : Tube rho) (hrho : 0 < rho)
    (hrhoOne : rho <= 1) :
    Nonempty (JohnAxisWitness T.body) := by
  obtain ⟨frame, hframe⟩ := T.exists_alignedFrame
  let center : Space := tubeCenter T
  let radius : Fin 3 -> NNReal := tubeJohnRadii rho
  have hrhoReal : 0 < (rho : Real) := NNReal.coe_pos.mpr hrho
  have hrho0 : (rho : Real) ≠ 0 := hrhoReal.ne'
  have hrhoOneReal : (rho : Real) <= 1 := by
    exact_mod_cast hrhoOne
  refine ⟨
    { center := center
      frame := frame
      radius := radius
      inner := ?_
      outer := ?_ }⟩
  · intro x hx
    rcases hx with ⟨z, hz, rfl⟩
    rw [Fin.sum_univ_three] at hz
    norm_num at hz
    have hz2sq : (z 2) ^ 2 <= 1 := by
      nlinarith [sq_nonneg (z 0), sq_nonneg (z 1)]
    have hz2lo : -1 <= z 2 := by nlinarith [sq_nonneg (z 2 + 1)]
    have hz2hi : z 2 <= 1 := by nlinarith [sq_nonneg (z 2 - 1)]
    let t : Real := (2 : Real)⁻¹ + z 2 / 2
    have ht : t ∈ Set.Icc (0 : Real) 1 := by
      constructor <;> dsimp only [t] <;> norm_num at * <;> linarith
    apply Metric.mem_cthickening_of_dist_le
      (center + ∑ i, (z i * (radius i : Real)) • frame i)
      (T.axis.base + t • T.axis.direction) (rho : Real)
      T.axis.carrier (T.axis.mem_carrier_of_mem_Icc ht)
    have hvec :
        center + ∑ i, (z i * (radius i : Real)) • frame i -
            (T.axis.base + t • T.axis.direction) =
          (z 0 * (rho : Real)) • frame 0 +
            (z 1 * (rho : Real)) • frame 1 := by
      rw [Fin.sum_univ_three]
      dsimp only [center, tubeCenter, t]
      simp [radius, tubeJohnRadii]
      rw [hframe]
      module
    rw [dist_eq_norm, hvec]
    apply (sq_le_sq₀ (norm_nonneg _) (NNReal.zero_le_coe)).mp
    have hnormSq :
        ‖(z 0 * (rho : Real)) • frame 0 +
            (z 1 * (rho : Real)) • frame 1‖ ^ 2 =
          (rho : Real) ^ 2 * ((z 0) ^ 2 + (z 1) ^ 2) := by
      rw [← real_inner_self_eq_norm_sq]
      simp only [inner_add_left, inner_add_right, real_inner_smul_left,
        real_inner_smul_right, frame.inner_eq_ite]
      norm_num
      ring
    rw [hnormSq]
    have hz01 : (z 0) ^ 2 + (z 1) ^ 2 <= 1 := by
      nlinarith [sq_nonneg (z 2)]
    calc
      (rho : Real) ^ 2 * ((z 0) ^ 2 + (z 1) ^ 2) <=
          (rho : Real) ^ 2 * 1 := by gcongr
      _ = (rho : Real) ^ 2 := by ring
  · intro x hx
    rw [Tube.coe_body] at hx
    rw [Tube.carrier,
      T.axis.isCompact_carrier.cthickening_eq_biUnion_closedBall
        (show 0 <= (rho : Real) by positivity)] at hx
    simp only [Set.mem_iUnion, Metric.mem_closedBall] at hx
    obtain ⟨y, hy, hxy⟩ := hx
    rw [T.axis.carrier_eq_image] at hy
    obtain ⟨t, ht, rfl⟩ := hy
    let q : Space := T.axis.base + t • T.axis.direction
    let e : Space := x - q
    let d : Fin 3 -> Real := fun i => ⟪frame i, x - center⟫_Real
    let z : Fin 3 -> Real := fun i =>
      if i = 2 then 2 * d i else d i / (rho : Real)
    have heNorm : ‖e‖ <= (rho : Real) := by
      simpa only [e, q, dist_eq_norm, norm_sub_rev] using hxy
    have heNormSq : ‖e‖ ^ 2 <= (rho : Real) ^ 2 := by
      nlinarith [norm_nonneg e]
    have hparseval := frame.sum_sq_inner_right e
    rw [Fin.sum_univ_three] at hparseval
    have hdtrans (i : Fin 3) (hi : i ≠ 2) :
        d i = ⟪frame i, e⟫_Real := by
      dsimp only [d, e, q, center, tubeCenter]
      rw [inner_sub_right, inner_sub_right, inner_add_right,
        inner_add_right, real_inner_smul_right, real_inner_smul_right,
        ← hframe, frame.inner_eq_zero hi]
      ring
    have hunitNum :
        (d 0) ^ 2 + (d 1) ^ 2 + ⟪frame 2, e⟫_Real ^ 2 <=
          (rho : Real) ^ 2 := by
      rw [hdtrans 0 (by decide), hdtrans 1 (by decide)]
      nlinarith [hparseval, heNormSq]
    have hunit :
        (d 0 / (rho : Real)) ^ 2 + (d 1 / (rho : Real)) ^ 2 +
            (⟪frame 2, e⟫_Real / (rho : Real)) ^ 2 <= 1 := by
      rw [div_pow, div_pow, div_pow, ← add_div, ← add_div]
      apply (div_le_iff₀ (sq_pos_of_pos hrhoReal)).2
      simpa only [one_mul] using hunitNum
    have htcenter : |t - (2 : Real)⁻¹| <= (2 : Real)⁻¹ := by
      rw [abs_le]
      constructor <;> norm_num at * <;> linarith [ht.1, ht.2]
    have hd2eq : d 2 =
        (t - (2 : Real)⁻¹) + ⟪frame 2, e⟫_Real := by
      dsimp only [d, e, q, center, tubeCenter]
      rw [inner_sub_right, inner_sub_right, inner_add_right,
        inner_add_right, real_inner_smul_right, real_inner_smul_right,
        hframe, real_inner_self_eq_norm_sq, T.axis.norm_direction]
      norm_num
      ring
    let a : Real := t - (2 : Real)⁻¹
    let x2 : Real := ⟪frame 2, e⟫_Real / (rho : Real)
    let b : Real := 2 * a + (2 * (rho : Real) - 1) * x2
    have hx2sq : x2 ^ 2 <= 1 := by
      dsimp only [x2]
      nlinarith [hunit,
        sq_nonneg (d 0 / (rho : Real)),
        sq_nonneg (d 1 / (rho : Real))]
    have hx2Abs : |x2| <= 1 := by
      rw [abs_le]
      constructor <;> nlinarith [sq_nonneg (x2 + 1), sq_nonneg (x2 - 1)]
    have h2aAbs : |2 * a| <= 1 := by
      dsimp only [a]
      rw [abs_mul, abs_of_nonneg (by norm_num : (0 : Real) <= 2)]
      norm_num
      linarith
    have hcoefAbs : |2 * (rho : Real) - 1| <= 1 := by
      rw [abs_le]
      constructor <;> nlinarith
    have hbAbs : |b| <= 2 := by
      dsimp only [b]
      calc
        |2 * a + (2 * (rho : Real) - 1) * x2| <=
            |2 * a| + |(2 * (rho : Real) - 1) * x2| := abs_add_le _ _
        _ = |2 * a| + |2 * (rho : Real) - 1| * |x2| := by
          simp only [abs_mul]
        _ <= 1 + 1 * 1 := by
          exact add_le_add h2aAbs
            (mul_le_mul hcoefAbs hx2Abs (abs_nonneg _) (by norm_num))
        _ = 2 := by norm_num
    have hx2mul : (rho : Real) * x2 = ⟪frame 2, e⟫_Real := by
      dsimp only [x2]
      field_simp
    have h2d : 2 * d 2 = x2 + b := by
      rw [hd2eq]
      dsimp only [a, b]
      rw [← hx2mul]
      ring
    have hcross : 2 * x2 * b <= 4 := by
      calc
        2 * x2 * b <= |2 * x2 * b| := le_abs_self _
        _ = 2 * |x2| * |b| := by
          rw [abs_mul, abs_mul]
          norm_num
        _ <= 2 * 1 * 2 := by gcongr
        _ = 4 := by norm_num
    have hbBounds := abs_le.mp hbAbs
    have hbSq : b ^ 2 <= 4 := by nlinarith
    have hz0 : z 0 = d 0 / (rho : Real) := by simp [z]
    have hz1 : z 1 = d 1 / (rho : Real) := by simp [z]
    have hz2 : z 2 = 2 * d 2 := by simp [z]
    have hzsum : ∑ i, (z i) ^ 2 <= (3 : Real) ^ 2 := by
      rw [Fin.sum_univ_three, hz0, hz1, hz2, h2d]
      calc
        (d 0 / (rho : Real)) ^ 2 + (d 1 / (rho : Real)) ^ 2 +
              (x2 + b) ^ 2 =
            ((d 0 / (rho : Real)) ^ 2 + (d 1 / (rho : Real)) ^ 2 +
              x2 ^ 2) + 2 * x2 * b + b ^ 2 := by ring
        _ <= 1 + 4 + 4 := add_le_add (add_le_add hunit hcross) hbSq
        _ = (3 : Real) ^ 2 := by norm_num
    have hzmul (i : Fin 3) : z i * (radius i : Real) = d i := by
      fin_cases i
      · simp [z, radius, tubeJohnRadii, hrho0]
      · simp [z, radius, tubeJohnRadii, hrho0]
      · simp [z, radius, tubeJohnRadii]
        ring
    refine ⟨z, hzsum, ?_⟩
    have hsum : ∑ i, d i • frame i = x - center := by
      simpa only [d] using frame.sum_repr' (x - center)
    calc
      x = center + (x - center) := by abel
      _ = center + ∑ i, d i • frame i := by rw [hsum]
      _ = center + ∑ i, (z i * (radius i : Real)) • frame i := by
        congr 2
        funext i
        rw [hzmul i]

#print axioms Tube.johnAxisWitness_of_pos_le_one

end
end Family8TubeJohnAxisWitnessLeOneV6
