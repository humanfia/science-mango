import ArchonPhysics.CanonicalLInfinityLogEntropyProductionContinuity

/-!
# Quadratic Taylor control for the positive logarithm

On a common strictly positive floor, the derivative of the logarithm is
Lipschitz with coefficient `floor⁻²`.  The mean-value theorem therefore gives
a quadratic first-order remainder.  This scalar estimate is the pointwise
input needed to differentiate the canonical integrated logarithmic entropy
along an `L-infinity` trajectory.
-/

namespace ArchonPhysics.PositiveLogTaylorRemainder

open Set
open ArchonPhysics.CanonicalLInfinityLogEntropyProductionContinuity

/-- First-order logarithmic Taylor remainder on a common positive half-line. -/
theorem norm_log_sub_log_sub_inv_mul_sub_le
    {floor x y : Real} (hfloor : 0 < floor)
    (hx : floor ≤ x) (hy : floor ≤ y) :
    ‖Real.log y - Real.log x - x⁻¹ * (y - x)‖ ≤
      floor⁻¹ ^ 2 * ‖y - x‖ ^ 2 := by
  let remainderPrimitive : Real → Real := fun z =>
    Real.log z - x⁻¹ * (z - x)
  have hxpos : 0 < x := hfloor.trans_le hx
  have hypos : 0 < y := hfloor.trans_le hy
  have hprimitiveDifference :
      remainderPrimitive y - remainderPrimitive x =
        Real.log y - Real.log x - x⁻¹ * (y - x) := by
    dsimp [remainderPrimitive]
    ring
  rcases le_total x y with hxy | hyx
  · have hderiv : ∀ z ∈ Icc x y,
        HasDerivWithinAt remainderPrimitive (z⁻¹ - x⁻¹) (Icc x y) z := by
      intro z hz
      have hzpos : 0 < z := hxpos.trans_le hz.1
      have hlinear : HasDerivAt (fun u : Real => x⁻¹ * (u - x)) x⁻¹ z := by
        simpa using ((hasDerivAt_id z).sub_const x).const_mul x⁻¹
      exact ((Real.hasDerivAt_log hzpos.ne').sub hlinear).hasDerivWithinAt
    have hbound : ∀ z ∈ Ico x y,
        ‖z⁻¹ - x⁻¹‖ ≤ floor⁻¹ ^ 2 * ‖y - x‖ := by
      intro z hz
      have hzfloor : floor ≤ z := hx.trans hz.1
      refine (norm_inv_sub_inv_le_of_floor hfloor hzfloor hx).trans ?_
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
      rw [Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg (sub_nonneg.mpr hz.1),
        abs_of_nonneg (sub_nonneg.mpr hxy)]
      linarith [hz.2]
    have hmean := norm_image_sub_le_of_norm_deriv_le_segment'
      hderiv hbound y (right_mem_Icc.mpr hxy)
    calc
      ‖Real.log y - Real.log x - x⁻¹ * (y - x)‖ =
          ‖remainderPrimitive y - remainderPrimitive x‖ := by
            rw [hprimitiveDifference]
      _ ≤ (floor⁻¹ ^ 2 * ‖y - x‖) * (y - x) := hmean
      _ = floor⁻¹ ^ 2 * ‖y - x‖ ^ 2 := by
        rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hxy)]
        ring
  · have hderiv : ∀ z ∈ Icc y x,
        HasDerivWithinAt remainderPrimitive (z⁻¹ - x⁻¹) (Icc y x) z := by
      intro z hz
      have hzpos : 0 < z := hypos.trans_le hz.1
      have hlinear : HasDerivAt (fun u : Real => x⁻¹ * (u - x)) x⁻¹ z := by
        simpa using ((hasDerivAt_id z).sub_const x).const_mul x⁻¹
      exact ((Real.hasDerivAt_log hzpos.ne').sub hlinear).hasDerivWithinAt
    have hbound : ∀ z ∈ Ico y x,
        ‖z⁻¹ - x⁻¹‖ ≤ floor⁻¹ ^ 2 * ‖y - x‖ := by
      intro z hz
      have hzfloor : floor ≤ z := hy.trans hz.1
      refine (norm_inv_sub_inv_le_of_floor hfloor hzfloor hx).trans ?_
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
      rw [Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonpos (sub_nonpos.mpr hz.2.le),
        abs_of_nonpos (sub_nonpos.mpr hyx)]
      linarith [hz.1]
    have hmean := norm_image_sub_le_of_norm_deriv_le_segment'
      hderiv hbound x (right_mem_Icc.mpr hyx)
    calc
      ‖Real.log y - Real.log x - x⁻¹ * (y - x)‖ =
          ‖remainderPrimitive y - remainderPrimitive x‖ := by
            rw [hprimitiveDifference]
      _ = ‖remainderPrimitive x - remainderPrimitive y‖ :=
        norm_sub_rev _ _
      _ ≤ (floor⁻¹ ^ 2 * ‖y - x‖) * (x - y) := hmean
      _ = floor⁻¹ ^ 2 * ‖y - x‖ ^ 2 := by
        rw [Real.norm_eq_abs, abs_of_nonpos (sub_nonpos.mpr hyx)]
        ring

end ArchonPhysics.PositiveLogTaylorRemainder
