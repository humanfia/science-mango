import Mathlib.Analysis.Calculus.Deriv.Slope

set_option autoImplicit false

open Filter Metric Set
open scoped Topology

namespace FamilyStickyCinematicL32Prop41GraphTransverseSignV1

/-!
# Local sign change at a nonzero derivative

This is the calculus core of an internal proper graph crossing.  It is stated
with an explicit metric radius and is obtained directly from convergence of
secant slopes to the derivative.
-/

theorem exists_radius_derivative_mul_slope_pos
    {h : Real → Real} {x derivative : Real}
    (hderiv : HasDerivAt h derivative x) (hne : derivative ≠ 0) :
    ∃ eta : Real, 0 < eta ∧ ∀ y : Real,
      y ≠ x → |y - x| < eta →
        0 < derivative * slope h x y := by
  have hsign : derivative < 0 ∨ 0 < derivative := lt_or_gt_of_ne hne
  rcases hsign with hneg | hpos
  · have hevent : ∀ᶠ y in nhdsWithin x ({x}ᶜ), slope h x y < 0 :=
      hderiv.tendsto_slope (isOpen_Iio.mem_nhds hneg)
    have heventMul : ∀ᶠ y in nhdsWithin x ({x}ᶜ),
        0 < derivative * slope h x y :=
      hevent.mono (fun _ hy ↦ mul_pos_of_neg_of_neg hneg hy)
    rcases Metric.mem_nhdsWithin_iff.mp heventMul with
      ⟨eta, heta, hsubset⟩
    refine ⟨eta, heta, ?_⟩
    intro y hyne hyeta
    apply hsubset
    constructor
    · simpa [Real.dist_eq] using hyeta
    · simpa using hyne
  · have hevent : ∀ᶠ y in nhdsWithin x ({x}ᶜ), 0 < slope h x y :=
      hderiv.tendsto_slope (isOpen_Ioi.mem_nhds hpos)
    have heventMul : ∀ᶠ y in nhdsWithin x ({x}ᶜ),
        0 < derivative * slope h x y :=
      hevent.mono (fun _ hy ↦ mul_pos hpos hy)
    rcases Metric.mem_nhdsWithin_iff.mp heventMul with
      ⟨eta, heta, hsubset⟩
    refine ⟨eta, heta, ?_⟩
    intro y hyne hyeta
    apply hsubset
    constructor
    · simpa [Real.dist_eq] using hyeta
    · simpa using hyne

theorem exists_radius_derivative_oriented_value_sign
    {h : Real → Real} {x derivative : Real}
    (hzero : h x = 0)
    (hderiv : HasDerivAt h derivative x) (hne : derivative ≠ 0) :
    ∃ eta : Real, 0 < eta ∧ ∀ y : Real,
      y ≠ x → |y - x| < eta →
        (y < x → derivative * h y < 0) ∧
        (x < y → 0 < derivative * h y) := by
  rcases exists_radius_derivative_mul_slope_pos hderiv hne with
    ⟨eta, heta, hslope⟩
  refine ⟨eta, heta, ?_⟩
  intro y hyne hyeta
  have hslopePos := hslope y hyne hyeta
  have hid : (y - x) * slope h x y = h y := by
    simpa [hzero] using sub_smul_slope h x y
  have hproduct : 0 < (y - x) * (derivative * h y) := by
    calc
      0 < (y - x) ^ 2 * (derivative * slope h x y) :=
        mul_pos (sq_pos_of_ne_zero (sub_ne_zero.mpr hyne)) hslopePos
      _ = (y - x) * (derivative * h y) := by
        rw [← hid]
        ring
  constructor
  · intro hyx
    rcases (mul_pos_iff.mp hproduct) with hboth | hboth
    · linarith [hboth.1]
    · exact hboth.2
  · intro hxy
    rcases (mul_pos_iff.mp hproduct) with hboth | hboth
    · exact hboth.2
    · linarith [hboth.1]

theorem exists_radius_graph_difference_strict_sign_change
    {g h : Real → Real} {x gDerivative hDerivative : Real}
    (hroot : g x = h x)
    (hg : HasDerivAt g gDerivative x)
    (hh : HasDerivAt h hDerivative x)
    (hne : gDerivative ≠ hDerivative) :
    ∃ eta : Real, 0 < eta ∧ ∀ y : Real,
      y ≠ x → |y - x| < eta →
        (y < x → (gDerivative - hDerivative) * (g y - h y) < 0) ∧
        (x < y → 0 < (gDerivative - hDerivative) * (g y - h y)) := by
  apply exists_radius_derivative_oriented_value_sign
  · exact sub_eq_zero.mpr hroot
  · exact hg.sub hh
  · exact sub_ne_zero.mpr hne

#print axioms exists_radius_derivative_mul_slope_pos
#print axioms exists_radius_derivative_oriented_value_sign
#print axioms exists_radius_graph_difference_strict_sign_change

end FamilyStickyCinematicL32Prop41GraphTransverseSignV1
