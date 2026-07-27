import Mathlib
import Physlib.SpaceAndTime.Space.Basic

open Asymptotics Filter
open scoped Topology

namespace IPhO2026Problems
namespace IPhO2026_2_C_3

noncomputable section

/-- The two-dimensional cross-section of the half-cylindrical mirror.
`Space 2` is Physlib's physical Euclidean space with a fixed choice of length
unit; its real coordinates are therefore length readouts in that unit. -/
abbrev PlanarPoint := Space 2

/-- The `x` coordinate in the coordinate system of Figure 2g. -/
def xCoord (p : PlanarPoint) : ℝ := p 0

/-- The `y` coordinate in the coordinate system of Figure 2g. -/
def yCoord (p : PlanarPoint) : ℝ := p 1

/-- A point specified by its Figure 2g coordinate readouts. -/
def planarPoint (x y : ℝ) : PlanarPoint :=
  ⟨fun i => Fin.cases x (fun _ => y) i⟩

@[simp]
lemma xCoord_planarPoint (x y : ℝ) : xCoord (planarPoint x y) = x := by
  rfl

@[simp]
lemma yCoord_planarPoint (x y : ℝ) : yCoord (planarPoint x y) = y := by
  rfl

/-- A directed physical ray in the two-dimensional cross-section.  The vertex
is the reflection point and the direction selects the outgoing half-line. -/
structure OrientedRay2D where
  vertex : PlanarPoint
  directionX : ℝ
  directionY : ℝ
  direction_ne_zero : directionX ≠ 0 ∨ directionY ≠ 0

/-- Membership in the outgoing branch of an oriented ray.  Requiring a
nonnegative affine parameter preserves the orientation shown by the arrows in
Figure 2g. -/
def OrientedRay2D.Contains (ray : OrientedRay2D) (p : PlanarPoint) : Prop :=
  ∃ t : ℝ, 0 ≤ t ∧
    xCoord p = xCoord ray.vertex + t * ray.directionX ∧
    yCoord p = yCoord ray.vertex + t * ray.directionY

/-- The incidence angles represented on the right half of the upper
semicircular mirror in Figure 2g. -/
def IsAdmissibleAngle (α : ℝ) : Prop :=
  0 < α ∧ α < Real.pi / 2

/-- The upper semicircle of radius `R`, expressed in the coordinate readouts of
Figure 2g. -/
def OnUpperSemicircularMirror (R : ℝ) (p : PlanarPoint) : Prop :=
  xCoord p ^ 2 + yCoord p ^ 2 = R ^ 2 ∧ 0 ≤ yCoord p

/-- The point at which the vertical incoming ray indexed by `α` meets the
mirror. -/
def impactPoint (R α : ℝ) : PlanarPoint :=
  planarPoint (R * Real.sin α) (R * Real.cos α)

/-- The dimensionless slope of a reflected ray, as obtained in part C.1. -/
def reflectedSlope (α : ℝ) : ℝ :=
  Real.cot (2 * α)

/-- The length-valued intercept readout of a reflected ray, as obtained in
part C.1.  `R` and this intercept are measured in the same coordinate unit. -/
def reflectedIntercept (R α : ℝ) : ℝ :=
  R / (2 * Real.cos α)

/-- The affine support line of the reflected ray at incidence angle `α`. -/
def LiesOnReflectedSupport (R α : ℝ) (p : PlanarPoint) : Prop :=
  yCoord p = reflectedSlope α * xCoord p + reflectedIntercept R α

/-- Governing geometry and reflection data for Figure 2g.

All incoming rays share the displayed vertical direction, so rays indexed by
`θ` and `θ + Δθ` are parallel before reflection.  The last field is the
reusable C.1 reflection law; it constrains every point of the outgoing branch
by an explicit affine equation and does not prescribe the caustic. -/
structure Figure2gOptics (R : ℝ) where
  radiusPositive : 0 < R
  incomingDirectionX : ℝ
  incomingDirectionY : ℝ
  incomingVertical : incomingDirectionX = 0
  incomingForward : 0 < incomingDirectionY
  incomingImpact : ℝ → PlanarPoint
  incomingImpact_eq :
    ∀ α, IsAdmissibleAngle α → incomingImpact α = impactPoint R α
  reflectedRay : ℝ → OrientedRay2D
  reflectedStartsAtImpact :
    ∀ α, IsAdmissibleAngle α →
      (reflectedRay α).vertex = incomingImpact α
  reflectedLineLaw :
    ∀ α, IsAdmissibleAngle α → ∀ p,
      (reflectedRay α).Contains p → LiesOnReflectedSupport R α p

/-- The incidence point given by the Figure 2g coordinate readout lies on the
upper semicircular mirror. -/
theorem impactPoint_on_upperSemicircularMirror
    (R α : ℝ) (hR : 0 < R) (hα : IsAdmissibleAngle α) :
    OnUpperSemicircularMirror R (impactPoint R α) := by
  rcases hα with ⟨hα0, hαpi⟩
  have hcos : 0 < Real.cos α :=
    Real.cos_pos_of_mem_Ioo ⟨by nlinarith [Real.pi_pos], hαpi⟩
  constructor
  · simp only [impactPoint, xCoord_planarPoint, yCoord_planarPoint]
    nlinarith [Real.sin_sq_add_cos_sq α]
  · simp only [impactPoint, yCoord_planarPoint]
    positivity

/-- The explicit, constraining meaning of being the intersection of reflected
ray `A` at `θ` and neighboring reflected ray `B` at `θ + δ`. -/
def IsNeighboringReflectedIntersection {R : ℝ}
    (model : Figure2gOptics R) (θ δ : ℝ) (p : PlanarPoint) : Prop :=
  0 < δ ∧
  IsAdmissibleAngle θ ∧
  IsAdmissibleAngle (θ + δ) ∧
  (model.reflectedRay θ).Contains p ∧
  (model.reflectedRay (θ + δ)).Contains p

/-- Remainder in the C.2 first-order expansion of the neighboring reflected
ray's slope.  The coefficient `2 / sin(2θ)^2` is `2 csc(2θ)^2`. -/
def slopeFirstOrderRemainder (θ δ : ℝ) : ℝ :=
  reflectedSlope (θ + δ) -
    (reflectedSlope θ - 2 / Real.sin (2 * θ) ^ 2 * δ)

/-- Remainder in the C.2 first-order expansion of the neighboring reflected
ray's intercept. -/
def interceptFirstOrderRemainder (R θ δ : ℝ) : ℝ :=
  reflectedIntercept R (θ + δ) -
    (reflectedIntercept R θ * (1 + Real.tan θ * δ))

/-- The precise `O(Δθ²)` interpretation of both first-order expansions quoted
from part C.2. -/
def HasFigure2gFirstOrderExpansions (R θ : ℝ) : Prop :=
  IsBigO (𝓝 (0 : ℝ)) (slopeFirstOrderRemainder θ) (fun δ : ℝ => δ ^ 2) ∧
  IsBigO (𝓝 (0 : ℝ)) (interceptFirstOrderRemainder R θ) (fun δ : ℝ => δ ^ 2)

/-- The reusable result of part C.2, formulated with an actual asymptotic error
rather than an informal truncation symbol. -/
theorem previousPartC2_firstOrderExpansions
    (R θ : ℝ) (hθ : IsAdmissibleAngle θ) :
    HasFigure2gFirstOrderExpansions R θ := by
  rcases hθ with ⟨hθ0, hθpi⟩
  have hsin2θ : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by nlinarith) (by nlinarith)
  have hcosθ : 0 < Real.cos θ :=
    Real.cos_pos_of_mem_Ioo ⟨by nlinarith [Real.pi_pos], hθpi⟩
  have analytic_remainder_bigO {f : ℝ → ℝ} {x f' : ℝ}
      (ha : AnalyticAt ℝ f x) (hd : HasDerivAt f f' x) :
      (fun δ : ℝ => f (x + δ) - (f x + f' * δ)) =O[𝓝 0]
        (fun δ : ℝ => δ ^ 2) := by
    rcases ha with ⟨p, hp⟩
    have hmap : continuousMultilinearCurryFin1 ℝ ℝ ℝ (p 1) =
        (1 : ℝ →L[ℝ] ℝ).smulRight f' := by
      rw [← hp.fderiv_eq]
      exact hd.hasFDerivAt.fderiv
    have hp1 (δ : ℝ) : p 1 (fun _ => δ) = f' * δ := by
      have heq := congrArg (fun L : ℝ →L[ℝ] ℝ => L δ) hmap
      rw [continuousMultilinearCurryFin1_apply] at heq
      simpa [mul_comm] using heq
    have hp0 (δ : ℝ) : p 0 (fun _ => δ) = f x := hp.coeff_zero _
    apply (hp.isBigO_sub_partialSum_pow 2).congr
    · intro δ
      congr 1
      rw [FormalMultilinearSeries.partialSum, Finset.sum_range_succ,
        Finset.sum_range_one]
      simp only [hp0, hp1]
    · intro δ
      simp [Real.norm_eq_abs]
  have hSlope :
      HasDerivAt reflectedSlope (-2 / Real.sin (2 * θ) ^ 2) θ := by
    have hinner : HasDerivAt (fun x : ℝ => 2 * x) 2 θ := by
      simpa using (hasDerivAt_id θ).const_mul 2
    have hdiv := (Real.hasDerivAt_cos (2 * θ)).div
      (Real.hasDerivAt_sin (2 * θ)) hsin2θ.ne'
    have hcot :
        HasDerivAt Real.cot (-1 / Real.sin (2 * θ) ^ 2) (2 * θ) := by
      apply (hdiv.congr_deriv ?_).congr_of_eventuallyEq
      · filter_upwards with x
        exact Real.cot_eq_cos_div_sin x
      · rw [show -Real.sin (2 * θ) * Real.sin (2 * θ) -
            Real.cos (2 * θ) * Real.cos (2 * θ) = -1 by
              nlinarith [Real.sin_sq_add_cos_sq (2 * θ)]]
    have hc : HasDerivAt (Real.cot ∘ fun x : ℝ => 2 * x)
        (-2 / Real.sin (2 * θ) ^ 2) θ :=
      (hcot.comp θ hinner).congr_deriv (by ring)
    apply hc.congr_of_eventuallyEq
    filter_upwards with x
    rfl
  have hIntercept :
      HasDerivAt (reflectedIntercept R)
        (reflectedIntercept R θ * Real.tan θ) θ := by
    have hden :
        HasDerivAt (fun x : ℝ => 2 * Real.cos x) (-2 * Real.sin θ) θ := by
      simpa using (Real.hasDerivAt_cos θ).const_mul 2
    have hd := (hasDerivAt_const θ R).div hden
      (mul_ne_zero (by norm_num) hcosθ.ne')
    have hd' :
        HasDerivAt ((fun _ : ℝ => R) / fun x => 2 * Real.cos x)
          (reflectedIntercept R θ * Real.tan θ) θ :=
      hd.congr_deriv (by
        rw [Real.tan_eq_sin_div_cos, reflectedIntercept]
        field_simp
        ring)
    apply hd'.congr_of_eventuallyEq
    filter_upwards with x
    rfl
  have haSlope :
      AnalyticAt ℝ (fun δ : ℝ => reflectedSlope (θ + δ)) 0 := by
    have ha : AnalyticAt ℝ
        (fun δ : ℝ =>
          Real.cos (2 * (θ + δ)) / Real.sin (2 * (θ + δ))) 0 := by
      apply AnalyticAt.div
      · fun_prop
      · fun_prop
      · simpa using hsin2θ.ne'
    simpa only [reflectedSlope, Real.cot_eq_cos_div_sin] using ha
  have haIntercept :
      AnalyticAt ℝ (fun δ : ℝ => reflectedIntercept R (θ + δ)) 0 := by
    change AnalyticAt ℝ (fun δ : ℝ => R / (2 * Real.cos (θ + δ))) 0
    apply AnalyticAt.div
    · fun_prop
    · fun_prop
    · simpa using mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) hcosθ.ne'
  have hInner : HasDerivAt (fun δ : ℝ => θ + δ) 1 0 := by
    have hi : HasDerivAt ((fun _ : ℝ => θ) + id) 1 0 := by
      simpa using
        (hasDerivAt_const (x := (0 : ℝ)) θ).add (hasDerivAt_id 0)
    apply hi.congr_of_eventuallyEq
    filter_upwards with δ
    rfl
  have hSlopeAtZero :
      HasDerivAt (fun δ : ℝ => reflectedSlope (θ + δ))
        (-2 / Real.sin (2 * θ) ^ 2) 0 := by
    have hs :
        HasDerivAt reflectedSlope (-2 / Real.sin (2 * θ) ^ 2) (θ + 0) := by
      simpa using hSlope
    have hc := hs.comp 0 hInner
    have hc' := hc.congr_deriv (by ring :
      -2 / Real.sin (2 * θ) ^ 2 * 1 =
        -2 / Real.sin (2 * θ) ^ 2)
    apply hc'.congr_of_eventuallyEq
    filter_upwards with δ
    rfl
  have hInterceptAtZero :
      HasDerivAt (fun δ : ℝ => reflectedIntercept R (θ + δ))
        (reflectedIntercept R θ * Real.tan θ) 0 := by
    have hi :
        HasDerivAt (reflectedIntercept R)
          (reflectedIntercept R θ * Real.tan θ) (θ + 0) := by
      simpa using hIntercept
    have hc := hi.comp 0 hInner
    have hc' := hc.congr_deriv (by ring :
      reflectedIntercept R θ * Real.tan θ * 1 =
        reflectedIntercept R θ * Real.tan θ)
    apply hc'.congr_of_eventuallyEq
    filter_upwards with δ
    rfl
  constructor
  · apply (analytic_remainder_bigO haSlope hSlopeAtZero).congr_left
    intro δ
    simp only [slopeFirstOrderRemainder, zero_add, add_zero]
    ring
  · apply (analytic_remainder_bigO haIntercept hInterceptAtZero).congr_left
    intro δ
    simp only [interceptFirstOrderRemainder, zero_add, add_zero]
    ring

/-- The intersection of two distinct affine support lines, written in Figure
2g coordinates.  This is an algebraic bridge, not the limiting caustic
formula. -/
def supportIntersectionCandidate (R α β : ℝ) : PlanarPoint :=
  let x :=
    (reflectedIntercept R β - reflectedIntercept R α) /
      (reflectedSlope α - reflectedSlope β)
  planarPoint x (reflectedSlope α * x + reflectedIntercept R α)

/-- On the admissible branch, increasing the incidence angle changes the
reflected slope, so neighboring support lines are distinct. -/
theorem reflectedSlope_ne_of_angle_lt
    {α β : ℝ}
    (hα : IsAdmissibleAngle α)
    (hβ : IsAdmissibleAngle β)
    (hαβ : α < β) :
    reflectedSlope α ≠ reflectedSlope β := by
  rcases hα with ⟨hα0, hαpi⟩
  rcases hβ with ⟨hβ0, hβpi⟩
  have hsinα : 0 < Real.sin (2 * α) :=
    Real.sin_pos_of_pos_of_lt_pi (by nlinarith) (by nlinarith)
  have hsinβ : 0 < Real.sin (2 * β) :=
    Real.sin_pos_of_pos_of_lt_pi (by nlinarith) (by nlinarith)
  have hsinβα : 0 < Real.sin (2 * β - 2 * α) :=
    Real.sin_pos_of_pos_of_lt_pi (by nlinarith) (by nlinarith)
  intro h
  simp only [reflectedSlope, Real.cot_eq_cos_div_sin] at h
  have hcross :
      Real.cos (2 * α) * Real.sin (2 * β) =
        Real.cos (2 * β) * Real.sin (2 * α) := by
    apply (div_eq_div_iff hsinα.ne' hsinβ.ne').mp
    exact h
  rw [Real.sin_sub] at hsinβα
  nlinarith

/-- Ray membership and the C.1 support-line law determine the finite
neighboring-ray intersection uniquely. -/
theorem neighboringIntersection_eq_supportIntersectionCandidate
    {R θ δ : ℝ}
    (model : Figure2gOptics R)
    (p : PlanarPoint)
    (hIntersection : IsNeighboringReflectedIntersection model θ δ p) :
    p = supportIntersectionCandidate R θ (θ + δ) := by
  rcases hIntersection with ⟨hδ, hθ, hθδ, hpθ, hpθδ⟩
  have hlineθ := model.reflectedLineLaw θ hθ p hpθ
  have hlineθδ := model.reflectedLineLaw (θ + δ) hθδ p hpθδ
  have hslope :
      reflectedSlope θ ≠ reflectedSlope (θ + δ) :=
    reflectedSlope_ne_of_angle_lt hθ hθδ (by linarith)
  have hx :
      xCoord p =
        (reflectedIntercept R (θ + δ) - reflectedIntercept R θ) /
          (reflectedSlope θ - reflectedSlope (θ + δ)) := by
    rw [LiesOnReflectedSupport] at hlineθ hlineθδ
    field_simp
    nlinarith
  have hy :
      yCoord p =
        reflectedSlope θ *
          ((reflectedIntercept R (θ + δ) - reflectedIntercept R θ) /
            (reflectedSlope θ - reflectedSlope (θ + δ))) +
          reflectedIntercept R θ := by
    rw [LiesOnReflectedSupport] at hlineθ
    rw [hlineθ, hx]
  apply Space.eq_of_apply
  intro i
  fin_cases i
  · change xCoord p = xCoord (supportIntersectionCandidate R θ (θ + δ))
    simpa [supportIntersectionCandidate] using hx
  · change yCoord p = yCoord (supportIntersectionCandidate R θ (θ + δ))
    simpa [supportIntersectionCandidate] using hy

/-- Pure analytic bridge: the intersections of the C.1 support lines tend to
the displayed caustic point as the positive angular separation tends to zero.
The proof obligation includes the trigonometric simplification of both
coordinates. -/
theorem supportIntersectionCandidate_tendsto
    (R θ : ℝ)
    (hθ : IsAdmissibleAngle θ) :
    Tendsto
      (fun δ : ℝ => supportIntersectionCandidate R θ (θ + δ))
      (𝓝[>] (0 : ℝ))
      (𝓝 (planarPoint
        (R * Real.sin θ ^ 3)
        ((R / 2) * Real.cos θ * (2 - Real.cos (2 * θ))))) := by
  rcases hθ with ⟨hθ0, hθpi⟩
  have hsinθ : 0 < Real.sin θ :=
    Real.sin_pos_of_pos_of_lt_pi hθ0 (by nlinarith [Real.pi_pos])
  have hcosθ : 0 < Real.cos θ :=
    Real.cos_pos_of_mem_Ioo ⟨by nlinarith [Real.pi_pos], hθpi⟩
  have hsin2θ : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by nlinarith) (by nlinarith)
  have hSlope :
      HasDerivAt reflectedSlope (-2 / Real.sin (2 * θ) ^ 2) θ := by
    have hinner : HasDerivAt (fun x : ℝ => 2 * x) 2 θ := by
      simpa using (hasDerivAt_id θ).const_mul 2
    have hdiv := (Real.hasDerivAt_cos (2 * θ)).div
      (Real.hasDerivAt_sin (2 * θ)) hsin2θ.ne'
    have hcot :
        HasDerivAt Real.cot (-1 / Real.sin (2 * θ) ^ 2) (2 * θ) := by
      apply (hdiv.congr_deriv ?_).congr_of_eventuallyEq
      · filter_upwards with x
        exact Real.cot_eq_cos_div_sin x
      · rw [show -Real.sin (2 * θ) * Real.sin (2 * θ) -
            Real.cos (2 * θ) * Real.cos (2 * θ) = -1 by
              nlinarith [Real.sin_sq_add_cos_sq (2 * θ)]]
    have hc : HasDerivAt (Real.cot ∘ fun x : ℝ => 2 * x)
        (-2 / Real.sin (2 * θ) ^ 2) θ :=
      (hcot.comp θ hinner).congr_deriv (by ring)
    apply hc.congr_of_eventuallyEq
    filter_upwards with x
    rfl
  have hIntercept :
      HasDerivAt (reflectedIntercept R)
        (R * Real.sin θ / (2 * Real.cos θ ^ 2)) θ := by
    have hden :
        HasDerivAt (fun x : ℝ => 2 * Real.cos x) (-2 * Real.sin θ) θ := by
      simpa using (Real.hasDerivAt_cos θ).const_mul 2
    have hd := (hasDerivAt_const θ R).div hden
      (mul_ne_zero (by norm_num) hcosθ.ne')
    have hd' := hd.congr_deriv (by ring :
      (0 * (2 * Real.cos θ) - R * (-2 * Real.sin θ)) /
          (2 * Real.cos θ) ^ 2 =
        R * Real.sin θ / (2 * Real.cos θ ^ 2))
    apply hd'.congr_of_eventuallyEq
    filter_upwards with x
    rfl
  have hNum :
      Tendsto
        (fun δ : ℝ =>
          (reflectedIntercept R (θ + δ) - reflectedIntercept R θ) / δ)
        (𝓝[>] (0 : ℝ))
        (𝓝 (R * Real.sin θ / (2 * Real.cos θ ^ 2))) := by
    simpa [div_eq_mul_inv, mul_comm] using
      hIntercept.tendsto_slope_zero_right
  have hDenAux :
      Tendsto
        (fun δ : ℝ =>
          -(δ⁻¹ * (reflectedSlope (θ + δ) - reflectedSlope θ)))
        (𝓝[>] (0 : ℝ))
        (𝓝 (2 / Real.sin (2 * θ) ^ 2)) := by
    simpa [neg_div] using hSlope.tendsto_slope_zero_right.neg
  have hDen :
      Tendsto
        (fun δ : ℝ =>
          (reflectedSlope θ - reflectedSlope (θ + δ)) / δ)
        (𝓝[>] (0 : ℝ))
        (𝓝 (2 / Real.sin (2 * θ) ^ 2)) := by
    apply hDenAux.congr'
    filter_upwards with δ
    rw [div_eq_mul_inv]
    ring
  have hDenNe : 2 / Real.sin (2 * θ) ^ 2 ≠ 0 :=
    div_ne_zero (by norm_num) (pow_ne_zero 2 hsin2θ.ne')
  have hRatio := hNum.div hDen hDenNe
  have hXLimit :
      (R * Real.sin θ / (2 * Real.cos θ ^ 2)) /
          (2 / Real.sin (2 * θ) ^ 2) =
        R * Real.sin θ ^ 3 := by
    rw [Real.sin_two_mul]
    field_simp
  rw [hXLimit] at hRatio
  have hX :
      Tendsto
        (fun δ : ℝ =>
          (reflectedIntercept R (θ + δ) - reflectedIntercept R θ) /
            (reflectedSlope θ - reflectedSlope (θ + δ)))
        (𝓝[>] (0 : ℝ))
        (𝓝 (R * Real.sin θ ^ 3)) := by
    apply hRatio.congr'
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    exact div_div_div_cancel_right₀ (ne_of_gt hδ) _ _
  have hYPre :
      Tendsto
        (fun δ : ℝ =>
          reflectedSlope θ *
              ((reflectedIntercept R (θ + δ) - reflectedIntercept R θ) /
                (reflectedSlope θ - reflectedSlope (θ + δ))) +
            reflectedIntercept R θ)
        (𝓝[>] (0 : ℝ))
        (𝓝 (reflectedSlope θ * (R * Real.sin θ ^ 3) +
          reflectedIntercept R θ)) :=
    (tendsto_const_nhds.mul hX).add tendsto_const_nhds
  have hYLimit :
      reflectedSlope θ * (R * Real.sin θ ^ 3) + reflectedIntercept R θ =
        (R / 2) * Real.cos θ * (2 - Real.cos (2 * θ)) := by
    rw [reflectedSlope, reflectedIntercept, Real.cot_eq_cos_div_sin,
      Real.sin_two_mul]
    field_simp
    rw [Real.cos_two_mul]
    rw [show Real.sin θ ^ 2 = 1 - Real.cos θ ^ 2 by
      nlinarith [Real.sin_sq_add_cos_sq θ]]
    ring
  rw [hYLimit] at hYPre
  have tendsto_planarPoint
      {ι : Type} {l : Filter ι} {fx fy : ι → ℝ} {x y : ℝ}
      (hx : Tendsto fx l (𝓝 x)) (hy : Tendsto fy l (𝓝 y)) :
      Tendsto (fun z => planarPoint (fx z) (fy z)) l
        (𝓝 (planarPoint x y)) := by
    rw [tendsto_iff_dist_tendsto_zero]
    have hsum :
        Tendsto (fun z => (fx z - x) ^ 2 + (fy z - y) ^ 2) l (𝓝 0) := by
      convert ((hx.sub tendsto_const_nhds).pow 2).add
        ((hy.sub tendsto_const_nhds).pow 2) using 1
      all_goals norm_num
    have hsqrt := Real.continuous_sqrt.continuousAt.tendsto.comp hsum
    convert hsqrt using 1
    · funext z
      rw [Space.dist_eq]
      congr 1
      rw [Fin.sum_univ_two]
      congr 1
    · norm_num
  simpa only [supportIntersectionCandidate] using
    tendsto_planarPoint hX hYPre

/-- IPhO 2026 problem 2, part C.3: the limiting intersection coordinates of
neighboring reflected rays are
`X_c = R sin(θ)^3` and
`Y_c = (R/2) cos(θ) (2 - cos(2θ))`.

The intersection function is constrained only by actual membership in both
outgoing reflected rays for all sufficiently small positive separations. -/
theorem limitingIntersectionCoordinates
    {R θ δMax : ℝ}
    (model : Figure2gOptics R)
    (intersection : ℝ → PlanarPoint)
    (hθ : IsAdmissibleAngle θ)
    (hδMax : 0 < δMax)
    (hAngleWindow : θ + δMax < Real.pi / 2)
    (hIntersection :
      ∀ δ, 0 < δ → δ < δMax →
        IsNeighboringReflectedIntersection model θ δ (intersection δ)) :
    Tendsto intersection
      (𝓝[>] (0 : ℝ))
      (𝓝 (planarPoint
        (R * Real.sin θ ^ 3)
        ((R / 2) * Real.cos θ * (2 - Real.cos (2 * θ))))) := by
  apply (supportIntersectionCandidate_tendsto R θ hθ).congr'
  have hlt :
      ∀ᶠ δ : ℝ in 𝓝[>] (0 : ℝ), δ < δMax :=
    (eventually_lt_nhds hδMax).filter_mono nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin, hlt] with δ hδ hδmax
  exact (neighboringIntersection_eq_supportIntersectionCandidate model
    (intersection δ) (hIntersection δ hδ hδmax)).symm

end
end IPhO2026_2_C_3
end IPhO2026Problems
