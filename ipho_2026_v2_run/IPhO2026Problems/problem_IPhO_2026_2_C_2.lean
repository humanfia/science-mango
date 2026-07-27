import Mathlib
import Physlib.Units.WithDim.Basic

open Filter
open scoped Topology

namespace IPhO2026Problems.IPhO2026_2_C_2

/-! ## Dimensionful length data -/

/-- A unit-independent physical length, represented by Physlib's
dimensionful-quantity interface. -/
def LengthQuantity :=
  Dimensionful (WithDim Dimension.L𝓭 ℝ)

/-- The scalar readout of a physical length in Physlib's SI unit choice
(metres).  Analytic coordinate equations are stated through this projection. -/
noncomputable def lengthSI (length : LengthQuantity) : ℝ :=
  (length.1 UnitChoices.SI).val

/-- A point in the two-dimensional cross-section used in Figure 2g.
Both coordinates are physical lengths and share the named SI projection. -/
structure Point2D where
  x : LengthQuantity
  y : LengthQuantity

/-- A directed vector in the Figure 2g coordinate frame.  Its components are
used only to retain the incoming/outgoing orientation of an optical ray. -/
structure Direction2D where
  dx : ℝ
  dy : ℝ

/-- The upward vertical direction of the parallel incident rays in Figure 2g. -/
def verticalIncomingDirection : Direction2D where
  dx := 0
  dy := 1

/-- A scalar-coordinate description of a reflected straight line.
The slope is dimensionless, while `yIntercept` is a physical length. -/
structure AffineLineReadout where
  slope : ℝ
  yIntercept : LengthQuantity

/-- Incidence-point labels from Figure 2g. -/
inductive Figure2gRayLabel
  | A
  | B

/-- The data retained for an incident ray and its reflected branch.  Angles
are real numbers measured in radians in the convention of Figure 2g. -/
structure OpticalRay2D where
  label : Figure2gRayLabel
  incidenceAngle : ℝ
  incidencePoint : Point2D
  incomingDirection : Direction2D
  outgoingDirection : Direction2D
  reflectedLine : AffineLineReadout

/-- The half-cylindrical mirror, represented by its circular cross-section
radius.  `radius` is a positive physical length. -/
structure HalfCylindricalMirror where
  radius : LengthQuantity
  radius_pos : 0 < lengthSI radius

/-- A point lies on the upper semicircular cross-section of the mirror. -/
def OnUpperSemicircle (mirror : HalfCylindricalMirror) (point : Point2D) : Prop :=
  lengthSI point.x ^ 2 + lengthSI point.y ^ 2 =
      lengthSI mirror.radius ^ 2 ∧
    0 ≤ lengthSI point.y

/-- A point lies on a reflected line in the signed coordinate convention of
Figure 2g. -/
def AffineLineReadout.Contains (line : AffineLineReadout) (point : Point2D) : Prop :=
  lengthSI point.y =
    line.slope * lengthSI point.x + lengthSI line.yIntercept

/-- The geometry and orientation read directly from Figure 2g for a ray whose
incidence angle is `φ`.  In particular, the incoming ray is vertical and the
reflected ray is taken on the left-going branch. -/
def HasFigure2gGeometry
    (mirror : HalfCylindricalMirror) (label : Figure2gRayLabel)
    (φ : ℝ) (ray : OpticalRay2D) : Prop :=
  ray.label = label ∧
    ray.incidenceAngle = φ ∧
    lengthSI ray.incidencePoint.x =
      lengthSI mirror.radius * Real.sin φ ∧
    lengthSI ray.incidencePoint.y =
      lengthSI mirror.radius * Real.cos φ ∧
    OnUpperSemicircle mirror ray.incidencePoint ∧
    ray.incomingDirection = verticalIncomingDirection ∧
    ray.reflectedLine.Contains ray.incidencePoint ∧
    ray.outgoingDirection.dx < 0 ∧
    ray.outgoingDirection.dy =
      ray.reflectedLine.slope * ray.outgoingDirection.dx

/-- The two incident rays are parallel with the same directed incoming
orientation, as specified in C.2. -/
def HaveParallelIncomingDirections (rayA rayB : OpticalRay2D) : Prop :=
  rayA.incomingDirection = rayB.incomingDirection

/-- The reusable result of C.1 for the ray labelled `A`.  This is previous-part
input, rather than either of the first-order conclusions requested in C.2. -/
def SatisfiesPreviousPartC1
    (mirror : HalfCylindricalMirror) (θ : ℝ) (rayA : OpticalRay2D) : Prop :=
  rayA.reflectedLine.slope = Real.cot (2 * θ) ∧
    lengthSI rayA.reflectedLine.yIntercept =
      lengthSI mirror.radius / (2 * Real.cos θ)

/-- The exact coefficient consequence of specular reflection from the circular
mirror at an arbitrary incidence angle.  C.2 applies this governing law at
`θ + Δθ` and then takes its first-order expansion. -/
def SatisfiesHalfCylindricalSpecularLaw
    (mirror : HalfCylindricalMirror) (ray : OpticalRay2D) : Prop :=
  ray.reflectedLine.slope =
      Real.cot (2 * ray.incidenceAngle) ∧
    lengthSI ray.reflectedLine.yIntercept =
      lengthSI mirror.radius / (2 * Real.cos ray.incidenceAngle)

/-- The exact slope equation exposed by the circular-mirror reflection law. -/
theorem slope_eq_of_specular_law
    {mirror : HalfCylindricalMirror} {ray : OpticalRay2D}
    (h : SatisfiesHalfCylindricalSpecularLaw mirror ray) :
    ray.reflectedLine.slope = Real.cot (2 * ray.incidenceAngle) :=
  h.1

/-- The exact intercept equation exposed by the circular-mirror reflection law. -/
theorem intercept_eq_of_specular_law
    {mirror : HalfCylindricalMirror} {ray : OpticalRay2D}
    (h : SatisfiesHalfCylindricalSpecularLaw mirror ray) :
    lengthSI ray.reflectedLine.yIntercept =
      lengthSI mirror.radius / (2 * Real.cos ray.incidenceAngle) :=
  h.2

/-- IPhO 2026 Problem 2 C.2: the reflected line of the neighboring ray `B`
has the stated first-order slope and intercept expansions as `Δθ → 0`.

The two `IsBigO` conclusions say that the displayed remainders are bounded by
a constant multiple of `Δθ²` near zero.  Thus the approximation order in the
source is part of the theorem contract rather than being silently discarded. -/
theorem rayB_firstOrderExpansion
    (mirror : HalfCylindricalMirror) (θ : ℝ)
    (rayA : OpticalRay2D) (rayB : ℝ → OpticalRay2D)
    (hθ_pos : 0 < θ) (hθ_lt : θ < Real.pi / 2)
    (hsin : Real.sin (2 * θ) ≠ 0) (hcos : Real.cos θ ≠ 0)
    (hA_geometry : HasFigure2gGeometry mirror Figure2gRayLabel.A θ rayA)
    (hB_geometry :
      ∀ᶠ Δθ in 𝓝 (0 : ℝ),
        HasFigure2gGeometry mirror Figure2gRayLabel.B (θ + Δθ) (rayB Δθ))
    (h_parallel :
      ∀ᶠ Δθ in 𝓝 (0 : ℝ), HaveParallelIncomingDirections rayA (rayB Δθ))
    (hC1 : SatisfiesPreviousPartC1 mirror θ rayA)
    (h_reflection :
      ∀ᶠ Δθ in 𝓝 (0 : ℝ),
        SatisfiesHalfCylindricalSpecularLaw mirror (rayB Δθ)) :
    ((fun Δθ : ℝ =>
        (rayB Δθ).reflectedLine.slope -
          (Real.cot (2 * θ) -
            2 * (Real.sin (2 * θ))⁻¹ ^ 2 * Δθ))
        =O[𝓝 (0 : ℝ)] (fun Δθ : ℝ => Δθ ^ 2)) ∧
      ((fun Δθ : ℝ =>
        lengthSI (rayB Δθ).reflectedLine.yIntercept -
          (lengthSI mirror.radius / (2 * Real.cos θ) *
            (1 + Real.tan θ * Δθ)))
        =O[𝓝 (0 : ℝ)] (fun Δθ : ℝ => Δθ ^ 2)) := by
  have second_order_of_eventually_hasDeriv
      (g g' : ℝ → ℝ) (g'' : ℝ)
      (hg : ∀ᶠ x in 𝓝 (0 : ℝ), HasDerivAt g (g' x) x)
      (hg' : HasDerivAt g' g'' 0) :
      (fun x : ℝ => g x - (g 0 + g' 0 * x)) =O[𝓝 (0 : ℝ)]
        (fun x : ℝ => x ^ 2) := by
    rw [Metric.eventually_nhds_iff] at hg
    obtain ⟨ε, hε, hg⟩ := hg
    let r : ℝ → ℝ := fun x =>
      g x - g 0 - g' 0 * x - (g'' / 2) * x ^ 2
    let r' : ℝ → ℝ := fun x => g' x - g' 0 - g'' * x
    have hr_deriv : ∀ x ∈ Metric.ball (0 : ℝ) ε,
        HasDerivWithinAt r (r' x) (Metric.ball (0 : ℝ) ε) x := by
      intro x hx
      have hxg : HasDerivAt g (g' x) x := hg hx
      have hxid : HasDerivAt (fun y : ℝ => y) 1 x := hasDerivAt_id x
      have htmp :=
        (((hxg.sub_const (g 0)).sub (hxid.const_mul (g' 0))).sub
          ((hxid.pow 2).const_mul (g'' / 2)))
      have hsame : HasDerivAt r
          (g' x - g' 0 * 1 -
            (g'' / 2) * ((2 : ℝ) * x ^ (2 - 1) * 1)) x := by
        apply htmp.congr_of_eventuallyEq
        filter_upwards [] with y
        simp [r]
      apply (hsame.congr_deriv ?_).hasDerivWithinAt
      dsimp [r']
      ring
    have hr'_little : r' =o[𝓝 (0 : ℝ)] (fun x : ℝ => x) := by
      simpa [r', smul_eq_mul, mul_comm] using hg'.isLittleO
    have hr_little_within :
        (fun x => r x - r 0) =o[𝓝[Metric.ball (0 : ℝ) ε] (0 : ℝ)]
          (fun x : ℝ => (x - 0) ^ (1 + 1)) :=
      (convex_ball (0 : ℝ) ε).isLittleO_pow_succ_real
        (Metric.mem_ball_self hε) hr_deriv
        (by simpa using hr'_little.mono nhdsWithin_le_nhds)
    have hr_little : r =o[𝓝 (0 : ℝ)] (fun x : ℝ => x ^ 2) := by
      rw [Metric.isOpen_ball.nhdsWithin_eq (Metric.mem_ball_self hε)] at hr_little_within
      simpa [r] using hr_little_within
    have hquad : (fun x : ℝ => (g'' / 2) * x ^ 2) =O[𝓝 (0 : ℝ)]
        (fun x : ℝ => x ^ 2) :=
      (Asymptotics.isBigO_refl (fun x : ℝ => x ^ 2) (𝓝 (0 : ℝ))).const_mul_left
        (g'' / 2)
    have hsum := hr_little.isBigO.add hquad
    exact hsum.congr (fun x => by dsimp [r]; ring) (fun _ => rfl)

  have hsin_eventually :
      ∀ᶠ x in 𝓝 (0 : ℝ), Real.sin (2 * (θ + x)) ≠ 0 := by
    have hcont :
        ContinuousAt (fun x : ℝ => Real.sin (2 * (θ + x))) 0 := by
      fun_prop
    exact hcont.eventually_ne (by simpa using hsin)
  have hcos_eventually :
      ∀ᶠ x in 𝓝 (0 : ℝ), Real.cos (θ + x) ≠ 0 := by
    have hcont : ContinuousAt (fun x : ℝ => Real.cos (θ + x)) 0 := by
      fun_prop
    exact hcont.eventually_ne (by simpa using hcos)

  have hslope_deriv :
      ∀ᶠ x in 𝓝 (0 : ℝ),
        HasDerivAt (fun y : ℝ => Real.cot (2 * (θ + y)))
          (-2 * (Real.sin (2 * (θ + x)))⁻¹ ^ 2) x := by
    filter_upwards [hsin_eventually] with x hx
    have hu0 :=
      ((hasDerivAt_const x θ).add (hasDerivAt_id x)).const_mul 2
    have hu1 : HasDerivAt (fun y : ℝ => 2 * (θ + y))
        (2 * (0 + 1)) x := by
      apply hu0.congr_of_eventuallyEq
      filter_upwards [] with y
      simp
    have hu : HasDerivAt (fun y : ℝ => 2 * (θ + y)) 2 x :=
      hu1.congr_deriv (by ring)
    have hs := hu.sin
    have hc := hu.cos
    rw [show (fun y : ℝ => Real.cot (2 * (θ + y))) =
        (fun y : ℝ =>
          Real.cos (2 * (θ + y)) / Real.sin (2 * (θ + y))) by
      funext y
      exact Real.cot_eq_cos_div_sin _]
    have hq := hc.div hs hx
    apply hq.congr_deriv
    field_simp
    nlinarith [Real.sin_sq_add_cos_sq (2 * (θ + x))]
  have hslope_deriv_differentiable :
      DifferentiableAt ℝ
        (fun x : ℝ => -2 * (Real.sin (2 * (θ + x)))⁻¹ ^ 2) 0 := by
    fun_prop (disch := aesop)
  have hslope_taylor_raw :=
    second_order_of_eventually_hasDeriv
      (fun x : ℝ => Real.cot (2 * (θ + x)))
      (fun x : ℝ => -2 * (Real.sin (2 * (θ + x)))⁻¹ ^ 2)
      (deriv (fun x : ℝ => -2 * (Real.sin (2 * (θ + x)))⁻¹ ^ 2) 0)
      hslope_deriv hslope_deriv_differentiable.hasDerivAt
  have hslope_taylor :
      (fun x : ℝ =>
        Real.cot (2 * (θ + x)) -
          (Real.cot (2 * θ) -
            2 * (Real.sin (2 * θ))⁻¹ ^ 2 * x))
        =O[𝓝 (0 : ℝ)] (fun x : ℝ => x ^ 2) :=
    hslope_taylor_raw.congr
      (fun x => by simp; ring)
      (fun _ => rfl)

  have hintercept_deriv :
      ∀ᶠ x in 𝓝 (0 : ℝ),
        HasDerivAt
          (fun y : ℝ =>
            lengthSI mirror.radius / (2 * Real.cos (θ + y)))
          (lengthSI mirror.radius / (2 * Real.cos (θ + x)) *
            Real.tan (θ + x)) x := by
    filter_upwards [hcos_eventually] with x hx
    have hu0 := (hasDerivAt_const x θ).add (hasDerivAt_id x)
    have hu1 : HasDerivAt (fun y : ℝ => θ + y) (0 + 1) x := by
      apply hu0.congr_of_eventuallyEq
      filter_upwards [] with y
      simp
    have hu : HasDerivAt (fun y : ℝ => θ + y) 1 x :=
      hu1.congr_deriv (by ring)
    have hc := hu.cos
    have hi := hc.inv hx
    have htmp := hi.const_mul (lengthSI mirror.radius / 2)
    have hsame :
        HasDerivAt
          (fun y : ℝ =>
            lengthSI mirror.radius / (2 * Real.cos (θ + y)))
          ((lengthSI mirror.radius / 2) *
            (-(-Real.sin (θ + x) * 1) / Real.cos (θ + x) ^ 2)) x := by
      apply htmp.congr_of_eventuallyEq
      filter_upwards [] with y
      simp [div_eq_mul_inv]
      ring
    apply hsame.congr_deriv
    rw [Real.tan_eq_sin_div_cos]
    field_simp
  have hintercept_deriv_differentiable :
      DifferentiableAt ℝ
        (fun x : ℝ =>
          lengthSI mirror.radius / (2 * Real.cos (θ + x)) *
            Real.tan (θ + x)) 0 := by
    rw [show
        (fun x : ℝ =>
          lengthSI mirror.radius / (2 * Real.cos (θ + x)) *
            Real.tan (θ + x)) =
        (fun x : ℝ =>
          lengthSI mirror.radius / (2 * Real.cos (θ + x)) *
            (Real.sin (θ + x) / Real.cos (θ + x))) by
      funext x
      rw [Real.tan_eq_sin_div_cos]]
    fun_prop (disch := aesop)
  have hintercept_taylor_raw :=
    second_order_of_eventually_hasDeriv
      (fun x : ℝ =>
        lengthSI mirror.radius / (2 * Real.cos (θ + x)))
      (fun x : ℝ =>
        lengthSI mirror.radius / (2 * Real.cos (θ + x)) *
          Real.tan (θ + x))
      (deriv
        (fun x : ℝ =>
          lengthSI mirror.radius / (2 * Real.cos (θ + x)) *
            Real.tan (θ + x)) 0)
      hintercept_deriv hintercept_deriv_differentiable.hasDerivAt
  have hintercept_taylor :
      (fun x : ℝ =>
        lengthSI mirror.radius / (2 * Real.cos (θ + x)) -
          (lengthSI mirror.radius / (2 * Real.cos θ) *
            (1 + Real.tan θ * x)))
        =O[𝓝 (0 : ℝ)] (fun x : ℝ => x ^ 2) :=
    hintercept_taylor_raw.congr
      (fun x => by simp; ring)
      (fun _ => rfl)

  have hslope_eq :
      ∀ᶠ x in 𝓝 (0 : ℝ),
        (rayB x).reflectedLine.slope = Real.cot (2 * (θ + x)) := by
    filter_upwards [hB_geometry, h_reflection] with x hx_geometry hx_reflection
    rw [slope_eq_of_specular_law hx_reflection, hx_geometry.2.1]
  have hintercept_eq :
      ∀ᶠ x in 𝓝 (0 : ℝ),
        lengthSI (rayB x).reflectedLine.yIntercept =
          lengthSI mirror.radius / (2 * Real.cos (θ + x)) := by
    filter_upwards [hB_geometry, h_reflection] with x hx_geometry hx_reflection
    rw [intercept_eq_of_specular_law hx_reflection, hx_geometry.2.1]

  constructor
  · exact hslope_taylor.congr'
      (by
        filter_upwards [hslope_eq] with x hx
        rw [hx])
      Filter.EventuallyEq.rfl
  · exact hintercept_taylor.congr'
      (by
        filter_upwards [hintercept_eq] with x hx
        rw [hx])
      Filter.EventuallyEq.rfl

end IPhO2026Problems.IPhO2026_2_C_2
