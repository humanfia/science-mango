import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Physlib.Units.WithDim.Basic

open Filter Asymptotics
open scoped Topology

namespace IPhO2026_2_C_2

open Dimension

/-- A physical length, independent of the unit used for its scalar readout. -/
abbrev PhysicalLength := Dimensionful (WithDim L𝓭 ℝ)

/-- The scalar projection of a physical length into the common coordinate unit
chosen for Figure 2g. -/
noncomputable def figure2gLengthReadout
    (coordinateUnits : UnitChoices) (length : PhysicalLength) : ℝ :=
  (length coordinateUnits).val

/-- The data of a reflected ray in the coordinate convention of Figure 2g.

The slope is dimensionless, while the intercept is a physical length. -/
structure ReflectedRayReadout where
  slope : ℝ
  intercept : PhysicalLength

/-- The equation `y = m * x + b` used for the reflected rays in Figure 2g. -/
noncomputable def ReflectedRayReadout.yCoordinateLengthReadout
    (coordinateUnits : UnitChoices)
    (ray : ReflectedRayReadout) (x : PhysicalLength) : ℝ :=
  ray.slope * figure2gLengthReadout coordinateUnits x +
    figure2gLengthReadout coordinateUnits ray.intercept

/-- Physical and figure data for the half-cylindrical mirror.

Angles are dimensionless radian readouts. The function `reflectedRayReadoutAt`
describes the reflected members of the one parallel incident beam shown in
Figure 2g, indexed by their angle at the circular mirror. -/
structure Figure2gSetup where
  coordinateUnits : UnitChoices
  radius : PhysicalLength
  incidenceAngleRad : ℝ
  reflectedRayReadoutAt : ℝ → ReflectedRayReadout
  radiusLengthReadout_pos :
    0 < figure2gLengthReadout coordinateUnits radius
  incidenceAngleRad_pos : 0 < incidenceAngleRad
  incidenceAngleRad_lt_pi_div_two : incidenceAngleRad < Real.pi / 2

/-- Ray `A` is the reflected ray at the central incidence angle `θ`. -/
def rayA (setup : Figure2gSetup) : ReflectedRayReadout :=
  setup.reflectedRayReadoutAt setup.incidenceAngleRad

/-- Ray `B` is the neighboring reflected ray at angle `θ + Δθ`. -/
def rayB (setup : Figure2gSetup) (angularIncrementRad : ℝ) : ReflectedRayReadout :=
  setup.reflectedRayReadoutAt (setup.incidenceAngleRad + angularIncrementRad)

/-- The specular-reflection geometry law for the half-cylindrical mirror.

This is a governing law, stated for every physically admissible angle. It is
the exact relation to be Taylor-expanded; it does not assert either requested
first-order expansion. -/
def HalfCylindricalReflectionLaw (setup : Figure2gSetup) : Prop :=
  ∀ angleRad : ℝ, 0 < angleRad → angleRad < Real.pi / 2 →
    (setup.reflectedRayReadoutAt angleRad).slope = Real.cot (2 * angleRad) ∧
    figure2gLengthReadout setup.coordinateUnits
        (setup.reflectedRayReadoutAt angleRad).intercept =
      figure2gLengthReadout setup.coordinateUnits setup.radius /
        (2 * Real.cos angleRad)

/-- The reusable result of part C.1 for the line of ray `A`. -/
def PreviousPartC1Result (setup : Figure2gSetup) : Prop :=
  (rayA setup).slope = Real.cot (2 * setup.incidenceAngleRad) ∧
  figure2gLengthReadout setup.coordinateUnits (rayA setup).intercept =
    figure2gLengthReadout setup.coordinateUnits setup.radius /
      (2 * Real.cos setup.incidenceAngleRad)

/-- The first-order slope formula for neighboring ray `B`, with a remainder
bounded by a constant times `(Δθ)²` as `Δθ → 0`. -/
theorem rayB_slope_firstOrder
    (setup : Figure2gSetup)
    (reflectionLaw : HalfCylindricalReflectionLaw setup)
    (previousPart : PreviousPartC1Result setup) :
    (fun angularIncrementRad : ℝ =>
        (rayB setup angularIncrementRad).slope -
          (Real.cot (2 * setup.incidenceAngleRad) -
            2 * (Real.sin (2 * setup.incidenceAngleRad))⁻¹ ^ 2 *
              angularIncrementRad))
      =O[𝓝 0] (fun angularIncrementRad : ℝ => angularIncrementRad ^ 2) := by
  let θ := setup.incidenceAngleRad
  have h2θ_pos : 0 < 2 * θ := by
    dsimp [θ]
    linarith [setup.incidenceAngleRad_pos]
  have h2θ_lt_pi : 2 * θ < Real.pi := by
    dsimp [θ]
    linarith [setup.incidenceAngleRad_lt_pi_div_two]
  have hsin_pos : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi h2θ_pos h2θ_lt_pi

  have hlinear_deriv : HasDerivAt (fun angleRad : ℝ => 2 * angleRad) 2 θ := by
    simpa using (hasDerivAt_id θ).const_mul 2
  have hcos_deriv :
      HasDerivAt (fun angleRad : ℝ => Real.cos (2 * angleRad))
        (-Real.sin (2 * θ) * 2) θ :=
    hlinear_deriv.cos
  have hsin_deriv :
      HasDerivAt (fun angleRad : ℝ => Real.sin (2 * angleRad))
        (Real.cos (2 * θ) * 2) θ :=
    hlinear_deriv.sin
  have hquotient_deriv :
      HasDerivAt
        (fun angleRad : ℝ =>
          Real.cos (2 * angleRad) / Real.sin (2 * angleRad))
        ((-Real.sin (2 * θ) * 2 * Real.sin (2 * θ) -
            Real.cos (2 * θ) * (Real.cos (2 * θ) * 2)) /
          Real.sin (2 * θ) ^ 2) θ :=
    hcos_deriv.div hsin_deriv hsin_pos.ne'
  have hderiv_coefficient :
      ((-Real.sin (2 * θ) * 2 * Real.sin (2 * θ) -
            Real.cos (2 * θ) * (Real.cos (2 * θ) * 2)) /
          Real.sin (2 * θ) ^ 2) =
        -2 * (Real.sin (2 * θ))⁻¹ ^ 2 := by
    field_simp
    nlinarith [Real.sin_sq_add_cos_sq (2 * θ)]
  have hcot_deriv :
      HasDerivAt (fun angleRad : ℝ => Real.cot (2 * angleRad))
        (-2 * (Real.sin (2 * θ))⁻¹ ^ 2) θ := by
    rw [show (fun angleRad : ℝ => Real.cot (2 * angleRad)) =
        (fun angleRad : ℝ =>
          Real.cos (2 * angleRad) / Real.sin (2 * angleRad)) by
          funext angleRad
          exact Real.cot_eq_cos_div_sin (2 * angleRad)]
    exact hquotient_deriv.congr_deriv hderiv_coefficient

  have hlinear_analytic :
      AnalyticAt ℝ (fun angleRad : ℝ => 2 * angleRad) θ := by
    fun_prop
  have hcos_analytic :
      AnalyticAt ℝ (fun angleRad : ℝ => Real.cos (2 * angleRad)) θ := by
    change AnalyticAt ℝ (Real.cos ∘ fun angleRad : ℝ => 2 * angleRad) θ
    exact Real.analyticAt_cos.comp hlinear_analytic
  have hsin_analytic :
      AnalyticAt ℝ (fun angleRad : ℝ => Real.sin (2 * angleRad)) θ := by
    change AnalyticAt ℝ (Real.sin ∘ fun angleRad : ℝ => 2 * angleRad) θ
    exact Real.analyticAt_sin.comp hlinear_analytic
  have hcot_analytic :
      AnalyticAt ℝ (fun angleRad : ℝ => Real.cot (2 * angleRad)) θ := by
    rw [show (fun angleRad : ℝ => Real.cot (2 * angleRad)) =
        (fun angleRad : ℝ =>
          Real.cos (2 * angleRad) / Real.sin (2 * angleRad)) by
          funext angleRad
          exact Real.cot_eq_cos_div_sin (2 * angleRad)]
    exact hcos_analytic.div hsin_analytic hsin_pos.ne'

  have analytic_remainder_bigO
      (f : ℝ → ℝ) (x f' : ℝ)
      (hf : AnalyticAt ℝ f x) (hderiv : HasDerivAt f f' x) :
      (fun h : ℝ => f (x + h) - (f x + f' * h))
        =O[𝓝 0] (fun h : ℝ => h ^ 2) := by
    rcases hf with ⟨powerSeries, hpowerSeries⟩
    have hremainder := hpowerSeries.isBigO_sub_partialSum_pow 2
    refine hremainder.congr ?_ ?_
    · intro h
      simp only [FormalMultilinearSeries.partialSum, Finset.sum_range_succ]
      rw [hpowerSeries.coeff_zero]
      have hlinear_term :
          powerSeries 1 (fun _ => h) = f' * h := by
        have hcoeff :
            powerSeries 1 (fun _ => 1) = f' := by
          rw [← hpowerSeries.deriv, hderiv.deriv]
        rw [← hcoeff]
        have hconstant :
            (fun _ : Fin 1 => h) = fun i => h • (1 : ℝ) := by
          ext i
          simp
        rw [hconstant, ContinuousMultilinearMap.map_smul_univ]
        simp [mul_comm]
      rw [hlinear_term]
      simp
    · intro h
      rw [Real.norm_eq_abs]
      exact sq_abs h

  have hTaylor :
      (fun h : ℝ =>
          Real.cot (2 * (θ + h)) -
            (Real.cot (2 * θ) +
              (-2 * (Real.sin (2 * θ))⁻¹ ^ 2) * h))
        =O[𝓝 0] (fun h : ℝ => h ^ 2) :=
    analytic_remainder_bigO
      (fun angleRad : ℝ => Real.cot (2 * angleRad)) θ
      (-2 * (Real.sin (2 * θ))⁻¹ ^ 2) hcot_analytic hcot_deriv

  have hangle_tendsto :
      Tendsto (fun h : ℝ => θ + h) (𝓝 0) (𝓝 θ) := by
    simpa using
      ((tendsto_const_nhds :
          Tendsto (fun _ : ℝ => θ) (𝓝 0) (𝓝 θ)).add tendsto_id)
  have hadmissible :
      ∀ᶠ h : ℝ in 𝓝 0, 0 < θ + h ∧ θ + h < Real.pi / 2 :=
    hangle_tendsto.eventually
      (Ioo_mem_nhds setup.incidenceAngleRad_pos
        setup.incidenceAngleRad_lt_pi_div_two)
  refine hTaylor.congr' ?_ (Filter.Eventually.of_forall fun h => rfl)
  filter_upwards [hadmissible] with h hh
  have hray := reflectionLaw (θ + h) hh.1 hh.2
  change
    Real.cot (2 * (θ + h)) -
        (Real.cot (2 * θ) +
          (-2 * (Real.sin (2 * θ))⁻¹ ^ 2) * h) =
      (setup.reflectedRayReadoutAt (θ + h)).slope -
        (Real.cot (2 * θ) - 2 * (Real.sin (2 * θ))⁻¹ ^ 2 * h)
  rw [hray.1]
  ring

/-- The first-order intercept formula for neighboring ray `B`, with a
remainder bounded by a constant times `(Δθ)²` as `Δθ → 0`. -/
theorem rayB_intercept_firstOrder
    (setup : Figure2gSetup)
    (reflectionLaw : HalfCylindricalReflectionLaw setup)
    (previousPart : PreviousPartC1Result setup) :
    (fun angularIncrementRad : ℝ =>
        figure2gLengthReadout setup.coordinateUnits
            (rayB setup angularIncrementRad).intercept -
          (figure2gLengthReadout setup.coordinateUnits setup.radius /
              (2 * Real.cos setup.incidenceAngleRad) *
            (1 + Real.tan setup.incidenceAngleRad * angularIncrementRad)))
      =O[𝓝 0] (fun angularIncrementRad : ℝ => angularIncrementRad ^ 2) := by
  let θ := setup.incidenceAngleRad
  let radiusReadout :=
    figure2gLengthReadout setup.coordinateUnits setup.radius
  have hcos_pos : 0 < Real.cos θ := by
    apply Real.cos_pos_of_mem_Ioo
    constructor
    · dsimp [θ]
      linarith [setup.incidenceAngleRad_pos, Real.pi_pos]
    · exact setup.incidenceAngleRad_lt_pi_div_two
  have hdenominator_deriv :
      HasDerivAt (fun angleRad : ℝ => 2 * Real.cos angleRad)
        (2 * -Real.sin θ) θ :=
    (Real.hasDerivAt_cos θ).const_mul 2
  have hquotient_deriv :
      HasDerivAt (fun angleRad : ℝ =>
          radiusReadout / (2 * Real.cos angleRad))
        ((0 * (2 * Real.cos θ) -
            radiusReadout * (2 * -Real.sin θ)) /
          (2 * Real.cos θ) ^ 2) θ := by
    exact
      (hasDerivAt_const θ radiusReadout).div hdenominator_deriv
        (mul_ne_zero (by norm_num) hcos_pos.ne')
  have hderiv_coefficient :
      ((0 * (2 * Real.cos θ) -
            radiusReadout * (2 * -Real.sin θ)) /
          (2 * Real.cos θ) ^ 2) =
        (radiusReadout / (2 * Real.cos θ)) * Real.tan θ := by
    rw [Real.tan_eq_sin_div_cos]
    field_simp
    ring
  have hintercept_deriv :
      HasDerivAt (fun angleRad : ℝ =>
          radiusReadout / (2 * Real.cos angleRad))
        ((radiusReadout / (2 * Real.cos θ)) * Real.tan θ) θ :=
    hquotient_deriv.congr_deriv hderiv_coefficient
  have hintercept_analytic :
      AnalyticAt ℝ (fun angleRad : ℝ =>
          radiusReadout / (2 * Real.cos angleRad)) θ := by
    have hdenominator_analytic :
        AnalyticAt ℝ (fun angleRad : ℝ => 2 * Real.cos angleRad) θ := by
      fun_prop
    exact
      analyticAt_const.div hdenominator_analytic
        (mul_ne_zero (by norm_num) hcos_pos.ne')

  have analytic_remainder_bigO
      (f : ℝ → ℝ) (x f' : ℝ)
      (hf : AnalyticAt ℝ f x) (hderiv : HasDerivAt f f' x) :
      (fun h : ℝ => f (x + h) - (f x + f' * h))
        =O[𝓝 0] (fun h : ℝ => h ^ 2) := by
    rcases hf with ⟨powerSeries, hpowerSeries⟩
    have hremainder := hpowerSeries.isBigO_sub_partialSum_pow 2
    refine hremainder.congr ?_ ?_
    · intro h
      simp only [FormalMultilinearSeries.partialSum, Finset.sum_range_succ]
      rw [hpowerSeries.coeff_zero]
      have hlinear_term :
          powerSeries 1 (fun _ => h) = f' * h := by
        have hcoeff :
            powerSeries 1 (fun _ => 1) = f' := by
          rw [← hpowerSeries.deriv, hderiv.deriv]
        rw [← hcoeff]
        have hconstant :
            (fun _ : Fin 1 => h) = fun i => h • (1 : ℝ) := by
          ext i
          simp
        rw [hconstant, ContinuousMultilinearMap.map_smul_univ]
        simp [mul_comm]
      rw [hlinear_term]
      simp
    · intro h
      rw [Real.norm_eq_abs]
      exact sq_abs h

  have hTaylor :
      (fun h : ℝ =>
          radiusReadout / (2 * Real.cos (θ + h)) -
            (radiusReadout / (2 * Real.cos θ) +
              (radiusReadout / (2 * Real.cos θ) * Real.tan θ) * h))
        =O[𝓝 0] (fun h : ℝ => h ^ 2) :=
    analytic_remainder_bigO
      (fun angleRad : ℝ =>
        radiusReadout / (2 * Real.cos angleRad))
      θ ((radiusReadout / (2 * Real.cos θ)) * Real.tan θ)
      hintercept_analytic hintercept_deriv

  have hangle_tendsto :
      Tendsto (fun h : ℝ => θ + h) (𝓝 0) (𝓝 θ) := by
    simpa using
      ((tendsto_const_nhds :
          Tendsto (fun _ : ℝ => θ) (𝓝 0) (𝓝 θ)).add tendsto_id)
  have hadmissible :
      ∀ᶠ h : ℝ in 𝓝 0, 0 < θ + h ∧ θ + h < Real.pi / 2 :=
    hangle_tendsto.eventually
      (Ioo_mem_nhds setup.incidenceAngleRad_pos
        setup.incidenceAngleRad_lt_pi_div_two)
  refine hTaylor.congr' ?_ (Filter.Eventually.of_forall fun h => rfl)
  filter_upwards [hadmissible] with h hh
  have hray := reflectionLaw (θ + h) hh.1 hh.2
  change
    radiusReadout / (2 * Real.cos (θ + h)) -
        (radiusReadout / (2 * Real.cos θ) +
          (radiusReadout / (2 * Real.cos θ) * Real.tan θ) * h) =
      figure2gLengthReadout setup.coordinateUnits
          (setup.reflectedRayReadoutAt (θ + h)).intercept -
        (radiusReadout / (2 * Real.cos θ) *
          (1 + Real.tan θ * h))
  rw [hray.2]
  ring

/-- IPhO 2026 Problem 2 C.2: both requested first-order expansions of ray `B`.

The two conclusions say precisely that the displayed residuals are
`O((Δθ)²)` in the neighboring-ray limit `Δθ → 0`. -/
theorem IPhO_2026_2_C_2
    (setup : Figure2gSetup)
    (reflectionLaw : HalfCylindricalReflectionLaw setup)
    (previousPart : PreviousPartC1Result setup) :
    ((fun angularIncrementRad : ℝ =>
          (rayB setup angularIncrementRad).slope -
            (Real.cot (2 * setup.incidenceAngleRad) -
              2 * (Real.sin (2 * setup.incidenceAngleRad))⁻¹ ^ 2 *
                angularIncrementRad))
        =O[𝓝 0] (fun angularIncrementRad : ℝ => angularIncrementRad ^ 2)) ∧
      ((fun angularIncrementRad : ℝ =>
          figure2gLengthReadout setup.coordinateUnits
              (rayB setup angularIncrementRad).intercept -
            (figure2gLengthReadout setup.coordinateUnits setup.radius /
                (2 * Real.cos setup.incidenceAngleRad) *
              (1 + Real.tan setup.incidenceAngleRad * angularIncrementRad)))
        =O[𝓝 0] (fun angularIncrementRad : ℝ => angularIncrementRad ^ 2)) := by
  exact
    ⟨rayB_slope_firstOrder setup reflectionLaw previousPart,
      rayB_intercept_firstOrder setup reflectionLaw previousPart⟩

end IPhO2026_2_C_2
