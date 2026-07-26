import Physlib.Optics.Basic
import Physlib.Units.WithDim.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0037

/-- The two optical media separated by the smooth swimming-pool surface. -/
inductive OpticalMedium where
  | air
  | water
  deriving DecidableEq, Repr

/-- Qualitative polarization state of the reflected sunlight. -/
inductive PolarizationState where
  | unpolarized
  | partiallyPolarized
  | completelyPolarized
  deriving DecidableEq, Repr

/--
The physical objects and scalar readouts in the displayed air--water ray diagram.
Directions live in the two-dimensional plane of incidence.  The three angle
fields are real-valued radian readouts measured from the dashed surface normal;
refractive indices are dimensionless.
-/
structure PoolReflectionSetup where
  /-- Point at which the incident sunlight meets the pool surface. -/
  incidencePoint : EuclideanSpace ℝ (Fin 2)
  /-- Unit-normal direction pointing from the water into the air. -/
  surfaceNormalTowardAir : EuclideanSpace ℝ (Fin 2)
  /-- Propagation direction of the incident ray. -/
  incidentDirection : EuclideanSpace ℝ (Fin 2)
  /-- Propagation direction of the reflected ray. -/
  reflectedDirection : EuclideanSpace ℝ (Fin 2)
  /-- Propagation direction of the refracted ray in the water. -/
  refractedDirection : EuclideanSpace ℝ (Fin 2)
  /-- Dimension-tagged, dimensionless refractive index for each medium. -/
  refractiveIndex : OpticalMedium → WithDim (1 : Dimension) ℝ
  /-- Incident angle from the normal, the left-hand figure label `θₚ`. -/
  incidentAngleRadians : ℝ
  /-- Reflection angle from the normal, the right-hand figure label `θₚ`. -/
  reflectedAngleRadians : ℝ
  /-- Refraction angle from the normal in water, the figure label `θ_b`. -/
  refractedAngleRadians : ℝ
  /-- The interface is the smooth surface of a swimming pool. -/
  poolSurfaceIsSmooth : Prop
  /-- The incident beam is sunlight. -/
  incidentLightIsSunlight : Prop
  /-- Polarization state of the reflected beam. -/
  reflectedPolarization : PolarizationState

/--
The three scalar angle fields are the undirected geometric angles between the
corresponding ray directions and the appropriate side of the interface normal.
The incident propagation direction is reversed to measure the incoming ray.
-/
def HasNormalAngleReadouts (setup : PoolReflectionSetup) : Prop :=
  setup.incidentAngleRadians =
      InnerProductGeometry.angle
        (-setup.incidentDirection) setup.surfaceNormalTowardAir ∧
    setup.reflectedAngleRadians =
      InnerProductGeometry.angle
        setup.reflectedDirection setup.surfaceNormalTowardAir ∧
    setup.refractedAngleRadians =
      InnerProductGeometry.angle
        setup.refractedDirection (-setup.surfaceNormalTowardAir)

/-- Snell's law for dimensionless refractive indices and radian angle readouts. -/
def SatisfiesSnellLaw (setup : PoolReflectionSetup) : Prop :=
  (setup.refractiveIndex .air).val * Real.sin setup.incidentAngleRadians =
    (setup.refractiveIndex .water).val * Real.sin setup.refractedAngleRadians

/--
Problem-statement and figure readouts.  In particular, the right-angle marker
states that the reflected and refracted propagation directions are perpendicular.
None of these fields states the requested numerical reflection angle.
-/
structure PoolFigureReadouts (setup : PoolReflectionSetup) : Prop where
  smooth_surface : setup.poolSurfaceIsSmooth
  sunlight : setup.incidentLightIsSunlight
  air_index : (setup.refractiveIndex .air).val = (1 : ℝ)
  water_index : (setup.refractiveIndex .water).val = (133 : ℝ) / 100
  unit_normal : ‖setup.surfaceNormalTowardAir‖ = 1
  unit_incident_direction : ‖setup.incidentDirection‖ = 1
  unit_reflected_direction : ‖setup.reflectedDirection‖ = 1
  unit_refracted_direction : ‖setup.refractedDirection‖ = 1
  normal_angle_readouts : HasNormalAngleReadouts setup
  right_angle_marker :
    InnerProductGeometry.angle
        setup.reflectedDirection setup.refractedDirection =
      Real.pi / 2

/--
Governing geometrical-optics laws for the depicted configuration.  The Brewster
criterion relates complete reflected polarization to perpendicular reflected and
refracted rays, expressed by the sum of their acute normal-angle readouts.
-/
structure PoolOpticsLaws (setup : PoolReflectionSetup) : Prop where
  refractive_indices_positive :
    ∀ medium : OpticalMedium, 0 < (setup.refractiveIndex medium).val
  incident_angle_acute :
    setup.incidentAngleRadians ∈ Set.Ioo 0 (Real.pi / 2)
  reflected_angle_acute :
    setup.reflectedAngleRadians ∈ Set.Ioo 0 (Real.pi / 2)
  refracted_angle_acute :
    setup.refractedAngleRadians ∈ Set.Ioo 0 (Real.pi / 2)
  law_of_reflection :
    setup.reflectedAngleRadians = setup.incidentAngleRadians
  snell_law : SatisfiesSnellLaw setup
  brewster_criterion :
    setup.reflectedPolarization = .completelyPolarized ↔
      setup.reflectedAngleRadians + setup.refractedAngleRadians =
        Real.pi / 2

/-- The four reflected-angle choices printed with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Degree readout printed beside each answer choice. -/
def answerAngleDegrees : AnswerChoice → ℝ
  | .A => 60
  | .B => (531 : ℝ) / 10
  | .C => 68
  | .D => (674 : ℝ) / 10

/-- Convert a real-valued degree readout to radians. -/
def degreesToRadians (degrees : ℝ) : ℝ :=
  degrees * Real.pi / 180

/--
A radian angle rounds to the displayed one-decimal-place answer when it is
within half of `0.1°` of that answer's degree readout.
-/
def MatchesAnswerToNearestTenthDegree
    (angleRadians : ℝ) (choice : AnswerChoice) : Prop :=
  |angleRadians - degreesToRadians (answerAngleDegrees choice)| ≤
    degreesToRadians ((1 : ℝ) / 20)

/--
For sunlight reflected from the stated air--water interface, a completely
polarized reflected beam has reflection angle `53.1°` to the displayed
precision, hence answer choice B.

Blueprint label: `thm:physics:phyx_mini_0037:target`.
-/
theorem completelyPolarizedReflection_is_answer_B
    (setup : PoolReflectionSetup)
    (_figure : PoolFigureReadouts setup)
    (_laws : PoolOpticsLaws setup)
    (_complete :
      setup.reflectedPolarization = .completelyPolarized) :
    MatchesAnswerToNearestTenthDegree setup.reflectedAngleRadians .B := by
  have hcomplement :
      setup.reflectedAngleRadians + setup.refractedAngleRadians =
        Real.pi / 2 :=
    _laws.brewster_criterion.mp _complete
  have hrefracted :
      setup.refractedAngleRadians =
        Real.pi / 2 - setup.reflectedAngleRadians := by
    linarith only [hcomplement]
  have hsnell := _laws.snell_law
  simp only [SatisfiesSnellLaw, _figure.air_index,
    _figure.water_index] at hsnell
  rw [← _laws.law_of_reflection, hrefracted,
    Real.sin_pi_div_two_sub] at hsnell
  have hsin_cos :
      (100 : ℝ) * Real.sin setup.reflectedAngleRadians =
        133 * Real.cos setup.reflectedAngleRadians := by
    nlinarith only [hsnell]

  let delta : ℝ := setup.reflectedAngleRadians - Real.pi / 4
  have hdelta_mem :
      delta ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
    dsimp [delta]
    constructor <;>
      nlinarith only [_laws.reflected_angle_acute.1,
        _laws.reflected_angle_acute.2, Real.pi_pos]
  have hcos_delta_pos : 0 < Real.cos delta :=
    Real.cos_pos_of_mem_Ioo hdelta_mem
  have hdelta_relation :
      (233 : ℝ) * Real.sin delta = 33 * Real.cos delta := by
    dsimp [delta]
    rw [Real.sin_sub, Real.cos_sub, Real.sin_pi_div_four,
      Real.cos_pi_div_four]
    linear_combination Real.sqrt 2 * hsin_cos
  have htan_delta : Real.tan delta = (33 : ℝ) / 233 := by
    rw [Real.tan_eq_sin_div_cos,
      div_eq_iff hcos_delta_pos.ne']
    nlinarith only [hdelta_relation]

  have hr2_sq : Real.sqrt 2 ^ 2 = (2 : ℝ) :=
    Real.sq_sqrt (by norm_num)
  have hr2_nonneg : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
  have hr2_lower : (1.41421 : ℝ) < Real.sqrt 2 := by
    nlinarith only [hr2_sq, hr2_nonneg]
  have hr2_upper : Real.sqrt 2 < (1.414214 : ℝ) := by
    nlinarith only [hr2_sq, hr2_nonneg]
  have hr3_arg : 0 ≤ (2 : ℝ) + Real.sqrt 2 := by positivity
  have hr3_sq :
      Real.sqrt (2 + Real.sqrt 2) ^ 2 = 2 + Real.sqrt 2 :=
    Real.sq_sqrt hr3_arg
  have hr3_nonneg : 0 ≤ Real.sqrt (2 + Real.sqrt 2) :=
    Real.sqrt_nonneg _
  have hr3_lower :
      (1.8477581 : ℝ) < Real.sqrt (2 + Real.sqrt 2) := by
    nlinarith only [hr2_lower, hr3_sq, hr3_nonneg]
  have hr3_upper :
      Real.sqrt (2 + Real.sqrt 2) < (1.8477595 : ℝ) := by
    nlinarith only [hr2_upper, hr3_sq, hr3_nonneg]
  have hs_arg : 0 ≤ (2 : ℝ) - Real.sqrt (2 + Real.sqrt 2) := by
    linarith only [hr3_upper]
  have hs_sq :
      Real.sqrt (2 - Real.sqrt (2 + Real.sqrt 2)) ^ 2 =
        2 - Real.sqrt (2 + Real.sqrt 2) :=
    Real.sq_sqrt hs_arg
  have hs_nonneg :
      0 ≤ Real.sqrt (2 - Real.sqrt (2 + Real.sqrt 2)) :=
    Real.sqrt_nonneg _
  have hs_upper :
      Real.sqrt (2 - Real.sqrt (2 + Real.sqrt 2)) <
        (0.390182 : ℝ) := by
    nlinarith only [hr3_lower, hs_sq, hs_nonneg]
  have hs_lower :
      (0.39018 : ℝ) <
        Real.sqrt (2 - Real.sqrt (2 + Real.sqrt 2)) := by
    nlinarith only [hr3_upper, hs_sq, hs_nonneg]
  have hsin_pi_upper :
      Real.sin (Real.pi / 16) < (0.195091 : ℝ) := by
    rw [Real.sin_pi_div_sixteen]
    linarith only [hs_upper]
  have hsin_pi_lower :
      (0.19509 : ℝ) < Real.sin (Real.pi / 16) := by
    rw [Real.sin_pi_div_sixteen]
    linarith only [hs_lower]

  let piSixteenth : ℝ := Real.pi / 16
  have hpiSixteenth_nonneg : 0 ≤ piSixteenth := by
    dsimp [piSixteenth]
    positivity
  have hpiSixteenth_le_quarter :
      piSixteenth ≤ (1 / 4 : ℝ) := by
    dsimp [piSixteenth]
    nlinarith only [Real.pi_le_four]
  have hpiSixteenth_abs : |piSixteenth| ≤ 1 := by
    rw [abs_of_nonneg hpiSixteenth_nonneg]
    linarith only [hpiSixteenth_le_quarter]
  have hpiSixteenth_sin_bound :=
    Real.sin_bound hpiSixteenth_abs
  rw [abs_of_nonneg hpiSixteenth_nonneg] at hpiSixteenth_sin_bound
  have hpiSixteenth_approx_lower :=
    (abs_le.mp hpiSixteenth_sin_bound).1
  have hpiSixteenth_approx_upper :=
    (abs_le.mp hpiSixteenth_sin_bound).2
  have hpi_gt_31 : (3.1 : ℝ) < Real.pi := by
    by_contra h
    have hpi_le : Real.pi ≤ (3.1 : ℝ) := le_of_not_gt h
    have hfourth :
        piSixteenth ^ 4 ≤ ((3.1 : ℝ) / 16) ^ 4 := by
      apply pow_le_pow_left₀ hpiSixteenth_nonneg _ 4
      dsimp [piSixteenth]
      nlinarith only [hpi_le]
    have hcube_nonneg : 0 ≤ piSixteenth ^ 3 :=
      pow_nonneg hpiSixteenth_nonneg _
    dsimp [piSixteenth] at hpiSixteenth_approx_upper hfourth hcube_nonneg
    nlinarith only [hsin_pi_lower, hpiSixteenth_approx_upper,
      hfourth, hcube_nonneg, hpi_le]
  have hpiSixteenth_ge_31 :
      (3.1 : ℝ) / 16 ≤ piSixteenth := by
    dsimp [piSixteenth]
    nlinarith only [hpi_gt_31.le]
  have hpi_lower : (3.139 : ℝ) < Real.pi := by
    have hcube :
        ((3.1 : ℝ) / 16) ^ 3 ≤ piSixteenth ^ 3 :=
      pow_le_pow_left₀ (by norm_num) hpiSixteenth_ge_31 3
    by_contra h
    have hpi_le : Real.pi ≤ (3.139 : ℝ) := le_of_not_gt h
    have hfourth :
        piSixteenth ^ 4 ≤ ((3.139 : ℝ) / 16) ^ 4 := by
      apply pow_le_pow_left₀ hpiSixteenth_nonneg _ 4
      dsimp [piSixteenth]
      nlinarith only [hpi_le]
    dsimp [piSixteenth] at hpiSixteenth_approx_upper hcube hfourth
    nlinarith only [hsin_pi_lower, hpiSixteenth_approx_upper,
      hcube, hfourth, hpi_le]
  have hpi_lt_32 : Real.pi < (3.2 : ℝ) := by
    have hcube :
        piSixteenth ^ 3 ≤ (1 / 4 : ℝ) ^ 3 :=
      pow_le_pow_left₀ hpiSixteenth_nonneg
        hpiSixteenth_le_quarter 3
    have hfourth :
        piSixteenth ^ 4 ≤ (1 / 4 : ℝ) ^ 4 :=
      pow_le_pow_left₀ hpiSixteenth_nonneg
        hpiSixteenth_le_quarter 4
    by_contra h
    have hpi_ge : (3.2 : ℝ) ≤ Real.pi := le_of_not_gt h
    dsimp [piSixteenth] at hpiSixteenth_approx_lower hcube hfourth
    nlinarith only [hsin_pi_upper, hpiSixteenth_approx_lower,
      hcube, hfourth, hpi_ge]
  have hpiSixteenth_le_32 :
      piSixteenth ≤ (3.2 : ℝ) / 16 := by
    dsimp [piSixteenth]
    nlinarith only [hpi_lt_32.le]
  have hpi_lt_315 : Real.pi < (3.15 : ℝ) := by
    have hcube :
        piSixteenth ^ 3 ≤ ((3.2 : ℝ) / 16) ^ 3 :=
      pow_le_pow_left₀ hpiSixteenth_nonneg
        hpiSixteenth_le_32 3
    have hfourth :
        piSixteenth ^ 4 ≤ ((3.2 : ℝ) / 16) ^ 4 :=
      pow_le_pow_left₀ hpiSixteenth_nonneg
        hpiSixteenth_le_32 4
    by_contra h
    have hpi_ge : (3.15 : ℝ) ≤ Real.pi := le_of_not_gt h
    dsimp [piSixteenth] at hpiSixteenth_approx_lower hcube hfourth
    nlinarith only [hsin_pi_upper, hpiSixteenth_approx_lower,
      hcube, hfourth, hpi_ge]
  have hpiSixteenth_le_315 :
      piSixteenth ≤ (3.15 : ℝ) / 16 := by
    dsimp [piSixteenth]
    nlinarith only [hpi_lt_315.le]
  have hpi_lt_3145 : Real.pi < (3.145 : ℝ) := by
    have hcube :
        piSixteenth ^ 3 ≤ ((3.15 : ℝ) / 16) ^ 3 :=
      pow_le_pow_left₀ hpiSixteenth_nonneg
        hpiSixteenth_le_315 3
    have hfourth :
        piSixteenth ^ 4 ≤ ((3.15 : ℝ) / 16) ^ 4 :=
      pow_le_pow_left₀ hpiSixteenth_nonneg
        hpiSixteenth_le_315 4
    by_contra h
    have hpi_ge : (3.145 : ℝ) ≤ Real.pi := le_of_not_gt h
    dsimp [piSixteenth] at hpiSixteenth_approx_lower hcube hfourth
    nlinarith only [hsin_pi_upper, hpiSixteenth_approx_lower,
      hcube, hfourth, hpi_ge]
  have hpiSixteenth_le_3145 :
      piSixteenth ≤ (3.145 : ℝ) / 16 := by
    dsimp [piSixteenth]
    nlinarith only [hpi_lt_3145.le]
  have hpi_upper : Real.pi < (3.143 : ℝ) := by
    have hcube :
        piSixteenth ^ 3 ≤ ((3.145 : ℝ) / 16) ^ 3 :=
      pow_le_pow_left₀ hpiSixteenth_nonneg
        hpiSixteenth_le_3145 3
    have hfourth :
        piSixteenth ^ 4 ≤ ((3.145 : ℝ) / 16) ^ 4 :=
      pow_le_pow_left₀ hpiSixteenth_nonneg
        hpiSixteenth_le_3145 4
    by_contra h
    have hpi_ge : (3.143 : ℝ) ≤ Real.pi := le_of_not_gt h
    dsimp [piSixteenth] at hpiSixteenth_approx_lower hcube hfourth
    nlinarith only [hsin_pi_upper, hpiSixteenth_approx_lower,
      hcube, hfourth, hpi_ge]

  let lower : ℝ := 161 * Real.pi / 3600
  have hlower_nonneg : 0 ≤ lower := by
    dsimp [lower]
    positivity
  have hlower_lower : (0.1403 : ℝ) < lower := by
    dsimp [lower]
    nlinarith only [hpi_lower]
  have hlower_upper : lower < (0.14057 : ℝ) := by
    dsimp [lower]
    nlinarith only [hpi_upper]
  have hlower_abs : |lower| ≤ 1 := by
    rw [abs_of_nonneg hlower_nonneg]
    linarith only [hlower_upper]
  have hlower_sin_bound := Real.sin_bound hlower_abs
  have hlower_cos_bound := Real.cos_bound hlower_abs
  rw [abs_of_nonneg hlower_nonneg] at hlower_sin_bound
  rw [abs_of_nonneg hlower_nonneg] at hlower_cos_bound
  have hlower_sin_upper := (abs_le.mp hlower_sin_bound).2
  have hlower_cos_lower := (abs_le.mp hlower_cos_bound).1
  have hlower_sq_upper :
      lower ^ 2 ≤ (0.14057 : ℝ) ^ 2 :=
    pow_le_pow_left₀ hlower_nonneg hlower_upper.le 2
  have hlower_cube_lower :
      (0.1403 : ℝ) ^ 3 ≤ lower ^ 3 :=
    pow_le_pow_left₀ (by norm_num) hlower_lower.le 3
  have hlower_fourth_upper :
      lower ^ 4 ≤ (0.14057 : ℝ) ^ 4 :=
    pow_le_pow_left₀ hlower_nonneg hlower_upper.le 4
  have hlower_linear :
      (233 : ℝ) * Real.sin lower < 33 * Real.cos lower := by
    nlinarith only [hlower_sin_upper, hlower_cos_lower,
      hlower_sq_upper, hlower_cube_lower, hlower_fourth_upper]
  have hlower_mem :
      lower ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor
    · linarith only [hlower_nonneg, Real.pi_pos]
    · dsimp [lower]
      nlinarith only [Real.pi_pos]
  have hcos_lower_pos : 0 < Real.cos lower :=
    Real.cos_pos_of_mem_Ioo hlower_mem
  have htan_lower :
      Real.tan lower < (33 : ℝ) / 233 := by
    rw [Real.tan_eq_sin_div_cos,
      div_lt_iff₀ hcos_lower_pos]
    nlinarith only [hlower_linear]

  let upper : ℝ := 163 * Real.pi / 3600
  have hupper_nonneg : 0 ≤ upper := by
    dsimp [upper]
    positivity
  have hupper_lower : (0.14212 : ℝ) < upper := by
    dsimp [upper]
    nlinarith only [hpi_lower]
  have hupper_upper : upper < (0.14231 : ℝ) := by
    dsimp [upper]
    nlinarith only [hpi_upper]
  have hupper_abs : |upper| ≤ 1 := by
    rw [abs_of_nonneg hupper_nonneg]
    linarith only [hupper_upper]
  have hupper_sin_bound := Real.sin_bound hupper_abs
  have hupper_cos_bound := Real.cos_bound hupper_abs
  rw [abs_of_nonneg hupper_nonneg] at hupper_sin_bound
  rw [abs_of_nonneg hupper_nonneg] at hupper_cos_bound
  have hupper_sin_lower := (abs_le.mp hupper_sin_bound).1
  have hupper_cos_upper := (abs_le.mp hupper_cos_bound).2
  have hupper_sq_lower :
      (0.14212 : ℝ) ^ 2 ≤ upper ^ 2 :=
    pow_le_pow_left₀ (by norm_num) hupper_lower.le 2
  have hupper_cube_upper :
      upper ^ 3 ≤ (0.14231 : ℝ) ^ 3 :=
    pow_le_pow_left₀ hupper_nonneg hupper_upper.le 3
  have hupper_fourth_upper :
      upper ^ 4 ≤ (0.14231 : ℝ) ^ 4 :=
    pow_le_pow_left₀ hupper_nonneg hupper_upper.le 4
  have hupper_linear :
      (33 : ℝ) * Real.cos upper < 233 * Real.sin upper := by
    nlinarith only [hupper_sin_lower, hupper_cos_upper,
      hupper_lower, hupper_sq_lower, hupper_cube_upper,
      hupper_fourth_upper]
  have hupper_mem :
      upper ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor
    · linarith only [hupper_nonneg, Real.pi_pos]
    · dsimp [upper]
      nlinarith only [Real.pi_pos]
  have hcos_upper_pos : 0 < Real.cos upper :=
    Real.cos_pos_of_mem_Ioo hupper_mem
  have htan_upper :
      (33 : ℝ) / 233 < Real.tan upper := by
    rw [Real.tan_eq_sin_div_cos,
      lt_div_iff₀ hcos_upper_pos]
    nlinarith only [hupper_linear]

  have hdelta_lower : lower < delta := by
    apply (Real.strictMonoOn_tan.lt_iff_lt hlower_mem hdelta_mem).mp
    rw [htan_delta]
    exact htan_lower
  have hdelta_upper : delta < upper := by
    apply (Real.strictMonoOn_tan.lt_iff_lt hdelta_mem hupper_mem).mp
    rw [htan_delta]
    exact htan_upper

  simp only [MatchesAnswerToNearestTenthDegree, answerAngleDegrees,
    degreesToRadians]
  rw [abs_le]
  dsimp [lower, upper, delta] at hdelta_lower hdelta_upper
  constructor <;>
    nlinarith only [hdelta_lower, hdelta_upper, Real.pi_pos]

end PhyXMiniProblems.ProblemPhyXMini0037
