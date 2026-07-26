import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Physlib.Units.WithDim.Basic

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0051

/-!
# Circle of light above a submerged point source

The pool depth, source depth, light-circle radius, and light-circle diameter
are physical lengths, independent of a choice of units. Their numerical data
and the final answer are stated as meter readouts. Refractive indices are
dimensionless, and angles are real-valued radian readouts measured from the
normal to the planar water--air interface.
-/

open Dimension

/-- A physical length, represented independently of any particular unit choice. -/
abbrev DimLength : Type := Dimensionful (WithDim L𝓭 ℝ)

/-- The numerical value of a dimensionful length when measured in SI meters. -/
def lengthInMeters (quantity : DimLength) : ℝ :=
  (quantity UnitChoices.SI).val

/-- The two homogeneous optical media shown on either side of the surface. -/
inductive OpticalMedium where
  | water
  | air
  deriving DecidableEq, Repr

/--
The physical quantities labelled in the pool diagram. The critical and edge
angles are kept separate so that their identification remains figure data.
No numerical value for the requested diameter is stored here.
-/
structure PoolLightSetup where
  /-- Figure label `h`: the vertical water depth. -/
  poolDepth : DimLength
  /-- Vertical distance from the point light source to the water surface. -/
  sourceDepthBelowSurface : DimLength
  /-- Radius from the vertical axis to a critical ray's surface intersection. -/
  lightCircleRadius : DimLength
  /-- Figure label `D`: diameter of the circle visible from above. -/
  lightCircleDiameter : DimLength
  /-- Dimensionless refractive-index readout for each medium. -/
  refractiveIndexDimensionless : OpticalMedium → ℝ
  /-- Critical incidence angle `θ_c`, in radians and measured from the normal. -/
  criticalAngleRadians : ℝ
  /-- Incidence angle of a ray forming the depicted circle boundary. -/
  edgeRayIncidenceAngleRadians : ℝ

/--
Problem and figure readouts: a `3.0 m` deep pool, a source at its bottom,
water index `n₁ = 1.33`, air index `n₂ = 1.00`, boundary rays at the critical
angle, and the full circle diameter equal to twice its radius.
-/
structure MatchesPoolFigure (setup : PoolLightSetup) : Prop where
  poolDepthReadout :
    lengthInMeters setup.poolDepth = 3.0
  sourceAtPoolBottom :
    setup.sourceDepthBelowSurface = setup.poolDepth
  waterIndexReadout :
    setup.refractiveIndexDimensionless .water = 1.33
  airIndexReadout :
    setup.refractiveIndexDimensionless .air = 1.00
  edgeRayAtCriticalAngle :
    setup.edgeRayIncidenceAngleRadians = setup.criticalAngleRadians
  diameterFromRadius :
    lengthInMeters setup.lightCircleDiameter =
      2 * lengthInMeters setup.lightCircleRadius

/--
Right-triangle geometry for a boundary ray from the point source to the
surface: its horizontal reach is the source depth times the tangent of its
incidence angle from the vertical normal.
-/
structure SatisfiesCriticalRayGeometry (setup : PoolLightSetup) : Prop where
  radiusFromBoundaryRay :
    lengthInMeters setup.lightCircleRadius =
      lengthInMeters setup.sourceDepthBelowSurface *
        Real.tan setup.edgeRayIncidenceAngleRadians

/--
Snell's law at the water--air critical angle. At the threshold, the
transmitted ray is tangent to the interface, so its refraction angle from the
normal is `π / 2`.
-/
structure SatisfiesWaterAirCriticalAngleLaw (setup : PoolLightSetup) : Prop where
  refractiveIndicesPositive :
    ∀ medium, 0 < setup.refractiveIndexDimensionless medium
  waterIndexGreaterThanAir :
    setup.refractiveIndexDimensionless .air <
      setup.refractiveIndexDimensionless .water
  criticalAnglePositive :
    0 < setup.criticalAngleRadians
  criticalAngleAcute :
    setup.criticalAngleRadians < Real.pi / 2
  snellAtCriticalBoundary :
    setup.refractiveIndexDimensionless .water *
        Real.sin setup.criticalAngleRadians =
      setup.refractiveIndexDimensionless .air * Real.sin (Real.pi / 2)

/-- The four diameter choices printed in the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- The meter readout printed beside each answer choice. -/
def answerDiameterMeters : AnswerChoice → ℝ
  | .A => 6.4
  | .B => 6.8
  | .C => 8.9
  | .D => 1.24

/-- Agreement with a diameter displayed to the nearest tenth of a meter. -/
def MatchesAnswerToNearestTenth
    (diameter : DimLength) (choice : AnswerChoice) : Prop :=
  |lengthInMeters diameter - answerDiameterMeters choice| ≤ 0.05

/-
The critical ray's right triangle and the circle's diameter--radius relation
give `D = 2 h tan θ_c` in meter readouts. This is an intermediate geometric
conclusion, not a premise of the numerical result.
-/
lemma critical_ray_circle_diameter_formula
    (setup : PoolLightSetup)
    (figure : MatchesPoolFigure setup)
    (geometry : SatisfiesCriticalRayGeometry setup) :
    lengthInMeters setup.lightCircleDiameter =
      2 * lengthInMeters setup.poolDepth *
        Real.tan setup.criticalAngleRadians := by
  calc
    lengthInMeters setup.lightCircleDiameter =
        2 * lengthInMeters setup.lightCircleRadius :=
      figure.diameterFromRadius
    _ = 2 *
        (lengthInMeters setup.sourceDepthBelowSurface *
          Real.tan setup.edgeRayIncidenceAngleRadians) := by
      rw [geometry.radiusFromBoundaryRay]
    _ = 2 * lengthInMeters setup.poolDepth *
        Real.tan setup.criticalAngleRadians := by
      rw [figure.sourceAtPoolBottom, figure.edgeRayAtCriticalAngle]
      ring

/-
For a point source at the bottom of a `3.0 m` pool with water refractive index
`1.33` and air refractive index `1.00`, the critical-angle law and boundary-ray
geometry give a circle of light whose diameter rounds to `6.8 m`, answer B.

Blueprint: `thm:physics:phyx_mini_0051:target`.
-/
theorem problem_phyx_mini_0051
    (setup : PoolLightSetup)
    (figure : MatchesPoolFigure setup)
    (geometry : SatisfiesCriticalRayGeometry setup)
    (optics : SatisfiesWaterAirCriticalAngleLaw setup) :
    lengthInMeters setup.lightCircleDiameter =
        2 * lengthInMeters setup.poolDepth *
          Real.tan setup.criticalAngleRadians ∧
      MatchesAnswerToNearestTenth setup.lightCircleDiameter .B := by
  have hdiam :=
    critical_ray_circle_diameter_formula setup figure geometry
  constructor
  · exact hdiam
  · unfold MatchesAnswerToNearestTenth
    rw [hdiam, figure.poolDepthReadout]
    have hsin :
        Real.sin setup.criticalAngleRadians = (100 : ℝ) / 133 := by
      have h := optics.snellAtCriticalBoundary
      rw [figure.waterIndexReadout, figure.airIndexReadout,
        Real.sin_pi_div_two] at h
      norm_num at h ⊢
      linarith
    have hcos : 0 < Real.cos setup.criticalAngleRadians := by
      apply Real.cos_pos_of_mem_Ioo
      constructor
      · linarith [Real.pi_pos, optics.criticalAnglePositive]
      · exact optics.criticalAngleAcute
    have hcos_sq :
        (Real.cos setup.criticalAngleRadians) ^ 2 =
          (7689 : ℝ) / 17689 := by
      nlinarith [Real.sin_sq_add_cos_sq setup.criticalAngleRadians]
    have hcos_lower :
        (12000 : ℝ) / 18221 <
          Real.cos setup.criticalAngleRadians := by
      by_contra h
      have hle :
          Real.cos setup.criticalAngleRadians ≤ (12000 : ℝ) / 18221 :=
        le_of_not_gt h
      nlinarith [hcos_sq]
    have hcos_upper :
        Real.cos setup.criticalAngleRadians < (800 : ℝ) / 1197 := by
      by_contra h
      have hle :
          (800 : ℝ) / 1197 ≤ Real.cos setup.criticalAngleRadians :=
        le_of_not_gt h
      nlinarith [hcos_sq]
    have htan_lower :
        (9 : ℝ) / 8 ≤ Real.tan setup.criticalAngleRadians := by
      rw [Real.tan_eq_sin_div_cos, hsin]
      apply (le_div_iff₀ hcos).2
      nlinarith
    have htan_upper :
        Real.tan setup.criticalAngleRadians ≤ (137 : ℝ) / 120 := by
      rw [Real.tan_eq_sin_div_cos, hsin]
      apply (div_le_iff₀ hcos).2
      nlinarith
    simp only [answerDiameterMeters]
    rw [abs_le]
    constructor <;> norm_num at * <;> linarith

end PhyXMiniProblems.ProblemPhyXMini0051
