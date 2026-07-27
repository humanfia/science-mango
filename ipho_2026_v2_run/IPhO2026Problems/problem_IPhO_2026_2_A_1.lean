import Mathlib
import Physlib.Units.WithDim.Basic

/-!
# IPhO 2026 Problem 2, part A.1

Parallel rays enter a half-cylindrical mirror.  The formalization keeps the
mirror radius, incident transverse coordinate, and positive threshold as
Physlib length quantities.  Trigonometric coordinate equations are stated
using the explicitly named SI projection `siLengthValue`.
-/

noncomputable section

open Dimension

namespace IPhO2026Problem2A1

/-- A physical length represented through Physlib's unit-dependent
dimensionful-quantity interface. -/
abbrev LengthQuantity : Type :=
  Dimensionful (WithDim L𝓭 ℝ)

/-- The numerical value of a physical length in SI metres. -/
def siLengthValue (length : LengthQuantity) : ℝ :=
  (length UnitChoices.SI).val

/-- The three source panels used for the multiple-reflection model:
Figure 2c is the physical half-cylinder, Figure 2d is its planar
cross-section, and Figure 2e is the reflection-count plot. -/
inductive SourceFigure
  | mirrorAssembly2c
  | crossSection2d
  | reflectionCountPlot2e
  deriving DecidableEq

/-- The orientation of a ray parallel to the optical axis in the coordinate
frame of Figure 2d. -/
inductive AxialDirection
  | towardPositiveY
  | towardNegativeY
  deriving DecidableEq

/-- A half-cylindrical mirror with a positive length-valued radius.  The
source-panel field ties this carrier to the apparatus in Figure 2c. -/
structure HalfCylindricalMirror where
  radius : LengthQuantity
  radius_si_pos : 0 < siLengthValue radius
  sourcePanel : SourceFigure
  source_panel_from_figure : sourcePanel = .mirrorAssembly2c

/-- The diameter marked `2R` in Figure 2c, as a physical length quantity. -/
def HalfCylindricalMirror.diameter
    (mirror : HalfCylindricalMirror) : LengthQuantity :=
  (2 : NNReal) • mirror.radius

/-- The reflecting upper semicircle in the coordinate frame of Figure 2d.
Both coordinates are physical lengths.  The optical axis is the `y`-axis and
the origin is the circle center; the displayed equation uses SI projections. -/
def OnReflectingSemicircle (mirror : HalfCylindricalMirror)
    (point : LengthQuantity × LengthQuantity) : Prop :=
  siLengthValue point.1 ^ 2 + siLengthValue point.2 ^ 2 =
      siLengthValue mirror.radius ^ 2 ∧
    0 ≤ siLengthValue point.2

universe u

/-- Typed ray data for the experiment in Figures 2d--2e.

`Ray` is an abstract physical primitive.  Its transverse coordinate is a
Physlib length quantity, its incidence and reflection angles are
dimensionless real readouts in radians, and `reflectionCount` records the
discrete number of mirror impacts. -/
structure MultipleReflectionExperiment (mirror : HalfCylindricalMirror) where
  Ray : Type u
  transverseCoordinate : Ray → LengthQuantity
  reflectionCount : Ray → ℕ
  isParallelIncident : Ray → Prop
  incomingDirection : AxialDirection
  incoming_direction_from_figure : incomingDirection = .towardPositiveY
  crossSectionPanel : SourceFigure
  cross_section_panel_from_figure : crossSectionPanel = .crossSection2d
  reflectionCountPanel : SourceFigure
  reflection_count_panel_from_figure :
    reflectionCountPanel = .reflectionCountPlot2e
  incidenceAngleAt : Ray → ℕ → ℝ
  reflectionAngleAt : Ray → ℕ → ℝ
  incident_coordinate_in_aperture :
    ∀ ray, isParallelIncident ray →
      |siLengthValue (transverseCoordinate ray)| <
        siLengthValue mirror.radius
  incident_ray_at_coordinate :
    ∀ x : LengthQuantity,
      |siLengthValue x| < siLengthValue mirror.radius →
        ∃ ray, isParallelIncident ray ∧ transverseCoordinate ray = x
  reflection_count_positive :
    ∀ ray, isParallelIncident ray → 0 < reflectionCount ray
  reflection_count_symmetric :
    ∀ ray₁ ray₂,
      isParallelIncident ray₁ →
      isParallelIncident ray₂ →
      siLengthValue (transverseCoordinate ray₂) =
        -siLengthValue (transverseCoordinate ray₁) →
      reflectionCount ray₂ = reflectionCount ray₁

/-- The equal-angle law of specular reflection, stated at every actual impact.
Angles are dimensionless real readouts in radians. -/
def ObeysSpecularReflection {mirror : HalfCylindricalMirror}
    (experiment : MultipleReflectionExperiment mirror) : Prop :=
  ∀ ray impact,
    experiment.isParallelIncident ray →
    impact < experiment.reflectionCount ray →
    experiment.reflectionAngleAt ray impact =
      experiment.incidenceAngleAt ray impact

/-- `xN` is the positive maximum physical transverse distance among incident
rays that undergo at most `N` reflections.  The predicate expresses
positivity, attainment, and maximality; it does not define the requested
closed form. -/
def IsPositiveReflectionThreshold {mirror : HalfCylindricalMirror}
    (experiment : MultipleReflectionExperiment mirror) (N : ℕ)
    (xN : LengthQuantity) : Prop :=
  0 < siLengthValue xN ∧
    siLengthValue xN < siLengthValue mirror.radius ∧
    (∃ ray,
      experiment.isParallelIncident ray ∧
      experiment.transverseCoordinate ray = xN ∧
      experiment.reflectionCount ray ≤ N) ∧
    ∀ ray,
      experiment.isParallelIncident ray →
      experiment.reflectionCount ray ≤ N →
      |siLengthValue (experiment.transverseCoordinate ray)| ≤
        siLengthValue xN

/-- A limiting ray on the positive-`x` branch, together with its first impact
point and the acute polar angle of that point measured from the positive
`x`-axis.  This polar angle is distinct from the optical incidence angle
relative to the surface normal. -/
structure LimitingRayWitness {mirror : HalfCylindricalMirror}
    (experiment : MultipleReflectionExperiment mirror) (N : ℕ)
    (xN : LengthQuantity) where
  ray : experiment.Ray
  is_parallel_incident : experiment.isParallelIncident ray
  on_positive_branch : experiment.transverseCoordinate ray = xN
  reflection_count_eq : experiment.reflectionCount ray = N
  firstImpactPoint : LengthQuantity × LengthQuantity
  first_impact_on_mirror :
    OnReflectingSemicircle mirror firstImpactPoint
  first_impact_transverse_coordinate :
    firstImpactPoint.1 = experiment.transverseCoordinate ray
  firstImpactPolarAngle : ℝ
  first_impact_angle_pos : 0 < firstImpactPolarAngle
  first_impact_angle_acute : firstImpactPolarAngle < Real.pi / 2

/-- The projection read from the right triangle in the circular cross-section:
the positive transverse SI coordinate is `R cos θ`. -/
structure HalfCircleProjectionGeometry {mirror : HalfCylindricalMirror}
    (experiment : MultipleReflectionExperiment mirror) (N : ℕ)
    (xN : LengthQuantity)
    (limiting : LimitingRayWitness experiment N xN) : Prop where
  coordinate_eq_radius_mul_cos :
    siLengthValue xN =
      siLengthValue mirror.radius *
        Real.cos limiting.firstImpactPolarAngle

/-- The angular closure obtained by repeatedly applying equal-angle reflection
to the limiting ray in a semicircle.  The `2N + 1` factor retains the endpoint
and orientation information of the positive limiting branch. -/
structure RepeatedReflectionClosure {mirror : HalfCylindricalMirror}
    (experiment : MultipleReflectionExperiment mirror) (N : ℕ)
    (xN : LengthQuantity)
    (limiting : LimitingRayWitness experiment N xN) : Prop where
  angle_closure :
    (2 * (N : ℝ) + 1) * limiting.firstImpactPolarAngle = Real.pi

/-- The governing-law interface needed from geometric optics.

The final field makes the dependency on the equal-angle law explicit: applying
specular reflection to a positive limiting threshold produces both the
half-circle projection and the `(2N+1)` angular closure.  Neither official
closed form is a field of this structure. -/
structure HalfCylinderReflectionLaws {mirror : HalfCylindricalMirror}
    (experiment : MultipleReflectionExperiment mirror) : Prop where
  obeys_specular_reflection : ObeysSpecularReflection experiment
  limiting_ray_geometry :
    ObeysSpecularReflection experiment →
      ∀ (N : ℕ) (xN : LengthQuantity),
        0 < N →
        IsPositiveReflectionThreshold experiment N xN →
        ∃ limiting : LimitingRayWitness experiment N xN,
          HalfCircleProjectionGeometry experiment N xN limiting ∧
            RepeatedReflectionClosure experiment N xN limiting

/-- Algebraic bridge from the repeated-reflection closure to the unique
limiting angle. -/
lemma limiting_first_impact_angle {mirror : HalfCylindricalMirror}
    {experiment : MultipleReflectionExperiment mirror} {N : ℕ}
    {xN : LengthQuantity} (hN : 0 < N)
    (limiting : LimitingRayWitness experiment N xN)
    (closure : RepeatedReflectionClosure experiment N xN limiting) :
    limiting.firstImpactPolarAngle =
      Real.pi / (2 * (N : ℝ) + 1) := by
  have hN_real : 0 < (N : ℝ) := by
    exact_mod_cast hN
  have hfactor_ne : 2 * (N : ℝ) + 1 ≠ 0 := by
    positivity
  apply (eq_div_iff hfactor_ne).2
  nlinarith [closure.angle_closure]

/-- The two angles occurring in the official sine and cosine answer forms are
complementary. -/
lemma official_answer_angles_complementary (N : ℕ) (hN : 0 < N) :
    Real.pi / 2 - Real.pi / (2 * (N : ℝ) + 1) =
      (2 * (N : ℝ) - 1) * Real.pi / (4 * (N : ℝ) + 2) := by
  have hN_real : 0 < (N : ℝ) := by
    exact_mod_cast hN
  have h2N1_ne : 2 * (N : ℝ) + 1 ≠ 0 := by
    positivity
  have h4N2_ne : 4 * (N : ℝ) + 2 ≠ 0 := by
    positivity
  field_simp [h2N1_ne, h4N2_ne]
  ring

/-- Trigonometric bridge between the two official closed forms.  The Mathlib
carrier for the complementary-angle step is `Real.sin_pi_div_two_sub`. -/
lemma official_sine_cosine_forms_agree (N : ℕ) (hN : 0 < N) :
    Real.sin ((2 * (N : ℝ) - 1) * Real.pi / (4 * (N : ℝ) + 2)) =
      Real.cos (Real.pi / (2 * (N : ℝ) + 1)) := by
  rw [← official_answer_angles_complementary N hN]
  exact Real.sin_pi_div_two_sub _

/-- IPhO 2026 Problem 2 A.1: the positive threshold for at most `N`
reflections in the half-cylindrical mirror has the two equivalent official
closed forms, stated on the explicitly named SI length projection. -/
theorem positive_reflection_threshold_formula
    {mirror : HalfCylindricalMirror}
    (experiment : MultipleReflectionExperiment mirror)
    (laws : HalfCylinderReflectionLaws experiment)
    (N : ℕ) (hN : 0 < N) (xN : LengthQuantity)
    (hThreshold : IsPositiveReflectionThreshold experiment N xN) :
    siLengthValue xN =
        siLengthValue mirror.radius *
          Real.sin ((2 * (N : ℝ) - 1) * Real.pi / (4 * (N : ℝ) + 2)) ∧
      siLengthValue xN =
        siLengthValue mirror.radius *
          Real.cos (Real.pi / (2 * (N : ℝ) + 1)) := by
  obtain ⟨limiting, geometry, closure⟩ :=
    laws.limiting_ray_geometry laws.obeys_specular_reflection
      N xN hN hThreshold
  have hcos := geometry.coordinate_eq_radius_mul_cos
  rw [limiting_first_impact_angle hN limiting closure] at hcos
  constructor
  · rw [official_sine_cosine_forms_agree N hN]
    exact hcos
  · exact hcos

end IPhO2026Problem2A1
