import Mathlib
import Physlib.Units.WithDim.Basic

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0033

open Dimension

/-!
# Paraxial focusing by a glass hemisphere

A parallel beam enters the flat face of a glass hemisphere normally, travels
through the glass without acquiring vergence at that plane face, and leaves
through the spherical face into air. The figure labels the magnitude of the
spherical radius by `R`, the axial focus by `I`, and the distance from the
spherical exit vertex to `I` by `q`.

Lengths remain dimensionful physical quantities. Refractive indices and ray
angles are dimensionless, while optical vergences below are scalar readouts in
inverse centimeters so that the paraxial surface law is unit-consistent.
-/

/-- A physical length, independent of the unit used to read it. -/
abbrev LengthQuantity : Type := Dimensionful (WithDim L𝓭 ℝ)

/-- The scalar centimeter readout of a physical length. -/
def lengthInCentimeters (length : LengthQuantity) : ℝ :=
  (length { UnitChoices.SI with length := LengthUnit.centimeters }).val

/-- The two homogeneous optical media traversed by the pictured beam. -/
inductive OpticalMedium where
  | ambientAir
  | glass
  deriving DecidableEq, Repr

/-- The two refracting surfaces met from left to right in the figure. -/
inductive OpticalSurfaceLabel where
  | flatEntranceFace
  | sphericalExitFace
  deriving DecidableEq, Repr

/-- The medium on the incident side of each labeled surface. -/
def incidentMedium : OpticalSurfaceLabel → OpticalMedium
  | .flatEntranceFace => .ambientAir
  | .sphericalExitFace => .glass

/-- The medium on the transmitted side of each labeled surface. -/
def transmittedMedium : OpticalSurfaceLabel → OpticalMedium
  | .flatEntranceFace => .glass
  | .sphericalExitFace => .ambientAir

/-- Whether the ray model uses full ray tracing or the stated paraxial model. -/
inductive OpticalApproximation where
  | exactRayTracing
  | paraxial
  deriving DecidableEq, Repr

/--
Physical quantities and scalar ray readouts in the hemispherical-lens diagram.

`radiusR` is the positive magnitude `R`. `flatFaceToExitVertex` records the
hemisphere geometry. `focusDistanceQ` is the signed axial distance `q` from
the spherical exit vertex to the focus `I`, positive in the direction of
propagation. The two vergence fields are measured in inverse centimeters.
-/
structure HemisphericalLensSetup where
  radiusR : LengthQuantity
  flatFaceToExitVertex : LengthQuantity
  focusDistanceQ : LengthQuantity
  refractiveIndex : OpticalMedium → ℝ
  flatFaceIncidenceAngleRadians : ℝ
  inGlassAngleAtFlatFaceRadians : ℝ
  incidentVergencePerCentimeter : ℝ
  inGlassVergencePerCentimeter : ℝ
  approximation : OpticalApproximation

/--
The surface center is to the left of the exit vertex, so its signed radius is
negative when the propagation direction (left to right) is positive.
-/
def signedExitRadiusInCentimeters (setup : HemisphericalLensSetup) : ℝ :=
  -lengthInCentimeters setup.radiusR

/--
Branch, positivity, and hemisphere conditions for the physical configuration.
In particular, the focus `I` is a real point in the outgoing air region.
-/
def HasPhysicalHemisphericalConfiguration
    (setup : HemisphericalLensSetup) : Prop :=
  0 < lengthInCentimeters setup.radiusR ∧
    setup.flatFaceToExitVertex = setup.radiusR ∧
    0 < lengthInCentimeters setup.focusDistanceQ ∧
    ∀ medium, 0 < setup.refractiveIndex medium

/--
Problem and figure readouts: `R = 6.00 cm`, glass index `n = 1.560`, air
index one, a parallel incident beam, normal incidence at the flat face, and
the paraxial approximation requested in the question.
-/
def MatchesFigureReadouts (setup : HemisphericalLensSetup) : Prop :=
  lengthInCentimeters setup.radiusR = 6.00 ∧
    setup.refractiveIndex .glass = 1.560 ∧
    setup.refractiveIndex .ambientAir = 1 ∧
    setup.incidentVergencePerCentimeter = 0 ∧
    setup.flatFaceIncidenceAngleRadians = 0 ∧
    setup.approximation = .paraxial

/--
The governing paraxial law at the plane entrance face. Its surface power is
zero, so optical vergence is preserved; paraxial Snell refraction relates the
two angles from the normal.
-/
def SatisfiesFlatFaceParaxialRefraction
    (setup : HemisphericalLensSetup) : Prop :=
  setup.inGlassVergencePerCentimeter =
      setup.incidentVergencePerCentimeter ∧
    setup.refractiveIndex (incidentMedium .flatEntranceFace) *
        setup.flatFaceIncidenceAngleRadians =
      setup.refractiveIndex (transmittedMedium .flatEntranceFace) *
        setup.inGlassAngleAtFlatFaceRadians

/--
The governing paraxial vergence law `L' = L + (n₂ - n₁) / r` at the
spherical glass-to-air surface. Here `L' = n_air / q`; `r` is negative by
the figure orientation. This is a general physical relation and contains no
numerical value for the requested distance `q`.
-/
def SatisfiesSphericalFaceParaxialRefraction
    (setup : HemisphericalLensSetup) : Prop :=
  setup.inGlassVergencePerCentimeter +
      (setup.refractiveIndex (transmittedMedium .sphericalExitFace) -
          setup.refractiveIndex (incidentMedium .sphericalExitFace)) /
        signedExitRadiusInCentimeters setup =
    setup.refractiveIndex (transmittedMedium .sphericalExitFace) /
      lengthInCentimeters setup.focusDistanceQ

/-- The four focus-distance choices printed in the problem, in centimeters. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- The scalar centimeter readout displayed beside each answer choice. -/
def answerDistanceInCentimeters : AnswerChoice → ℝ
  | .A => 14.4
  | .B => 5.2
  | .C => 6.2
  | .D => 10.7

/-- Agreement with a displayed focus distance to the nearest tenth centimeter. -/
def MatchesAnswerToNearestTenth
    (distance : LengthQuantity) (choice : AnswerChoice) : Prop :=
  |lengthInCentimeters distance - answerDistanceInCentimeters choice| ≤ 0.05

/--
Normal incidence and the zero power of the plane face leave the beam axial
and parallel while it travels inside the glass.
-/
lemma internalBeam_is_parallel_and_axial
    (setup : HemisphericalLensSetup)
    (h_physical : HasPhysicalHemisphericalConfiguration setup)
    (h_figure : MatchesFigureReadouts setup)
    (h_flat : SatisfiesFlatFaceParaxialRefraction setup) :
    setup.inGlassVergencePerCentimeter = 0 ∧
      setup.inGlassAngleAtFlatFaceRadians = 0 := by
  rcases h_figure with ⟨_, h_glass, h_air, h_incident, h_angle, _⟩
  rcases h_flat with ⟨h_vergence, h_snell⟩
  constructor
  · linarith
  · simp only [incidentMedium, transmittedMedium] at h_snell
    rw [h_glass, h_air, h_angle] at h_snell
    norm_num at h_snell ⊢
    linarith

/--
The spherical paraxial refraction law gives the exact exit-vertex-to-focus
distance `q = 75/7 cm` (approximately `10.714 cm`).
-/
lemma focusDistanceQ_eq
    (setup : HemisphericalLensSetup)
    (h_physical : HasPhysicalHemisphericalConfiguration setup)
    (h_figure : MatchesFigureReadouts setup)
    (h_flat : SatisfiesFlatFaceParaxialRefraction setup)
    (h_spherical : SatisfiesSphericalFaceParaxialRefraction setup) :
    lengthInCentimeters setup.focusDistanceQ = 75 / 7 := by
  have h_internal :=
    internalBeam_is_parallel_and_axial setup h_physical h_figure h_flat
  rcases h_internal with ⟨h_vergence, _⟩
  rcases h_physical with ⟨_, _, h_focus_positive, _⟩
  rcases h_figure with ⟨h_radius, h_glass, h_air, _, _, _⟩
  simp only [SatisfiesSphericalFaceParaxialRefraction, incidentMedium,
    transmittedMedium, signedExitRadiusInCentimeters] at h_spherical
  rw [h_vergence, h_radius, h_glass, h_air] at h_spherical
  have h_focus_ne :
      lengthInCentimeters setup.focusDistanceQ ≠ 0 :=
    ne_of_gt h_focus_positive
  field_simp [h_focus_ne] at h_spherical
  norm_num at h_spherical ⊢
  linarith

/--
The focus `I` lies `75/7 cm` beyond the spherical exit vertex. This rounds to
`10.7 cm`, answer choice D.

This formalizes `thm:physics:phyx_mini_0033:target`.
-/
theorem problem_phyx_mini_0033
    (setup : HemisphericalLensSetup)
    (h_physical : HasPhysicalHemisphericalConfiguration setup)
    (h_figure : MatchesFigureReadouts setup)
    (h_flat : SatisfiesFlatFaceParaxialRefraction setup)
    (h_spherical : SatisfiesSphericalFaceParaxialRefraction setup) :
    lengthInCentimeters setup.focusDistanceQ = 75 / 7 ∧
      MatchesAnswerToNearestTenth setup.focusDistanceQ .D := by
  have h_focus :=
    focusDistanceQ_eq setup h_physical h_figure h_flat h_spherical
  constructor
  · exact h_focus
  · rw [MatchesAnswerToNearestTenth, h_focus]
    norm_num [answerDistanceInCentimeters, abs_of_nonneg]

end PhyXMiniProblems.ProblemPhyXMini0033
