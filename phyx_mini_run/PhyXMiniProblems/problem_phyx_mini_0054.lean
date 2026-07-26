import Mathlib
import Physlib.Units.WithDim.Basic

/- USER: The source file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0054

open Dimension

/-!
# Real image formed by a hemispherical glass-rod end

The small bulb is modeled as an on-axis point object in air. Its rays cross a
single convex spherical air--glass interface and converge to a real image
inside the rod. Physical lengths are dimensionful; numerical values are scalar
readouts in centimeters. Refractive indices are dimensionless real readouts.

The primary figure reads `n₁ = 1.00`, `n₂ = 1.50`, `2R = 4.0 cm`, and
`s = 6.0 cm`. Thus the auxiliary caption's readings `R = 40 cm` and
`s = 60 cm` are treated as OCR errors.
-/

/-- A signed physical length whose readout changes coherently with unit choice. -/
abbrev LengthQuantity : Type := Dimensionful (WithDim L𝓭 ℝ)

/-- SI base units with centimeters selected as the length unit. -/
noncomputable def centimeterUnitChoices : UnitChoices :=
  { UnitChoices.SI with length := LengthUnit.centimeters }

/-- The signed scalar readout of a physical length in centimeters. -/
def lengthInCentimeters (length : LengthQuantity) : ℝ :=
  (length centimeterUnitChoices).val

/-- The two optical regions separated by the hemispherical rod surface. -/
inductive OpticalRegion where
  | ambientAir
  | glassRod
  deriving DecidableEq, Repr

/-- The three labeled points on the optical axis in the primary figure. -/
inductive FigurePoint where
  | object
  | surfaceVertex
  | image
  deriving DecidableEq, Repr

/-- Whether the depicted image is formed by rays or by backward extensions. -/
inductive GeometricalImageKind where
  | real
  | virtual
  deriving DecidableEq, Repr

/-!
The dimensionful and dimensionless quantities in the rod setup.

The surface radius is positive for the convex surface whose center of
curvature lies inside the glass. The axial positions increase from the bulb,
through the surface vertex, into the rod.
-/
structure HemisphericalGlassRodSetup where
  axisPosition : FigurePoint → LengthQuantity
  rodDiameter : LengthQuantity
  surfaceRadius : LengthQuantity
  refractiveIndex : OpticalRegion → ℝ
  objectRegion : OpticalRegion
  imageRegion : OpticalRegion
  imageKind : GeometricalImageKind

/-- Signed separation of two figure points, read in a specified unit system. -/
def axialSeparationReadout
    (setup : HemisphericalGlassRodSetup) (units : UnitChoices)
    (left right : FigurePoint) : ℝ :=
  (setup.axisPosition right units).val - (setup.axisPosition left units).val

/-- The positive object-distance readout `s`, from the bulb to the vertex. -/
def objectDistanceReadout
    (setup : HemisphericalGlassRodSetup) (units : UnitChoices) : ℝ :=
  axialSeparationReadout setup units .object .surfaceVertex

/-- The positive real-image-distance readout `s'`, from the vertex into the rod. -/
def imageDistanceReadout
    (setup : HemisphericalGlassRodSetup) (units : UnitChoices) : ℝ :=
  axialSeparationReadout setup units .surfaceVertex .image

/-- The object distance in the centimeter unit system used by the figure. -/
def objectDistanceInCentimeters (setup : HemisphericalGlassRodSetup) : ℝ :=
  objectDistanceReadout setup centimeterUnitChoices

/-- The requested real-image distance in centimeters. -/
def imageDistanceInCentimeters (setup : HemisphericalGlassRodSetup) : ℝ :=
  imageDistanceReadout setup centimeterUnitChoices

/-!
Problem-statement and primary-figure data. The image is explicitly depicted as
a real convergence point in the glass. No numerical value for its distance is
included here.
-/
structure MatchesProblemAndPrimaryFigure
    (setup : HemisphericalGlassRodSetup) : Prop where
  rod_diameter_readout : lengthInCentimeters setup.rodDiameter = 4
  object_distance_readout : objectDistanceInCentimeters setup = 6
  incident_index_readout : setup.refractiveIndex .ambientAir = 1
  transmitted_index_readout : setup.refractiveIndex .glassRod = 3 / 2
  object_is_in_air : setup.objectRegion = .ambientAir
  image_is_in_glass : setup.imageRegion = .glassRod
  image_is_real : setup.imageKind = .real

/-!
Geometric meaning of “one end of the rod is shaped like a hemisphere”:
the spherical surface radius is half the rod diameter. This is setup geometry,
not the requested image-distance result.
-/
def ModelsHemisphericalRodEnd (setup : HemisphericalGlassRodSetup) : Prop :=
  ∀ units : UnitChoices,
    (setup.surfaceRadius units).val = (setup.rodDiameter units).val / 2

/-- Positivity and axial-order conditions for the physical branch in the figure. -/
structure HasDepictedPhysicalConfiguration
    (setup : HemisphericalGlassRodSetup) : Prop where
  diameter_positive : 0 < lengthInCentimeters setup.rodDiameter
  radius_positive : 0 < lengthInCentimeters setup.surfaceRadius
  object_distance_positive : 0 < objectDistanceInCentimeters setup
  image_distance_positive : 0 < imageDistanceInCentimeters setup
  refractive_indices_positive :
    ∀ region : OpticalRegion, 0 < setup.refractiveIndex region
  glass_optically_denser :
    setup.refractiveIndex .ambientAir < setup.refractiveIndex .glassRod

/-!
The Gaussian paraxial equation for refraction at one convex spherical surface,
written with positive object distance `s`, positive real-image distance `s'`,
and positive radius `R`:

`n₁ / s + n₂ / s' = (n₂ - n₁) / R`.

It is required for every unit choice, so it is a dimensionally coherent
governing law rather than a formula specialized to the requested answer.
-/
def ObeysParaxialSphericalSurfaceEquation
    (setup : HemisphericalGlassRodSetup) : Prop :=
  ∀ units : UnitChoices,
    setup.refractiveIndex .ambientAir / objectDistanceReadout setup units +
        setup.refractiveIndex .glassRod / imageDistanceReadout setup units =
      (setup.refractiveIndex .glassRod -
          setup.refractiveIndex .ambientAir) /
        (setup.surfaceRadius units).val

/-- Labels of the four displayed answer choices. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- The centimeter readout printed beside each answer choice. -/
def answerImageDistanceInCentimeters : AnswerChoice → ℝ
  | .A => 14
  | .B => 18
  | .C => 96
  | .D => 74

/-- Agreement of the physical image-distance readout with a displayed choice. -/
def MatchesAnswerChoice
    (setup : HemisphericalGlassRodSetup) (choice : AnswerChoice) : Prop :=
  imageDistanceInCentimeters setup =
    answerImageDistanceInCentimeters choice

/-- The `4.0 cm` diameter and hemispherical geometry give `R = 2.0 cm`. -/
lemma surfaceRadiusInCentimeters_eq_two
    (setup : HemisphericalGlassRodSetup)
    (_figure : MatchesProblemAndPrimaryFigure setup)
    (_hemisphere : ModelsHemisphericalRodEnd setup) :
    lengthInCentimeters setup.surfaceRadius = 2 := by
  have h_radius := _hemisphere centimeterUnitChoices
  have h_diameter := _figure.rod_diameter_readout
  change (setup.surfaceRadius centimeterUnitChoices).val =
    (setup.rodDiameter centimeterUnitChoices).val / 2 at h_radius
  change (setup.rodDiameter centimeterUnitChoices).val = 4 at h_diameter
  change (setup.surfaceRadius centimeterUnitChoices).val = 2
  rw [h_radius, h_diameter]
  norm_num

/-!
For the `4.0 cm` diameter glass rod, `6.0 cm` object distance, and refractive
indices `n₁ = 1.00`, `n₂ = 1.50`, the real image is `18 cm` inside the rod,
which is answer choice B.

This formalizes `thm:physics:phyx_mini_0054:target`.
-/
theorem problem_phyx_mini_0054
    (setup : HemisphericalGlassRodSetup)
    (_figure : MatchesProblemAndPrimaryFigure setup)
    (_hemisphere : ModelsHemisphericalRodEnd setup)
    (_physical : HasDepictedPhysicalConfiguration setup)
    (_refraction : ObeysParaxialSphericalSurfaceEquation setup) :
    imageDistanceInCentimeters setup = 18 ∧
      MatchesAnswerChoice setup .B := by
  have h_radius :=
    surfaceRadiusInCentimeters_eq_two setup _figure _hemisphere
  have h_refraction := _refraction centimeterUnitChoices
  have h_image_positive := _physical.image_distance_positive
  change
    setup.refractiveIndex .ambientAir / objectDistanceInCentimeters setup +
        setup.refractiveIndex .glassRod / imageDistanceInCentimeters setup =
      (setup.refractiveIndex .glassRod -
          setup.refractiveIndex .ambientAir) /
        lengthInCentimeters setup.surfaceRadius at h_refraction
  rw [_figure.incident_index_readout, _figure.transmitted_index_readout,
    _figure.object_distance_readout, h_radius] at h_refraction
  have h_image_nonzero : imageDistanceInCentimeters setup ≠ 0 :=
    ne_of_gt h_image_positive
  field_simp [h_image_nonzero] at h_refraction
  have h_image : imageDistanceInCentimeters setup = 18 := by
    nlinarith
  constructor
  · exact h_image
  · simpa [MatchesAnswerChoice, answerImageDistanceInCentimeters] using h_image

end PhyXMiniProblems.ProblemPhyXMini0054
