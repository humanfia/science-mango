import Mathlib
import Physlib.Units.WithDim.Basic

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0067

open Dimension

/-!
# Focal length of a polystyrene meniscus lens

The primary image shows a meniscus lens and two radius constructions from its
surfaces to centers on the optical axis.  Their labels are `30 cm` and `40 cm`.
The optical axis is oriented from left to right, so both signed radii are
positive in the convention used below.

Lengths are genuine Physlib dimensionful quantities.  Real numbers occur only
as scalar readouts in a specified length unit and as dimensionless refractive
indices.
-/

/-- A signed physical optical length, independent of a choice of units. -/
abbrev OpticalLength : Type := Dimensionful (WithDim L𝓭 ℝ)

/-- The signed scalar readout of an optical length in the selected unit. -/
def lengthReadout (unit : LengthUnit) (length : OpticalLength) : ℝ :=
  (length { UnitChoices.SI with length := unit }).val

/-- The homogeneous optical media relevant to the lensmaker model. -/
inductive OpticalMedium where
  | ambientAir
  | polystyrenePlastic
  deriving DecidableEq, Repr

/-- The cross-sectional lens profile explicitly named in the problem. -/
inductive LensProfile where
  | meniscus
  deriving DecidableEq, Repr

/-- The optical approximation used by the governing lensmaker equation. -/
inductive OpticalApproximation where
  | paraxialThinLens
  deriving DecidableEq, Repr

/-- The two refracting surfaces in left-to-right propagation order. -/
inductive LensSurface where
  | front
  | back
  deriving DecidableEq, Repr

/-- Axial points determined by the two spherical-surface constructions. -/
inductive AxisPoint where
  | frontVertex
  | backVertex
  | frontCenterOfCurvature
  | backCenterOfCurvature
  deriving DecidableEq, Repr

/-- The axial vertex belonging to a refracting surface. -/
def LensSurface.vertex : LensSurface → AxisPoint
  | .front => .frontVertex
  | .back => .backVertex

/-- The axial center of curvature belonging to a refracting surface. -/
def LensSurface.centerOfCurvature : LensSurface → AxisPoint
  | .front => .frontCenterOfCurvature
  | .back => .backCenterOfCurvature

/--
Physical quantities attached to the polystyrene meniscus-lens diagram.
`axialPosition` is a signed coordinate on the displayed optical axis;
`focalLength` is the signed effective focal length of the complete lens.
-/
structure MeniscusLensSetup where
  profile : LensProfile
  approximation : OpticalApproximation
  lensMedium : OpticalMedium
  surroundingMedium : OpticalMedium
  refractiveIndexDimensionless : OpticalMedium → ℝ
  axialPosition : AxisPoint → OpticalLength
  focalLength : OpticalLength

/-- Signed axial separation from `start` to `finish`. -/
def axialSeparationReadout
    (setup : MeniscusLensSetup) (unit : LengthUnit)
    (start finish : AxisPoint) : ℝ :=
  lengthReadout unit (setup.axialPosition finish) -
    lengthReadout unit (setup.axialPosition start)

/--
The signed spherical radius of a surface.  It is positive when its center of
curvature is to the right of its vertex on the oriented optical axis.
-/
def signedSurfaceRadiusReadout
    (setup : MeniscusLensSetup) (unit : LengthUnit)
    (surface : LensSurface) : ℝ :=
  axialSeparationReadout setup unit surface.vertex surface.centerOfCurvature

/--
Data read directly from the primary figure: a meniscus profile, radius labels
`30 cm` and `40 cm`, and the depicted left-to-right ordering of the vertices
and centers.  No focal-length value occurs in this predicate.
-/
structure MatchesPrimaryFigure (setup : MeniscusLensSetup) : Prop where
  profile_is_meniscus : setup.profile = .meniscus
  front_radius_label :
    signedSurfaceRadiusReadout setup LengthUnit.centimeters .front = 30
  back_radius_label :
    signedSurfaceRadiusReadout setup LengthUnit.centimeters .back = 40
  front_vertex_before_back_vertex :
    lengthReadout LengthUnit.centimeters
        (setup.axialPosition .frontVertex) <
      lengthReadout LengthUnit.centimeters
        (setup.axialPosition .backVertex)
  back_vertex_before_front_center :
    lengthReadout LengthUnit.centimeters
        (setup.axialPosition .backVertex) <
      lengthReadout LengthUnit.centimeters
        (setup.axialPosition .frontCenterOfCurvature)
  front_center_before_back_center :
    lengthReadout LengthUnit.centimeters
        (setup.axialPosition .frontCenterOfCurvature) <
      lengthReadout LengthUnit.centimeters
        (setup.axialPosition .backCenterOfCurvature)

/--
Material-table and modeling data implicit in “polystyrene plastic lens”:
the lens is in air, the idealized refractive indices are `1.6` and `1`, and
the thin paraxial approximation is selected.  These are input data rather
than a statement of the requested focal length.
-/
structure MatchesPolystyreneThinLensModel (setup : MeniscusLensSetup) : Prop where
  approximation_is_paraxial_thin_lens :
    setup.approximation = .paraxialThinLens
  lens_medium_is_polystyrene : setup.lensMedium = .polystyrenePlastic
  surrounding_medium_is_air : setup.surroundingMedium = .ambientAir
  polystyrene_index :
    setup.refractiveIndexDimensionless .polystyrenePlastic = 8 / 5
  air_index : setup.refractiveIndexDimensionless .ambientAir = 1

/-- Positivity and nondegeneracy conditions for the depicted optical branch. -/
structure HasPhysicalConfiguration (setup : MeniscusLensSetup) : Prop where
  lens_index_positive :
    0 < setup.refractiveIndexDimensionless setup.lensMedium
  surrounding_index_positive :
    0 < setup.refractiveIndexDimensionless setup.surroundingMedium
  front_radius_positive :
    0 < signedSurfaceRadiusReadout setup LengthUnit.centimeters .front
  back_radius_positive :
    0 < signedSurfaceRadiusReadout setup LengthUnit.centimeters .back
  focal_length_positive :
    0 < lengthReadout LengthUnit.centimeters setup.focalLength

/--
The thin-lens lensmaker equation in a common surrounding medium,

`1 / f = (n_lens / n_medium - 1) (1 / R_front - 1 / R_back)`.

It is stated for every length unit, so both sides transform as inverse length.
This governing law contains no numerical focal-length answer.
-/
def SatisfiesThinLensmakerEquation (setup : MeniscusLensSetup) : Prop :=
  ∀ unit : LengthUnit,
    1 / lengthReadout unit setup.focalLength =
      (setup.refractiveIndexDimensionless setup.lensMedium /
          setup.refractiveIndexDimensionless setup.surroundingMedium - 1) *
        (1 / signedSurfaceRadiusReadout setup unit .front -
          1 / signedSurfaceRadiusReadout setup unit .back)

/-- Labels of the four answer choices printed with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- The whole-centimeter focal length printed beside each answer choice. -/
def displayedFocalLengthInCentimeters : AnswerChoice → ℝ
  | .A => 24
  | .B => 56
  | .C => 20
  | .D => 28

/-- The answer label recorded by the dataset. -/
def recordedAnswerChoice : AnswerChoice := .C

/-- Exact agreement between the modeled focal length and a displayed choice. -/
def MatchesDisplayedFocalLength
    (setup : MeniscusLensSetup) (choice : AnswerChoice) : Prop :=
  lengthReadout LengthUnit.centimeters setup.focalLength =
    displayedFocalLengthInCentimeters choice

/-- The source's recorded claim that choice C, `20 cm`, is the answer. -/
def RecordedAnswerClaim (setup : MeniscusLensSetup) : Prop :=
  MatchesDisplayedFocalLength setup recordedAnswerChoice

/--
With the image's `30 cm` and `40 cm` signed radii and the idealized
polystyrene index `1.6`, the thin-lens lensmaker equation gives `f = 200 cm`.
-/
lemma focalLengthInCentimeters_eq_twoHundred
    (setup : MeniscusLensSetup)
    (_figure : MatchesPrimaryFigure setup)
    (_model : MatchesPolystyreneThinLensModel setup)
    (_physical : HasPhysicalConfiguration setup)
    (_lensmaker : SatisfiesThinLensmakerEquation setup) :
    lengthReadout LengthUnit.centimeters setup.focalLength = 200 := by
  have h := _lensmaker LengthUnit.centimeters
  rw [_figure.front_radius_label, _figure.back_radius_label,
    _model.lens_medium_is_polystyrene,
    _model.surrounding_medium_is_air,
    _model.polystyrene_index, _model.air_index] at h
  norm_num at h
  have hne : lengthReadout LengthUnit.centimeters setup.focalLength ≠ 0 :=
    ne_of_gt _physical.focal_length_positive
  field_simp [hne] at h
  linarith

/--
The physically grounded result is `200 cm`, so none of the displayed choices
matches exactly and in particular the dataset's recorded `20 cm` claim does
not follow from the primary image.

This formalizes `thm:physics:phyx_mini_0067:target` while exposing the
factor-of-ten discrepancy between the source image and its recorded answer.
-/
theorem problem_phyx_mini_0067
    (setup : MeniscusLensSetup)
    (_figure : MatchesPrimaryFigure setup)
    (_model : MatchesPolystyreneThinLensModel setup)
    (_physical : HasPhysicalConfiguration setup)
    (_lensmaker : SatisfiesThinLensmakerEquation setup) :
    lengthReadout LengthUnit.centimeters setup.focalLength = 200 ∧
      (∀ choice : AnswerChoice, ¬ MatchesDisplayedFocalLength setup choice) ∧
      ¬ RecordedAnswerClaim setup := by
  have hf :=
    focalLengthInCentimeters_eq_twoHundred
      setup _figure _model _physical _lensmaker
  refine ⟨hf, ?_, ?_⟩
  · intro choice
    cases choice <;>
      simp [MatchesDisplayedFocalLength, displayedFocalLengthInCentimeters, hf]
  · simp [RecordedAnswerClaim, MatchesDisplayedFocalLength, recordedAnswerChoice,
      displayedFocalLengthInCentimeters, hf]

end PhyXMiniProblems.ProblemPhyXMini0067
