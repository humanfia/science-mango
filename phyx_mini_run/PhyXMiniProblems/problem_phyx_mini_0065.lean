import Mathlib
import Physlib.SpaceAndTime.Space.LengthUnit
import Physlib.Units.WithDim.Basic

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0065

open Dimension

/-!
# Focal length of a planoconvex polystyrene lens

The primary figure shows a planoconvex lens on a horizontal principal axis.
Its curved face is on the left, its planar face is on the right, and the
`40 cm` arrow joins the marked center of curvature to the curved surface.
Thus `40 cm` is the spherical-face radius, rather than the requested focal
length.

Lengths are represented by Physlib dimensionful quantities.  Real numbers
are used only for dimensionless refractive indices and scalar readouts in a
stated unit.  The optical calculation uses the paraxial thin-lens lensmaker
equation for a lens in air.
-/

/-- A signed physical length whose scalar readout changes coherently with units. -/
abbrev LengthQuantity : Type := Dimensionful (WithDim L𝓭 ℝ)

/-- SI base units with centimeters selected as the length unit. -/
noncomputable def centimeterUnitChoices : UnitChoices :=
  { UnitChoices.SI with length := LengthUnit.centimeters }

/-- The scalar centimeter readout of a dimensionful length. -/
def lengthInCentimeters (length : LengthQuantity) : ℝ :=
  (length centimeterUnitChoices).val

/-- The two homogeneous media in the optical model. -/
inductive OpticalMedium where
  | ambientAir
  | polystyrenePlastic
  deriving DecidableEq, Repr

/-- The two physical faces of the lens. -/
inductive LensFace where
  | planarFace
  | convexFace
  deriving DecidableEq, Repr

/-- Left and right sides of the horizontal principal axis in the figure. -/
inductive AxisSide where
  | left
  | right
  deriving DecidableEq, Repr

/-- Geometrical roles of the two endpoints of the `40 cm` arrow. -/
inductive RadiusArrowEndpoint where
  | centerOfCurvature
  | pointOnCurvedSurface
  deriving DecidableEq, Repr

/-- A lens face is either planar or spherical with a physical radius magnitude. -/
inductive LensSurfaceProfile where
  | planar
  | spherical (radiusMagnitude : LengthQuantity)

/-- The planoconvex lens and the physical quantity requested by the problem. -/
structure PlanoConvexLens where
  surfaceProfile : LensFace → LensSurfaceProfile
  curvedSurfaceRadiusMagnitude : LengthQuantity
  focalLength : LengthQuantity
  lensMedium : OpticalMedium
  exteriorMedium : OpticalMedium
  refractiveIndex : OpticalMedium → ℝ

/-- The dimensionful radius annotation printed in the primary figure. -/
structure RadiusArrowAnnotation where
  fromEndpoint : RadiusArrowEndpoint
  toEndpoint : RadiusArrowEndpoint
  indicatedLength : LengthQuantity

/-- Qualitative geometry and quantitative annotation read from the figure. -/
structure PlanoConvexFigure where
  curvedFaceSide : AxisSide
  planarFaceSide : AxisSide
  curvatureCenterSide : AxisSide
  principalAxisIsHorizontal : Bool
  radiusArrow : RadiusArrowAnnotation

/-- The lens together with its associated source figure. -/
structure PlanoConvexLensSetup where
  lens : PlanoConvexLens
  figure : PlanoConvexFigure

/-!
Problem and primary-figure readouts.  The arrow endpoints record its geometric
meaning, and its indicated length is identified with the lens's spherical
radius.  No focal-length value occurs in these data.
-/
structure MatchesProblemAndFigure
    (setup : PlanoConvexLensSetup) : Prop where
  lens_is_polystyrene :
    setup.lens.lensMedium = .polystyrenePlastic
  exterior_is_air :
    setup.lens.exteriorMedium = .ambientAir
  planar_face_profile :
    setup.lens.surfaceProfile .planarFace = .planar
  convex_face_profile :
    setup.lens.surfaceProfile .convexFace =
      .spherical setup.lens.curvedSurfaceRadiusMagnitude
  curved_face_is_left :
    setup.figure.curvedFaceSide = .left
  planar_face_is_right :
    setup.figure.planarFaceSide = .right
  curvature_center_is_right :
    setup.figure.curvatureCenterSide = .right
  principal_axis_is_horizontal :
    setup.figure.principalAxisIsHorizontal = true
  radius_arrow_starts_at_center :
    setup.figure.radiusArrow.fromEndpoint = .centerOfCurvature
  radius_arrow_ends_on_surface :
    setup.figure.radiusArrow.toEndpoint = .pointOnCurvedSurface
  radius_arrow_is_lens_radius :
    setup.figure.radiusArrow.indicatedLength =
      setup.lens.curvedSurfaceRadiusMagnitude
  radius_readout_centimeters :
    lengthInCentimeters setup.figure.radiusArrow.indicatedLength = 40

/-!
The standard dimensionless refractive-index data used for the named media:
ordinary air has index `1`, and polystyrene plastic has index `1.59`.
These are material data, not a statement of the requested focal length.
-/
structure UsesStandardMaterialIndices
    (setup : PlanoConvexLensSetup) : Prop where
  air_index : setup.lens.refractiveIndex .ambientAir = 1
  polystyrene_index :
    setup.lens.refractiveIndex .polystyrenePlastic = 159 / 100

/-- Positivity and optical-density conditions selecting the physical branch. -/
structure HasPhysicalOpticalParameters
    (setup : PlanoConvexLensSetup) : Prop where
  radius_positive :
    0 < lengthInCentimeters setup.lens.curvedSurfaceRadiusMagnitude
  focal_length_positive :
    0 < lengthInCentimeters setup.lens.focalLength
  refractive_indices_positive :
    ∀ medium : OpticalMedium, 0 < setup.lens.refractiveIndex medium
  lens_optically_denser_than_air :
    setup.lens.refractiveIndex .ambientAir <
      setup.lens.refractiveIndex .polystyrenePlastic

/-!
The paraxial thin-lens lensmaker equation for one planar face and one convex
spherical face,

`1 / f = (n_lens / n_air - 1) / R`.

The equation is required in every unit choice, so it is dimensionally
coherent.  It is a governing physical law and contains no numerical value for
the requested focal length.
-/
def ObeysParaxialPlanoConvexLensmakerEquation
    (setup : PlanoConvexLensSetup) : Prop :=
  ∀ units : UnitChoices,
    1 / (setup.lens.focalLength units).val =
      (setup.lens.refractiveIndex setup.lens.lensMedium /
          setup.lens.refractiveIndex setup.lens.exteriorMedium - 1) *
        (1 / (setup.lens.curvedSurfaceRadiusMagnitude units).val)

/-- Labels of the four displayed multiple-choice answers. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- The whole-centimeter focal-length readout printed beside each choice. -/
def answerFocalLengthInCentimeters : AnswerChoice → ℝ
  | .A => 24
  | .B => 56
  | .C => 68
  | .D => 80

/-- Agreement of an exact focal length with a displayed nearest-centimeter choice. -/
def MatchesAnswerToNearestCentimeter
    (exactFocalLengthInCentimeters : ℝ) (choice : AnswerChoice) : Prop :=
  |exactFocalLengthInCentimeters -
      answerFocalLengthInCentimeters choice| ≤ 1 / 2

/-!
The radius, material indices, and lensmaker equation determine the exact
thin-lens focal-length readout `4000/59 cm`.
-/
lemma focalLengthInCentimeters_eq_four_thousand_over_fifty_nine
    (setup : PlanoConvexLensSetup)
    (_figure : MatchesProblemAndFigure setup)
    (_indices : UsesStandardMaterialIndices setup)
    (_physical : HasPhysicalOpticalParameters setup)
    (_lensmaker : ObeysParaxialPlanoConvexLensmakerEquation setup) :
    lengthInCentimeters setup.lens.focalLength = (4000 / 59 : ℝ) := by
  have h_radius :
      lengthInCentimeters setup.lens.curvedSurfaceRadiusMagnitude = 40 := by
    rw [← _figure.radius_arrow_is_lens_radius]
    exact _figure.radius_readout_centimeters
  have h_lensmaker := _lensmaker centimeterUnitChoices
  change 1 / lengthInCentimeters setup.lens.focalLength =
      (setup.lens.refractiveIndex setup.lens.lensMedium /
          setup.lens.refractiveIndex setup.lens.exteriorMedium - 1) *
        (1 / lengthInCentimeters setup.lens.curvedSurfaceRadiusMagnitude)
    at h_lensmaker
  rw [_figure.lens_is_polystyrene, _figure.exterior_is_air,
    _indices.polystyrene_index, _indices.air_index, h_radius] at h_lensmaker
  have hf_ne : lengthInCentimeters setup.lens.focalLength ≠ 0 :=
    ne_of_gt _physical.focal_length_positive
  field_simp [hf_ne] at h_lensmaker
  apply (eq_div_iff (by norm_num : (59 : ℝ) ≠ 0)).2
  linarith

/-!
For a `40 cm`-radius planoconvex polystyrene lens in air, lensmaker's law
gives the exact paraxial focal length `4000/59 cm`, approximately `67.80 cm`.
It therefore matches the displayed whole-centimeter value `68 cm`, answer
choice C.

This formalizes blueprint label `thm:physics:phyx_mini_0065:target`.
-/
theorem problem_phyx_mini_0065
    (setup : PlanoConvexLensSetup)
    (_figure : MatchesProblemAndFigure setup)
    (_indices : UsesStandardMaterialIndices setup)
    (_physical : HasPhysicalOpticalParameters setup)
    (_lensmaker : ObeysParaxialPlanoConvexLensmakerEquation setup) :
    lengthInCentimeters setup.lens.focalLength = (4000 / 59 : ℝ) ∧
      MatchesAnswerToNearestCentimeter
        (lengthInCentimeters setup.lens.focalLength) .C := by
  have h_exact := focalLengthInCentimeters_eq_four_thousand_over_fifty_nine
    setup _figure _indices _physical _lensmaker
  constructor
  · exact h_exact
  · rw [h_exact]
    norm_num [MatchesAnswerToNearestCentimeter, answerFocalLengthInCentimeters,
      abs_of_nonpos]

end PhyXMiniProblems.ProblemPhyXMini0065
