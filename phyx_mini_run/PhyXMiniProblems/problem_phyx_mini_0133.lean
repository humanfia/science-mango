import Mathlib
import Physlib.Units.WithDim.Basic

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0133

open Dimension

/-!
# Focal length of a convex meniscus lens

The primary figure shows a convex-meniscus glass lens, with both curvature
centres `C₁` and `C₂` to the right of their respective surface vertices.  It
labels the first radius `R₁ = 22 cm` and draws the second radius arrow from
`C₂` back toward the lens with label `R₂ = -46 cm`.

The negative sign on the second *figure arrow* is kept separately from the
Cartesian surface-to-centre radius used in lensmaker's equation.  In that
convention both lensmaker radii are positive: `+22 cm` and `+46 cm`.  This
distinction is necessary for the depicted positive meniscus and the recorded
answer to be mutually consistent.

Every focal length, radius, radius annotation, and axial position below is a
dimensionful physical length.  Real numbers are used only for unit readouts
and dimensionless refractive indices.
-/

/-- A signed, unit-independent physical quantity carrying length dimension. -/
abbrev OpticalLength : Type := Dimensionful (WithDim L𝓭 ℝ)

/-- Read a signed physical length as a real number in a selected length unit. -/
def lengthReadout (unit : LengthUnit) (length : OpticalLength) : ℝ :=
  (length { UnitChoices.SI with length := unit }).val

/-- The metre readout of a signed physical length. -/
def lengthInMeters (length : OpticalLength) : ℝ :=
  lengthReadout LengthUnit.meters length

/-- The centimetre readout used by the radius labels in the figure. -/
def lengthInCentimeters (length : OpticalLength) : ℝ :=
  lengthReadout LengthUnit.centimeters length

/-- The two spherical surfaces encountered by light travelling left to right. -/
inductive LensSurface where
  | left
  | right
  deriving DecidableEq, Repr

/-- Qualitative surface shape as viewed from outside the lens. -/
inductive SurfaceShape where
  | convex
  | concave
  deriving DecidableEq, Repr

/-- Labeled points and surface vertices on the horizontal optical axis. -/
inductive FigurePoint where
  | leftSurfaceVertex
  | rightSurfaceVertex
  | C1
  | C2
  deriving DecidableEq, Repr

/-- The optical media needed for the relative refractive index. -/
inductive OpticalMedium where
  | air
  | glass
  deriving DecidableEq, Repr

/-- Lens descriptions occurring in the problem prose and auxiliary caption. -/
inductive LensDescription where
  | convexMeniscus
  | biconcave
  deriving DecidableEq, Repr

/-- The paraxial approximation under which the thin-lens law is used. -/
inductive OpticalApproximation where
  | thinLensParaxial
  deriving DecidableEq, Repr

/-- Which source controls when the auxiliary caption conflicts with the image. -/
inductive FigureEvidencePolicy where
  | imagePrimary
  deriving DecidableEq, Repr

/-- The vertex belonging to each labeled spherical surface. -/
def surfaceVertex : LensSurface → FigurePoint
  | .left => .leftSurfaceVertex
  | .right => .rightSurfaceVertex

/-- The curvature centre label belonging to each spherical surface. -/
def curvatureCenter : LensSurface → FigurePoint
  | .left => .C1
  | .right => .C2

/-!
The physical meniscus-lens model.

`lensmakerRadius` is directed from a surface vertex to its curvature centre,
the Cartesian convention used in the governing equation.  By contrast,
`figureRadiusAnnotation` preserves the signed arrows printed in the primary
figure and is not silently substituted into lensmaker's equation.
-/
structure MeniscusLensSetup where
  refractiveIndex : OpticalMedium → ℝ
  focalLength : OpticalLength
  lensmakerRadius : LensSurface → OpticalLength
  figureRadiusAnnotation : LensSurface → OpticalLength
  axisPosition : FigurePoint → OpticalLength
  surfaceShape : LensSurface → SurfaceShape
  depictedLensDescription : LensDescription
  auxiliaryCaptionDescription : LensDescription
  approximation : OpticalApproximation
  evidencePolicy : FigureEvidencePolicy

/-- Directed axial separation between two figure points in a selected unit. -/
def axialSeparationReadout
    (setup : MeniscusLensSetup) (unit : LengthUnit)
    (start finish : FigurePoint) : ℝ :=
  lengthReadout unit (setup.axisPosition finish) -
    lengthReadout unit (setup.axisPosition start)

/-!
Problem-text data: the lens is a convex meniscus made from glass of index
`1.50`, surrounded by air of index `1`.  The auxiliary caption's incompatible
word "biconcave" is retained as provenance, while the stated image-primary
policy selects the profile actually drawn.
-/
structure MatchesProblemDescription (setup : MeniscusLensSetup) : Prop where
  glass_refractive_index : setup.refractiveIndex .glass = 3 / 2
  air_refractive_index : setup.refractiveIndex .air = 1
  depicted_lens_kind : setup.depictedLensDescription = .convexMeniscus
  auxiliary_caption_kind : setup.auxiliaryCaptionDescription = .biconcave
  primary_evidence : setup.evidencePolicy = .imagePrimary

/-!
Primary-figure readouts and spatial relations.  The surface profile is convex
on the left and concave on the right.  Both curvature centres lie to the right
of the corresponding vertices, `C₁` precedes `C₂`, and the axial vertex-to-
centre distances are `22 cm` and `46 cm`.  The signed annotations printed in
the image are kept verbatim as `+22 cm` and `-46 cm`.
-/
structure MatchesPrimaryFigure (setup : MeniscusLensSetup) : Prop where
  left_surface_shape : setup.surfaceShape .left = .convex
  right_surface_shape : setup.surfaceShape .right = .concave
  vertices_ordered :
    lengthInCentimeters (setup.axisPosition .leftSurfaceVertex) <
      lengthInCentimeters (setup.axisPosition .rightSurfaceVertex)
  first_center_right_of_lens :
    lengthInCentimeters (setup.axisPosition .rightSurfaceVertex) <
      lengthInCentimeters (setup.axisPosition .C1)
  centers_ordered :
    lengthInCentimeters (setup.axisPosition .C1) <
      lengthInCentimeters (setup.axisPosition .C2)
  first_radius_distance :
    axialSeparationReadout setup LengthUnit.centimeters
      .leftSurfaceVertex .C1 = 22
  second_radius_distance :
    axialSeparationReadout setup LengthUnit.centimeters
      .rightSurfaceVertex .C2 = 46
  first_radius_annotation :
    lengthInCentimeters (setup.figureRadiusAnnotation .left) = 22
  second_radius_annotation :
    lengthInCentimeters (setup.figureRadiusAnnotation .right) = -46

/-!
The Cartesian sign convention for lensmaker's equation.  A signed surface
radius is the displacement from that surface's vertex to its curvature centre
in every unit system.  Thus the image's left-pointing `R₂` annotation is the
opposite orientation from the second lensmaker radius; this predicate states
only the geometric convention, not the unknown focal length.
-/
structure UsesSurfaceToCenterLensmakerConvention
    (setup : MeniscusLensSetup) : Prop where
  radius_from_geometry : ∀ (surface : LensSurface) (units : UnitChoices),
    (setup.lensmakerRadius surface units).val =
      (setup.axisPosition (curvatureCenter surface) units).val -
        (setup.axisPosition (surfaceVertex surface) units).val
  first_annotation_agrees : ∀ units : UnitChoices,
    (setup.figureRadiusAnnotation .left units).val =
      (setup.lensmakerRadius .left units).val
  second_annotation_reverses_orientation : ∀ units : UnitChoices,
    (setup.figureRadiusAnnotation .right units).val =
      -(setup.lensmakerRadius .right units).val

/-- Positivity and nondegeneracy of the optical parameters. -/
structure HasPhysicalOpticalParameters (setup : MeniscusLensSetup) : Prop where
  glass_index_positive : 0 < setup.refractiveIndex .glass
  air_index_positive : 0 < setup.refractiveIndex .air
  first_radius_nonzero :
    lengthInMeters (setup.lensmakerRadius .left) ≠ 0
  second_radius_nonzero :
    lengthInMeters (setup.lensmakerRadius .right) ≠ 0
  focal_length_nonzero : lengthInMeters setup.focalLength ≠ 0

/-!
The thin-lens lensmaker equation in a surrounding medium,

`1 / f = (n_glass / n_air - 1) * (1 / R₁ - 1 / R₂)`.

It is stated in every unit system.  This is the governing optical law and does
not assume a numerical focal length.
-/
structure ObeysThinLensLensmakerEquation (setup : MeniscusLensSetup) : Prop where
  uses_thin_lens_paraxial_approximation :
    setup.approximation = .thinLensParaxial
  lensmaker_equation : ∀ units : UnitChoices,
    1 / (setup.focalLength units).val =
      (setup.refractiveIndex .glass / setup.refractiveIndex .air - 1) *
        (1 / (setup.lensmakerRadius .left units).val -
          1 / (setup.lensmakerRadius .right units).val)

/-- The figure and its sign convention determine the two Cartesian radii. -/
lemma lensmaker_radius_readouts_from_figure
    (setup : MeniscusLensSetup)
    (_figure : MatchesPrimaryFigure setup)
    (_signConvention : UsesSurfaceToCenterLensmakerConvention setup) :
    lengthInCentimeters (setup.lensmakerRadius .left) = 22 ∧
      lengthInCentimeters (setup.lensmakerRadius .right) = 46 := by
  constructor
  · change
      (setup.lensmakerRadius .left
        {UnitChoices.SI with length := LengthUnit.centimeters}).val = 22
    rw [_signConvention.radius_from_geometry .left]
    simpa [axialSeparationReadout, lengthReadout, surfaceVertex,
      curvatureCenter] using _figure.first_radius_distance
  · change
      (setup.lensmakerRadius .right
        {UnitChoices.SI with length := LengthUnit.centimeters}).val = 46
    rw [_signConvention.radius_from_geometry .right]
    simpa [axialSeparationReadout, lengthReadout, surfaceVertex,
      curvatureCenter] using _figure.second_radius_distance

/-- Labels of the four displayed multiple-choice answers. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Focal length in metres printed beside each answer label. -/
def answerFocalLengthMeters : AnswerChoice → ℝ
  | .A => 18 / 25
  | .B => 39 / 50
  | .C => 21 / 25
  | .D => 23 / 25

/-- Dataset metadata recording answer C; this is not a theorem premise. -/
def recordedAnswerChoice : AnswerChoice := .C

/-!
A computed physical focal length matches a two-decimal-place answer when its
metre readout differs by at most half of `0.01 m`.
-/
def MatchesAnswerToNearestHundredthMeter
    (focalLength : OpticalLength) (choice : AnswerChoice) : Prop :=
  |lengthInMeters focalLength - answerFocalLengthMeters choice| ≤ 1 / 200

/-!
Lensmaker's equation with `n_glass = 1.50`, `n_air = 1`, `R₁ = +22 cm`, and
`R₂ = +46 cm` gives the exact focal length `253/300 m`.  Its nearest-hundredth
metre display is `0.84 m`, answer choice C.

This formalizes blueprint label `thm:physics:phyx_mini_0133:target`.
-/
theorem problem_phyx_mini_0133
    (setup : MeniscusLensSetup)
    (_problem : MatchesProblemDescription setup)
    (_figure : MatchesPrimaryFigure setup)
    (_signConvention : UsesSurfaceToCenterLensmakerConvention setup)
    (_physical : HasPhysicalOpticalParameters setup)
    (_lensmaker : ObeysThinLensLensmakerEquation setup) :
    lengthInMeters setup.focalLength = 253 / 300 ∧
      MatchesAnswerToNearestHundredthMeter setup.focalLength .C := by
  have length_centimeters_eq (length : OpticalLength) :
      lengthInCentimeters length = 100 * lengthInMeters length := by
    change
      (length {UnitChoices.SI with length := LengthUnit.centimeters}).val =
        100 * (length UnitChoices.SI).val
    rw [length.2 UnitChoices.SI
      {UnitChoices.SI with length := LengthUnit.centimeters}]
    have hscale :
        UnitChoices.dimScale UnitChoices.SI
          {UnitChoices.SI with length := LengthUnit.centimeters}
          (dim (WithDim L𝓭 ℝ)) = 100 := by
      apply NNReal.eq
      norm_num [UnitChoices.dimScale, LengthUnit.centimeters,
        LengthUnit.meters, LengthUnit.scale, LengthUnit.div_eq_val]
      rfl
    rw [hscale]
    norm_num [WithDim.smul_val, NNReal.smul_def, smul_eq_mul]
  have hradii :=
    lensmaker_radius_readouts_from_figure setup _figure _signConvention
  have hr1 :
      lengthInMeters (setup.lensmakerRadius .left) = 11 / 50 := by
    have h := hradii.1
    rw [length_centimeters_eq] at h
    norm_num at h ⊢
    linarith
  have hr2 :
      lengthInMeters (setup.lensmakerRadius .right) = 23 / 50 := by
    have h := hradii.2
    rw [length_centimeters_eq] at h
    norm_num at h ⊢
    linarith
  have hequation := _lensmaker.lensmaker_equation UnitChoices.SI
  change
    1 / lengthInMeters setup.focalLength =
      (setup.refractiveIndex .glass / setup.refractiveIndex .air - 1) *
        (1 / lengthInMeters (setup.lensmakerRadius .left) -
          1 / lengthInMeters (setup.lensmakerRadius .right)) at hequation
  rw [_problem.glass_refractive_index, _problem.air_refractive_index,
    hr1, hr2] at hequation
  have hf : lengthInMeters setup.focalLength = 253 / 300 := by
    have hf_ne := _physical.focal_length_nonzero
    field_simp [hf_ne] at hequation
    norm_num at hequation ⊢
    linarith
  refine ⟨hf, ?_⟩
  rw [MatchesAnswerToNearestHundredthMeter, hf]
  norm_num [answerFocalLengthMeters, abs_of_nonneg, abs_of_pos]

end PhyXMiniProblems.ProblemPhyXMini0133
