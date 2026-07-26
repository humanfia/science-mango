import Mathlib
import Physlib.Units.WithDim.Basic

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0035

open Dimension

/-!
# Refractive index of a thin biconvex lens

The figure places an eye, an object, a thin converging lens, and a concave
spherical mirror on one horizontal optical axis.  Signed axial coordinates and
signed radii of curvature are physical lengths.  Real numbers are used only
for scalar readouts in centimeters and for dimensionless refractive indices.

For light traveling from the object toward the mirror, the first surface of
the biconvex lens has positive radius and the second has negative radius.  The
material index is determined by the thin-lens lensmaker equation; the mirror
and object distances are retained as setup data even though they do not enter
that determination.
-/

/-- A signed physical length, independent of the unit in which it is read. -/
abbrev LengthQuantity : Type := Dimensionful (WithDim L𝓭 ℝ)

/-- Unit choices whose length component is the centimeter used in the source. -/
noncomputable def centimeterUnitChoices : UnitChoices :=
  { UnitChoices.SI with length := LengthUnit.centimeters }

/-- The signed scalar centimeter readout of a dimensionful length. -/
def lengthInCentimeters (length : LengthQuantity) : ℝ :=
  (length centimeterUnitChoices).val

/-- Labeled points shown on the common horizontal optical axis. -/
inductive FigurePoint where
  | eye
  | object
  | lensCenter
  | focalPointF1
  | focalPointF2
  | mirrorVertex
  deriving DecidableEq, Repr

/-- The optical type of the thin lens depicted in the figure. -/
inductive ThinLensKind where
  | converging
  | diverging
  deriving DecidableEq, Repr

/-- The optical type of the spherical mirror depicted in the figure. -/
inductive SphericalMirrorKind where
  | concave
  | convex
  deriving DecidableEq, Repr

/--
The physical lens--mirror apparatus and its labeled one-dimensional geometry.

The two surface radii are signed according to the Cartesian convention.  The
focal length and all axial positions are also signed physical lengths.  Both
refractive indices are dimensionless.
-/
structure LensMirrorSetup where
  axisPosition : FigurePoint → LengthQuantity
  lensKind : ThinLensKind
  mirrorKind : SphericalMirrorKind
  firstSurfaceRadius : LengthQuantity
  secondSurfaceRadius : LengthQuantity
  lensFocalLength : LengthQuantity
  mirrorRadiusMagnitude : LengthQuantity
  lensMaterialRefractiveIndex : ℝ
  surroundingMediumRefractiveIndex : ℝ

/-- The centimeter separation of two labeled points along the optical axis. -/
def axialSeparationCentimeters
    (setup : LensMirrorSetup) (left right : FigurePoint) : ℝ :=
  lengthInCentimeters (setup.axisPosition right) -
    lengthInCentimeters (setup.axisPosition left)

/--
Figure and problem-statement readouts.  The eye and object lie to the left of
the lens; the mirror lies to its right.  The lens--mirror and object--lens
separations are respectively `20.0 cm` and `8.00 cm`.  The two labeled focal
points are each `5.00 cm` from the lens center.  Only magnitudes of the lens
surface radii are supplied here, exactly as in the source.
-/
structure MatchesFigureReadouts (setup : LensMirrorSetup) : Prop where
  depicted_types :
    setup.lensKind = .converging ∧ setup.mirrorKind = .concave
  eye_left_of_object :
    lengthInCentimeters (setup.axisPosition .eye) <
      lengthInCentimeters (setup.axisPosition .object)
  object_lens_separation :
    axialSeparationCentimeters setup .object .lensCenter = 8
  lens_mirror_separation :
    axialSeparationCentimeters setup .lensCenter .mirrorVertex = 20
  first_focal_point_separation :
    axialSeparationCentimeters setup .focalPointF1 .lensCenter = 5
  second_focal_point_separation :
    axialSeparationCentimeters setup .lensCenter .focalPointF2 = 5
  focal_length_readout :
    lengthInCentimeters setup.lensFocalLength = 5
  first_surface_radius_magnitude :
    |lengthInCentimeters setup.firstSurfaceRadius| = 9
  second_surface_radius_magnitude :
    |lengthInCentimeters setup.secondSurfaceRadius| = 11
  mirror_radius_magnitude :
    lengthInCentimeters setup.mirrorRadiusMagnitude = 8
  surrounding_medium_is_air :
    setup.surroundingMediumRefractiveIndex = 1

/--
The Cartesian sign branch appropriate to light traveling from the object,
through the lens, toward the mirror.  It converts the stated radius magnitudes
to the signed radii `R₁ = +9 cm` and `R₂ = -11 cm` used by lensmaker's law.
-/
structure UsesLensmakerSignConvention (setup : LensMirrorSetup) : Prop where
  first_surface_radius :
    lengthInCentimeters setup.firstSurfaceRadius = 9
  second_surface_radius :
    lengthInCentimeters setup.secondSurfaceRadius = -11

/-- Qualitative positivity conditions for the physical optical parameters. -/
structure HasPhysicalOpticalParameters (setup : LensMirrorSetup) : Prop where
  focal_length_positive :
    0 < lengthInCentimeters setup.lensFocalLength
  mirror_radius_positive :
    0 < lengthInCentimeters setup.mirrorRadiusMagnitude
  material_index_positive :
    0 < setup.lensMaterialRefractiveIndex
  surrounding_index_positive :
    0 < setup.surroundingMediumRefractiveIndex

/--
The thin-lens lensmaker equation in a surrounding medium,

`1 / f = (n_lens / n_medium - 1) * (1 / R₁ - 1 / R₂)`.

It is required in every choice of units.  Consequently all three inverse
length readouts scale together, while the refractive-index factor is
dimensionless.  This is a governing law, not the requested numerical answer.
-/
def ObeysThinLensLensmakerEquation (setup : LensMirrorSetup) : Prop :=
  ∀ units : UnitChoices,
    1 / (setup.lensFocalLength units).val =
      (setup.lensMaterialRefractiveIndex /
          setup.surroundingMediumRefractiveIndex - 1) *
        (1 / (setup.firstSurfaceRadius units).val -
          1 / (setup.secondSurfaceRadius units).val)

/-- Labels of the four displayed multiple-choice answers. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- The dimensionless refractive-index readout printed beside each choice. -/
def answerRefractiveIndex : AnswerChoice → ℝ
  | .A => 33 / 25
  | .B => 36 / 25
  | .C => 3 / 2
  | .D => 199 / 100

/--
The lensmaker equation with `f = 5.00 cm`, `|R₁| = 9.00 cm`, and
`|R₂| = 11.0 cm` determines the lens material's refractive index to be exactly
`199/100 = 1.99`, which is answer choice D.

The mirror radius, object distance, and lens--mirror separation are represented
in `MatchesFigureReadouts`; they do not affect this material-index calculation.

This formalizes `thm:physics:phyx_mini_0035:target`.
-/
theorem problem_phyx_mini_0035
    (setup : LensMirrorSetup)
    (_figure : MatchesFigureReadouts setup)
    (_signConvention : UsesLensmakerSignConvention setup)
    (_physical : HasPhysicalOpticalParameters setup)
    (_lensmaker : ObeysThinLensLensmakerEquation setup) :
    setup.lensMaterialRefractiveIndex = 199 / 100 ∧
      setup.lensMaterialRefractiveIndex = answerRefractiveIndex .D := by
  have hf :
      (setup.lensFocalLength centimeterUnitChoices).val = 5 := by
    simpa [lengthInCentimeters] using _figure.focal_length_readout
  have hR₁ :
      (setup.firstSurfaceRadius centimeterUnitChoices).val = 9 := by
    simpa [lengthInCentimeters] using _signConvention.first_surface_radius
  have hR₂ :
      (setup.secondSurfaceRadius centimeterUnitChoices).val = -11 := by
    simpa [lengthInCentimeters] using _signConvention.second_surface_radius
  have hnMedium : setup.surroundingMediumRefractiveIndex = 1 :=
    _figure.surrounding_medium_is_air
  have hlensmaker := _lensmaker centimeterUnitChoices
  rw [hf, hR₁, hR₂, hnMedium] at hlensmaker
  have hn : setup.lensMaterialRefractiveIndex = 199 / 100 := by
    norm_num at hlensmaker ⊢
    linarith
  exact ⟨hn, by simpa [answerRefractiveIndex] using hn⟩

end PhyXMiniProblems.ProblemPhyXMini0035
