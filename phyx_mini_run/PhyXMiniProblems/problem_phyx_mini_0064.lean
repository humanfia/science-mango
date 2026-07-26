import Mathlib
import Physlib.SpaceAndTime.Space.LengthUnit
import Physlib.Units.WithDim.Basic

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0064

open Dimension

/-!
# Focal length of a biconvex glass lens

The primary figure shows a biconvex lens on a horizontal principal axis.  Its
two black axial dots are centers of curvature: the left dot's arrow terminates
on the outgoing face and is labeled `40 cm`, while the right dot's arrow
terminates on the incident face and is labeled `24 cm`.

Lengths are represented by Physlib dimensionful quantities.  Real numbers are
used only for dimensionless refractive indices and scalar readouts in a stated
unit.  The value `30 cm` requested by the problem appears only in conclusions
and in the answer-choice table.
-/

/-- A nonnegative physical quantity carrying the dimension of length. -/
abbrev LengthMagnitude : Type := Dimensionful (WithDim L𝓭 NNReal)

/-- The numerical readout, in centimeters, of a physical length magnitude. -/
def lengthInCentimeters (length : LengthMagnitude) : ℝ :=
  ((length {UnitChoices.SI with length := LengthUnit.centimeters}).val : ℝ)

/-- Axial sides relative to light propagation from left to right. -/
inductive AxialSide where
  | incident
  | outgoing
  deriving DecidableEq, Repr

/-- The two spherical faces of the lens, ordered along the propagation axis. -/
inductive LensSurfaceLabel where
  | incidentFace
  | outgoingFace
  deriving DecidableEq, Repr

/-- The two black centers of curvature drawn on the principal axis. -/
inductive CenterOfCurvatureDot where
  | leftDot
  | rightDot
  deriving DecidableEq, Repr

/-- The optical media on the two sides of each refracting interface. -/
inductive OpticalMedium where
  | ambientAir
  | lensGlass
  deriving DecidableEq, Repr

/-- Direction used to assign incident/outgoing faces and signed radii. -/
inductive PropagationDirection where
  | leftToRight
  | rightToLeft
  deriving DecidableEq, Repr

/-
A spherical refracting surface retains both its physical radius magnitude and
the side containing its center of curvature.  Thus the sign convention is not
hidden by representing a radius as a bare scalar.
-/
structure SphericalLensSurface where
  radiusMagnitude : LengthMagnitude
  centerOfCurvatureSide : AxialSide

/-- A physical thin biconvex lens with two labeled spherical faces. -/
structure ThinBiconvexGlassLens where
  surface : LensSurfaceLabel → SphericalLensSurface
  focalLength : LengthMagnitude

/-
The radius arrows and qualitative geometry visible in the primary figure.
`radiusArrowTarget` records the cross-lens arrow endpoints that distinguish
the two printed numbers from object and image distances.
-/
structure CurvatureRadiusFigure where
  centerDotSide : CenterOfCurvatureDot → AxialSide
  radiusArrowTarget : CenterOfCurvatureDot → LensSurfaceLabel
  radiusArrowMagnitude : CenterOfCurvatureDot → LengthMagnitude
  principalAxisShown : Bool
  lensDrawnBiconvex : Bool

/-- The physical lens, material data, propagation convention, and figure. -/
structure GlassLensmakerSetup where
  lens : ThinBiconvexGlassLens
  refractiveIndex : OpticalMedium → ℝ
  propagationDirection : PropagationDirection
  figure : CurvatureRadiusFigure

/-
Signed surface-radius readout in centimeters.  For left-to-right propagation,
a center on the outgoing side gives a positive radius and a center on the
incident side gives a negative radius.
-/
def signedSurfaceRadiusInCentimeters
    (surface : SphericalLensSurface) : ℝ :=
  match surface.centerOfCurvatureSide with
  | .incident => -lengthInCentimeters surface.radiusMagnitude
  | .outgoing => lengthInCentimeters surface.radiusMagnitude

/-
The primary-figure data.  The left dot is the center of the outgoing surface
and carries the `40 cm` arrow; the right dot is the center of the incident
surface and carries the `24 cm` arrow.  No focal-length value occurs here.
-/
def MatchesFigureGeometryAndReadouts (setup : GlassLensmakerSetup) : Prop :=
  setup.propagationDirection = .leftToRight ∧
    setup.figure.principalAxisShown = true ∧
    setup.figure.lensDrawnBiconvex = true ∧
    setup.figure.centerDotSide .leftDot = .incident ∧
    setup.figure.centerDotSide .rightDot = .outgoing ∧
    setup.figure.radiusArrowTarget .leftDot = .outgoingFace ∧
    setup.figure.radiusArrowTarget .rightDot = .incidentFace ∧
    setup.figure.radiusArrowMagnitude .leftDot =
      (setup.lens.surface .outgoingFace).radiusMagnitude ∧
    setup.figure.radiusArrowMagnitude .rightDot =
      (setup.lens.surface .incidentFace).radiusMagnitude ∧
    lengthInCentimeters (setup.figure.radiusArrowMagnitude .leftDot) = 40 ∧
    lengthInCentimeters (setup.figure.radiusArrowMagnitude .rightDot) = 24 ∧
    (setup.lens.surface .incidentFace).centerOfCurvatureSide = .outgoing ∧
    (setup.lens.surface .outgoingFace).centerOfCurvatureSide = .incident

/-
The conventional material calibration implicit in the phrase “glass lens”
and required by the recorded multiple-choice answer: ordinary air has index
one and the modeled glass has index `1.5`.  This contains no focal-length
claim.
-/
def UsesStandardGlassInAirIndices (setup : GlassLensmakerSetup) : Prop :=
  setup.refractiveIndex .ambientAir = 1 ∧
    setup.refractiveIndex .lensGlass = (3 : ℝ) / 2

/-- Positivity and optical-branch conditions for the modeled lens. -/
def HasPhysicalLensParameters (setup : GlassLensmakerSetup) : Prop :=
  (∀ medium, 0 < setup.refractiveIndex medium) ∧
    setup.refractiveIndex .ambientAir < setup.refractiveIndex .lensGlass ∧
    0 < lengthInCentimeters setup.lens.focalLength ∧
    (∀ face,
      0 < lengthInCentimeters (setup.lens.surface face).radiusMagnitude)

/-
The paraxial thin-lens lensmaker equation in a surrounding medium.  The two
signed radii use the incident-first convention `1/R₁ - 1/R₂`.  This is a
generic governing law and does not contain the requested numerical answer.
-/
def SatisfiesThinLensmakerEquation (setup : GlassLensmakerSetup) : Prop :=
  1 / lengthInCentimeters setup.lens.focalLength =
    (setup.refractiveIndex .lensGlass /
        setup.refractiveIndex .ambientAir - 1) *
      (1 / signedSurfaceRadiusInCentimeters
          (setup.lens.surface .incidentFace) -
        1 / signedSurfaceRadiusInCentimeters
          (setup.lens.surface .outgoingFace))

/-- Labels of the four displayed multiple-choice answers. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Focal-length readout printed beside each answer choice, in centimeters. -/
def answerFocalLengthInCentimeters : AnswerChoice → ℝ
  | .A => 24
  | .B => 56
  | .C => 30
  | .D => 35

/-
The arrow geometry gives signed radii `R₁ = +24 cm` and `R₂ = -40 cm` in the
left-to-right lensmaker convention.
-/
lemma signed_surface_radius_readouts
    (setup : GlassLensmakerSetup)
    (h_figure : MatchesFigureGeometryAndReadouts setup) :
    signedSurfaceRadiusInCentimeters
        (setup.lens.surface .incidentFace) = 24 ∧
      signedSurfaceRadiusInCentimeters
        (setup.lens.surface .outgoingFace) = -40 := by
  rcases h_figure with
    ⟨_, _, _, _, _, _, _, h_left_radius, h_right_radius,
      h_left_readout, h_right_readout, h_incident_side, h_outgoing_side⟩
  constructor
  · simp [signedSurfaceRadiusInCentimeters, h_incident_side,
      ← h_right_radius, h_right_readout]
  · simp [signedSurfaceRadiusInCentimeters, h_outgoing_side,
      ← h_left_radius, h_left_readout]

/-
The standard glass/air indices, the two signed curvature radii, and the
lensmaker equation determine reciprocal focal length `1/30 cm⁻¹`.
-/
lemma reciprocal_focal_length_eq_one_over_thirty
    (setup : GlassLensmakerSetup)
    (h_figure : MatchesFigureGeometryAndReadouts setup)
    (h_indices : UsesStandardGlassInAirIndices setup)
    (h_lensmaker : SatisfiesThinLensmakerEquation setup) :
    1 / lengthInCentimeters setup.lens.focalLength = (1 : ℝ) / 30 := by
  have h_radii := signed_surface_radius_readouts setup h_figure
  norm_num [UsesStandardGlassInAirIndices] at h_indices
  norm_num [SatisfiesThinLensmakerEquation, h_indices.1, h_indices.2,
    h_radii.1, h_radii.2] at h_lensmaker ⊢
  exact h_lensmaker

/-
The biconvex glass lens therefore has focal length `30 cm`, which is the
dataset's recorded answer choice C.

This formalizes blueprint label `thm:physics:phyx_mini_0064:target`.
-/
theorem problem_phyx_mini_0064
    (setup : GlassLensmakerSetup)
    (h_figure : MatchesFigureGeometryAndReadouts setup)
    (h_indices : UsesStandardGlassInAirIndices setup)
    (h_physical : HasPhysicalLensParameters setup)
    (h_lensmaker : SatisfiesThinLensmakerEquation setup) :
    lengthInCentimeters setup.lens.focalLength = 30 ∧
      lengthInCentimeters setup.lens.focalLength =
        answerFocalLengthInCentimeters .C := by
  have h_reciprocal :=
    reciprocal_focal_length_eq_one_over_thirty setup h_figure h_indices h_lensmaker
  have h_positive : 0 < lengthInCentimeters setup.lens.focalLength :=
    h_physical.2.2.1
  have h_nonzero : lengthInCentimeters setup.lens.focalLength ≠ 0 :=
    ne_of_gt h_positive
  field_simp [h_nonzero] at h_reciprocal
  have h_focal : lengthInCentimeters setup.lens.focalLength = 30 := by
    linarith
  constructor
  · exact h_focal
  · simpa [answerFocalLengthInCentimeters] using h_focal

end PhyXMiniProblems.ProblemPhyXMini0064
