import Mathlib
import Physlib.SpaceAndTime.Space.LengthUnit
import Physlib.Units.WithDim.Basic

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0057

open Dimension

/-!
# Curved-face radius of a planoconvex microscope objective

The figure shows light travelling from a specimen through the planar face
`R₁` and then the spherical face `R₂`.  It gives `s = 8.0 mm`,
`s' = 160 mm`, and glass refractive index `n = 1.50`; the image is real and
the drawn distances are explicitly not to scale.

Lengths are represented by Physlib dimensionful quantities.  Real numbers are
used only for dimensionless refractive indices and readouts in a stated unit.
-/

/-- A nonnegative physical quantity carrying the dimension of length. -/
abbrev LengthMagnitude : Type := Dimensionful (WithDim L𝓭 NNReal)

/-- The numerical readout, in millimeters, of a physical length magnitude. -/
def lengthInMillimeters (length : LengthMagnitude) : ℝ :=
  ((length {UnitChoices.SI with length := LengthUnit.millimeters}).val : ℝ)

/-- Axial sides relative to propagation from the specimen toward the image. -/
inductive AxialSide where
  | incident
  | outgoing
  deriving DecidableEq, Repr

/-- The surface labels printed in the figure. -/
inductive LensSurfaceLabel where
  | R1
  | R2
  deriving DecidableEq, Repr

/-- The two distance-arrow labels printed in the figure. -/
inductive FigureDistanceLabel where
  | s
  | sPrime
  deriving DecidableEq, Repr

/-- The optical media relevant to the objective. -/
inductive OpticalMedium where
  | ambientAir
  | glass
  deriving DecidableEq, Repr

/-- Whether rays actually meet at the image or only appear to do so. -/
inductive ImageNature where
  | real
  | virtual
  deriving DecidableEq, Repr

/-- Direction in which the pictured rays propagate. -/
inductive PropagationDirection where
  | specimenToImage
  | imageToSpecimen
  deriving DecidableEq, Repr

/-
A planar surface represents the figure label `R₁ = ∞`.  A spherical surface
retains both its positive radius magnitude and the side containing its center
of curvature, so sign-convention information is not hidden in a scalar.
-/
inductive LensSurfaceProfile where
  | planar
  | spherical (radiusMagnitude : LengthMagnitude)
      (centerOfCurvatureSide : AxialSide)

/-- The planoconvex objective together with its two labeled faces. -/
structure PlanoconvexObjective where
  surfaceProfile : LensSurfaceLabel → LensSurfaceProfile
  curvedSurfaceRadiusMagnitude : LengthMagnitude
  flatFaceSide : AxialSide

/-- Quantitative arrows and qualitative ray information read from the figure. -/
structure ObjectiveLensFigure where
  distanceReadout : FigureDistanceLabel → LengthMagnitude
  distancesDrawnToScale : Bool
  raysShownConverging : Bool

/-- Physical quantities and roles in the thin-lens microscope setup. -/
structure MicroscopeObjectiveSetup where
  lens : PlanoconvexObjective
  objectDistance : LengthMagnitude
  imageDistance : LengthMagnitude
  focalLength : LengthMagnitude
  refractiveIndex : OpticalMedium → ℝ
  objectSide : AxialSide
  imageSide : AxialSide
  imageNature : ImageNature
  propagationDirection : PropagationDirection
  figure : ObjectiveLensFigure

/-
Signed surface curvature in inverse millimeters.  With the convention used by
the lensmaker equation below, an outgoing-side center has positive radius and
an incident-side center has negative radius.  A plane has zero curvature.
-/
def surfaceCurvatureInInverseMillimeters
    (profile : LensSurfaceProfile) : ℝ :=
  match profile with
  | .planar => 0
  | .spherical radius .incident => -(1 / lengthInMillimeters radius)
  | .spherical radius .outgoing => 1 / lengthInMillimeters radius

/-
The data and geometry read from the problem and its figure.  In particular,
the curved-face radius is not assigned a numerical value here.
-/
def MatchesProblemAndFigureReadouts
    (setup : MicroscopeObjectiveSetup) : Prop :=
  setup.figure.distanceReadout .s = setup.objectDistance ∧
    setup.figure.distanceReadout .sPrime = setup.imageDistance ∧
    lengthInMillimeters (setup.figure.distanceReadout .s) = 8 ∧
    lengthInMillimeters (setup.figure.distanceReadout .sPrime) = 160 ∧
    setup.refractiveIndex .glass = 3 / 2 ∧
    setup.lens.flatFaceSide = .incident ∧
    setup.lens.surfaceProfile .R1 = .planar ∧
    setup.lens.surfaceProfile .R2 =
      .spherical setup.lens.curvedSurfaceRadiusMagnitude .incident ∧
    setup.objectSide = .incident ∧
    setup.imageSide = .outgoing ∧
    setup.imageNature = .real ∧
    setup.propagationDirection = .specimenToImage ∧
    setup.figure.distancesDrawnToScale = false ∧
    setup.figure.raysShownConverging = true

/-- Positivity and refractive-index branch conditions for the physical setup. -/
def HasPhysicalParameters (setup : MicroscopeObjectiveSetup) : Prop :=
  (∀ medium, 0 < setup.refractiveIndex medium) ∧
    setup.refractiveIndex .ambientAir < setup.refractiveIndex .glass ∧
    0 < lengthInMillimeters setup.objectDistance ∧
    0 < lengthInMillimeters setup.imageDistance ∧
    0 < lengthInMillimeters setup.focalLength ∧
    0 < lengthInMillimeters setup.lens.curvedSurfaceRadiusMagnitude

/-- The surrounding optical medium is ordinary air, of refractive index one. -/
def ModelsAmbientAir (setup : MicroscopeObjectiveSetup) : Prop :=
  setup.refractiveIndex .ambientAir = 1

/-
The governing paraxial thin-lens and lensmaker laws.  Both are stated using
millimeter and inverse-millimeter readouts, so the equations are dimensionally
consistent.  Neither field contains the requested radius value.
-/
structure SatisfiesParaxialObjectiveLaws
    (setup : MicroscopeObjectiveSetup) : Prop where
  thinLensEquation :
    1 / lengthInMillimeters setup.focalLength =
      1 / lengthInMillimeters setup.objectDistance +
        1 / lengthInMillimeters setup.imageDistance
  lensmakerEquation :
    1 / lengthInMillimeters setup.focalLength =
      (setup.refractiveIndex .glass /
          setup.refractiveIndex .ambientAir - 1) *
        (surfaceCurvatureInInverseMillimeters
            (setup.lens.surfaceProfile .R1) -
          surfaceCurvatureInInverseMillimeters
            (setup.lens.surfaceProfile .R2))

/-- Labels of the four displayed multiple-choice answers. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- The radius readout printed beside each answer label, in millimeters. -/
def answerRadiusInMillimeters : AnswerChoice → ℝ
  | .A => 14 / 10
  | .B => 86 / 10
  | .C => 38 / 10
  | .D => 74 / 10

/-- Agreement of an exact radius with a displayed nearest-tenth readout. -/
def MatchesAnswerToNearestTenth
    (exactRadiusInMillimeters : ℝ) (choice : AnswerChoice) : Prop :=
  |exactRadiusInMillimeters - answerRadiusInMillimeters choice| ≤ 1 / 20

/-
The planar first face has zero curvature, while the center of curvature of the
second face lies on the incident side and hence gives a negative curvature.
-/
lemma surfaceCurvatureReadouts
    (setup : MicroscopeObjectiveSetup)
    (h_figure : MatchesProblemAndFigureReadouts setup) :
    surfaceCurvatureInInverseMillimeters
        (setup.lens.surfaceProfile .R1) = 0 ∧
      surfaceCurvatureInInverseMillimeters
          (setup.lens.surfaceProfile .R2) =
        -(1 /
          lengthInMillimeters setup.lens.curvedSurfaceRadiusMagnitude) := by
  rcases h_figure with ⟨_, _, _, _, _, _, hR1, hR2, _⟩
  simp [hR1, hR2, surfaceCurvatureInInverseMillimeters]

/-- The imaging equation and the two distance readouts give `1/f = 21/160`. -/
lemma reciprocalFocalLength_eq_twenty_one_over_one_sixty
    (setup : MicroscopeObjectiveSetup)
    (h_figure : MatchesProblemAndFigureReadouts setup)
    (h_laws : SatisfiesParaxialObjectiveLaws setup) :
    1 / lengthInMillimeters setup.focalLength = (21 / 160 : ℝ) := by
  rcases h_figure with ⟨hs, hs', hs8, hs160, _⟩
  rw [h_laws.thinLensEquation, ← hs, ← hs', hs8, hs160]
  norm_num

/-
The two governing equations, the glass/air indices, and the figure geometry
determine the physical curved-face radius as `80/21 mm`.
-/
lemma curvedSurfaceRadius_eq_eighty_over_twenty_one
    (setup : MicroscopeObjectiveSetup)
    (h_physical : HasPhysicalParameters setup)
    (h_figure : MatchesProblemAndFigureReadouts setup)
    (h_air : ModelsAmbientAir setup)
    (h_laws : SatisfiesParaxialObjectiveLaws setup) :
    lengthInMillimeters setup.lens.curvedSurfaceRadiusMagnitude =
      (80 / 21 : ℝ) := by
  have h_focal :=
    reciprocalFocalLength_eq_twenty_one_over_one_sixty setup h_figure h_laws
  obtain ⟨h_plane, h_sphere⟩ := surfaceCurvatureReadouts setup h_figure
  have h_lens := h_laws.lensmakerEquation
  rw [h_focal, h_figure.2.2.2.2.1, h_air, h_plane, h_sphere] at h_lens
  field_simp [ne_of_gt h_physical.2.2.2.2.2] at h_lens ⊢
  nlinarith

/-
The curved surface therefore has radius `80/21 mm`, displayed to the nearest
tenth as `3.8 mm`, which is answer choice C.

This formalizes blueprint label `thm:physics:phyx_mini_0057:target`.
-/
theorem problem_phyx_mini_0057
    (setup : MicroscopeObjectiveSetup)
    (h_physical : HasPhysicalParameters setup)
    (h_figure : MatchesProblemAndFigureReadouts setup)
    (h_air : ModelsAmbientAir setup)
    (h_laws : SatisfiesParaxialObjectiveLaws setup) :
    lengthInMillimeters setup.lens.curvedSurfaceRadiusMagnitude =
        (80 / 21 : ℝ) ∧
      MatchesAnswerToNearestTenth
        (lengthInMillimeters setup.lens.curvedSurfaceRadiusMagnitude) .C := by
  have h_radius :=
    curvedSurfaceRadius_eq_eighty_over_twenty_one
      setup h_physical h_figure h_air h_laws
  constructor
  · exact h_radius
  · simp only [MatchesAnswerToNearestTenth, answerRadiusInMillimeters, h_radius]
    norm_num [abs_of_nonneg]

end PhyXMiniProblems.ProblemPhyXMini0057
