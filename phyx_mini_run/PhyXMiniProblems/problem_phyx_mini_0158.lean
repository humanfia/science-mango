import Mathlib
import Physlib.Units.WithDim.Basic
import Physlib.SpaceAndTime.Space.LengthUnit

/- USER: The assigned Lean file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0158

/-!
# Apparent depth of an air bubble in a glass porthole

A fish in the surrounding water views an air bubble located at the center of
a plane-parallel glass porthole.  The ray model below concerns the glass--water
surface facing the fish.  Lengths are dimensionful Physlib quantities;
centimeter values, refractive indices, radian angles, and paraxial slopes are
scalar readouts.

The source gives no numerical refractive index for either glass or water.
Consequently the physical answer is stated symbolically in terms of those two
indices.  The dataset's recorded choice B (`2.2 cm`) is retained only as source
metadata, not asserted by the theorem.

For the generic refraction figure, `P` is the bubble, `PPrime` is its virtual
image, `n1` is the glass index, `n2` is the water index, `theta1` and `theta2`
are measured from the optical axis, and `s`, `sPrime`, and `l` have the roles
shown in the source diagram.
-/

open Dimension

/-- A physical length represented coherently in every choice of units. -/
abbrev DimLength : Type := Dimensionful (WithDim L𝓭 ℝ)

/-- Unit choices in which length is read in centimeters and all other units are SI. -/
def centimeterUnitChoices : UnitChoices :=
  { UnitChoices.SI with length := LengthUnit.centimeters }

/-- The scalar centimeter readout of a physical length. -/
def lengthInCentimeters (length : DimLength) : ℝ :=
  (length centimeterUnitChoices).val

/-- Homogeneous optical media relevant to the two observers and the porthole. -/
inductive OpticalMedium where
  | glass
  | surroundingWater
  | submarineAir
  deriving DecidableEq, Repr

/-- The two observers named in the problem. -/
inductive Observer where
  | fish
  | sailor
  deriving DecidableEq, Repr

/-- The two plane faces of the porthole. -/
inductive PortholeSurface where
  | fishFacing
  | sailorFacing
  deriving DecidableEq, Repr

/-- Medium-index labels printed in the generic refraction figure. -/
inductive FigureMediumLabel where
  | n1
  | n2
  deriving DecidableEq, Repr

/-- Angle labels printed in the generic refraction figure. -/
inductive FigureAngleLabel where
  | theta1
  | theta2
  deriving DecidableEq, Repr

/-- Length labels printed in the generic refraction figure. -/
inductive FigureLengthLabel where
  | s
  | sPrime
  | l
  deriving DecidableEq, Repr

/-- Point labels needed to record the depicted actual and virtual ray paths. -/
inductive FigurePoint where
  | P
  | PPrime
  | interfacePoint
  | fishEye
  deriving DecidableEq, Repr

/--
Physical quantities and figure readouts for the porthole observation.

`incidentSlopeInGlass` and `refractedSlopeInWater` are positive transverse
displacement per axial displacement for a neighboring paraxial ray.  The
requested apparent depth remains an unconstrained physical length field until
the ray-geometry and refraction-law hypotheses are supplied.
-/
structure PortholeApparentDepthSetup where
  glassThickness : DimLength
  bubbleDepthFromSurface : PortholeSurface → DimLength
  apparentDepthSeenBy : Observer → DimLength
  rayHeight : DimLength
  refractiveIndex : OpticalMedium → ℝ
  observerMedium : Observer → OpticalMedium
  viewingSurface : Observer → PortholeSurface
  figureMedium : FigureMediumLabel → OpticalMedium
  figureAngleRadians : FigureAngleLabel → ℝ
  figureLength : FigureLengthLabel → DimLength
  incidentSlopeInGlass : ℝ
  refractedSlopeInWater : ℝ
  actualRayPath : List FigurePoint
  virtualBackwardExtension : List FigurePoint

/--
Problem readouts: the porthole is `5.0 cm` thick, the bubble is midway between
its faces, and the fish and sailor occupy the water and submarine-air sides,
respectively.
-/
def MatchesProblemDescription (setup : PortholeApparentDepthSetup) : Prop :=
  lengthInCentimeters setup.glassThickness = 5 ∧
    lengthInCentimeters
        (setup.bubbleDepthFromSurface .fishFacing) =
      lengthInCentimeters setup.glassThickness / 2 ∧
    lengthInCentimeters
        (setup.bubbleDepthFromSurface .sailorFacing) =
      lengthInCentimeters setup.glassThickness / 2 ∧
    setup.observerMedium .fish = .surroundingWater ∧
    setup.observerMedium .sailor = .submarineAir ∧
    setup.viewingSurface .fish = .fishFacing ∧
    setup.viewingSurface .sailor = .sailorFacing

/--
Interpretation of every label in the generic refraction figure for the fish's
view.  In particular, `s` is the true bubble depth, `sPrime` is the virtual
image depth, and `l` is the common transverse ray height.  The ordering says
only that the depicted virtual image lies between the bubble and the surface.
-/
def MatchesRefractionFigure (setup : PortholeApparentDepthSetup) : Prop :=
  setup.figureMedium .n1 = .glass ∧
    setup.figureMedium .n2 = .surroundingWater ∧
    setup.figureLength .s = setup.bubbleDepthFromSurface .fishFacing ∧
    setup.figureLength .sPrime = setup.apparentDepthSeenBy .fish ∧
    setup.figureLength .l = setup.rayHeight ∧
    setup.actualRayPath = [.P, .interfacePoint, .fishEye] ∧
    setup.virtualBackwardExtension = [.fishEye, .interfacePoint, .PPrime] ∧
    0 < lengthInCentimeters (setup.figureLength .sPrime) ∧
    lengthInCentimeters (setup.figureLength .sPrime) <
      lengthInCentimeters (setup.figureLength .s)

/-- Positivity and principal-angle conditions for the physical paraxial branch. -/
def HasPhysicalOpticalParameters (setup : PortholeApparentDepthSetup) : Prop :=
  (∀ medium, 0 < setup.refractiveIndex medium) ∧
    0 < lengthInCentimeters setup.glassThickness ∧
    0 < lengthInCentimeters (setup.figureLength .s) ∧
    0 < lengthInCentimeters (setup.figureLength .sPrime) ∧
    0 < lengthInCentimeters (setup.figureLength .l) ∧
    0 < setup.incidentSlopeInGlass ∧
    0 < setup.refractedSlopeInWater ∧
    0 < setup.figureAngleRadians .theta1 ∧
    setup.figureAngleRadians .theta1 < Real.pi / 2 ∧
    0 < setup.figureAngleRadians .theta2 ∧
    setup.figureAngleRadians .theta2 < Real.pi / 2

/--
Paraxial ray geometry for `P`, `PPrime`, and the common interface point.
The first two equalities connect the displayed angles to ray slopes; the last
two say that slope times axial depth equals the shared height `l`.
-/
def HasParaxialRayGeometry (setup : PortholeApparentDepthSetup) : Prop :=
  setup.incidentSlopeInGlass =
      Real.tan (setup.figureAngleRadians .theta1) ∧
    setup.refractedSlopeInWater =
      Real.tan (setup.figureAngleRadians .theta2) ∧
    setup.incidentSlopeInGlass *
        lengthInCentimeters (setup.figureLength .s) =
      lengthInCentimeters (setup.figureLength .l) ∧
    setup.refractedSlopeInWater *
        lengthInCentimeters (setup.figureLength .sPrime) =
      lengthInCentimeters (setup.figureLength .l)

/--
First-order Snell law at the plane glass--water surface,
`n₁ slope₁ = n₂ slope₂`.
-/
def ObeysParaxialSnellLaw (setup : PortholeApparentDepthSetup) : Prop :=
  setup.refractiveIndex (setup.figureMedium .n1) *
      setup.incidentSlopeInGlass =
    setup.refractiveIndex (setup.figureMedium .n2) *
      setup.refractedSlopeInWater

/-- Labels of the four displayed multiple-choice answers. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- The apparent depth printed beside each answer choice, in centimeters. -/
def AnswerChoice.depthInCentimeters : AnswerChoice → ℝ
  | .A => 2
  | .B => 22 / 10
  | .C => 17 / 10
  | .D => 15 / 10

/-- Dataset metadata: the recorded multiple-choice answer is B (`2.2 cm`). -/
def recordedAnswerChoice : AnswerChoice := .B

/--
The generic paraxial geometry and first-order Snell law imply
`s′ = s * n₂ / n₁` for a virtual image viewed across a plane interface.
-/
lemma apparentDepth_eq_trueDepth_mul_indexRatio
    (setup : PortholeApparentDepthSetup)
    (hPhysical : HasPhysicalOpticalParameters setup)
    (hGeometry : HasParaxialRayGeometry setup)
    (hSnell : ObeysParaxialSnellLaw setup) :
    lengthInCentimeters (setup.figureLength .sPrime) =
      lengthInCentimeters (setup.figureLength .s) *
        setup.refractiveIndex (setup.figureMedium .n2) /
          setup.refractiveIndex (setup.figureMedium .n1) := by
  have hn1ne : setup.refractiveIndex (setup.figureMedium .n1) ≠ 0 :=
    ne_of_gt (hPhysical.1 _)
  have hbne : setup.refractedSlopeInWater ≠ 0 :=
    ne_of_gt hPhysical.2.2.2.2.2.2.1
  apply (eq_div_iff hn1ne).2
  apply mul_left_cancel₀ hbne
  calc
    setup.refractedSlopeInWater *
          (lengthInCentimeters (setup.figureLength .sPrime) *
            setup.refractiveIndex (setup.figureMedium .n1)) =
        setup.refractiveIndex (setup.figureMedium .n1) *
          (setup.refractedSlopeInWater *
            lengthInCentimeters (setup.figureLength .sPrime)) := by
      ring
    _ = setup.refractiveIndex (setup.figureMedium .n1) *
          (setup.incidentSlopeInGlass *
            lengthInCentimeters (setup.figureLength .s)) := by
      rw [hGeometry.2.2.2, hGeometry.2.2.1]
    _ = (setup.refractiveIndex (setup.figureMedium .n1) *
            setup.incidentSlopeInGlass) *
          lengthInCentimeters (setup.figureLength .s) := by
      ring
    _ = (setup.refractiveIndex (setup.figureMedium .n2) *
            setup.refractedSlopeInWater) *
          lengthInCentimeters (setup.figureLength .s) := by
      rw [hSnell]
    _ = setup.refractedSlopeInWater *
          (lengthInCentimeters (setup.figureLength .s) *
            setup.refractiveIndex (setup.figureMedium .n2)) := by
      ring

/--
A bubble at the center of a `5.0 cm` glass porthole is truly `2.5 cm` behind
the fish-facing surface.  Paraxial ray geometry and first-order Snell
refraction therefore give the source-supported symbolic answer
`s' = (5/2) * n_water / n_glass` centimeters.

Because the source and figure supply neither `n_water` nor `n_glass`, the
recorded numerical choice B is not a conclusion of this theorem.

This formalizes `thm:physics:phyx_mini_0158:target`.
-/
theorem problem_phyx_mini_0158
    (setup : PortholeApparentDepthSetup)
    (hDescription : MatchesProblemDescription setup)
    (hFigure : MatchesRefractionFigure setup)
    (hPhysical : HasPhysicalOpticalParameters setup)
    (hGeometry : HasParaxialRayGeometry setup)
    (hSnell : ObeysParaxialSnellLaw setup) :
    lengthInCentimeters (setup.apparentDepthSeenBy .fish) =
      (5 : ℝ) / 2 *
        setup.refractiveIndex .surroundingWater /
          setup.refractiveIndex .glass := by
  have hDepth :=
    apparentDepth_eq_trueDepth_mul_indexRatio setup hPhysical hGeometry hSnell
  rw [hFigure.2.2.2.1, hFigure.2.2.1, hFigure.2.1, hFigure.1,
    hDescription.2.1, hDescription.1] at hDepth
  exact hDepth

end PhyXMiniProblems.ProblemPhyXMini0158
