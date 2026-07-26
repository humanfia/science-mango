import Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle
import Mathlib.LinearAlgebra.Ray
import Physlib.Optics.Basic

/-!
# PhyX mini problem 0006: refraction from a 45-45-90 prism

A laser ray enters one leg of a right isosceles prism normally, so its path
inside the prism continues in the incident direction.  It then leaves through
the hypotenuse.  The primary image marks the acute prism angle as `45°` and
the deviation of the outgoing ray below the original incident direction as
`θ = 15°`.  Thus the exit incidence and refraction angles, measured from the
hypotenuse normal, are respectively `45°` and `60°`.

Angles are represented by Mathlib's `Real.Angle`; refractive indices and the
displayed multiple-choice values are dimensionless real readouts.  The figure
data, prism/ray geometry, physical branch assumptions, and Snell's law are
kept separate from the requested refractive-index conclusion.

`Physlib.Optics.Basic` is imported as the relevant formal-physics module.  It
is currently an explicit placeholder and supplies no refraction or Snell-law
declaration, so the governing optical relation is stated locally below while
Mathlib's angle and nonzero-ray types are reused directly.
-/

namespace PhyXMiniProblems.ProblemPhyxMini0006

noncomputable section

/-! ## Angle units and diagram labels -/

/-- Convert a degree readout to Mathlib's physical angle type. -/
noncomputable def angleFromDegrees (angleDegrees : ℝ) : Real.Angle :=
  ((angleDegrees * Real.pi / 180 : ℝ) : Real.Angle)

/-- The Cartesian plane in which the cross-section of the prism is drawn. -/
abbrev DiagramPlane := ℝ × ℝ

/-- The three directed portions of the laser path distinguished in the
primary image and its physical interpretation. -/
inductive RaySegment where
  | incoming
  | insidePrism
  | transmitted
  deriving DecidableEq, Repr

/-- The three faces of the triangular prism cross-section. -/
inductive PrismFace where
  | entryFace
  | base
  | hypotenuse
  deriving DecidableEq, Repr

/-- The interfaces at which the laser passes between homogeneous media. -/
inductive RefractingInterface where
  | entryFace
  | hypotenuse
  deriving DecidableEq, Repr

/-- The two homogeneous optical media traversed by the laser. -/
inductive OpticalMedium where
  | air
  | prism
  deriving DecidableEq, Repr

/-- The two numerical angle labels printed in the primary image. -/
inductive FigureAngleLabel where
  | prismAcuteAngle
  | theta
  deriving DecidableEq, Repr

/-- Incident medium along the shown propagation direction at each interface. -/
def incidentMedium : RefractingInterface → OpticalMedium
  | .entryFace => .air
  | .hypotenuse => .prism

/-- Transmitted medium along the shown propagation direction at each
interface. -/
def transmittedMedium : RefractingInterface → OpticalMedium
  | .entryFace => .prism
  | .hypotenuse => .air

/-! ## Physical setup and primary-image readouts -/

/--
Physical quantities and labelled geometry carried by the prism diagram.

Incidence and refraction angles are measured from the normal directed toward
the transmitted medium.  `exitDeviationAngle` is instead the angle between
the transmitted ray and the original incident-ray direction, as indicated by
the horizontal dashed reference line in the primary image.
-/
structure PrismRefractionDiagram where
  /-- Dimensionless refractive index of each homogeneous optical medium. -/
  refractiveIndex : OpticalMedium → ℝ
  /-- Incident angle from the interface normal. -/
  incidenceAngle : RefractingInterface → Real.Angle
  /-- Transmitted angle from the interface normal. -/
  refractionAngle : RefractingInterface → Real.Angle
  /-- Deviation of the emergent ray from the incident-ray direction. -/
  exitDeviationAngle : Real.Angle
  /-- Physical angle associated to each printed figure label. -/
  angleForLabel : FigureAngleLabel → Real.Angle
  /-- Smaller interior angle between two labelled prism faces. -/
  angleBetweenFaces : PrismFace → PrismFace → Real.Angle
  /-- Nonzero direction vector of each laser-ray segment. -/
  rayDirection : RaySegment → RayVector ℝ DiagramPlane
  /-- Normal direction at each interface, oriented toward the transmitted
  medium along the shown propagation path. -/
  interfaceNormalDirection :
    RefractingInterface → RayVector ℝ DiagramPlane
  /-- Whether a named ray segment is depicted. -/
  raySegmentDepicted : RaySegment → Prop
  /-- Whether a named prism face is depicted. -/
  faceDepicted : PrismFace → Prop
  /-- Whether the dashed continuation of the incident direction is depicted. -/
  incidentDirectionReferenceDepicted : Prop

/--
Textual and primary-image readouts.  These premises record the right-isosceles
prism, normal entry, the `45°` and `θ = 15°` labels, and the ambient-air index.
They do not assign any value to the prism's refractive index.
-/
structure MatchesPrismFigure (diagram : PrismRefractionDiagram) : Prop where
  allRaySegmentsDepicted : ∀ ray, diagram.raySegmentDepicted ray
  allFacesDepicted : ∀ face, diagram.faceDepicted face
  incidentDirectionReferenceDepicted :
    diagram.incidentDirectionReferenceDepicted
  incidentRayNormalToEntryFace :
    diagram.rayDirection .incoming =
      diagram.interfaceNormalDirection .entryFace
  thetaLabelsExitDeviation :
    diagram.angleForLabel .theta = diagram.exitDeviationAngle
  thetaReadout :
    diagram.angleForLabel .theta = angleFromDegrees 15
  acuteLabelMatchesBaseHypotenuseAngle :
    diagram.angleForLabel .prismAcuteAngle =
      diagram.angleBetweenFaces .base .hypotenuse
  acuteAngleReadout :
    diagram.angleForLabel .prismAcuteAngle = angleFromDegrees 45
  rightAngleAtEntryBaseVertex :
    diagram.angleBetweenFaces .entryFace .base = angleFromDegrees 90
  airIndexReadout : diagram.refractiveIndex .air = 1

/-- An incidence or refraction angle lies on the physical branch used in the
drawing, including normal incidence and excluding grazing incidence. -/
def IsPhysicalRayAngle (angle : Real.Angle) : Prop :=
  0 ≤ angle.toReal ∧ angle.toReal < Real.pi / 2

/-- Positivity and acute-branch assumptions for the elementary optical model. -/
structure HasPhysicalOpticalParameters
    (diagram : PrismRefractionDiagram) : Prop where
  refractiveIndexPositive :
    ∀ medium, 0 < diagram.refractiveIndex medium
  incidenceAnglesPhysical :
    ∀ interface, IsPhysicalRayAngle (diagram.incidenceAngle interface)
  refractionAnglesPhysical :
    ∀ interface, IsPhysicalRayAngle (diagram.refractionAngle interface)
  exitDeviationPhysical : IsPhysicalRayAngle diagram.exitDeviationAngle

/-! ## Governing optics and prism-ray geometry -/

/-- Snell's law `n₁ sin θ₁ = n₂ sin θ₂` at one labelled interface. -/
def SnellsLawAt
    (diagram : PrismRefractionDiagram)
    (interface : RefractingInterface) : Prop :=
  diagram.refractiveIndex (incidentMedium interface) *
      Real.Angle.sin (diagram.incidenceAngle interface) =
    diagram.refractiveIndex (transmittedMedium interface) *
      Real.Angle.sin (diagram.refractionAngle interface)

/-- The laser obeys Snell's law when entering and leaving the prism. -/
structure ObeysSnellsLaw (diagram : PrismRefractionDiagram) : Prop where
  atInterface : ∀ interface, SnellsLawAt diagram interface

/--
Relations supplied by normal entry and the displayed 45-45-90 geometry.
At the hypotenuse the normal is `45°` above the incident direction, while the
emergent ray is `15°` below it, so the exit refraction angle is the sum of the
exit incidence and deviation angles.  No relation here fixes a refractive
index or an answer choice.
-/
structure MatchesPrismRayGeometry
    (diagram : PrismRefractionDiagram) : Prop where
  entryIncidenceIsZero :
    diagram.incidenceAngle .entryFace = angleFromDegrees 0
  entryRefractionIsZero :
    diagram.refractionAngle .entryFace = angleFromDegrees 0
  normalEntryContinuesStraight :
    diagram.rayDirection .insidePrism = diagram.rayDirection .incoming
  exitIncidenceFromAcutePrismAngle :
    diagram.incidenceAngle .hypotenuse =
      diagram.angleForLabel .prismAcuteAngle
  exitRefractionFromDeviation :
    diagram.refractionAngle .hypotenuse =
      diagram.incidenceAngle .hypotenuse + diagram.exitDeviationAngle

/-! ## Multiple-choice target -/

/-- Labels of the four displayed answer choices. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Dimensionless refractive-index readout printed for each answer choice. -/
def AnswerChoice.refractiveIndexReadout : AnswerChoice → ℝ
  | .A => 1.09
  | .B => 1.38
  | .C => 1.22
  | .D => 1.45

/-- Dataset metadata: the recorded answer label is C.  This definition is not
used as a premise of the target theorem. -/
def recordedAnswerChoice : AnswerChoice := .C

/-- A physical index rounds to the displayed value to the nearest hundredth.
The strict half-hundredth bound excludes ties. -/
def RoundsToNearestHundredth
    (actualIndex displayedIndex : ℝ) : Prop :=
  |actualIndex - displayedIndex| < 1 / 200

/-- A displayed choice is strictly nearer to the physical refractive index
than every other displayed choice. -/
def IsNearestAnswerChoice
    (actualIndex : ℝ) (choice : AnswerChoice) : Prop :=
  ∀ otherChoice : AnswerChoice,
    otherChoice ≠ choice →
      |actualIndex - choice.refractiveIndexReadout| <
        |actualIndex - otherChoice.refractiveIndexReadout|

/--
**Physics formalization target
(`thm:physics:phyx_mini_0006:target`).**

For the depicted normal-entry `45°` prism path with a `15°` emergent
deviation, Snell's law determines the prism index exactly as `sqrt (3 / 2)`.
That value rounds to `1.22` and is uniquely closest to answer C.
-/
theorem prismRefractiveIndexIsAnswerC
    (diagram : PrismRefractionDiagram)
    (hFigure : MatchesPrismFigure diagram)
    (hParameters : HasPhysicalOpticalParameters diagram)
    (hGeometry : MatchesPrismRayGeometry diagram)
    (hSnell : ObeysSnellsLaw diagram) :
    diagram.refractiveIndex .prism = Real.sqrt ((3 : ℝ) / 2) ∧
      RoundsToNearestHundredth
        (diagram.refractiveIndex .prism)
        AnswerChoice.C.refractiveIndexReadout ∧
      IsNearestAnswerChoice
        (diagram.refractiveIndex .prism) .C := by
  have hExitIncidence :
      diagram.incidenceAngle .hypotenuse = angleFromDegrees 45 := by
    calc
      diagram.incidenceAngle .hypotenuse =
          diagram.angleForLabel .prismAcuteAngle :=
        hGeometry.exitIncidenceFromAcutePrismAngle
      _ = angleFromDegrees 45 := hFigure.acuteAngleReadout
  have hExitDeviation :
      diagram.exitDeviationAngle = angleFromDegrees 15 := by
    calc
      diagram.exitDeviationAngle = diagram.angleForLabel .theta :=
        hFigure.thetaLabelsExitDeviation.symm
      _ = angleFromDegrees 15 := hFigure.thetaReadout
  have hExitRefraction :
      diagram.refractionAngle .hypotenuse = angleFromDegrees 60 := by
    rw [hGeometry.exitRefractionFromDeviation, hExitIncidence, hExitDeviation]
    change ((45 * Real.pi / 180 : ℝ) : Real.Angle) +
        ((15 * Real.pi / 180 : ℝ) : Real.Angle) =
      ((60 * Real.pi / 180 : ℝ) : Real.Angle)
    rw [← Real.Angle.coe_add]
    congr 1
    ring
  have hSin45 :
      Real.Angle.sin (angleFromDegrees 45) = Real.sqrt 2 / 2 := by
    change Real.sin (45 * Real.pi / 180) = _
    rw [show (45 : ℝ) * Real.pi / 180 = Real.pi / 4 by ring]
    exact Real.sin_pi_div_four
  have hSin60 :
      Real.Angle.sin (angleFromDegrees 60) = Real.sqrt 3 / 2 := by
    change Real.sin (60 * Real.pi / 180) = _
    rw [show (60 : ℝ) * Real.pi / 180 = Real.pi / 3 by ring]
    exact Real.sin_pi_div_three
  have hSnellExit := hSnell.atInterface .hypotenuse
  unfold SnellsLawAt incidentMedium transmittedMedium at hSnellExit
  rw [hExitIncidence, hExitRefraction, hFigure.airIndexReadout,
    hSin45, hSin60] at hSnellExit
  have hSqrtTwoPositive : 0 < Real.sqrt (2 : ℝ) :=
    Real.sqrt_pos.2 (by norm_num)
  have hIndexAsQuotient :
      diagram.refractiveIndex .prism = Real.sqrt 3 / Real.sqrt 2 := by
    apply (eq_div_iff (ne_of_gt hSqrtTwoPositive)).2
    nlinarith [hSnellExit, hParameters.refractiveIndexPositive .prism]
  have hIndex :
      diagram.refractiveIndex .prism = Real.sqrt ((3 : ℝ) / 2) := by
    calc
      diagram.refractiveIndex .prism = Real.sqrt 3 / Real.sqrt 2 :=
        hIndexAsQuotient
      _ = Real.sqrt ((3 : ℝ) / 2) :=
        (Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 3) 2).symm
  have hLower :
      (153 : ℝ) / 125 < Real.sqrt ((3 : ℝ) / 2) :=
    (Real.lt_sqrt (by norm_num)).2 (by norm_num)
  have hUpper :
      Real.sqrt ((3 : ℝ) / 2) < (49 : ℝ) / 40 :=
    (Real.sqrt_lt' (by norm_num)).2 (by norm_num)
  refine ⟨hIndex, ?_, ?_⟩
  · rw [hIndex]
    unfold RoundsToNearestHundredth AnswerChoice.refractiveIndexReadout
    rw [abs_of_nonneg (by linarith [hLower])]
    linarith [hUpper]
  · rw [hIndex]
    unfold IsNearestAnswerChoice
    intro otherChoice hOtherChoice
    cases otherChoice with
    | A =>
        unfold AnswerChoice.refractiveIndexReadout
        rw [abs_of_nonneg (by linarith [hLower])]
        rw [abs_of_nonneg (by linarith [hLower])]
        norm_num
    | B =>
        unfold AnswerChoice.refractiveIndexReadout
        rw [abs_of_nonneg (by linarith [hLower])]
        rw [abs_of_nonpos (by linarith [hUpper])]
        linarith [hUpper]
    | C =>
        exact (hOtherChoice rfl).elim
    | D =>
        unfold AnswerChoice.refractiveIndexReadout
        rw [abs_of_nonneg (by linarith [hLower])]
        rw [abs_of_nonpos (by linarith [hUpper])]
        linarith [hUpper]

end

end PhyXMiniProblems.ProblemPhyxMini0006
