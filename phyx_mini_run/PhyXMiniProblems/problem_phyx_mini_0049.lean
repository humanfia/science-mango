import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic
import Mathlib.LinearAlgebra.Ray
import Physlib.Units.WithDim.Basic

/-!
# Direction of a laser after a parallel glass sheet

This file formalizes `phyx_mini_0049`.  The laser crosses two parallel
air--glass interfaces.  Length is represented dimensionfully, refractive
indices are dimensionless, ray directions are nonzero vectors in the diagram
plane, and scalar angle readouts are measured in radians.

The source image belongs to a different mirror-and-room problem.  Its labels
are retained below in a separate auxiliary structure and are deliberately not
used as premises of the glass-sheet theorem.
-/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0049

open CarriesDimension Dimension

/-! ## Units and geometric roles -/

/-- A physical length whose scalar carrier is real-valued. -/
abbrev DimLength := Dimensionful (WithDim L𝓭 ℝ)

/-- Unit choices in which length readouts are expressed in centimeters. -/
def centimeterUnitChoices : UnitChoices :=
  { UnitChoices.SI with length := LengthUnit.centimeters }

/-- The dimensionful sheet thickness specified by the problem, `1.0 cm`. -/
noncomputable def oneCentimeter : DimLength :=
  toDimensionful centimeterUnitChoices ⟨1⟩

/-- Convert a degree readout to the radian scalar used by `Real.sin`. -/
def degreesToRadians (angleDegrees : ℝ) : ℝ :=
  angleDegrees * Real.pi / 180

/-- The two-dimensional plane of the ray diagram. -/
abbrev DiagramPlane := EuclideanSpace ℝ (Fin 2)

/-- A geometric propagation direction is a nonzero vector in the diagram plane. -/
abbrev RayDirection := RayVector ℝ DiagramPlane

/-- The three homogeneous optical regions traversed in propagation order. -/
inductive OpticalRegion where
  | incidentAir
  | glass
  | emergentAir
  deriving DecidableEq, Repr

/-- The parallel entry and exit faces of the sheet. -/
inductive SheetInterface where
  | entryFace
  | exitFace
  deriving DecidableEq, Repr

/-- The three directed portions of the laser path. -/
inductive RaySegment where
  | incoming
  | insideGlass
  | outgoing
  deriving DecidableEq, Repr

/-- Incident optical region at each interface, in propagation order. -/
def incidentRegion : SheetInterface → OpticalRegion
  | .entryFace => .incidentAir
  | .exitFace => .glass

/-- Transmitted optical region at each interface, in propagation order. -/
def transmittedRegion : SheetInterface → OpticalRegion
  | .entryFace => .glass
  | .exitFace => .emergentAir

/-- Ray segment incident on each interface. -/
def incidentSegment : SheetInterface → RaySegment
  | .entryFace => .incoming
  | .exitFace => .insideGlass

/-- Ray segment transmitted through each interface. -/
def transmittedSegment : SheetInterface → RaySegment
  | .entryFace => .insideGlass
  | .exitFace => .outgoing

/-! ## Glass-sheet data and governing laws -/

/--
Physical quantities and labelled geometry for the parallel glass sheet.

Each face normal points in the direction of propagation through that face.
The incidence and refraction angles are scalar radian readouts measured from
those normals.  `incomingElevationRadians` is instead measured above the sheet
surface, matching the wording of the problem.
-/
structure ParallelGlassSheetDiagram where
  /-- Physical thickness of the glass sheet. -/
  thickness : DimLength
  /-- Dimensionless refractive index in each homogeneous optical region. -/
  refractiveIndex : OpticalRegion → ℝ
  /-- Nonzero propagation direction of each laser-ray segment. -/
  rayDirection : RaySegment → RayDirection
  /-- Propagation-oriented normal direction at each sheet face. -/
  faceNormalDirection : SheetInterface → RayDirection
  /-- A consistently oriented tangent direction along each sheet face. -/
  faceTangentDirection : SheetInterface → RayDirection
  /-- Angle from the face normal of the incident ray at each interface. -/
  incidenceAngleRadians : SheetInterface → ℝ
  /-- Angle from the face normal of the transmitted ray at each interface. -/
  refractionAngleRadians : SheetInterface → ℝ
  /-- Elevation of the incoming ray above the entry-face surface. -/
  incomingElevationRadians : ℝ

/-- The undirected radian angle between two nonzero diagram directions. -/
def angleBetweenDirections (first second : RayDirection) : ℝ :=
  InnerProductGeometry.angle first.1 second.1

/-- An angle readout lies on the acute geometrical-optics branch. -/
def IsPhysicalAcuteAngle (angleRadians : ℝ) : Prop :=
  0 ≤ angleRadians ∧ angleRadians ≤ Real.pi / 2

/--
Textual problem data: a `1.0 cm` glass sheet, a `30°` incoming elevation,
and the same ambient air on both sides.  No outgoing-angle value is recorded
here.
-/
structure MatchesGlassSheetProblemData
    (diagram : ParallelGlassSheetDiagram) : Prop where
  thicknessReadout : diagram.thickness = oneCentimeter
  incomingElevationReadout :
    diagram.incomingElevationRadians = degreesToRadians 30
  sameAmbientAirOnBothSides :
    diagram.refractiveIndex .incidentAir =
      diagram.refractiveIndex .emergentAir

/-- Positivity and principal-branch conditions for the optical model. -/
structure HasPhysicalOpticalParameters
    (diagram : ParallelGlassSheetDiagram) : Prop where
  refractiveIndexPositive :
    ∀ region, 0 < diagram.refractiveIndex region
  incidenceAnglesPhysical :
    ∀ interface, IsPhysicalAcuteAngle (diagram.incidenceAngleRadians interface)
  refractionAnglesPhysical :
    ∀ interface, IsPhysicalAcuteAngle (diagram.refractionAngleRadians interface)
  incomingElevationPhysical :
    IsPhysicalAcuteAngle diagram.incomingElevationRadians

/--
Geometric relations supplied by the ray diagram and the parallel planar
faces.  In particular, the internal ray meets both equal-oriented normals at
the same angle.  The incoming elevation and entry incidence are complementary.
-/
structure SatisfiesParallelSheetGeometry
    (diagram : ParallelGlassSheetDiagram) : Prop where
  parallelFaceNormals :
    diagram.faceNormalDirection .entryFace =
      diagram.faceNormalDirection .exitFace
  parallelFaceTangents :
    diagram.faceTangentDirection .entryFace =
      diagram.faceTangentDirection .exitFace
  tangentNormalPerpendicular :
    ∀ interface,
      angleBetweenDirections
          (diagram.faceTangentDirection interface)
          (diagram.faceNormalDirection interface) =
        Real.pi / 2
  incidenceAngleFromDirections :
    ∀ interface,
      diagram.incidenceAngleRadians interface =
        angleBetweenDirections
          (diagram.rayDirection (incidentSegment interface))
          (diagram.faceNormalDirection interface)
  refractionAngleFromDirections :
    ∀ interface,
      diagram.refractionAngleRadians interface =
        angleBetweenDirections
          (diagram.rayDirection (transmittedSegment interface))
          (diagram.faceNormalDirection interface)
  incomingElevationFromDirections :
    diagram.incomingElevationRadians =
      angleBetweenDirections
        (diagram.rayDirection .incoming)
        (diagram.faceTangentDirection .entryFace)
  incomingAnglesComplementary :
    diagram.incomingElevationRadians +
        diagram.incidenceAngleRadians .entryFace =
      Real.pi / 2
  internalAnglePreservedByParallelFaces :
    diagram.refractionAngleRadians .entryFace =
      diagram.incidenceAngleRadians .exitFace

/-- Snell's law `n₁ sin θ₁ = n₂ sin θ₂` at one sheet interface. -/
def SatisfiesSnellsLawAt
    (diagram : ParallelGlassSheetDiagram)
    (interface : SheetInterface) : Prop :=
  diagram.refractiveIndex (incidentRegion interface) *
      Real.sin (diagram.incidenceAngleRadians interface) =
    diagram.refractiveIndex (transmittedRegion interface) *
      Real.sin (diagram.refractionAngleRadians interface)

/-- The laser obeys Snell's law at both faces of the glass sheet. -/
structure ObeysSnellsLaw (diagram : ParallelGlassSheetDiagram) : Prop where
  atInterface : ∀ interface, SatisfiesSnellsLawAt diagram interface

/-! ## Auxiliary, mismatched source-image labels -/

/--
Labels visible in the supplied auxiliary image, which depicts a bulb and a
vertical mirror rather than the glass-sheet scenario.  Distances are scalar
meter readouts; `thetaOneRadians` and `thetaTwoRadians` are the displayed
angle labels.  The unknown horizontal labels `l₁` and `l₂` remain parameters.
-/
structure AuxiliaryMirrorRoomFigure where
  roomHeightMetres : ℝ
  bulbToRightWallMetres : ℝ
  mirrorTopGapMetres : ℝ
  mirrorHeightMetres : ℝ
  mirrorBottomGapMetres : ℝ
  lOneMetres : ℝ
  lTwoMetres : ℝ
  thetaOneRadians : ℝ
  thetaTwoRadians : ℝ

/-- Numerical length readouts visible in the mismatched auxiliary image. -/
structure MatchesAuxiliaryMirrorRoomImage
    (figure : AuxiliaryMirrorRoomFigure) : Prop where
  roomHeightReadout : figure.roomHeightMetres = 2.50
  bulbToRightWallReadout : figure.bulbToRightWallMetres = 1.00
  mirrorTopGapReadout : figure.mirrorTopGapMetres = 0.50
  mirrorHeightReadout : figure.mirrorHeightMetres = 1.50
  mirrorBottomGapReadout : figure.mirrorBottomGapMetres = 0.50
  lOnePositive : 0 < figure.lOneMetres
  lTwoPositive : 0 < figure.lTwoMetres

/-! ## Multiple-choice target -/

/-- The four displayed answer labels. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Direction-angle readout in degrees printed beside each answer choice. -/
def AnswerChoice.directionDegrees : AnswerChoice → ℝ
  | .A => 64.0
  | .B => 60.0
  | .C => 50.0
  | .D => 56.0

/-- Dataset metadata: the recorded answer label, not a theorem premise. -/
def recordedAnswerChoice : AnswerChoice := .B

/--
For a ray entering a `1.0 cm` parallel glass sheet at an elevation of `30°`
above its surface, Snell's law at the two parallel faces and equal air media
make the outgoing angle from the exit-face normal `60°`, answer B.

Blueprint: `thm:physics:phyx_mini_0049:target`.
-/
theorem outgoingDirectionIsAnswerB
    (diagram : ParallelGlassSheetDiagram)
    (hProblemData : MatchesGlassSheetProblemData diagram)
    (hPhysical : HasPhysicalOpticalParameters diagram)
    (hGeometry : SatisfiesParallelSheetGeometry diagram)
    (hSnell : ObeysSnellsLaw diagram) :
    diagram.refractionAngleRadians .exitFace =
      degreesToRadians AnswerChoice.B.directionDegrees := by
  rcases hPhysical.incidenceAnglesPhysical .entryFace with
    ⟨hEntryNonneg, hEntryLe⟩
  rcases hPhysical.refractionAnglesPhysical .exitFace with
    ⟨hExitNonneg, hExitLe⟩
  have hEntry := hSnell.atInterface .entryFace
  have hExit := hSnell.atInterface .exitFace
  simp only [SatisfiesSnellsLawAt, incidentRegion, transmittedRegion] at hEntry hExit
  rw [hGeometry.internalAnglePreservedByParallelFaces] at hEntry
  rw [← hProblemData.sameAmbientAirOnBothSides] at hExit
  have hSin :
      Real.sin (diagram.incidenceAngleRadians .entryFace) =
        Real.sin (diagram.refractionAngleRadians .exitFace) := by
    have hAirIndexNe :=
      ne_of_gt (hPhysical.refractiveIndexPositive .incidentAir)
    apply mul_left_cancel₀ hAirIndexNe
    linarith
  have hAngles := Real.injOn_sin
    (show diagram.incidenceAngleRadians .entryFace ∈
        Set.Icc (-(Real.pi / 2)) (Real.pi / 2) by
      constructor
      · linarith [Real.pi_pos]
      · exact hEntryLe)
    (show diagram.refractionAngleRadians .exitFace ∈
        Set.Icc (-(Real.pi / 2)) (Real.pi / 2) by
      constructor
      · linarith [Real.pi_pos]
      · exact hExitLe)
    hSin
  rw [← hAngles]
  have hComplement := hGeometry.incomingAnglesComplementary
  rw [hProblemData.incomingElevationReadout] at hComplement
  norm_num [degreesToRadians, AnswerChoice.directionDegrees] at hComplement ⊢
  linarith

end PhyXMiniProblems.ProblemPhyXMini0049
