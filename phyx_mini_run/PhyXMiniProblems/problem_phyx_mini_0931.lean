import Mathlib
import Physlib.Electromagnetism.Basic
import Physlib.Units.WithDim.Speed

/- USER: The assigned source file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0931

open Dimension

/-!
# Maximum induced current while a diamond-oriented square enters a field

The primary raster shows a square conducting loop, drawn as a diamond, moving
rightward into a half-plane containing a uniform `0.80 T` magnetic field.  The
field points into the page.  Each side of the loop is `10 cm`, its speed is
`10 m/s`, its resistance is `0.10 Ω`, and its leading vertex reaches the field
boundary at `t = 0 s`.

At the instant when the vertical field boundary cuts the square along its
vertical diagonal, the swept-area rate is maximal.  That diagonal has length
`s * √2`, so Faraday's law and Ohm's law give

`I_max = B * v * s * √2 / R = 8 * √2 A ≈ 11.31 A`.

Thus the closest displayed integer current is `11 A`, answer B.

All lengths, times, speeds, resistance, field strength, areas, fluxes, emfs,
and currents below are unit-independent Physlib quantities.  Real numbers are
used only for coherent-SI readouts, dimensionless diagram coordinates, and
the scalar values printed in the multiple-choice answers.

Assumption/target split:

* governing laws: constant translation, square-diagonal and boundary-sweep
  geometry, uniform half-plane field, `Φ = B A`, Faraday's law, and Ohm's law;
* previous-part results: none;
* figure/data readouts: diamond-oriented orange square, two `10 cm` guides,
  dashed vertical boundary, rightward `10 m/s` arrow, into-page field crosses,
  `B = 0.80 T`, `R = 0.10 Ω`, and entry at `t = 0 s`;
* current targets: the maximum-current formula, its exact value `8 * √2 A`,
  and selection of the closest displayed value, answer B (`11 A`).

No setup field or premise contains a maximum-current value or answer choice.
-/

/-! ## Dimensionful physical quantities and coherent-SI readouts -/

/-- Physical dimension `L²` of area. -/
def areaDimension : Dimension :=
  L𝓭 * L𝓭

/-- Physical dimension `L² T⁻¹` of an area-change rate. -/
def areaRateDimension : Dimension :=
  areaDimension * T𝓭⁻¹

/-- Physical dimension `M T⁻¹ C⁻¹` of magnetic flux density. -/
def magneticFluxDensityDimension : Dimension :=
  M𝓭 * T𝓭⁻¹ * C𝓭⁻¹

/-- Physical dimension `M L² T⁻¹ C⁻¹` of magnetic flux. -/
def magneticFluxDimension : Dimension :=
  magneticFluxDensityDimension * areaDimension

/-- Physical dimension `M L² T⁻² C⁻¹` of electromotive force. -/
def electromotiveForceDimension : Dimension :=
  magneticFluxDimension * T𝓭⁻¹

/-- Physical dimension `C T⁻¹` of electric current. -/
def electricCurrentDimension : Dimension :=
  C𝓭 * T𝓭⁻¹

/-- Physical dimension `M L² T⁻¹ C⁻²` of electrical resistance. -/
def electricalResistanceDimension : Dimension :=
  M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * C𝓭⁻¹ * C𝓭⁻¹

/-- A nonnegative, unit-independent physical length. -/
abbrev LengthQuantity : Type :=
  Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative, unit-independent clock time. -/
abbrev TimeQuantity : Type :=
  Dimensionful (WithDim T𝓭 NNReal)

/-- A nonnegative, unit-independent speed. -/
abbrev SpeedQuantity : Type := DimSpeed

/-- A nonnegative, unit-independent area. -/
abbrev AreaQuantity : Type :=
  Dimensionful (WithDim areaDimension NNReal)

/-- Magnitude of the instantaneous overlap-area change rate. -/
abbrev AreaRateMagnitudeQuantity : Type :=
  Dimensionful (WithDim areaRateDimension NNReal)

/-- A nonnegative magnetic-flux-density magnitude. -/
abbrev MagneticFluxDensityQuantity : Type :=
  Dimensionful (WithDim magneticFluxDensityDimension NNReal)

/-- Magnitude of magnetic flux through the portion of loop in the field. -/
abbrev MagneticFluxMagnitudeQuantity : Type :=
  Dimensionful (WithDim magneticFluxDimension NNReal)

/-- Magnitude of a magnetic-flux change rate. -/
abbrev MagneticFluxRateMagnitudeQuantity : Type :=
  Dimensionful (WithDim electromotiveForceDimension NNReal)

/-- Magnitude of an induced electromotive force. -/
abbrev EmfMagnitudeQuantity : Type :=
  Dimensionful (WithDim electromotiveForceDimension NNReal)

/-- A nonnegative electrical resistance. -/
abbrev ResistanceQuantity : Type :=
  Dimensionful (WithDim electricalResistanceDimension NNReal)

/-- Magnitude of an induced electric current. -/
abbrev CurrentMagnitudeQuantity : Type :=
  Dimensionful (WithDim electricCurrentDimension NNReal)

/-- Coherent-SI readout of a nonnegative dimensionful quantity. -/
def nonnegativeSIReadout {dimension : Dimension}
    (quantity : Dimensionful (WithDim dimension NNReal)) : ℝ :=
  ((quantity UnitChoices.SI).val : ℝ)

/-- Metre readout of a physical length. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  nonnegativeSIReadout length

/-- Centimetre readout used by the two side-length guides. -/
def lengthInCentimeters (length : LengthQuantity) : ℝ :=
  100 * lengthInMeters length

/-- Second readout of a physical clock time. -/
def timeInSeconds (time : TimeQuantity) : ℝ :=
  nonnegativeSIReadout time

/-- Metre-per-second readout of a speed. -/
def speedInMetersPerSecond (speed : SpeedQuantity) : ℝ :=
  ((speed UnitChoices.SI).val : ℝ)

/-- Square-metre readout of an area. -/
def areaInSquareMeters (area : AreaQuantity) : ℝ :=
  nonnegativeSIReadout area

/-- Square-metre-per-second readout of an area-rate magnitude. -/
def areaRateInSquareMetersPerSecond
    (rate : AreaRateMagnitudeQuantity) : ℝ :=
  nonnegativeSIReadout rate

/-- Tesla readout of magnetic flux density. -/
def magneticFluxDensityInTeslas
    (density : MagneticFluxDensityQuantity) : ℝ :=
  nonnegativeSIReadout density

/-- Weber readout of a magnetic-flux magnitude. -/
def magneticFluxInWebers (flux : MagneticFluxMagnitudeQuantity) : ℝ :=
  nonnegativeSIReadout flux

/-- Weber-per-second readout of a magnetic-flux-rate magnitude. -/
def magneticFluxRateInWebersPerSecond
    (rate : MagneticFluxRateMagnitudeQuantity) : ℝ :=
  nonnegativeSIReadout rate

/-- Volt readout of an induced-emf magnitude. -/
def emfMagnitudeInVolts (emf : EmfMagnitudeQuantity) : ℝ :=
  nonnegativeSIReadout emf

/-- Ohm readout of an electrical resistance. -/
def resistanceInOhms (resistance : ResistanceQuantity) : ℝ :=
  nonnegativeSIReadout resistance

/-- Ampere readout of an electric-current magnitude. -/
def currentMagnitudeInAmperes (current : CurrentMagnitudeQuantity) : ℝ :=
  nonnegativeSIReadout current

/-! ## Diagram geometry and literal figure vocabulary -/

/-- A dimensionless direction vector in physical three-space. -/
abbrev DirectionVector : Type := EuclideanSpace ℝ (Fin 3)

/-- Unit direction pointing right in the plane of the figure. -/
def rightwardUnitVector : DirectionVector :=
  EuclideanSpace.single (0 : Fin 3) 1

/-- Unit direction pointing into the page. -/
def intoPageUnitVector : DirectionVector :=
  -EuclideanSpace.single (2 : Fin 3) 1

/-- Horizontal coordinate used to describe the field half-plane. -/
def horizontalAxis : Fin 3 := 0

/-- The four vertices of the diamond-oriented square. -/
inductive LoopVertex where
  | left
  | top
  | right
  | bottom
  deriving DecidableEq, Fintype, Repr

/-- The four equal sides of the square loop. -/
inductive LoopSide where
  | upperLeft
  | upperRight
  | lowerRight
  | lowerLeft
  deriving DecidableEq, Fintype, Repr

/-- The two sides carrying explicit `10 cm` dimension guides in the raster. -/
inductive GuidedSide where
  | upperLeft
  | upperRight
  deriving DecidableEq, Fintype, Repr

/-- Directions used for arrows and magnetic-field glyphs in the raster. -/
inductive DiagramDirection where
  | leftward
  | rightward
  | intoPage
  | outOfPage
  deriving DecidableEq, Repr

/-- Stroke colors visible in the supplied raster. -/
inductive DiagramColor where
  | orange
  | green
  | blue
  | black
  deriving DecidableEq, Repr

/-- The cross/dot convention used for page-normal vectors. -/
inductive PageNormalGlyph where
  | cross
  | dot
  deriving DecidableEq, Repr

/-- Geometric role assigned to the conducting loop. -/
inductive LoopShape where
  | square
  | other
  deriving DecidableEq, Repr

/-- In-plane orientation of the square in the supplied image. -/
inductive SquareOrientation where
  | diamond
  | axisAligned
  deriving DecidableEq, Repr

/-- Topological role assigned to the conductor. -/
inductive ConductorTopology where
  | closedSingleLoop
  | other
  deriving DecidableEq, Repr

/-- Motion model asserted by the problem statement. -/
inductive TranslationModel where
  | constantRightwardSpeed
  | other
  deriving DecidableEq, Repr

/-!
Literal presentation data transcribed from image `931.png`.  The displayed
scalars are calibrated to independent physical quantities below; no induced
current or answer-choice value is a field of this structure.
-/
structure MovingSquareLoopFigure where
  loopVertexShown : LoopVertex → Bool
  loopSideShown : LoopSide → Bool
  loopStrokeColor : DiagramColor
  loopDrawnAsDiamond : Bool
  sideLengthGuideShown : GuidedSide → Bool
  displayedSideLengthCentimeters : GuidedSide → ℝ
  boundaryLineShown : Bool
  boundaryLineVertical : Bool
  boundaryLineDashed : Bool
  fieldShownToRightOfBoundary : Bool
  fieldGlyphShown : Bool
  fieldGlyph : PageNormalGlyph
  fieldGlyphColor : DiagramColor
  fieldDirection : DiagramDirection
  displayedFieldMagnitudeTeslas : ℝ
  velocityArrowShown : Bool
  velocityArrowColor : DiagramColor
  velocityArrowDirection : DiagramDirection
  displayedSpeedMetersPerSecond : ℝ

/-! ## Independent physical setup -/

/-!
The loop, field, geometry, clock, and independent electromagnetic observables.
The maximum current is deliberately absent: `inducedCurrentMagnitudeAt` is an
arbitrary time-dependent physical observable constrained only by later laws.
-/
structure MovingSquareLoopSetup where
  topology : ConductorTopology
  loopShape : LoopShape
  squareOrientation : SquareOrientation
  translationModel : TranslationModel
  sideLength : LengthQuantity
  verticalDiagonalLength : LengthQuantity
  translationSpeed : SpeedQuantity
  loopResistance : ResistanceQuantity
  magneticFluxDensity : MagneticFluxDensityQuantity
  entryTime : TimeQuantity
  horizontalDisplacementSinceEntry : TimeQuantity → LengthQuantity
  overlapAreaAt : TimeQuantity → AreaQuantity
  overlapAreaGrowthRateMagnitudeAt : TimeQuantity → AreaRateMagnitudeQuantity
  magneticFluxMagnitudeAt : TimeQuantity → MagneticFluxMagnitudeQuantity
  magneticFluxChangeRateMagnitudeAt :
    TimeQuantity → MagneticFluxRateMagnitudeQuantity
  inducedEmfMagnitudeAt : TimeQuantity → EmfMagnitudeQuantity
  inducedCurrentMagnitudeAt : TimeQuantity → CurrentMagnitudeQuantity
  magneticField : Electromagnetism.MagneticField 3
  fieldRegion : Space 3 → Prop
  fieldBoundaryXCoordinate : ℝ
  loopVelocityDirection : DirectionVector
  magneticFieldDirection : DirectionVector
  figure : MovingSquareLoopFigure

/-! ## Scenario, image evidence, measurements, and governing laws -/

/-- Qualitative apparatus and motion roles stated by the problem. -/
structure MatchesMovingSquareLoopScenario
    (setup : MovingSquareLoopSetup) : Prop where
  conductorIsClosedSingleLoop : setup.topology = .closedSingleLoop
  conductorIsSquare : setup.loopShape = .square
  squareHasDiamondOrientation : setup.squareOrientation = .diamond
  motionIsConstantAndRightward :
    setup.translationModel = .constantRightwardSpeed
  velocityDirectionIsRightward :
    setup.loopVelocityDirection = rightwardUnitVector

/-! Literal visual features and numerical labels from the primary raster. -/
structure MatchesSuppliedMovingSquareLoopFigure
    (setup : MovingSquareLoopSetup) : Prop where
  allVerticesShown : ∀ vertex, setup.figure.loopVertexShown vertex = true
  allSidesShown : ∀ side, setup.figure.loopSideShown side = true
  loopIsOrange : setup.figure.loopStrokeColor = .orange
  diamondIsShown : setup.figure.loopDrawnAsDiamond = true
  bothSideGuidesShown : ∀ side,
    setup.figure.sideLengthGuideShown side = true
  bothSideGuidesReadTenCentimeters : ∀ side,
    setup.figure.displayedSideLengthCentimeters side = 10
  sideGuidesCalibratePhysicalSide : ∀ side,
    lengthInCentimeters setup.sideLength =
      setup.figure.displayedSideLengthCentimeters side
  dashedVerticalBoundaryShown :
    setup.figure.boundaryLineShown = true ∧
      setup.figure.boundaryLineVertical = true ∧
      setup.figure.boundaryLineDashed = true
  fieldIsDrawnToRight : setup.figure.fieldShownToRightOfBoundary = true
  blueCrossFieldGlyphs :
    setup.figure.fieldGlyphShown = true ∧
      setup.figure.fieldGlyph = .cross ∧
      setup.figure.fieldGlyphColor = .blue
  crossesMeanIntoPage : setup.figure.fieldDirection = .intoPage
  printedFieldMagnitude : setup.figure.displayedFieldMagnitudeTeslas = 4 / 5
  physicalFieldMatchesLabel :
    magneticFluxDensityInTeslas setup.magneticFluxDensity =
      setup.figure.displayedFieldMagnitudeTeslas
  greenVelocityArrowPointsRight :
    setup.figure.velocityArrowShown = true ∧
      setup.figure.velocityArrowColor = .green ∧
      setup.figure.velocityArrowDirection = .rightward
  printedSpeed : setup.figure.displayedSpeedMetersPerSecond = 10
  physicalSpeedMatchesLabel :
    speedInMetersPerSecond setup.translationSpeed =
      setup.figure.displayedSpeedMetersPerSecond

/-- Numerical data stated in the prose, including resistance and entry time. -/
structure MatchesProblemMeasurements
    (setup : MovingSquareLoopSetup) : Prop where
  sideLengthIsTenCentimeters :
    lengthInCentimeters setup.sideLength = 10
  fieldMagnitudeIsPointEightTesla :
    magneticFluxDensityInTeslas setup.magneticFluxDensity = 4 / 5
  speedIsTenMetersPerSecond :
    speedInMetersPerSecond setup.translationSpeed = 10
  resistanceIsPointOneOhm :
    resistanceInOhms setup.loopResistance = 1 / 10
  leadingVertexEntersAtZeroSeconds :
    timeInSeconds setup.entryTime = 0

/-- Positivity and nondegeneracy conditions for the physical branch. -/
structure HasPhysicalMovingLoopParameters
    (setup : MovingSquareLoopSetup) : Prop where
  sideLengthPositive : 0 < lengthInMeters setup.sideLength
  verticalDiagonalPositive :
    0 < lengthInMeters setup.verticalDiagonalLength
  speedPositive : 0 < speedInMetersPerSecond setup.translationSpeed
  resistancePositive : 0 < resistanceInOhms setup.loopResistance
  fieldMagnitudePositive :
    0 < magneticFluxDensityInTeslas setup.magneticFluxDensity

/-!
The supplied magnetic field occupies the half-plane to the right of the
dashed boundary, is uniform there, vanishes outside, and points into the page.
This uses Physlib's full space- and time-dependent magnetic-field object.
-/
structure ModelsUniformIntoPageHalfPlaneField
    (setup : MovingSquareLoopSetup) : Prop where
  regionIsRightHalfPlane : ∀ position,
    setup.fieldRegion position ↔
      setup.fieldBoundaryXCoordinate ≤ position.val horizontalAxis
  fieldDirectionIsIntoPage :
    setup.magneticFieldDirection = intoPageUnitVector
  uniformFieldInside : ∀ time position,
    setup.fieldRegion position →
      setup.magneticField time position =
        magneticFluxDensityInTeslas setup.magneticFluxDensity •
          intoPageUnitVector
  zeroFieldOutside : ∀ time position,
    ¬ setup.fieldRegion position → setup.magneticField time position = 0

/-- Constant-speed translation measured from the `t = 0` entry event. -/
structure SatisfiesConstantTranslationKinematics
    (setup : MovingSquareLoopSetup) : Prop where
  displacementAtEntryIsZero :
    lengthInMeters
      (setup.horizontalDisplacementSinceEntry setup.entryTime) = 0
  displacementLaw : ∀ time,
    timeInSeconds setup.entryTime ≤ timeInSeconds time →
      lengthInMeters (setup.horizontalDisplacementSinceEntry time) =
        speedInMetersPerSecond setup.translationSpeed *
          (timeInSeconds time - timeInSeconds setup.entryTime)

/-!
Geometry of a rigid square entering a vertical half-plane boundary.  The
vertical diagonal satisfies Pythagoras; every instantaneous swept width is at
most this diagonal, and the bound is attained when the boundary passes through
the top and bottom vertices.  This law mentions area rate but neither emf nor
current.
-/
structure SatisfiesDiamondBoundarySweepGeometry
    (setup : MovingSquareLoopSetup) : Prop where
  noOverlapAtEntry :
    areaInSquareMeters (setup.overlapAreaAt setup.entryTime) = 0
  verticalDiagonalPythagoreanLaw :
    lengthInMeters setup.verticalDiagonalLength ^ 2 =
      2 * lengthInMeters setup.sideLength ^ 2
  areaGrowthRateBound : ∀ time,
    areaRateInSquareMetersPerSecond
        (setup.overlapAreaGrowthRateMagnitudeAt time) ≤
      speedInMetersPerSecond setup.translationSpeed *
        lengthInMeters setup.verticalDiagonalLength
  areaGrowthRateBoundIsAttained : ∃ time,
    areaRateInSquareMetersPerSecond
        (setup.overlapAreaGrowthRateMagnitudeAt time) =
      speedInMetersPerSecond setup.translationSpeed *
        lengthInMeters setup.verticalDiagonalLength

/-!
For the uniform perpendicular field, flux magnitude is `B` times overlap area
and flux-rate magnitude is `B` times swept-area-rate magnitude.
-/
structure SatisfiesUniformOverlapFluxLaw
    (setup : MovingSquareLoopSetup) : Prop where
  fluxFromOverlapArea : ∀ time,
    magneticFluxInWebers (setup.magneticFluxMagnitudeAt time) =
      magneticFluxDensityInTeslas setup.magneticFluxDensity *
        areaInSquareMeters (setup.overlapAreaAt time)
  fluxRateFromAreaRate : ∀ time,
    magneticFluxRateInWebersPerSecond
        (setup.magneticFluxChangeRateMagnitudeAt time) =
      magneticFluxDensityInTeslas setup.magneticFluxDensity *
        areaRateInSquareMetersPerSecond
          (setup.overlapAreaGrowthRateMagnitudeAt time)

/-- Magnitude form of Faraday's induction law, `|ℰ| = |dΦ/dt|`. -/
structure SatisfiesFaradayInductionLaw
    (setup : MovingSquareLoopSetup) : Prop where
  inducedEmfMagnitude : ∀ time,
    emfMagnitudeInVolts (setup.inducedEmfMagnitudeAt time) =
      magneticFluxRateInWebersPerSecond
        (setup.magneticFluxChangeRateMagnitudeAt time)

/-!
Ohm's law for the passive resistive loop, written without division as
`I R = |ℰ|`.  It is a general circuit law and contains no maximum value.
-/
structure SatisfiesOhmsLaw
    (setup : MovingSquareLoopSetup) : Prop where
  currentResistanceProduct : ∀ time,
    currentMagnitudeInAmperes (setup.inducedCurrentMagnitudeAt time) *
        resistanceInOhms setup.loopResistance =
      emfMagnitudeInVolts (setup.inducedEmfMagnitudeAt time)

/-! ## Maximum relations and multiple-choice target -/

/-- A real readout is attained by, and bounds, a time-dependent observable. -/
def IsMaximumReadout
    (observable : TimeQuantity → ℝ) (candidate : ℝ) : Prop :=
  (∃ time, observable time = candidate) ∧
    ∀ time, observable time ≤ candidate

/-- A scalar ampere value is the maximum induced-current readout. -/
def IsMaximumCurrentInAmperes
    (setup : MovingSquareLoopSetup) (candidate : ℝ) : Prop :=
  IsMaximumReadout
    (fun time =>
      currentMagnitudeInAmperes (setup.inducedCurrentMagnitudeAt time))
    candidate

/-- Labels attached to the four displayed integer-current choices. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-!
Ampere value printed beside each answer label.  The source strings are
truncated after the numerals; amperes are inferred from the requested current.
-/
def AnswerChoice.displayedCurrentInAmperes : AnswerChoice → ℝ
  | .A => 13
  | .B => 11
  | .C => 10
  | .D => 9

/-- The answer label recorded by the supplied dataset metadata. -/
def recordedDatasetAnswer : AnswerChoice := .B

/-- A displayed current is at least as close as every other displayed choice. -/
def IsClosestDisplayedCurrent
    (physicalCurrent : ℝ) (choice : AnswerChoice) : Prop :=
  ∀ other : AnswerChoice,
    |physicalCurrent - choice.displayedCurrentInAmperes| ≤
      |physicalCurrent - other.displayedCurrentInAmperes|

/-!
The vertical diagonal of a positive square is its side length times `√2`.
This is a derived geometric result, not a field of the geometry premise.
-/
lemma vertical_diagonal_length_formula
    (setup : MovingSquareLoopSetup)
    (_physical : HasPhysicalMovingLoopParameters setup)
    (_geometry : SatisfiesDiamondBoundarySweepGeometry setup) :
    lengthInMeters setup.verticalDiagonalLength =
      lengthInMeters setup.sideLength * Real.sqrt 2 := by
  have hsqrt_nonnegative : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hsqrt_squared : (Real.sqrt 2) ^ 2 = (2 : ℝ) :=
    Real.sq_sqrt (by norm_num)
  have hsquares :
      lengthInMeters setup.verticalDiagonalLength ^ 2 =
        (lengthInMeters setup.sideLength * Real.sqrt 2) ^ 2 := by
    nlinarith [_geometry.verticalDiagonalPythagoreanLaw]
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsquares with hequal | hequal
  · exact hequal
  · nlinarith [_physical.sideLengthPositive,
      _physical.verticalDiagonalPositive]

/-! The boundary sweep reaches maximum area rate `v s √2`. -/
lemma maximum_overlap_area_growth_rate
    (setup : MovingSquareLoopSetup)
    (_physical : HasPhysicalMovingLoopParameters setup)
    (_geometry : SatisfiesDiamondBoundarySweepGeometry setup) :
    IsMaximumReadout
      (fun time => areaRateInSquareMetersPerSecond
        (setup.overlapAreaGrowthRateMagnitudeAt time))
      (speedInMetersPerSecond setup.translationSpeed *
        lengthInMeters setup.sideLength * Real.sqrt 2) := by
  rw [IsMaximumReadout]
  have hdiagonal :=
    vertical_diagonal_length_formula setup _physical _geometry
  constructor
  · obtain ⟨time, htime⟩ := _geometry.areaGrowthRateBoundIsAttained
    refine ⟨time, ?_⟩
    rw [htime, hdiagonal]
    ring
  · intro time
    calc
      areaRateInSquareMetersPerSecond
          (setup.overlapAreaGrowthRateMagnitudeAt time) ≤
          speedInMetersPerSecond setup.translationSpeed *
            lengthInMeters setup.verticalDiagonalLength :=
        _geometry.areaGrowthRateBound time
      _ = speedInMetersPerSecond setup.translationSpeed *
          lengthInMeters setup.sideLength * Real.sqrt 2 := by
        rw [hdiagonal]
        ring

/-! Faraday's law turns the maximal swept-area rate into maximal emf. -/
lemma maximum_induced_emf_formula
    (setup : MovingSquareLoopSetup)
    (_physical : HasPhysicalMovingLoopParameters setup)
    (_geometry : SatisfiesDiamondBoundarySweepGeometry setup)
    (_flux : SatisfiesUniformOverlapFluxLaw setup)
    (_faraday : SatisfiesFaradayInductionLaw setup) :
    IsMaximumReadout
      (fun time => emfMagnitudeInVolts (setup.inducedEmfMagnitudeAt time))
      (magneticFluxDensityInTeslas setup.magneticFluxDensity *
        speedInMetersPerSecond setup.translationSpeed *
        lengthInMeters setup.sideLength * Real.sqrt 2) := by
  rw [IsMaximumReadout]
  obtain ⟨⟨time, htime⟩, hbound⟩ :=
    maximum_overlap_area_growth_rate setup _physical _geometry
  constructor
  · refine ⟨time, ?_⟩
    change areaRateInSquareMetersPerSecond
        (setup.overlapAreaGrowthRateMagnitudeAt time) =
      speedInMetersPerSecond setup.translationSpeed *
        lengthInMeters setup.sideLength * Real.sqrt 2 at htime
    rw [_faraday.inducedEmfMagnitude time,
      _flux.fluxRateFromAreaRate time, htime]
    ring
  · intro time
    rw [_faraday.inducedEmfMagnitude time,
      _flux.fluxRateFromAreaRate time]
    calc
      magneticFluxDensityInTeslas setup.magneticFluxDensity *
          areaRateInSquareMetersPerSecond
            (setup.overlapAreaGrowthRateMagnitudeAt time) ≤
          magneticFluxDensityInTeslas setup.magneticFluxDensity *
            (speedInMetersPerSecond setup.translationSpeed *
              lengthInMeters setup.sideLength * Real.sqrt 2) :=
        mul_le_mul_of_nonneg_left (hbound time)
          (le_of_lt _physical.fieldMagnitudePositive)
      _ = magneticFluxDensityInTeslas setup.magneticFluxDensity *
          speedInMetersPerSecond setup.translationSpeed *
          lengthInMeters setup.sideLength * Real.sqrt 2 := by
        ring

/-! Ohm's law gives the symbolic maximum-current formula. -/
lemma maximum_induced_current_formula
    (setup : MovingSquareLoopSetup)
    (_physical : HasPhysicalMovingLoopParameters setup)
    (_geometry : SatisfiesDiamondBoundarySweepGeometry setup)
    (_flux : SatisfiesUniformOverlapFluxLaw setup)
    (_faraday : SatisfiesFaradayInductionLaw setup)
    (_ohm : SatisfiesOhmsLaw setup) :
    IsMaximumCurrentInAmperes setup
      (magneticFluxDensityInTeslas setup.magneticFluxDensity *
        speedInMetersPerSecond setup.translationSpeed *
        lengthInMeters setup.sideLength * Real.sqrt 2 /
          resistanceInOhms setup.loopResistance) := by
  rw [IsMaximumCurrentInAmperes, IsMaximumReadout]
  obtain ⟨⟨time, htime⟩, hbound⟩ :=
    maximum_induced_emf_formula setup _physical _geometry _flux _faraday
  have hresistance :
      0 < resistanceInOhms setup.loopResistance :=
    _physical.resistancePositive
  constructor
  · refine ⟨time, ?_⟩
    apply (eq_div_iff hresistance.ne').2
    calc
      currentMagnitudeInAmperes (setup.inducedCurrentMagnitudeAt time) *
          resistanceInOhms setup.loopResistance =
          emfMagnitudeInVolts (setup.inducedEmfMagnitudeAt time) :=
        _ohm.currentResistanceProduct time
      _ = magneticFluxDensityInTeslas setup.magneticFluxDensity *
          speedInMetersPerSecond setup.translationSpeed *
          lengthInMeters setup.sideLength * Real.sqrt 2 :=
        htime
  · intro time
    apply (le_div_iff₀ hresistance).2
    calc
      currentMagnitudeInAmperes (setup.inducedCurrentMagnitudeAt time) *
          resistanceInOhms setup.loopResistance =
          emfMagnitudeInVolts (setup.inducedEmfMagnitudeAt time) :=
        _ohm.currentResistanceProduct time
      _ ≤ magneticFluxDensityInTeslas setup.magneticFluxDensity *
          speedInMetersPerSecond setup.translationSpeed *
          lengthInMeters setup.sideLength * Real.sqrt 2 :=
        hbound time

/-!
For `B = 0.80 T`, `v = 10 m/s`, `s = 0.10 m`, and `R = 0.10 Ω`,
the maximum current is exactly `8 * √2 A`, approximately `11.31 A`.
Consequently the closest displayed integer current is `11 A`, answer B.

This declaration formalizes `thm:physics:phyx_mini_0931:target`.
-/
theorem problem_phyx_mini_0931
    (setup : MovingSquareLoopSetup)
    (_scenario : MatchesMovingSquareLoopScenario setup)
    (_figure : MatchesSuppliedMovingSquareLoopFigure setup)
    (_measurements : MatchesProblemMeasurements setup)
    (_physical : HasPhysicalMovingLoopParameters setup)
    (_field : ModelsUniformIntoPageHalfPlaneField setup)
    (_kinematics : SatisfiesConstantTranslationKinematics setup)
    (_geometry : SatisfiesDiamondBoundarySweepGeometry setup)
    (_flux : SatisfiesUniformOverlapFluxLaw setup)
    (_faraday : SatisfiesFaradayInductionLaw setup)
    (_ohm : SatisfiesOhmsLaw setup) :
    IsMaximumCurrentInAmperes setup (8 * Real.sqrt 2) ∧
      IsClosestDisplayedCurrent (8 * Real.sqrt 2) recordedDatasetAnswer := by
  have hside : lengthInMeters setup.sideLength = (1 / 10 : ℝ) := by
    have hcentimeters := _measurements.sideLengthIsTenCentimeters
    rw [lengthInCentimeters] at hcentimeters
    norm_num at hcentimeters ⊢
    linarith
  constructor
  · have hmaximum :=
      maximum_induced_current_formula setup _physical _geometry _flux
        _faraday _ohm
    rw [_measurements.fieldMagnitudeIsPointEightTesla,
      _measurements.speedIsTenMetersPerSecond, hside,
      _measurements.resistanceIsPointOneOhm] at hmaximum
    have hvalue :
        (4 / 5 : ℝ) * 10 * (1 / 10 : ℝ) * Real.sqrt 2 / (1 / 10 : ℝ) =
          8 * Real.sqrt 2 := by
      ring
    rw [hvalue] at hmaximum
    exact hmaximum
  · have hsqrt_nonnegative : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
    have hsqrt_squared : (Real.sqrt 2) ^ 2 = (2 : ℝ) :=
      Real.sq_sqrt (by norm_num)
    have hlower : (11 : ℝ) ≤ 8 * Real.sqrt 2 := by
      by_contra h
      have hleft : 0 < 11 - 8 * Real.sqrt 2 := by linarith
      have hright : 0 < 11 + 8 * Real.sqrt 2 := by positivity
      have hproduct :
          0 < (11 - 8 * Real.sqrt 2) * (11 + 8 * Real.sqrt 2) :=
        mul_pos hleft hright
      nlinarith
    have hupper : 8 * Real.sqrt 2 ≤ (12 : ℝ) := by
      by_contra h
      have hleft : 0 < 8 * Real.sqrt 2 - 12 := by linarith
      have hright : 0 < 8 * Real.sqrt 2 + 12 := by positivity
      have hproduct :
          0 < (8 * Real.sqrt 2 - 12) * (8 * Real.sqrt 2 + 12) :=
        mul_pos hleft hright
      nlinarith
    have hchoiceB :
        0 ≤ 8 * Real.sqrt 2 - (11 : ℝ) := sub_nonneg.mpr hlower
    have hchoiceA :
        8 * Real.sqrt 2 - (13 : ℝ) ≤ 0 := by linarith
    have hchoiceC :
        0 ≤ 8 * Real.sqrt 2 - (10 : ℝ) := by linarith
    have hchoiceD :
        0 ≤ 8 * Real.sqrt 2 - (9 : ℝ) := by linarith
    unfold IsClosestDisplayedCurrent recordedDatasetAnswer
    intro other
    cases other
    · simp only [AnswerChoice.displayedCurrentInAmperes]
      rw [abs_of_nonneg hchoiceB, abs_of_nonpos hchoiceA]
      linarith
    · exact le_rfl
    · simp only [AnswerChoice.displayedCurrentInAmperes]
      rw [abs_of_nonneg hchoiceB, abs_of_nonneg hchoiceC]
      linarith
    · simp only [AnswerChoice.displayedCurrentInAmperes]
      rw [abs_of_nonneg hchoiceB, abs_of_nonneg hchoiceD]
      linarith

end PhyXMiniProblems.ProblemPhyXMini0931
