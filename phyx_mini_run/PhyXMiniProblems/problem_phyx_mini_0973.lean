import Mathlib
import Physlib.Electromagnetism.Basic
import Physlib.SpaceAndTime.Space.LengthUnit
import Physlib.Units.WithDim.Speed

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0973

open Dimension

/-!
# Current induced while a rectangular loop enters a magnetic field

The primary image `973.png` shows a one-turn rectangular conducting loop moving
right into a wider region of uniform magnetic field.  The loop is `75.0 cm`
high and `50.0 cm` wide, its single resistor is labelled `12.5 Ω`, the speed is
`3.0 m/s`, and the field magnitude is `1.25 T`.

Physical magnitudes are represented by Physlib `Dimensionful` quantities.
Real numbers occur only at explicit unit readout boundaries and in literal
figure metadata.  The overlap-area rate, magnetic-flux rate, induced emf, and
induced current are independent observables constrained by governing laws; in
particular, the requested current is not defined from the recorded answer.
-/

/-! ## Physical dimensions, quantities, and readouts -/

/-- Area has dimension `L²`. -/
def areaDimension : Dimension := L𝓭 * L𝓭

/-- Electric current has dimension charge per time. -/
def electricCurrentDimension : Dimension := C𝓭 * T𝓭⁻¹

/-- Magnetic flux density, measured in teslas, has dimension `M T⁻¹ C⁻¹`. -/
def magneticFluxDensityDimension : Dimension :=
  M𝓭 * T𝓭⁻¹ * C𝓭⁻¹

/-- The rate at which loop area enters the field has dimension `L² T⁻¹`. -/
def areaRateDimension : Dimension := areaDimension * T𝓭⁻¹

/-- Magnetic flux has dimension magnetic flux density times area. -/
def magneticFluxDimension : Dimension :=
  magneticFluxDensityDimension * areaDimension

/-- A magnetic-flux rate has dimension magnetic flux per time. -/
def magneticFluxRateDimension : Dimension :=
  magneticFluxDimension * T𝓭⁻¹

/-- Electromotive force has dimension energy per charge. -/
def electromotiveForceDimension : Dimension :=
  M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹ * C𝓭⁻¹

/-- Electrical resistance has dimension emf divided by current. -/
def electricalResistanceDimension : Dimension :=
  electromotiveForceDimension * electricCurrentDimension⁻¹

/-- A nonnegative, unit-independent physical length. -/
abbrev LengthQuantity : Type :=
  Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative, unit-independent physical speed. -/
abbrev SpeedQuantity : Type := DimSpeed

/-- A nonnegative magnetic-flux-density magnitude. -/
abbrev MagneticFluxDensityMagnitudeQuantity : Type :=
  Dimensionful (WithDim magneticFluxDensityDimension NNReal)

/-- A nonnegative rate at which loop area overlaps the field region. -/
abbrev AreaRateMagnitudeQuantity : Type :=
  Dimensionful (WithDim areaRateDimension NNReal)

/-- A nonnegative magnetic-flux-rate magnitude. -/
abbrev MagneticFluxRateMagnitudeQuantity : Type :=
  Dimensionful (WithDim magneticFluxRateDimension NNReal)

/-- A nonnegative induced-emf magnitude. -/
abbrev EmfMagnitudeQuantity : Type :=
  Dimensionful (WithDim electromotiveForceDimension NNReal)

/-- A nonnegative electrical resistance. -/
abbrev ResistanceQuantity : Type :=
  Dimensionful (WithDim electricalResistanceDimension NNReal)

/-- A nonnegative induced-current magnitude. -/
abbrev ElectricCurrentMagnitudeQuantity : Type :=
  Dimensionful (WithDim electricCurrentDimension NNReal)

/-- Coherent-SI readout of a nonnegative dimensionful quantity. -/
def coherentSIReadout {d : Dimension}
    (quantity : Dimensionful (WithDim d NNReal)) : ℝ :=
  ((quantity UnitChoices.SI).val : ℝ)

/-- Read a length in the selected length unit. -/
def lengthReadout (unit : LengthUnit) (length : LengthQuantity) : ℝ :=
  ((length {UnitChoices.SI with length := unit}).val : ℝ)

/-- Read a length in metres. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  coherentSIReadout length

/-- Read a length in centimetres. -/
def lengthInCentimeters (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.centimeters length

/-- Read a speed in metres per second. -/
def speedInMetersPerSecond (speed : SpeedQuantity) : ℝ :=
  coherentSIReadout speed

/-- Read magnetic flux density in teslas. -/
def magneticFluxDensityInTeslas
    (density : MagneticFluxDensityMagnitudeQuantity) : ℝ :=
  coherentSIReadout density

/-- Read overlap-area rate in square metres per second. -/
def areaRateInSquareMetersPerSecond
    (rate : AreaRateMagnitudeQuantity) : ℝ :=
  coherentSIReadout rate

/-- Read magnetic-flux rate in webers per second. -/
def magneticFluxRateInWebersPerSecond
    (rate : MagneticFluxRateMagnitudeQuantity) : ℝ :=
  coherentSIReadout rate

/-- Read an emf magnitude in volts. -/
def emfInVolts (emf : EmfMagnitudeQuantity) : ℝ :=
  coherentSIReadout emf

/-- Read electrical resistance in ohms. -/
def resistanceInOhms (resistance : ResistanceQuantity) : ℝ :=
  coherentSIReadout resistance

/-- Read an electric-current magnitude in amperes. -/
def currentInAmperes (current : ElectricCurrentMagnitudeQuantity) : ℝ :=
  coherentSIReadout current

/-! ## Physical roles and primary-figure vocabulary -/

/-- The two geometrically distinct side lengths of the rectangular loop. -/
inductive LoopDimension where
  | verticalSide
  | horizontalSide
  deriving DecidableEq, Fintype, Repr

/-- The left and right vertical edges in the supplied image. -/
inductive VerticalEdge where
  | left
  | right
  deriving DecidableEq, Fintype, Repr

/-- Directions distinguished in the plane of the page. -/
inductive PlanarDirection where
  | left
  | right
  | up
  | down
  deriving DecidableEq, Fintype, Repr

/-- Direction normal to the page of the supplied image. -/
inductive PageNormalDirection where
  | intoPage
  | outOfPage
  deriving DecidableEq, Repr

/-- Glyph used in a diagram for a field normal to the page. -/
inductive MagneticFieldGlyph where
  | dots
  | crosses
  deriving DecidableEq, Repr

/-- Motion phase during the complete passage across the field region. -/
inductive TraversalPhase where
  | entering
  | fullyInside
  | exiting
  deriving DecidableEq, Fintype, Repr

/-- Kinematic idealization for the translating loop. -/
inductive MotionRegime where
  | constantVelocity
  | accelerating
  | stationary
  deriving DecidableEq, Repr

/-- Lumped circuit model represented by the loop and resistor symbol. -/
inductive CircuitModel where
  | idealWireWithSingleResistor
  | other
  deriving DecidableEq, Repr

/-- Orientation of the field relative to the plane of the rectangular loop. -/
inductive FieldLoopOrientation where
  | perpendicular
  | oblique
  deriving DecidableEq, Repr

/-- Qualitative comparison stated for the field-region and loop widths. -/
inductive RegionWidthRelation where
  | considerablyWiderThanLoop
  | comparableToLoop
  | narrowerThanLoop
  deriving DecidableEq, Repr

/-!
Literal presentation data transcribed from the primary raster.  Dots are
recorded as dots; their conventional physical interpretation is linked to the
field direction only in `MatchesSuppliedRectangularLoopFigure`.
-/
structure RectangularLoopFigure where
  rectangularLoopShown : Bool
  resistorZigzagShown : Bool
  magneticFieldVectorLabelShown : Bool
  velocityArrowShown : Bool
  fieldRegionShownToRightOfLoop : Bool
  fieldMarkersUniformlySpaced : Bool
  dimensionLabelInCentimeters : LoopDimension → ℝ
  printedResistanceInOhms : ℝ
  printedSpeedInMetersPerSecond : ℝ
  printedMagneticFluxDensityInTeslas : ℝ
  resistorEdge : VerticalEdge
  leadingEdge : VerticalEdge
  velocityArrowDirection : PlanarDirection
  fieldGlyph : MagneticFieldGlyph

/-!
The physical rectangular circuit.  Its emf and current are independent model
observables, not computed fields.
-/
structure RectangularCircuit where
  model : CircuitModel
  numberOfTurns : ℕ
  verticalSideLength : LengthQuantity
  horizontalSideLength : LengthQuantity
  totalResistance : ResistanceQuantity
  inducedEmfMagnitude : EmfMagnitudeQuantity
  inducedCurrentMagnitude : ElectricCurrentMagnitudeQuantity

/-!
A bounded magnetic-field region.  Physlib's `MagneticField` supplies the
spacetime-dependent vector field, while `fluxDensityMagnitude` carries its
physical tesla dimension.
-/
structure UniformMagneticFieldRegion where
  field : Electromagnetism.MagneticField 3
  contains : Space 3 → Prop
  referencePoint : Space 3
  width : LengthQuantity
  fluxDensityMagnitude : MagneticFluxDensityMagnitudeQuantity
  normalDirection : PageNormalDirection

/-!
Independent physical data at the instant when the loop is entering the field.
The entire entering/inside/exiting traversal is retained as part of the setup.
-/
structure EnteringRectangularLoopSetup where
  circuit : RectangularCircuit
  fieldRegion : UniformMagneticFieldRegion
  observationTime : Time
  loopCenterAt : Time → Space 3
  speed : SpeedQuantity
  velocityDirection : PlanarDirection
  motionRegime : MotionRegime
  phaseAtObservation : TraversalPhase
  traversalIncludes : TraversalPhase → Bool
  fieldLoopOrientation : FieldLoopOrientation
  widthRelation : RegionWidthRelation
  overlapAreaRateMagnitude : AreaRateMagnitudeQuantity
  magneticFluxRateMagnitude : MagneticFluxRateMagnitudeQuantity
  figure : RectangularLoopFigure

/-! ## Scenario, figure/data calibration, and physical nondegeneracy -/

/-!
Written scenario assumptions.  “Considerably wider” is preserved as a
qualitative relation and entails the conservative quantitative fact that the
field region is strictly wider than the loop's `50 cm` horizontal extent.
-/
structure MatchesWrittenEnteringScenario
    (setup : EnteringRectangularLoopSetup) : Prop where
  singleResistorCircuit :
    setup.circuit.model = .idealWireWithSingleResistor
  oneTurnLoop : setup.circuit.numberOfTurns = 1
  constantVelocity : setup.motionRegime = .constantVelocity
  movesRight : setup.velocityDirection = .right
  observedWhileEntering : setup.phaseAtObservation = .entering
  completeTraversal : ∀ phase, setup.traversalIncludes phase = true
  fieldPerpendicularToLoop :
    setup.fieldLoopOrientation = .perpendicular
  fieldRegionConsiderablyWider :
    setup.widthRelation = .considerablyWiderThanLoop
  fieldRegionStrictlyWider :
    lengthInMeters setup.circuit.horizontalSideLength <
      lengthInMeters setup.fieldRegion.width

/-!
Literal figure evidence and calibration of every printed number to the
independent dimensionful setup.  The dot glyph is interpreted by the standard
diagram convention as a field directed out of the page.  This follows the
primary image even though its auxiliary generated caption says “into”.
-/
structure MatchesSuppliedRectangularLoopFigure
    (setup : EnteringRectangularLoopSetup) : Prop where
  loopShown : setup.figure.rectangularLoopShown = true
  resistorShown : setup.figure.resistorZigzagShown = true
  magneticFieldLabelShown :
    setup.figure.magneticFieldVectorLabelShown = true
  velocityArrowShown : setup.figure.velocityArrowShown = true
  fieldRegionOnRight :
    setup.figure.fieldRegionShownToRightOfLoop = true
  fieldMarkersUniform : setup.figure.fieldMarkersUniformlySpaced = true
  verticalSideLabel :
    setup.figure.dimensionLabelInCentimeters .verticalSide = 75
  horizontalSideLabel :
    setup.figure.dimensionLabelInCentimeters .horizontalSide = 50
  resistorLabel : setup.figure.printedResistanceInOhms = 25 / 2
  speedLabel : setup.figure.printedSpeedInMetersPerSecond = 3
  magneticFieldLabel :
    setup.figure.printedMagneticFluxDensityInTeslas = 5 / 4
  resistorOnLeftEdge : setup.figure.resistorEdge = .left
  rightEdgeEntersFirst : setup.figure.leadingEdge = .right
  arrowPointsRight : setup.figure.velocityArrowDirection = .right
  fieldDrawnWithDots : setup.figure.fieldGlyph = .dots
  dotsMeanOutOfPage :
    setup.fieldRegion.normalDirection = .outOfPage
  verticalLengthCalibrated :
    lengthInCentimeters setup.circuit.verticalSideLength =
      setup.figure.dimensionLabelInCentimeters .verticalSide
  horizontalLengthCalibrated :
    lengthInCentimeters setup.circuit.horizontalSideLength =
      setup.figure.dimensionLabelInCentimeters .horizontalSide
  resistanceCalibrated :
    resistanceInOhms setup.circuit.totalResistance =
      setup.figure.printedResistanceInOhms
  speedCalibrated :
    speedInMetersPerSecond setup.speed =
      setup.figure.printedSpeedInMetersPerSecond
  fieldMagnitudeCalibrated :
    magneticFluxDensityInTeslas
        setup.fieldRegion.fluxDensityMagnitude =
      setup.figure.printedMagneticFluxDensityInTeslas
  physicalMotionMatchesArrow :
    setup.velocityDirection = setup.figure.velocityArrowDirection

/-!
The Physlib vector field is uniform inside the represented field region at the
observation time, vanishes in the idealized exterior, and has the calibrated
dimensionful magnitude at an interior reference point.
-/
structure DescribesUniformMagneticFieldRegion
    (setup : EnteringRectangularLoopSetup) : Prop where
  referencePointInside :
    setup.fieldRegion.contains setup.fieldRegion.referencePoint
  uniformInsideAtObservation :
    ∀ p q : Space 3,
      setup.fieldRegion.contains p →
      setup.fieldRegion.contains q →
      setup.fieldRegion.field setup.observationTime p =
        setup.fieldRegion.field setup.observationTime q
  vanishesOutsideAtObservation :
    ∀ p : Space 3,
      ¬ setup.fieldRegion.contains p →
      setup.fieldRegion.field setup.observationTime p = 0
  vectorMagnitudeMatchesTeslaReadout :
    ‖setup.fieldRegion.field setup.observationTime
        setup.fieldRegion.referencePoint‖ =
      magneticFluxDensityInTeslas
        setup.fieldRegion.fluxDensityMagnitude

/-- Positivity and nondegeneracy of the independent input parameters. -/
structure HasPhysicalEnteringLoopParameters
    (setup : EnteringRectangularLoopSetup) : Prop where
  verticalLengthPositive :
    0 < lengthInMeters setup.circuit.verticalSideLength
  horizontalLengthPositive :
    0 < lengthInMeters setup.circuit.horizontalSideLength
  speedPositive : 0 < speedInMetersPerSecond setup.speed
  resistancePositive :
    0 < resistanceInOhms setup.circuit.totalResistance
  fieldMagnitudePositive :
    0 < magneticFluxDensityInTeslas
      setup.fieldRegion.fluxDensityMagnitude
  fieldRegionWidthPositive :
    0 < lengthInMeters setup.fieldRegion.width

/-! ## Governing induction and circuit laws -/

/-!
For perpendicular entry, the overlap area grows at `height × speed`.  A
uniform perpendicular field gives flux-rate magnitude `B × area-rate`;
Faraday's law equates emf magnitude with the turn count times that rate; and
Ohm's law relates emf to current and total resistance.  None of these premise
fields states the requested numerical current.
-/
structure SatisfiesEnteringFaradayAndOhmLaws
    (setup : EnteringRectangularLoopSetup) : Prop where
  sweptAreaRateForRectangularEntry :
    areaRateInSquareMetersPerSecond setup.overlapAreaRateMagnitude =
      lengthInMeters setup.circuit.verticalSideLength *
        speedInMetersPerSecond setup.speed
  uniformPerpendicularFluxRate :
    magneticFluxRateInWebersPerSecond
        setup.magneticFluxRateMagnitude =
      magneticFluxDensityInTeslas
          setup.fieldRegion.fluxDensityMagnitude *
        areaRateInSquareMetersPerSecond
          setup.overlapAreaRateMagnitude
  faradayLawForEmfMagnitude :
    emfInVolts setup.circuit.inducedEmfMagnitude =
      (setup.circuit.numberOfTurns : ℝ) *
        magneticFluxRateInWebersPerSecond
          setup.magneticFluxRateMagnitude
  ohmsLawForInducedCurrent :
    emfInVolts setup.circuit.inducedEmfMagnitude =
      currentInAmperes setup.circuit.inducedCurrentMagnitude *
        resistanceInOhms setup.circuit.totalResistance

/-! ## General consequence, answer metadata, and requested result -/

/-!
Combining rectangular swept area, uniform-field flux, Faraday's law, and
Ohm's law gives the usual entering-loop current formula.  This is a derived
relation rather than a law field.
-/
lemma inducedCurrent_eq_field_mul_height_mul_speed_div_resistance
    (setup : EnteringRectangularLoopSetup)
    (hScenario : MatchesWrittenEnteringScenario setup)
    (hPhysical : HasPhysicalEnteringLoopParameters setup)
    (hLaws : SatisfiesEnteringFaradayAndOhmLaws setup) :
    currentInAmperes setup.circuit.inducedCurrentMagnitude =
      magneticFluxDensityInTeslas
          setup.fieldRegion.fluxDensityMagnitude *
        lengthInMeters setup.circuit.verticalSideLength *
        speedInMetersPerSecond setup.speed /
        resistanceInOhms setup.circuit.totalResistance := by
  have hResistanceNe :
      resistanceInOhms setup.circuit.totalResistance ≠ 0 :=
    ne_of_gt hPhysical.resistancePositive
  apply (eq_div_iff hResistanceNe).2
  calc
    currentInAmperes setup.circuit.inducedCurrentMagnitude *
          resistanceInOhms setup.circuit.totalResistance =
        emfInVolts setup.circuit.inducedEmfMagnitude :=
      hLaws.ohmsLawForInducedCurrent.symm
    _ = (setup.circuit.numberOfTurns : ℝ) *
          magneticFluxRateInWebersPerSecond
            setup.magneticFluxRateMagnitude :=
      hLaws.faradayLawForEmfMagnitude
    _ = magneticFluxRateInWebersPerSecond
          setup.magneticFluxRateMagnitude := by
      rw [hScenario.oneTurnLoop]
      norm_num
    _ = magneticFluxDensityInTeslas
            setup.fieldRegion.fluxDensityMagnitude *
          areaRateInSquareMetersPerSecond
            setup.overlapAreaRateMagnitude :=
      hLaws.uniformPerpendicularFluxRate
    _ = magneticFluxDensityInTeslas
            setup.fieldRegion.fluxDensityMagnitude *
          (lengthInMeters setup.circuit.verticalSideLength *
            speedInMetersPerSecond setup.speed) := by
      rw [hLaws.sweptAreaRateForRectangularEntry]
    _ = magneticFluxDensityInTeslas
            setup.fieldRegion.fluxDensityMagnitude *
          lengthInMeters setup.circuit.verticalSideLength *
          speedInMetersPerSecond setup.speed := by
      ring

/-- Labels of the four current magnitudes printed in the source. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Current magnitude in amperes displayed beside an answer label. -/
def AnswerChoice.displayedCurrentInAmperes : AnswerChoice → ℝ
  | .A => 9 / 400
  | .B => 9 / 40
  | .C => 0
  | .D => 47 / 500

/-- The dataset records answer label B. -/
def recordedDatasetAnswer : AnswerChoice := .B

/-- A displayed answer agrees with the independent induced-current observable. -/
def AnswerMatchesInducedCurrent
    (setup : EnteringRectangularLoopSetup)
    (choice : AnswerChoice) : Prop :=
  currentInAmperes setup.circuit.inducedCurrentMagnitude =
    choice.displayedCurrentInAmperes

/-!
At entry the changing area is determined by the `75.0 cm` vertical side, not
the `50.0 cm` direction-of-motion width.  Hence
`I = B h v / R = 1.25 × 0.75 × 3.0 / 12.5 = 0.225 A`, answer B.

This declaration formalizes `thm:physics:phyx_mini_0973:target`.
-/
theorem problem_phyx_mini_0973
    (setup : EnteringRectangularLoopSetup)
    (hScenario : MatchesWrittenEnteringScenario setup)
    (hFigure : MatchesSuppliedRectangularLoopFigure setup)
    (hFieldRegion : DescribesUniformMagneticFieldRegion setup)
    (hPhysical : HasPhysicalEnteringLoopParameters setup)
    (hLaws : SatisfiesEnteringFaradayAndOhmLaws setup) :
    currentInAmperes setup.circuit.inducedCurrentMagnitude = 9 / 40 ∧
      AnswerMatchesInducedCurrent setup recordedDatasetAnswer := by
  have centimeters_eq_meters (length : LengthQuantity) :
      lengthInCentimeters length = 100 * lengthInMeters length := by
    have h := congrArg (fun value ↦ ((value.val : NNReal) : ℝ))
      (length.2 UnitChoices.SI
        {UnitChoices.SI with length := LengthUnit.centimeters})
    norm_num [lengthInCentimeters, lengthInMeters, lengthReadout,
      coherentSIReadout, UnitChoices.dimScale, LengthUnit.centimeters,
      LengthUnit.meters, LengthUnit.scale, LengthUnit.div_eq_val,
      NNReal.smul_def, smul_eq_mul] at h ⊢
    exact h
  have hVerticalCentimeters :
      lengthInCentimeters setup.circuit.verticalSideLength = 75 := by
    calc
      lengthInCentimeters setup.circuit.verticalSideLength =
          setup.figure.dimensionLabelInCentimeters .verticalSide :=
        hFigure.verticalLengthCalibrated
      _ = 75 := hFigure.verticalSideLabel
  have hVerticalMeters :
      lengthInMeters setup.circuit.verticalSideLength = 3 / 4 := by
    rw [centimeters_eq_meters] at hVerticalCentimeters
    linarith
  have hResistance :
      resistanceInOhms setup.circuit.totalResistance = 25 / 2 := by
    calc
      resistanceInOhms setup.circuit.totalResistance =
          setup.figure.printedResistanceInOhms :=
        hFigure.resistanceCalibrated
      _ = 25 / 2 := hFigure.resistorLabel
  have hSpeed : speedInMetersPerSecond setup.speed = 3 := by
    calc
      speedInMetersPerSecond setup.speed =
          setup.figure.printedSpeedInMetersPerSecond :=
        hFigure.speedCalibrated
      _ = 3 := hFigure.speedLabel
  have hField :
      magneticFluxDensityInTeslas
          setup.fieldRegion.fluxDensityMagnitude = 5 / 4 := by
    calc
      magneticFluxDensityInTeslas
          setup.fieldRegion.fluxDensityMagnitude =
          setup.figure.printedMagneticFluxDensityInTeslas :=
        hFigure.fieldMagnitudeCalibrated
      _ = 5 / 4 := hFigure.magneticFieldLabel
  have hCurrent :=
    inducedCurrent_eq_field_mul_height_mul_speed_div_resistance
      setup hScenario hPhysical hLaws
  rw [hField, hVerticalMeters, hSpeed, hResistance] at hCurrent
  norm_num at hCurrent
  refine ⟨hCurrent, ?_⟩
  simpa [AnswerMatchesInducedCurrent, recordedDatasetAnswer,
    AnswerChoice.displayedCurrentInAmperes] using hCurrent

end PhyXMiniProblems.ProblemPhyXMini0973
