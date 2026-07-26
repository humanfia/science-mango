import Mathlib
import Physlib.Electromagnetism.Basic
import Physlib.Units.WithDim.Speed

/- USER: The assigned Lean file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0976

open Dimension

/-!
# Terminal speed of a battery-driven sliding bar

The raster `976.png` shows a vertical conducting bar bridging two horizontal
rails.  A battery and switch join the rails on the left, while crosses denote
a uniform magnetic field into the page.  Closing the switch drives current
downward through the bar and hence a magnetic force to the right.  Rightward
motion produces an opposing motional emf.

Assumption/target split:

* governing laws: perpendicular motional emf, the Kirchhoff--Ohm loop law,
  magnetic force on a straight current-carrying bar, frictionless horizontal
  force balance, Newton's second law, and the zero-acceleration definition of
  terminal motion;
* previous-part results: none;
* figure/data readouts: bar length `0.36 m`, field magnitude `2.4 T`, battery
  emf `12 V`, bar mass `0.90 kg`, bar resistance `5.0 Ω`, zero other
  resistance, switch closure at `t = 0`, and the literal geometry/polarity of
  the supplied figure;
* current target: the exact speed `125/9 m/s`, whose nearest displayed choice
  is B (`14 m/s`).

The terminal speed and all speed-dependent observables below are independent
fields.  No premise assigns the requested speed or selects answer B.
-/

/-! ## Physical dimensions and unit-independent quantities -/

/-- Linear acceleration has physical dimension `L T⁻²`. -/
def accelerationDimension : Dimension :=
  L𝓭 * T𝓭⁻¹ * T𝓭⁻¹

/-- Electric current has physical dimension charge per time. -/
def electricCurrentDimension : Dimension :=
  C𝓭 * T𝓭⁻¹

/-- Electromotive force has physical dimension `M L² T⁻² C⁻¹`. -/
def electromotiveForceDimension : Dimension :=
  M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹ * C𝓭⁻¹

/-- Electrical resistance has dimension emf divided by current. -/
def electricalResistanceDimension : Dimension :=
  electromotiveForceDimension * electricCurrentDimension⁻¹

/-- Magnetic flux density has the tesla dimension `M T⁻¹ C⁻¹`. -/
def magneticFluxDensityDimension : Dimension :=
  M𝓭 * T𝓭⁻¹ * C𝓭⁻¹

/-- Force has the newton dimension `M L T⁻²`. -/
def forceDimension : Dimension :=
  M𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹

/-- A nonnegative, unit-independent physical length. -/
abbrev LengthQuantity : Type :=
  Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative, unit-independent duration. -/
abbrev DurationQuantity : Type :=
  Dimensionful (WithDim T𝓭 NNReal)

/-- A nonnegative, unit-independent physical mass. -/
abbrev MassQuantity : Type :=
  Dimensionful (WithDim M𝓭 NNReal)

/-- A nonnegative, unit-independent speed. -/
abbrev SpeedQuantity : Type := DimSpeed

/-- A nonnegative, unit-independent magnetic-flux-density magnitude. -/
abbrev MagneticFluxDensityQuantity : Type :=
  Dimensionful (WithDim magneticFluxDensityDimension NNReal)

/-- A nonnegative, unit-independent emf magnitude. -/
abbrev EmfMagnitudeQuantity : Type :=
  Dimensionful (WithDim electromotiveForceDimension NNReal)

/-- A nonnegative, unit-independent electrical resistance. -/
abbrev ResistanceQuantity : Type :=
  Dimensionful (WithDim electricalResistanceDimension NNReal)

/-- Signed current, positive in the battery-driven direction through the bar. -/
abbrev SignedCurrentQuantity : Type :=
  Dimensionful (WithDim electricCurrentDimension ℝ)

/-- Signed horizontal force, positive in the chosen sliding direction. -/
abbrev SignedForceQuantity : Type :=
  Dimensionful (WithDim forceDimension ℝ)

/-- Signed horizontal acceleration, positive in the chosen sliding direction. -/
abbrev SignedAccelerationQuantity : Type :=
  Dimensionful (WithDim accelerationDimension ℝ)

/-! ## Coherent-unit readouts -/

/-- Read a nonnegative physical quantity in a coherent unit system. -/
def nonnegativeReadout {d : Dimension}
    (units : UnitChoices) (quantity : Dimensionful (WithDim d NNReal)) : ℝ :=
  ((quantity units).val : ℝ)

/-- Read a signed physical quantity in a coherent unit system. -/
def signedReadout {d : Dimension}
    (units : UnitChoices) (quantity : Dimensionful (WithDim d ℝ)) : ℝ :=
  (quantity units).val

def lengthReadout (units : UnitChoices) (length : LengthQuantity) : ℝ :=
  nonnegativeReadout units length

def durationReadout (units : UnitChoices) (duration : DurationQuantity) : ℝ :=
  nonnegativeReadout units duration

def massReadout (units : UnitChoices) (mass : MassQuantity) : ℝ :=
  nonnegativeReadout units mass

def speedReadout (units : UnitChoices) (speed : SpeedQuantity) : ℝ :=
  nonnegativeReadout units speed

def magneticFluxDensityReadout
    (units : UnitChoices) (density : MagneticFluxDensityQuantity) : ℝ :=
  nonnegativeReadout units density

def emfReadout (units : UnitChoices) (emf : EmfMagnitudeQuantity) : ℝ :=
  nonnegativeReadout units emf

def resistanceReadout
    (units : UnitChoices) (resistance : ResistanceQuantity) : ℝ :=
  nonnegativeReadout units resistance

def currentReadout
    (units : UnitChoices) (current : SignedCurrentQuantity) : ℝ :=
  signedReadout units current

def forceReadout (units : UnitChoices) (force : SignedForceQuantity) : ℝ :=
  signedReadout units force

def accelerationReadout
    (units : UnitChoices) (acceleration : SignedAccelerationQuantity) : ℝ :=
  signedReadout units acceleration

/-- SI readout of length, in metres. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  lengthReadout UnitChoices.SI length

/-- SI readout of duration, in seconds. -/
def durationInSeconds (duration : DurationQuantity) : ℝ :=
  durationReadout UnitChoices.SI duration

/-- SI readout of mass, in kilograms. -/
def massInKilograms (mass : MassQuantity) : ℝ :=
  massReadout UnitChoices.SI mass

/-- SI readout of speed, in metres per second. -/
def speedInMetersPerSecond (speed : SpeedQuantity) : ℝ :=
  speedReadout UnitChoices.SI speed

/-- SI readout of magnetic flux density, in teslas. -/
def magneticFluxDensityInTeslas
    (density : MagneticFluxDensityQuantity) : ℝ :=
  magneticFluxDensityReadout UnitChoices.SI density

/-- SI readout of emf, in volts. -/
def emfInVolts (emf : EmfMagnitudeQuantity) : ℝ :=
  emfReadout UnitChoices.SI emf

/-- SI readout of resistance, in ohms. -/
def resistanceInOhms (resistance : ResistanceQuantity) : ℝ :=
  resistanceReadout UnitChoices.SI resistance

/-- SI readout of signed current, in amperes. -/
def currentInAmperes (current : SignedCurrentQuantity) : ℝ :=
  currentReadout UnitChoices.SI current

/-- SI readout of signed force, in newtons. -/
def forceInNewtons (force : SignedForceQuantity) : ℝ :=
  forceReadout UnitChoices.SI force

/-- SI readout of signed acceleration, in metres per second squared. -/
def accelerationInMetersPerSecondSquared
    (acceleration : SignedAccelerationQuantity) : ℝ :=
  accelerationReadout UnitChoices.SI acceleration

/-! ## Physical roles and primary-figure vocabulary -/

/-- Components visibly present in the supplied apparatus figure. -/
inductive ApparatusComponent where
  | upperRail
  | lowerRail
  | slidingBar
  | battery
  | switch
  deriving DecidableEq, Fintype, Repr

/-- Symbolic labels printed in the supplied figure. -/
inductive FigureLabel where
  | magneticFieldB
  | batteryEmfEpsilon
  | switchS
  | railSeparationL
  deriving DecidableEq, Fintype, Repr

/-- Directions distinguished by the drawing and its page normal. -/
inductive FigureDirection where
  | left
  | right
  | up
  | down
  | intoPage
  | outOfPage
  deriving DecidableEq, Fintype, Repr

inductive FigureAxis where
  | horizontal
  | vertical
  deriving DecidableEq, Repr

/-- Crosses in the raster encode a field directed into the page. -/
inductive MagneticFieldGlyph where
  | crossesIntoPage
  | dotsOutOfPage
  | none
  deriving DecidableEq, Repr

inductive SwitchState where
  | open
  | closed
  deriving DecidableEq, Repr

inductive RailContactModel where
  | frictionlessSlidingContact
  | resistiveSlidingContact
  deriving DecidableEq, Repr

inductive SlidingBarGeometry where
  | straightBarOnParallelRails
  | other
  deriving DecidableEq, Repr

inductive CircuitResistanceModel where
  | barResistanceOnly
  | distributedResistance
  deriving DecidableEq, Repr

inductive MagneticFieldUniformity where
  | uniform
  | nonuniform
  deriving DecidableEq, Repr

/-!
Literal presentation data in `976.png`.  The switch is drawn open, matching
the instant just before its stated closure at `t = 0`.  The raster contains no
motion arrow and no terminal-speed readout.
-/
structure SlidingBarRailFigure where
  componentShown : ApparatusComponent → Bool
  labelShown : FigureLabel → Bool
  railAxis : ApparatusComponent → FigureAxis
  railsParallel : Bool
  barBridgesRails : Bool
  barAxis : FigureAxis
  magneticFieldGlyph : MagneticFieldGlyph
  magneticFieldGlyphsFillRailRegion : Bool
  switchDepictedState : SwitchState
  batteryPositiveTerminalToward : FigureDirection
  batteryNegativeTerminalToward : FigureDirection
  lengthMarkerAxis : FigureAxis
  lengthMarkerSpansRailSeparation : Bool
  motionArrowShown : Bool

/-- A dimensionless direction vector in physical three-space. -/
abbrev DirectionVector : Type := EuclideanSpace ℝ (Fin 3)

/-- Unit vector pointing into the page. -/
def intoPageUnitVector : DirectionVector :=
  -EuclideanSpace.single (2 : Fin 3) 1

/-!
Independent apparatus data and speed-dependent observables.  In particular,
`terminalSpeed` is a physical speed rather than a scalar answer value, and the
functions for emf, current, force, and acceleration are not defined from the
requested conclusion.
-/
structure SlidingBarRailSetup where
  geometry : SlidingBarGeometry
  railContact : RailContactModel
  resistanceModel : CircuitResistanceModel
  fieldUniformity : MagneticFieldUniformity
  magneticField : Electromagnetism.MagneticField 3
  magneticFluxDensity : MagneticFluxDensityQuantity
  magneticFieldDirection : FigureDirection
  barLength : LengthQuantity
  barMass : MassQuantity
  barResistance : ResistanceQuantity
  otherCircuitResistance : ResistanceQuantity
  batteryEmf : EmfMagnitudeQuantity
  switchClosingTime : DurationQuantity
  switchStateBeforeClosing : SwitchState
  switchStateAtAndAfterClosing : SwitchState
  positiveSlidingDirection : FigureDirection
  batteryDrivenCurrentDirectionThroughBar : FigureDirection
  magneticDriveForceDirection : FigureDirection
  terminalSpeed : SpeedQuantity
  motionalEmfAt : SpeedQuantity → EmfMagnitudeQuantity
  circuitCurrentAt : SpeedQuantity → SignedCurrentQuantity
  magneticForceAt : SpeedQuantity → SignedForceQuantity
  netSlidingForceAt : SpeedQuantity → SignedForceQuantity
  accelerationAt : SpeedQuantity → SignedAccelerationQuantity
  figure : SlidingBarRailFigure

/-! ## Scenario, figure evidence, measurements, and governing laws -/

/-- Qualitative apparatus facts stated in the problem prose. -/
structure MatchesWrittenSlidingBarScenario
    (setup : SlidingBarRailSetup) : Prop where
  straightBarOnParallelRails :
    setup.geometry = .straightBarOnParallelRails
  barSlidesWithoutFriction :
    setup.railContact = .frictionlessSlidingContact
  onlyBarResistanceIsRetained :
    setup.resistanceModel = .barResistanceOnly
  appliedFieldIsUniform : setup.fieldUniformity = .uniform
  appliedFieldPointsIntoPage :
    setup.magneticFieldDirection = .intoPage
  switchInitiallyOpen : setup.switchStateBeforeClosing = .open
  switchClosedFromClosingTimeOnward :
    setup.switchStateAtAndAfterClosing = .closed

/-- Literal geometry, labels, polarity, field glyphs, and switch state in the image. -/
structure MatchesSuppliedSlidingBarFigure
    (setup : SlidingBarRailSetup) : Prop where
  everyComponentShown : ∀ component,
    setup.figure.componentShown component = true
  everyLabelShown : ∀ label,
    setup.figure.labelShown label = true
  upperRailIsHorizontal :
    setup.figure.railAxis .upperRail = .horizontal
  lowerRailIsHorizontal :
    setup.figure.railAxis .lowerRail = .horizontal
  railsAreParallel : setup.figure.railsParallel = true
  barIsVertical : setup.figure.barAxis = .vertical
  barConnectsRails : setup.figure.barBridgesRails = true
  fieldUsesIntoPageCrosses :
    setup.figure.magneticFieldGlyph = .crossesIntoPage
  fieldCrossesFillRailRegion :
    setup.figure.magneticFieldGlyphsFillRailRegion = true
  fieldDirectionMatchesGlyph :
    setup.magneticFieldDirection = .intoPage
  switchIsDrawnOpen :
    setup.figure.switchDepictedState = .open
  drawingRepresentsPreclosureState :
    setup.figure.switchDepictedState = setup.switchStateBeforeClosing
  positiveBatteryTerminalConnectsUpperRail :
    setup.figure.batteryPositiveTerminalToward = .up
  negativeBatteryTerminalConnectsLowerRail :
    setup.figure.batteryNegativeTerminalToward = .down
  lengthMarkerIsVertical :
    setup.figure.lengthMarkerAxis = .vertical
  lengthMarkerSpansRails :
    setup.figure.lengthMarkerSpansRailSeparation = true
  noMotionArrowInRaster : setup.figure.motionArrowShown = false

/-!
The Physlib spacetime-dependent field is constant, points into the page, and
has norm calibrated by the independent dimensionful tesla magnitude.
-/
structure ModelsUniformIntoPageMagneticField
    (setup : SlidingBarRailSetup) : Prop where
  uniformIntoPageField : ∀ time position,
    setup.magneticField time position =
      magneticFluxDensityInTeslas setup.magneticFluxDensity •
        intoPageUnitVector

/-!
Numerical readouts stated by the problem.  Resistance outside the bar is zero
because it is explicitly ignored.  No speed, current, force, or acceleration
readout occurs here.
-/
structure HasSlidingBarProblemMeasurements
    (setup : SlidingBarRailSetup) : Prop where
  barLengthIsPointThirtySixMeters :
    lengthInMeters setup.barLength = (9 / 25 : ℝ)
  magneticFieldIsTwoPointFourTeslas :
    magneticFluxDensityInTeslas setup.magneticFluxDensity = (12 / 5 : ℝ)
  batteryEmfIsTwelveVolts :
    emfInVolts setup.batteryEmf = 12
  barMassIsPointNinetyKilograms :
    massInKilograms setup.barMass = (9 / 10 : ℝ)
  barResistanceIsFiveOhms :
    resistanceInOhms setup.barResistance = 5
  allOtherResistanceIsIgnored :
    resistanceInOhms setup.otherCircuitResistance = 0
  switchClosingTimeIsZeroSeconds :
    durationInSeconds setup.switchClosingTime = 0

/-- Positivity and nondegeneracy conditions needed by the physical laws. -/
structure HasPhysicalSlidingBarParameters
    (setup : SlidingBarRailSetup) : Prop where
  barLengthPositive : 0 < lengthInMeters setup.barLength
  magneticFluxDensityPositive :
    0 < magneticFluxDensityInTeslas setup.magneticFluxDensity
  batteryEmfPositive : 0 < emfInVolts setup.batteryEmf
  barMassPositive : 0 < massInKilograms setup.barMass
  barResistancePositive : 0 < resistanceInOhms setup.barResistance
  totalCircuitResistancePositive :
    0 < resistanceInOhms setup.barResistance +
      resistanceInOhms setup.otherCircuitResistance

/-!
Governing relations for every candidate speed.  They do not assign the
terminal speed or assert the terminal emf balance as a premise.
-/
structure SatisfiesBatteryDrivenSlidingBarLaws
    (setup : SlidingBarRailSetup) : Prop where
  motionalEmfForPerpendicularMotion :
    ∀ (speed : SpeedQuantity) (units : UnitChoices),
      emfReadout units (setup.motionalEmfAt speed) =
        magneticFluxDensityReadout units setup.magneticFluxDensity *
          lengthReadout units setup.barLength * speedReadout units speed
  kirchhoffOhmLoopLaw :
    ∀ (speed : SpeedQuantity) (units : UnitChoices),
      emfReadout units setup.batteryEmf -
          emfReadout units (setup.motionalEmfAt speed) =
        currentReadout units (setup.circuitCurrentAt speed) *
          (resistanceReadout units setup.barResistance +
            resistanceReadout units setup.otherCircuitResistance)
  straightWireMagneticForceLaw :
    ∀ (speed : SpeedQuantity) (units : UnitChoices),
      forceReadout units (setup.magneticForceAt speed) =
        currentReadout units (setup.circuitCurrentAt speed) *
          lengthReadout units setup.barLength *
            magneticFluxDensityReadout units setup.magneticFluxDensity
  frictionlessHorizontalForceBalance :
    ∀ (speed : SpeedQuantity) (units : UnitChoices),
      forceReadout units (setup.netSlidingForceAt speed) =
        forceReadout units (setup.magneticForceAt speed)
  newtonsSecondLawAlongRails :
    ∀ (speed : SpeedQuantity) (units : UnitChoices),
      massReadout units setup.barMass *
          accelerationReadout units (setup.accelerationAt speed) =
        forceReadout units (setup.netSlidingForceAt speed)
  positiveSlidingDirectionIsRight :
    setup.positiveSlidingDirection = .right
  batteryDrivesCurrentDownTheBar :
    setup.batteryDrivenCurrentDirectionThroughBar = .down
  positiveCurrentProducesRightwardForce :
    setup.magneticDriveForceDirection = .right

/-!
A terminal speed is characterized dynamically by zero acceleration.  This
definition contains no numerical speed and does not unfold to the answer.
-/
def IsTerminalSpeed
    (setup : SlidingBarRailSetup) (speed : SpeedQuantity) : Prop :=
  accelerationInMetersPerSecondSquared (setup.accelerationAt speed) = 0

/-! ## Derived relation and answer selection -/

/--
At zero acceleration, force and current vanish.  The loop law then balances
the battery and motional emfs, yielding the general terminal-speed formula.
-/
lemma terminalSpeed_eq_batteryEmf_div_field_length
    (setup : SlidingBarRailSetup)
    (hPhysical : HasPhysicalSlidingBarParameters setup)
    (hLaws : SatisfiesBatteryDrivenSlidingBarLaws setup)
    (hTerminal : IsTerminalSpeed setup setup.terminalSpeed) :
    speedInMetersPerSecond setup.terminalSpeed =
      emfInVolts setup.batteryEmf /
        (magneticFluxDensityInTeslas setup.magneticFluxDensity *
          lengthInMeters setup.barLength) := by
  have hAccelerationZero :
      accelerationReadout UnitChoices.SI
          (setup.accelerationAt setup.terminalSpeed) = 0 := by
    simpa only [IsTerminalSpeed, accelerationInMetersPerSecondSquared] using
      hTerminal
  have hNewton :=
    hLaws.newtonsSecondLawAlongRails setup.terminalSpeed UnitChoices.SI
  have hNetForceZero :
      forceReadout UnitChoices.SI
          (setup.netSlidingForceAt setup.terminalSpeed) = 0 := by
    rw [hAccelerationZero, mul_zero] at hNewton
    exact hNewton.symm
  have hForceBalance :=
    hLaws.frictionlessHorizontalForceBalance
      setup.terminalSpeed UnitChoices.SI
  have hMagneticForceZero :
      forceReadout UnitChoices.SI
          (setup.magneticForceAt setup.terminalSpeed) = 0 := by
    rw [hNetForceZero] at hForceBalance
    exact hForceBalance.symm
  have hMagneticForce :=
    hLaws.straightWireMagneticForceLaw setup.terminalSpeed UnitChoices.SI
  have hCurrentTimesFieldLength :
      currentReadout UnitChoices.SI
            (setup.circuitCurrentAt setup.terminalSpeed) *
          (lengthReadout UnitChoices.SI setup.barLength *
            magneticFluxDensityReadout UnitChoices.SI
              setup.magneticFluxDensity) = 0 := by
    rw [hMagneticForceZero] at hMagneticForce
    simpa only [mul_assoc] using hMagneticForce.symm
  have hLengthPositive :
      0 < lengthReadout UnitChoices.SI setup.barLength := by
    simpa only [lengthInMeters] using hPhysical.barLengthPositive
  have hFieldPositive :
      0 <
        magneticFluxDensityReadout UnitChoices.SI
          setup.magneticFluxDensity := by
    simpa only [magneticFluxDensityInTeslas] using
      hPhysical.magneticFluxDensityPositive
  have hLengthFieldNonzero :
      lengthReadout UnitChoices.SI setup.barLength *
          magneticFluxDensityReadout UnitChoices.SI
            setup.magneticFluxDensity ≠ 0 :=
    ne_of_gt (mul_pos hLengthPositive hFieldPositive)
  have hCurrentZero :
      currentReadout UnitChoices.SI
          (setup.circuitCurrentAt setup.terminalSpeed) = 0 :=
    (mul_eq_zero.mp hCurrentTimesFieldLength).resolve_right
      hLengthFieldNonzero
  have hLoop :=
    hLaws.kirchhoffOhmLoopLaw setup.terminalSpeed UnitChoices.SI
  rw [hCurrentZero, zero_mul] at hLoop
  have hEmfsBalance :
      emfReadout UnitChoices.SI setup.batteryEmf =
        emfReadout UnitChoices.SI
          (setup.motionalEmfAt setup.terminalSpeed) :=
    sub_eq_zero.mp hLoop
  have hMotionalEmf :=
    hLaws.motionalEmfForPerpendicularMotion
      setup.terminalSpeed UnitChoices.SI
  have hFieldLengthNonzero :
      magneticFluxDensityReadout UnitChoices.SI setup.magneticFluxDensity *
          lengthReadout UnitChoices.SI setup.barLength ≠ 0 :=
    ne_of_gt (mul_pos hFieldPositive hLengthPositive)
  change
    speedReadout UnitChoices.SI setup.terminalSpeed =
      emfReadout UnitChoices.SI setup.batteryEmf /
        (magneticFluxDensityReadout UnitChoices.SI
            setup.magneticFluxDensity *
          lengthReadout UnitChoices.SI setup.barLength)
  apply (eq_div_iff hFieldLengthNonzero).2
  calc
    speedReadout UnitChoices.SI setup.terminalSpeed *
          (magneticFluxDensityReadout UnitChoices.SI
              setup.magneticFluxDensity *
            lengthReadout UnitChoices.SI setup.barLength) =
        magneticFluxDensityReadout UnitChoices.SI
              setup.magneticFluxDensity *
            lengthReadout UnitChoices.SI setup.barLength *
              speedReadout UnitChoices.SI setup.terminalSpeed := by
      ac_rfl
    _ =
        emfReadout UnitChoices.SI
          (setup.motionalEmfAt setup.terminalSpeed) :=
      hMotionalEmf.symm
    _ = emfReadout UnitChoices.SI setup.batteryEmf := hEmfsBalance.symm

/-- Labels of the four terminal-speed choices printed with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Speed in metres per second printed beside each answer label. -/
def AnswerChoice.displayedSpeedInMetersPerSecond : AnswerChoice → ℝ
  | .A => 12
  | .B => 14
  | .C => 12 / 5
  | .D => 216 / 25

/-- Dataset answer metadata, retained separately and never used as a premise. -/
def recordedDatasetAnswer : AnswerChoice := .B

/-- A displayed answer is strictly closer to the physical speed than every rival. -/
def IsUniqueClosestAnswer
    (setup : SlidingBarRailSetup) (choice : AnswerChoice) : Prop :=
  ∀ other : AnswerChoice, other ≠ choice →
    |speedInMetersPerSecond setup.terminalSpeed -
        choice.displayedSpeedInMetersPerSecond| <
      |speedInMetersPerSecond setup.terminalSpeed -
        other.displayedSpeedInMetersPerSecond|

/-!
The exact ideal-model terminal speed is `125/9 m/s`, which is `1/9 m/s` below
the displayed `14 m/s`; therefore B is the unique closest choice.

This declaration formalizes `thm:physics:phyx_mini_0976:target`.
-/
theorem problem_phyx_mini_0976
    (setup : SlidingBarRailSetup)
    (hScenario : MatchesWrittenSlidingBarScenario setup)
    (hFigure : MatchesSuppliedSlidingBarFigure setup)
    (hField : ModelsUniformIntoPageMagneticField setup)
    (hMeasurements : HasSlidingBarProblemMeasurements setup)
    (hPhysical : HasPhysicalSlidingBarParameters setup)
    (hLaws : SatisfiesBatteryDrivenSlidingBarLaws setup)
    (hTerminal : IsTerminalSpeed setup setup.terminalSpeed) :
    speedInMetersPerSecond setup.terminalSpeed = (125 / 9 : ℝ) ∧
      |speedInMetersPerSecond setup.terminalSpeed -
          AnswerChoice.B.displayedSpeedInMetersPerSecond| = (1 / 9 : ℝ) ∧
      IsUniqueClosestAnswer setup .B := by
  have hSpeed :=
    terminalSpeed_eq_batteryEmf_div_field_length
      setup hPhysical hLaws hTerminal
  rw [hMeasurements.batteryEmfIsTwelveVolts,
    hMeasurements.magneticFieldIsTwoPointFourTeslas,
    hMeasurements.barLengthIsPointThirtySixMeters] at hSpeed
  norm_num at hSpeed
  refine ⟨hSpeed, ?_, ?_⟩
  rw [hSpeed]
  norm_num [AnswerChoice.displayedSpeedInMetersPerSecond]
  unfold IsUniqueClosestAnswer
  rw [hSpeed]
  intro other hOther
  fin_cases other
  · norm_num [AnswerChoice.displayedSpeedInMetersPerSecond]
  · exact (hOther rfl).elim
  · norm_num [AnswerChoice.displayedSpeedInMetersPerSecond]
  · norm_num [AnswerChoice.displayedSpeedInMetersPerSecond]

end PhyXMiniProblems.ProblemPhyXMini0976
