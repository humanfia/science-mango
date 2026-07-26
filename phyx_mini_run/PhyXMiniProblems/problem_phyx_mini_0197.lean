import Mathlib
import Physlib.Units.WithDim.Speed

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0197

open Dimension

/-!
# Doppler shift of a police siren reflected by a warehouse

The one-dimensional axis used in the supplied figure is positive from the
warehouse label `L` toward the car label `S`.  Thus the car's displayed
velocity component is `-30 m/s`, even though its motion arrow points from `S`
toward the warehouse.  The warehouse and still air have zero velocity in this
axis, and the pictured reflected wave travels from `L` to `S`.

Frequencies, sound speed, and signed velocity components are represented by
unit-independent Physlib quantities.  Real numbers occur only as readouts in
named units, propagation-direction signs, and displayed numerical choices.

The numerical choices are consistent with the common calibration established
at the start of the surrounding Doppler series: a `300 Hz` siren in still air
with sound speed `340 m/s`.  Those values are kept in a separate calibration
predicate because they are required for the recorded numerical answer but are
omitted from this individual question's text.
-/

/-- A nonnegative physical frequency, carrying inverse-time dimension. -/
abbrev FrequencyQuantity : Type :=
  Dimensionful (WithDim T𝓭⁻¹ NNReal)

/-- A nonnegative physical speed, independent of the unit used to read it. -/
abbrev SpeedQuantity : Type := DimSpeed

/-- A signed one-dimensional velocity component. -/
abbrev VelocityQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * T𝓭⁻¹) ℝ)

/-- Read a frequency in inverse units of the selected time unit. -/
def frequencyReadout
    (unit : TimeUnit) (frequency : FrequencyQuantity) : ℝ :=
  ((frequency {UnitChoices.SI with time := unit}).val : ℝ)

/-- Read a speed in a selected length unit per selected time unit. -/
def speedReadout
    (lengthUnit : LengthUnit) (timeUnit : TimeUnit)
    (speed : SpeedQuantity) : ℝ :=
  ((speed {UnitChoices.SI with
    length := lengthUnit, time := timeUnit}).val : ℝ)

/-- Read a signed velocity component in compatible length and time units. -/
def velocityReadout
    (lengthUnit : LengthUnit) (timeUnit : TimeUnit)
    (velocity : VelocityQuantity) : ℝ :=
  (velocity {UnitChoices.SI with
    length := lengthUnit, time := timeUnit}).val

/-- Hertz readout, i.e. cycles per SI second. -/
def frequencyInHertz (frequency : FrequencyQuantity) : ℝ :=
  frequencyReadout TimeUnit.seconds frequency

/-- Meter-per-second readout of a nonnegative speed. -/
def speedInMetersPerSecond (speed : SpeedQuantity) : ℝ :=
  speedReadout LengthUnit.meters TimeUnit.seconds speed

/-- Meter-per-second readout of a signed axial velocity component. -/
def velocityInMetersPerSecond (velocity : VelocityQuantity) : ℝ :=
  velocityReadout LengthUnit.meters TimeUnit.seconds velocity

/-- The two distinguished objects carrying the figure labels `S` and `L`. -/
inductive FigureEntity where
  | sourceAndDriverS
  | warehouseReflectorL
  deriving DecidableEq, Repr

/-- The two directions along the road between the labels `S` and `L`. -/
inductive PropagationDirection where
  | fromSToL
  | fromLToS
  deriving DecidableEq, Repr

/-- Sign of a direction in the displayed axis, which is positive from `L` to `S`. -/
def propagationSign : PropagationDirection → ℝ
  | .fromSToL => -1
  | .fromLToS => 1

/-- Qualitative acoustic medium used by the problem. -/
inductive AcousticMedium where
  | stillAir
  deriving DecidableEq, Repr

/-- The reflecting object's physical role in the acoustic model. -/
inductive ReflectorKind where
  | rigidWarehouseWall
  deriving DecidableEq, Repr

/-!
The discrete geometry and numerical annotations visible in the supplied
bitmap.  The velocity labels are explicitly scalar readouts in meters per
second; physical velocities themselves remain dimensionful setup fields.
-/
structure DopplerReflectionFigure where
  leftEntity : FigureEntity
  rightEntity : FigureEntity
  positiveAxisDirection : PropagationDirection
  carMotionArrow : PropagationDirection
  reflectedWaveDirection : PropagationDirection
  displayedVelocityMetersPerSecond : FigureEntity → ℝ
  showsReflectedWave : Bool

/-!
Physical quantities for the outgoing and reflected legs.  In particular,
the three post-emission frequencies are independent fields: none is defined
to have the requested numerical value.
-/
structure WarehouseReflectionSetup where
  medium : AcousticMedium
  reflectorKind : ReflectorKind
  soundSpeed : SpeedQuantity
  airVelocity : VelocityQuantity
  carVelocity : VelocityQuantity
  warehouseVelocity : VelocityQuantity
  emittedFrequency : FrequencyQuantity
  incidentFrequencyAtWarehouse : FrequencyQuantity
  reflectedFrequencyAtWarehouse : FrequencyQuantity
  driverHeardFrequency : FrequencyQuantity
  incidentDirection : PropagationDirection
  reflectedDirection : PropagationDirection
  figure : DopplerReflectionFigure

/-!
The calibration inherited from the common setup of the immediately preceding
Doppler questions: a `300 Hz` siren, `340 m/s` sound speed, and still air.  It
contains no incident, reflected, or driver-heard frequency conclusion.
-/
structure MatchesSharedDopplerCalibration
    (setup : WarehouseReflectionSetup) : Prop where
  mediumIsStillAir : setup.medium = .stillAir
  reflectorIsRigidWarehouse : setup.reflectorKind = .rigidWarehouseWall
  emittedFrequencyHertz : frequencyInHertz setup.emittedFrequency = 300
  soundSpeedMetersPerSecond :
    speedInMetersPerSecond setup.soundSpeed = 340
  airVelocityMetersPerSecond :
    velocityInMetersPerSecond setup.airVelocity = 0

/-!
Data read directly from the current problem statement and primary bitmap.
The car/source `S` is drawn on the left, the warehouse/reflector `L` on the
right, the displayed positive axis is `L` to `S`, the car moves from `S` to
`L`, and the reflected wave returns from `L` to `S`.  The velocity labels are
`v_S = -30 m/s` and `v_L = 0` in that displayed sign convention.
-/
structure MatchesSuppliedWarehouseFigure
    (setup : WarehouseReflectionSetup) : Prop where
  sourceAndDriverIsLeft : setup.figure.leftEntity = .sourceAndDriverS
  warehouseReflectorIsRight :
    setup.figure.rightEntity = .warehouseReflectorL
  positiveAxisIsLToS :
    setup.figure.positiveAxisDirection = .fromLToS
  carMovesTowardWarehouse : setup.figure.carMotionArrow = .fromSToL
  reflectedWaveReturnsLToS :
    setup.figure.reflectedWaveDirection = .fromLToS
  reflectedWaveIsShown : setup.figure.showsReflectedWave = true
  displayedCarVelocity :
    setup.figure.displayedVelocityMetersPerSecond .sourceAndDriverS = -30
  displayedWarehouseVelocity :
    setup.figure.displayedVelocityMetersPerSecond .warehouseReflectorL = 0
  carVelocityMatchesDisplay :
    velocityInMetersPerSecond setup.carVelocity =
      setup.figure.displayedVelocityMetersPerSecond .sourceAndDriverS
  warehouseVelocityMatchesDisplay :
    velocityInMetersPerSecond setup.warehouseVelocity =
      setup.figure.displayedVelocityMetersPerSecond .warehouseReflectorL
  incidentWaveTravelsSToL : setup.incidentDirection = .fromSToL
  reflectedWaveTravelsLToS : setup.reflectedDirection = .fromLToS

/-- Positivity and subsonic conditions for the two Doppler legs. -/
structure HasPhysicalDopplerParameters
    (setup : WarehouseReflectionSetup) : Prop where
  soundSpeedPositive : 0 < speedInMetersPerSecond setup.soundSpeed
  emittedFrequencyPositive : 0 < frequencyInHertz setup.emittedFrequency
  incidentFrequencyPositive :
    0 < frequencyInHertz setup.incidentFrequencyAtWarehouse
  reflectedFrequencyPositive :
    0 < frequencyInHertz setup.reflectedFrequencyAtWarehouse
  heardFrequencyPositive : 0 < frequencyInHertz setup.driverHeardFrequency
  carIsSubsonicRelativeToAir :
    |velocityInMetersPerSecond setup.carVelocity -
        velocityInMetersPerSecond setup.airVelocity| <
      speedInMetersPerSecond setup.soundSpeed
  warehouseIsSubsonicRelativeToAir :
    |velocityInMetersPerSecond setup.warehouseVelocity -
        velocityInMetersPerSecond setup.airVelocity| <
      speedInMetersPerSecond setup.soundSpeed

/-!
General one-dimensional acoustic laws used in the solution.

For a wave traveling with sign `d` through a medium at speed `c`, source and
receiver velocity components are measured relative to the medium.  The
received-to-emitted frequency ratio is

`(c - d * v_receiver) / (c - d * v_source)`.

The rigid warehouse preserves frequency in its own rest frame.  Applying the
general Doppler law first from car to warehouse and then from warehouse to car
models the double shift without assuming the requested numerical result.
-/
structure SatisfiesWarehouseReflectionLaws
    (setup : WarehouseReflectionSetup) : Prop where
  incidentDopplerLaw :
    ∀ (lengthUnit : LengthUnit) (timeUnit : TimeUnit),
      frequencyReadout timeUnit setup.incidentFrequencyAtWarehouse =
        frequencyReadout timeUnit setup.emittedFrequency *
          (speedReadout lengthUnit timeUnit setup.soundSpeed -
            propagationSign setup.incidentDirection *
              (velocityReadout lengthUnit timeUnit setup.warehouseVelocity -
                velocityReadout lengthUnit timeUnit setup.airVelocity)) /
          (speedReadout lengthUnit timeUnit setup.soundSpeed -
            propagationSign setup.incidentDirection *
              (velocityReadout lengthUnit timeUnit setup.carVelocity -
                velocityReadout lengthUnit timeUnit setup.airVelocity))
  rigidReflectionPreservesWarehouseFrameFrequency :
    ∀ timeUnit : TimeUnit,
      frequencyReadout timeUnit setup.reflectedFrequencyAtWarehouse =
        frequencyReadout timeUnit setup.incidentFrequencyAtWarehouse
  returnDopplerLaw :
    ∀ (lengthUnit : LengthUnit) (timeUnit : TimeUnit),
      frequencyReadout timeUnit setup.driverHeardFrequency =
        frequencyReadout timeUnit setup.reflectedFrequencyAtWarehouse *
          (speedReadout lengthUnit timeUnit setup.soundSpeed -
            propagationSign setup.reflectedDirection *
              (velocityReadout lengthUnit timeUnit setup.carVelocity -
                velocityReadout lengthUnit timeUnit setup.airVelocity)) /
          (speedReadout lengthUnit timeUnit setup.soundSpeed -
            propagationSign setup.reflectedDirection *
              (velocityReadout lengthUnit timeUnit setup.warehouseVelocity -
                velocityReadout lengthUnit timeUnit setup.airVelocity))

/-!
On the incident leg, the moving siren approaches the stationary warehouse.
The first Doppler shift therefore raises `300 Hz` to `10200/31 Hz` in the
warehouse frame.
-/
lemma incidentFrequencyAtWarehouse_eq_10200_over_31
    (setup : WarehouseReflectionSetup)
    (h_calibration : MatchesSharedDopplerCalibration setup)
    (h_figure : MatchesSuppliedWarehouseFigure setup)
    (h_physical : HasPhysicalDopplerParameters setup)
    (h_laws : SatisfiesWarehouseReflectionLaws setup) :
    frequencyInHertz setup.incidentFrequencyAtWarehouse =
      (10200 : ℝ) / 31 := by
  sorry

/-!
After frequency-preserving reflection, the driver approaches the returning
wave.  Combining the two general Doppler factors gives the unrounded heard
frequency `11100/31 Hz`.
-/
lemma driverHeardFrequency_eq_11100_over_31
    (setup : WarehouseReflectionSetup)
    (h_calibration : MatchesSharedDopplerCalibration setup)
    (h_figure : MatchesSuppliedWarehouseFigure setup)
    (h_physical : HasPhysicalDopplerParameters setup)
    (h_laws : SatisfiesWarehouseReflectionLaws setup) :
    frequencyInHertz setup.driverHeardFrequency =
      (11100 : ℝ) / 31 := by
  sorry

/-- Labels of the four frequency choices printed with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Displayed frequency beside an answer label, in hertz. -/
def displayedAnswerFrequencyHertz : AnswerChoice → ℝ
  | .A => 377
  | .B => 358
  | .C => 342
  | .D => 367

/-- The answer label recorded by the source dataset. -/
def recordedDatasetAnswer : AnswerChoice := .B

/-- Absolute discrepancy between the physical heard frequency and a choice. -/
def answerErrorHertz
    (setup : WarehouseReflectionSetup) (choice : AnswerChoice) : ℝ :=
  |frequencyInHertz setup.driverHeardFrequency -
    displayedAnswerFrequencyHertz choice|

/-- A displayed choice is strictly closer than every other displayed value. -/
def IsClosestDisplayedChoice
    (setup : WarehouseReflectionSetup) (choice : AnswerChoice) : Prop :=
  ∀ other : AnswerChoice,
    other ≠ choice → answerErrorHertz setup choice < answerErrorHertz setup other

/-- The exact Doppler result lies within half a hertz of the printed `358 Hz`. -/
lemma driverHeardFrequency_roundsTo_358
    (setup : WarehouseReflectionSetup)
    (h_calibration : MatchesSharedDopplerCalibration setup)
    (h_figure : MatchesSuppliedWarehouseFigure setup)
    (h_physical : HasPhysicalDopplerParameters setup)
    (h_laws : SatisfiesWarehouseReflectionLaws setup) :
    |frequencyInHertz setup.driverHeardFrequency - 358| < (1 : ℝ) / 2 := by
  sorry

/-!
The driver hears the twice-shifted frequency `11100/31 Hz`, which rounds to
`358 Hz`; among the four displayed values, choice `B` is uniquely closest.
-/
theorem problem_phyx_mini_0197
    (setup : WarehouseReflectionSetup)
    (h_calibration : MatchesSharedDopplerCalibration setup)
    (h_figure : MatchesSuppliedWarehouseFigure setup)
    (h_physical : HasPhysicalDopplerParameters setup)
    (h_laws : SatisfiesWarehouseReflectionLaws setup) :
    frequencyInHertz setup.driverHeardFrequency = (11100 : ℝ) / 31 ∧
      |frequencyInHertz setup.driverHeardFrequency -
          displayedAnswerFrequencyHertz .B| < (1 : ℝ) / 2 ∧
      IsClosestDisplayedChoice setup .B := by
  sorry

end PhyXMiniProblems.ProblemPhyXMini0197
