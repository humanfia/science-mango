import Mathlib
import Physlib.Thermodynamics.Temperature.Basic
import Physlib.Thermodynamics.Temperature.TemperatureUnits
import Physlib.Units.WithDim.Area
import Physlib.Units.WithDim.Pressure

/- USER: The assigned source file did not exist when this autoformalization task began. -/

/-!
# Final pressure in a rigid tank feeding a floating piston

A rigid tank `A` initially contains air at `225 psia` and `600 R` in a
`35 ft^3` volume.  Opening the valve transfers some of that air into cylinder
`B`.  The gas below its gravity-loaded piston remains at the `40 psia`
floating pressure while a piston of area `1 ft^2` rises by `7 ft`.  The valve
is then closed, and the entire process is isothermal at `600 R`.

Pressure and area use Physlib's unit-independent quantities.  Length and
volume are dimension-tagged locally because Physlib has no `DimLength` or
`DimVolume` declaration.  Real numbers are used only for named unit readouts,
molar-amount readouts, and the gas constant expressed in the problem's mixed
units.

Assumption/target split:

* `MatchesProblemAndPrimaryFigure` records the prose data, valve sequence, and
  the components, labels, connections, and directions visible in image
  `448.png`;
* `HasPhysicalParameters` supplies positivity of the independent physical
  readouts;
* `SatisfiesPistonSweepGeometry` gives the swept-volume relation
  `Delta V = A Delta h`;
* `SatisfiesIsothermalIdealGasInventory` applies `p V = n R T` separately to
  the initial tank inventory, final tank inventory, and air transferred into
  the constant-pressure swept volume;
* `ConservesAirDuringTransfer` states that air leaving tank `A` is exactly the
  amount admitted beneath the piston; and
* `finalTankPressure_eq_217_psia` concludes, rather than assumes, the requested
  final tank pressure and the corresponding answer choice D.
-/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0448

open Dimension

/-! ## Dimensionful quantities and named unit readouts -/

/-- A nonnegative physical piston displacement, carrying the length dimension. -/
abbrev LengthQuantity : Type :=
  Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative physical volume, carrying the dimension `L^3`. -/
abbrev VolumeQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * L𝓭 * L𝓭) NNReal)

/-- A physical absolute pressure. -/
abbrev PressureQuantity : Type := DimPressure

/-- A nonnegative physical cross-sectional area. -/
abbrev AreaQuantity : Type := DimArea

/-- Read a physical pressure in coherent SI pascals. -/
def pressureInPascals (pressure : PressureQuantity) : ℝ :=
  (pressure UnitChoices.SI).val

/-!
Read an absolute pressure in pounds per square inch.  The denominator is
Physlib's dimensionful quantity representing one `psi`; calling this `psia`
records that all pressures in this problem are absolute, not gauge pressures.
-/
def pressureInPsia (pressure : PressureQuantity) : ℝ :=
  pressureInPascals pressure / pressureInPascals DimPressure.psi

/-- Read a piston displacement in feet. -/
def lengthInFeet (length : LengthQuantity) : ℝ :=
  ((length {UnitChoices.SI with length := LengthUnit.feet}).val : ℝ)

/-- Read a cross-sectional area in square feet. -/
def areaInSquareFeet (area : AreaQuantity) : ℝ :=
  ((area UnitChoices.SI).val : ℝ) /
    ((DimArea.squareFoot UnitChoices.SI).val : ℝ)

/-- Read a physical volume using feet as the selected length unit. -/
def volumeInCubicFeet (volume : VolumeQuantity) : ℝ :=
  ((volume {UnitChoices.SI with length := LengthUnit.feet}).val : ℝ)

/-!
Rankine is the absolute Fahrenheit scale.  Physlib's `Temperature` deliberately
uses an arbitrary absolute unit; in this setup that unit is fixed to
`TemperatureUnit.absoluteFahrenheit`, and this is its real-valued readout.
-/
def temperatureInRankine (temperature : Temperature) : ℝ :=
  temperature.toReal

/-! ## Apparatus, process, and primary-figure vocabulary -/

/-- The gas species named by the problem. -/
inductive GasSpecies where
  | air
  deriving DecidableEq, Repr

/-- The two vessels labelled in the primary image. -/
inductive Vessel where
  | tankA
  | cylinderB
  deriving DecidableEq, Repr

/-- The stated mechanical character of tank `A`. -/
inductive TankBehavior where
  | rigid
  deriving DecidableEq, Repr

/-- The slow piston motion assumed by the textbook model. -/
inductive PistonMotionRegime where
  | quasistaticUpward
  deriving DecidableEq, Repr

/-- The thermal constraint stated for the valve-opening process. -/
inductive ThermalRegime where
  | isothermal
  deriving DecidableEq, Repr

/-- Direction in which air crosses the open valve. -/
inductive AirTransferDirection where
  | fromTankAToCylinderB
  deriving DecidableEq, Repr

/-- Three events in the valve operation described in the prose. -/
inductive ValveEvent where
  | beforeOpening
  | duringPistonMotion
  | afterClosing
  deriving DecidableEq, Repr

/-- Whether the valve is open or closed at a given event. -/
inductive ValvePosition where
  | open
  | closed
  deriving DecidableEq, Repr

/-- Vertical direction of the piston motion or gravity arrow. -/
inductive VerticalDirection where
  | upward
  | downward
  deriving DecidableEq, Repr

/-- Physical components distinguished in image `448.png`. -/
inductive FigureComponent where
  | tankA
  | cylinderB
  | piston
  | valve
  | connectingGasPassage
  | gasBelowPiston
  deriving DecidableEq, Repr

/-- Text or symbols printed in the primary image. -/
inductive FigureLabel where
  | tankA
  | cylinderB
  | piston
  | valve
  | gravityG
  deriving DecidableEq, Repr

/-- Relative left-to-right placement visible in the schematic. -/
inductive HorizontalPlacement where
  | leftOf
  | rightOf
  deriving DecidableEq, Repr

/-- Structured transcription of the components and geometry in image `448.png`. -/
structure TankPistonFigure where
  componentShown : FigureComponent → Bool
  labelShown : FigureLabel → Bool
  vesselPlacement : Vessel → Vessel → HorizontalPlacement
  gasPassageConnectsTankAndCylinder : Bool
  valveLiesOnConnectingPassage : Bool
  pistonIsInsideCylinderB : Bool
  gasRegionIsBelowPiston : Bool
  gravityArrowDirection : VerticalDirection

/-!
Independent physical quantities and measured scalar components of the setup.
In particular, `tankAFinalPressure` is an unconstrained physical-pressure
field: it is not defined from `217` or from an answer choice.
-/
structure RigidTankPistonSetup where
  gasSpecies : GasSpecies
  tankBehavior : TankBehavior
  pistonMotionRegime : PistonMotionRegime
  thermalRegime : ThermalRegime
  transferDirection : AirTransferDirection
  valvePosition : ValveEvent → ValvePosition
  tankAInitialPressure : PressureQuantity
  tankAFinalPressure : PressureQuantity
  pistonFloatingPressure : PressureQuantity
  tankAVolume : VolumeQuantity
  pistonArea : AreaQuantity
  pistonRise : LengthQuantity
  sweptCylinderVolume : VolumeQuantity
  airTemperature : Temperature
  selectedTemperatureUnit : TemperatureUnit
  initialTankAirAmountMoles : ℝ
  finalTankAirAmountMoles : ℝ
  airTransferredToCylinderMoles : ℝ
  gasConstantPsiaCubicFeetPerMoleRankine : ℝ
  figure : TankPistonFigure

/-! ## Problem data and primary-image readouts -/

/-!
Numerical data from the prose and qualitative data from the primary image.
No field here fixes the requested final tank pressure, `217 psia`, or an
answer-choice label.
-/
structure MatchesProblemAndPrimaryFigure
    (setup : RigidTankPistonSetup) : Prop where
  gasIsAir : setup.gasSpecies = .air
  tankAIsRigid : setup.tankBehavior = .rigid
  pistonMovesSlowlyUpward :
    setup.pistonMotionRegime = .quasistaticUpward
  processIsIsothermal : setup.thermalRegime = .isothermal
  airFlowsFromTankToCylinder :
    setup.transferDirection = .fromTankAToCylinderB
  valveInitiallyClosed :
    setup.valvePosition .beforeOpening = .closed
  valveOpenDuringPistonMotion :
    setup.valvePosition .duringPistonMotion = .open
  valveClosedAtEnd : setup.valvePosition .afterClosing = .closed
  tankVolumeIsThirtyFiveCubicFeet :
    volumeInCubicFeet setup.tankAVolume = 35
  initialTankPressureIsTwoHundredTwentyFivePsia :
    pressureInPsia setup.tankAInitialPressure = 225
  floatingPressureIsFortyPsia :
    pressureInPsia setup.pistonFloatingPressure = 40
  pistonAreaIsOneSquareFoot : areaInSquareFeet setup.pistonArea = 1
  pistonRiseIsSevenFeet : lengthInFeet setup.pistonRise = 7
  temperatureUnitIsRankine :
    setup.selectedTemperatureUnit = TemperatureUnit.absoluteFahrenheit
  airRemainsAtSixHundredRankine :
    temperatureInRankine setup.airTemperature = 600
  everyComponentIsShown :
    ∀ component, setup.figure.componentShown component = true
  everyLabelIsShown : ∀ label, setup.figure.labelShown label = true
  tankAIsDrawnLeftOfCylinderB :
    setup.figure.vesselPlacement .tankA .cylinderB = .leftOf
  cylinderBIsDrawnRightOfTankA :
    setup.figure.vesselPlacement .cylinderB .tankA = .rightOf
  passageConnectsTankAndCylinder :
    setup.figure.gasPassageConnectsTankAndCylinder = true
  valveIsOnPassage : setup.figure.valveLiesOnConnectingPassage = true
  pistonIsInsideCylinder : setup.figure.pistonIsInsideCylinderB = true
  gasIsBelowPiston : setup.figure.gasRegionIsBelowPiston = true
  gravityPointsDownward :
    setup.figure.gravityArrowDirection = .downward

/-! ## Positivity and governing physical laws -/

/-- Positivity conditions selecting the intended physical branch. -/
structure HasPhysicalParameters (setup : RigidTankPistonSetup) : Prop where
  initialTankPressurePositive :
    0 < pressureInPsia setup.tankAInitialPressure
  finalTankPressurePositive : 0 < pressureInPsia setup.tankAFinalPressure
  floatingPressurePositive :
    0 < pressureInPsia setup.pistonFloatingPressure
  tankVolumePositive : 0 < volumeInCubicFeet setup.tankAVolume
  pistonAreaPositive : 0 < areaInSquareFeet setup.pistonArea
  pistonRisePositive : 0 < lengthInFeet setup.pistonRise
  sweptVolumePositive : 0 < volumeInCubicFeet setup.sweptCylinderVolume
  temperaturePositive : 0 < temperatureInRankine setup.airTemperature
  gasConstantPositive :
    0 < setup.gasConstantPsiaCubicFeetPerMoleRankine
  initialTankAmountPositive : 0 < setup.initialTankAirAmountMoles
  finalTankAmountNonnegative : 0 ≤ setup.finalTankAirAmountMoles
  transferredAmountPositive : 0 < setup.airTransferredToCylinderMoles

/-!
The vertical piston displacement sweeps out `area * rise` beneath the piston.
This geometric law contains no pressure value and no requested conclusion.
-/
structure SatisfiesPistonSweepGeometry
    (setup : RigidTankPistonSetup) : Prop where
  sweptVolumeEqualsAreaTimesRise :
    volumeInCubicFeet setup.sweptCylinderVolume =
      areaInSquareFeet setup.pistonArea * lengthInFeet setup.pistonRise

/-!
Ideal-gas inventory equations in one consistent mixed-unit system.  The first
two equations describe the air remaining in the same rigid tank before and
after transfer.  The third describes the admitted air occupying the volume
swept beneath a quasistatic piston held at its floating pressure.  A single
temperature field expresses the stated isothermal condition.
-/
structure SatisfiesIsothermalIdealGasInventory
    (setup : RigidTankPistonSetup) : Prop where
  initialTankIdealGasLaw :
    pressureInPsia setup.tankAInitialPressure *
        volumeInCubicFeet setup.tankAVolume =
      setup.initialTankAirAmountMoles *
        setup.gasConstantPsiaCubicFeetPerMoleRankine *
          temperatureInRankine setup.airTemperature
  finalTankIdealGasLaw :
    pressureInPsia setup.tankAFinalPressure *
        volumeInCubicFeet setup.tankAVolume =
      setup.finalTankAirAmountMoles *
        setup.gasConstantPsiaCubicFeetPerMoleRankine *
          temperatureInRankine setup.airTemperature
  transferredAirIdealGasLaw :
    pressureInPsia setup.pistonFloatingPressure *
        volumeInCubicFeet setup.sweptCylinderVolume =
      setup.airTransferredToCylinderMoles *
        setup.gasConstantPsiaCubicFeetPerMoleRankine *
          temperatureInRankine setup.airTemperature

/-!
Air inventory is conserved while the valve is open: the loss from rigid tank
`A` equals the amount admitted to cylinder `B`.  This law contains no pressure
answer.
-/
structure ConservesAirDuringTransfer
    (setup : RigidTankPistonSetup) : Prop where
  tankLossEqualsCylinderGain :
    setup.initialTankAirAmountMoles =
      setup.finalTankAirAmountMoles + setup.airTransferredToCylinderMoles

/-! ## Displayed choices and requested conclusion -/

/-- Labels of the four answers printed with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Absolute-pressure value printed beside each displayed answer, in psia. -/
def answerPressureInPsia : AnswerChoice → ℝ
  | .A => 200
  | .B => 212
  | .C => 225
  | .D => 217

/-- The answer label recorded in the supplied dataset. -/
def recordedAnswerChoice : AnswerChoice := .D

/-!
The final absolute pressure in rigid tank `A` is `217 psia`, and this value
uniquely selects displayed answer D.

Blueprint label: `thm:physics:phyx_mini_0448:target`.
-/
theorem finalTankPressure_eq_217_psia
    (setup : RigidTankPistonSetup)
    (_data : MatchesProblemAndPrimaryFigure setup)
    (_physical : HasPhysicalParameters setup)
    (_geometry : SatisfiesPistonSweepGeometry setup)
    (_idealGas : SatisfiesIsothermalIdealGasInventory setup)
    (_conservation : ConservesAirDuringTransfer setup) :
    pressureInPsia setup.tankAFinalPressure = 217 ∧
      answerPressureInPsia .D =
        pressureInPsia setup.tankAFinalPressure ∧
      ∀ choice,
        answerPressureInPsia choice =
            pressureInPsia setup.tankAFinalPressure →
          choice = .D := by
  have sweptVolume_eq_seven :
      volumeInCubicFeet setup.sweptCylinderVolume = 7 := by
    calc
      volumeInCubicFeet setup.sweptCylinderVolume =
          areaInSquareFeet setup.pistonArea * lengthInFeet setup.pistonRise :=
        _geometry.sweptVolumeEqualsAreaTimesRise
      _ = 1 * 7 := by
        rw [_data.pistonAreaIsOneSquareFoot, _data.pistonRiseIsSevenFeet]
      _ = 7 := by norm_num
  have initialIdealGasLaw := _idealGas.initialTankIdealGasLaw
  have finalIdealGasLaw := _idealGas.finalTankIdealGasLaw
  have transferredIdealGasLaw := _idealGas.transferredAirIdealGasLaw
  rw [_data.initialTankPressureIsTwoHundredTwentyFivePsia,
    _data.tankVolumeIsThirtyFiveCubicFeet,
    _data.airRemainsAtSixHundredRankine] at initialIdealGasLaw
  rw [_data.tankVolumeIsThirtyFiveCubicFeet,
    _data.airRemainsAtSixHundredRankine] at finalIdealGasLaw
  rw [_data.floatingPressureIsFortyPsia, sweptVolume_eq_seven,
    _data.airRemainsAtSixHundredRankine] at transferredIdealGasLaw
  rw [_conservation.tankLossEqualsCylinderGain] at initialIdealGasLaw
  have finalPressure_eq :
      pressureInPsia setup.tankAFinalPressure = 217 := by
    nlinarith [initialIdealGasLaw, finalIdealGasLaw, transferredIdealGasLaw]
  refine ⟨finalPressure_eq, ?_, ?_⟩
  · simpa [answerPressureInPsia] using finalPressure_eq.symm
  · intro choice choicePressure_eq
    cases choice with
    | A => norm_num [answerPressureInPsia, finalPressure_eq] at choicePressure_eq
    | B => norm_num [answerPressureInPsia, finalPressure_eq] at choicePressure_eq
    | C => norm_num [answerPressureInPsia, finalPressure_eq] at choicePressure_eq
    | D => rfl

end PhyXMiniProblems.ProblemPhyXMini0448
