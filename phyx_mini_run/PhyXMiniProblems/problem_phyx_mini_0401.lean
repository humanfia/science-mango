import Mathlib
import Physlib.Thermodynamics.Temperature.Basic
import Physlib.Thermodynamics.Temperature.TemperatureUnits
import Physlib.Units.WithDim.Pressure

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0401

open Dimension

/-!
# Cooling of a rigid air tank after filling

A rigid one-cubic-metre tank initially contains air at `1 MPa` and `400 K`.
The tank is connected through a pipe and valve to an air line.  Air enters
until the tank reaches `5 MPa` and `450 K`; the valve is then closed.  The
sealed tank subsequently cools to `300 K`.

Pressure, volume, mass, and absolute temperature are retained as physical
quantities.  Real numbers below are only explicitly named SI readouts or
displayed multiple-choice values.
-/

/-! ## Dimensionful quantities and readouts -/

/-- A nonnegative physical volume with dimension length cubed. -/
abbrev VolumeQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * L𝓭 * L𝓭) NNReal)

/-- A nonnegative physical mass used to identify the trapped air sample. -/
abbrev AirMassQuantity : Type := Dimensionful (WithDim M𝓭 NNReal)

/-- Read a physical volume in coherent SI cubic metres. -/
def volumeInCubicMeters (volume : VolumeQuantity) : ℝ :=
  ((volume UnitChoices.SI).val : ℝ)

/-- Read a physical pressure in pascals. -/
def pressureInPascals (pressure : DimPressure) : ℝ :=
  (pressure UnitChoices.SI).val /
    (DimPressure.pascal UnitChoices.SI).val

/-- Read a physical pressure in megapascals. -/
def pressureInMegapascals (pressure : DimPressure) : ℝ :=
  pressureInPascals pressure / (10 ^ 6 : ℝ)

/-- Read a physical mass in coherent SI kilograms. -/
def airMassInKilograms (mass : AirMassQuantity) : ℝ :=
  ((mass UnitChoices.SI).val : ℝ)

/-! ## Apparatus, stages, and figure-derived topology -/

/-- The material in the tank and supply line. -/
inductive GasSpecies where
  | air
  | other
  deriving DecidableEq, Repr

/-- The thermodynamic equation-of-state model. -/
inductive GasModel where
  | ideal
  | other
  deriving DecidableEq, Repr

/-- Named stages in the process described by the problem. -/
inductive ProcessStage where
  | initial
  | valveClosure
  | cooled
  deriving DecidableEq, Fintype, Repr

/-- Whether a stage occurs after filling has ended and the valve was closed. -/
def IsPostClosureStage : ProcessStage → Prop
  | .initial => False
  | .valveClosure => True
  | .cooled => True

/-- The two valve positions relevant to filling and sealing the tank. -/
inductive ValvePosition where
  | open
  | closed
  deriving DecidableEq, Repr

/-- Individually labelled objects visible in the supplied raster. -/
inductive FigureObject where
  | tank
  | airLine
  | connectingPipe
  | valve
  deriving DecidableEq, Fintype, Repr

/-!
The raster supplies only qualitative topology: a tank on the left is joined
by a horizontal pipe, containing a valve, to the vertical air line on the
right.  It supplies no additional numerical dimensions.
-/
structure SuppliedTankAirLineFigure where
  showsObject : FigureObject → Bool
  showsTankLabel : Bool
  showsAirLineLabel : Bool
  tankIsRectangular : Bool
  tankIsLeftOfAirLine : Bool
  airLineIsVertical : Bool
  connectingPipeIsHorizontal : Bool
  pipeConnectsTankToAirLine : Bool
  valveIsInConnectingPipe : Bool

/-- One equilibrium state of the air in the rigid tank. -/
structure TankAirState where
  pressure : DimPressure
  volume : VolumeQuantity
  temperature : Temperature
  airMass : AirMassQuantity

/-- The physical apparatus and its observables throughout the process. -/
structure RigidTankAirLineSetup where
  figure : SuppliedTankAirLineFigure
  gasSpecies : GasSpecies
  gasModel : GasModel
  stateAt : ProcessStage → TankAirState
  temperatureStorageUnit : TemperatureUnit
  valvePositionAt : ProcessStage → ValvePosition
  tankIsRigid : Bool
  airFlowsIntoTankDuringFilling : Bool

/-!
Convert the stored absolute-temperature magnitude to a kelvin readout.  The
explicit storage unit prevents an arbitrary absolute-temperature scale from
being silently interpreted as kelvin.
-/
def temperatureInKelvin
    (setup : RigidTankAirLineSetup) (stage : ProcessStage) : ℝ :=
  let unitRatio : NNReal :=
    setup.temperatureStorageUnit / TemperatureUnit.kelvin
  (setup.stateAt stage).temperature.toReal * (unitRatio : ℝ)

/-- The qualitative connections and labels visible in the primary image. -/
def MatchesSuppliedTankAirLineFigure
    (setup : RigidTankAirLineSetup) : Prop :=
  setup.figure.showsObject .tank = true ∧
  setup.figure.showsObject .airLine = true ∧
    setup.figure.showsObject .connectingPipe = true ∧
    setup.figure.showsObject .valve = true ∧
    setup.figure.showsTankLabel = true ∧
    setup.figure.showsAirLineLabel = true ∧
    setup.figure.tankIsRectangular = true ∧
    setup.figure.tankIsLeftOfAirLine = true ∧
    setup.figure.airLineIsVertical = true ∧
    setup.figure.connectingPipeIsHorizontal = true ∧
    setup.figure.pipeConnectsTankToAirLine = true ∧
    setup.figure.valveIsInConnectingPipe = true

/-!
The numerical readouts and process facts stated in the problem.  In
particular, no cooled-pressure value or answer-choice label occurs here.
-/
structure HasSuppliedTankProcessData
    (setup : RigidTankAirLineSetup) : Prop where
  gasSpeciesIsAir : setup.gasSpecies = .air
  temperatureScaleIsKelvin :
    setup.temperatureStorageUnit = TemperatureUnit.kelvin
  initialTankVolumeIsOneCubicMeter :
    volumeInCubicMeters (setup.stateAt .initial).volume = 1
  initialPressureIsOneMegapascal :
    pressureInMegapascals (setup.stateAt .initial).pressure = 1
  initialTemperatureIs400Kelvin :
    temperatureInKelvin setup .initial = 400
  pressureAtValveClosureIsFiveMegapascals :
    pressureInMegapascals (setup.stateAt .valveClosure).pressure = 5
  temperatureAtValveClosureIs450Kelvin :
    temperatureInKelvin setup .valveClosure = 450
  cooledTemperatureIs300Kelvin :
    temperatureInKelvin setup .cooled = 300
  tankIsRigid : setup.tankIsRigid = true
  airFlowsIntoTankDuringFilling :
    setup.airFlowsIntoTankDuringFilling = true
  airMassIncreasesDuringFilling :
    airMassInKilograms (setup.stateAt .initial).airMass <
      airMassInKilograms (setup.stateAt .valveClosure).airMass
  valveIsClosedAtClosure :
    setup.valvePositionAt .valveClosure = .closed
  valveRemainsClosedWhileCooling :
    setup.valvePositionAt .cooled = .closed

/-- Positivity and nondegeneracy conditions for the physical states. -/
structure HasPhysicalTankParameters
    (setup : RigidTankAirLineSetup) : Prop where
  pressurePositive :
    ∀ stage, 0 < pressureInPascals (setup.stateAt stage).pressure
  volumePositive :
    ∀ stage, 0 < volumeInCubicMeters (setup.stateAt stage).volume
  absoluteTemperaturePositive :
    ∀ stage, 0 < temperatureInKelvin setup stage
  airMassPositive :
    ∀ stage, 0 < airMassInKilograms (setup.stateAt stage).airMass

/-!
Governing physics after the valve closes.

Rigidity preserves tank volume, closing the valve seals the tank and hence
preserves the trapped air mass, and the fixed-mass, fixed-volume ideal-gas law
makes pressure proportional to absolute temperature.  Its cross-multiplied
form is quantified over arbitrary post-closure stages and contains no solved
cooled pressure.
-/
structure SatisfiesClosedRigidTankIdealGasLaw
    (setup : RigidTankAirLineSetup) : Prop where
  gasModelIsIdeal : setup.gasModel = .ideal
  rigidTankVolumeIsConstant :
    ∀ first second,
      (setup.stateAt first).volume = (setup.stateAt second).volume
  valveSealsTankAfterClosure :
    ∀ stage, IsPostClosureStage stage →
      setup.valvePositionAt stage = .closed
  trappedAirMassIsConstantAfterClosure :
    ∀ first second,
      IsPostClosureStage first → IsPostClosureStage second →
        (setup.stateAt first).airMass = (setup.stateAt second).airMass
  constantVolumeIdealGasLaw :
    ∀ first second,
      IsPostClosureStage first → IsPostClosureStage second →
        pressureInPascals (setup.stateAt first).pressure *
            temperatureInKelvin setup second =
          pressureInPascals (setup.stateAt second).pressure *
            temperatureInKelvin setup first

/-! ## Displayed answers and target -/

/-- The four answer labels printed with the source problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Each displayed answer converted to megapascals. -/
def displayedPressureInMegapascals : AnswerChoice → ℝ
  | .A => 4
  | .B => 333 / 100
  | .C => 77 / 500
  | .D => 51 / 5000

/-!
A choice matches when its displayed pressure is the exact result rounded to
the nearest hundredth of a megapascal.  The strict half-unit tolerance also
rules out ties.
-/
def MatchesDisplayedPressure
    (setup : RigidTankAirLineSetup) (choice : AnswerChoice) : Prop :=
  |pressureInMegapascals (setup.stateAt .cooled).pressure -
      displayedPressureInMegapascals choice| < (1 / 200 : ℝ)

/-- A displayed choice is the unique match among the four alternatives. -/
def IsUniqueMatchingAnswer
    (setup : RigidTankAirLineSetup) (choice : AnswerChoice) : Prop :=
  MatchesDisplayedPressure setup choice ∧
    ∀ other, MatchesDisplayedPressure setup other → other = choice

/-!
After cooling at fixed volume and fixed air mass, the tank pressure is
`10 / 3 MPa`; consequently the hundredth-MPa display is `3.33 MPa`, answer B.

Blueprint label: `thm:physics:phyx_mini_0401:target`.
-/
theorem cooledTankPressureAndAnswer
    (setup : RigidTankAirLineSetup)
    (_figure : MatchesSuppliedTankAirLineFigure setup)
    (_physical : HasPhysicalTankParameters setup)
    (_data : HasSuppliedTankProcessData setup)
    (_laws : SatisfiesClosedRigidTankIdealGasLaw setup) :
    pressureInMegapascals (setup.stateAt .cooled).pressure = 10 / 3 ∧
      IsUniqueMatchingAnswer setup .B := by
  have hLaw :=
    _laws.constantVolumeIdealGasLaw .valveClosure .cooled (by trivial) (by trivial)
  have hClosure := _data.pressureAtValveClosureIsFiveMegapascals
  rw [_data.cooledTemperatureIs300Kelvin,
    _data.temperatureAtValveClosureIs450Kelvin] at hLaw
  have hPressure :
      pressureInMegapascals (setup.stateAt .cooled).pressure = 10 / 3 := by
    norm_num [pressureInMegapascals] at hClosure ⊢
    nlinarith [hLaw]
  refine ⟨hPressure, ?_⟩
  constructor
  · rw [MatchesDisplayedPressure, hPressure]
    norm_num [displayedPressureInMegapascals]
  · intro other hOther
    rw [MatchesDisplayedPressure, hPressure] at hOther
    cases other with
    | A => norm_num [displayedPressureInMegapascals] at hOther
    | B => rfl
    | C => norm_num [displayedPressureInMegapascals] at hOther
    | D => norm_num [displayedPressureInMegapascals] at hOther

end PhyXMiniProblems.ProblemPhyXMini0401
