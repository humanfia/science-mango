import Mathlib
import Physlib.Thermodynamics.Temperature.Basic
import Physlib.Thermodynamics.Temperature.TemperatureUnits
import Physlib.Units.WithDim.Pressure

/- USER: The assigned source file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0443

open Dimension

/-!
# Cooling of a rigid air tank after filling

A rigid `1 m³` tank initially contains air at `1 MPa` and `400 K`.  The tank
is connected through a pipe and valve to an air line.  The open valve admits
air until the tank reaches `5 MPa` and `450 K`; the valve is then closed, and
the sealed tank cools to `300 K`.

Pressure, volume, mass, and absolute temperature are retained as physical
quantities.  Real numbers below occur only as calibrated unit readouts and
displayed multiple-choice values.
-/

/-! ## Dimensionful quantities and calibrated readouts -/

/-- A nonnegative physical volume with dimension length cubed. -/
abbrev VolumeQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * L𝓭 * L𝓭) NNReal)

/-- A nonnegative physical mass used to identify the trapped air sample. -/
abbrev AirMassQuantity : Type :=
  Dimensionful (WithDim M𝓭 NNReal)

/-- Read a physical volume in coherent SI cubic metres. -/
def volumeInCubicMeters (volume : VolumeQuantity) : ℝ :=
  ((volume UnitChoices.SI).val : ℝ)

/-- Read a physical pressure in coherent SI pascals. -/
def pressureInPascals (pressure : DimPressure) : ℝ :=
  (pressure UnitChoices.SI).val /
    (DimPressure.pascal UnitChoices.SI).val

/-- Read a physical pressure in megapascals. -/
def pressureInMegapascals (pressure : DimPressure) : ℝ :=
  pressureInPascals pressure / (10 ^ 6 : ℝ)

/-- Read a physical air mass in coherent SI kilograms. -/
def airMassInKilograms (mass : AirMassQuantity) : ℝ :=
  ((mass UnitChoices.SI).val : ℝ)

/-! ## Apparatus, stages, and figure-derived topology -/

/-- The gas species named in the problem. -/
inductive GasSpecies where
  | air
  | other
  deriving DecidableEq, Repr

/-- The thermodynamic equation-of-state model used for the tank air. -/
inductive GasModel where
  | ideal
  | other
  deriving DecidableEq, Repr

/-- Named stages of the filling, valve-closing, and cooling process. -/
inductive ProcessStage where
  | initial
  | duringFilling
  | valveClosure
  | cooled
  deriving DecidableEq, Fintype, Repr

/-- Whether a stage occurs after filling has ended and the valve was closed. -/
def IsPostClosureStage : ProcessStage → Prop
  | .initial => False
  | .duringFilling => False
  | .valveClosure => True
  | .cooled => True

/-- The two valve positions relevant to filling and sealing the tank. -/
inductive ValvePosition where
  | open
  | closed
  deriving DecidableEq, Repr

/-- Individually identifiable objects in the supplied raster. -/
inductive FigureObject where
  | tank
  | airLine
  | connectingPipe
  | valve
  deriving DecidableEq, Fintype, Repr

/-!
Qualitative information read from the primary image: a light-blue rectangular
tank on the left is joined by a horizontal pipe and circled-cross valve to a
vertical air line on the right.  The image supplies no numerical dimensions.
-/
structure SuppliedTankAirLineFigure where
  showsObject : FigureObject → Bool
  showsTankLabel : Bool
  showsAirLineLabel : Bool
  tankIsRectangular : Bool
  tankInteriorIsLightBlue : Bool
  tankIsLeftOfAirLine : Bool
  airLineIsVertical : Bool
  connectingPipeIsHorizontal : Bool
  pipeConnectsTankToAirLine : Bool
  valveIsInConnectingPipe : Bool
  valveIsShownAsCircledCross : Bool

/-- One equilibrium state of the air inside the rigid tank. -/
structure TankAirState where
  pressure : DimPressure
  volume : VolumeQuantity
  temperature : Temperature
  airMass : AirMassQuantity

/-!
The apparatus and its observables.  The cooled pressure is stored as an
independent physical observable; it is not defined from the requested answer.
-/
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
Read an absolute temperature in kelvins.  The storage unit is explicit because
Physlib's `Temperature` permits an arbitrary zero-preserving unit.
-/
def temperatureInKelvin
    (setup : RigidTankAirLineSetup) (stage : ProcessStage) : ℝ :=
  let unitRatio : NNReal :=
    setup.temperatureStorageUnit / TemperatureUnit.kelvin
  (setup.stateAt stage).temperature.toReal * (unitRatio : ℝ)

/-! ## Figure evidence, supplied data, and governing physics -/

/-- The qualitative topology and labels visible in the primary image. -/
structure MatchesSuppliedTankAirLineFigure
    (setup : RigidTankAirLineSetup) : Prop where
  tankIsShown : setup.figure.showsObject .tank = true
  airLineIsShown : setup.figure.showsObject .airLine = true
  connectingPipeIsShown : setup.figure.showsObject .connectingPipe = true
  valveIsShown : setup.figure.showsObject .valve = true
  tankLabelIsShown : setup.figure.showsTankLabel = true
  airLineLabelIsShown : setup.figure.showsAirLineLabel = true
  tankIsRectangular : setup.figure.tankIsRectangular = true
  tankInteriorIsLightBlue : setup.figure.tankInteriorIsLightBlue = true
  tankIsLeftOfAirLine : setup.figure.tankIsLeftOfAirLine = true
  airLineIsVertical : setup.figure.airLineIsVertical = true
  connectingPipeIsHorizontal : setup.figure.connectingPipeIsHorizontal = true
  pipeConnectsTankToAirLine : setup.figure.pipeConnectsTankToAirLine = true
  valveIsInConnectingPipe : setup.figure.valveIsInConnectingPipe = true
  valveIsShownAsCircledCross : setup.figure.valveIsShownAsCircledCross = true

/-!
Numerical readouts and process facts supplied by the prose.  In particular,
this structure contains no cooled-pressure value and no answer-choice label.
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
  valveIsInitiallyClosed :
    setup.valvePositionAt .initial = .closed
  valveIsOpenDuringFilling :
    setup.valvePositionAt .duringFilling = .open
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

Rigidity preserves tank volume, the closed valve preserves trapped air mass,
and the fixed-mass, fixed-volume ideal-gas law makes pressure proportional to
absolute temperature.  The cross-multiplied law is quantified over arbitrary
post-closure stages and contains no solved cooled pressure.
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

/-! ## Displayed answers and current target -/

/-- The four answer labels printed with the source problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Each displayed answer converted to megapascals. -/
def displayedPressureInMegapascals : AnswerChoice → ℝ
  | .A => 1
  | .B => 5
  | .C => 267 / 100
  | .D => 333 / 100

/-- Dataset metadata recording the supplied answer label; never a theorem premise. -/
def recordedDatasetAnswer : AnswerChoice := .D

/-!
A choice matches when its displayed pressure is the exact result rounded to
the nearest hundredth of a megapascal.  The strict half-unit tolerance also
rules out ties.
-/
def MatchesDisplayedPressure
    (setup : RigidTankAirLineSetup) (choice : AnswerChoice) : Prop :=
  |pressureInMegapascals (setup.stateAt .cooled).pressure -
      displayedPressureInMegapascals choice| < (1 / 200 : ℝ)

/-- A displayed choice is the unique rounded match among all four alternatives. -/
def IsUniqueMatchingAnswer
    (setup : RigidTankAirLineSetup) (choice : AnswerChoice) : Prop :=
  MatchesDisplayedPressure setup choice ∧
    ∀ other, MatchesDisplayedPressure setup other → other = choice

/-!
After cooling at fixed volume and fixed air mass, the tank pressure is exactly
`10 / 3 MPa`; consequently its nearest-hundredth display is `3.33 MPa`, choice
D.

Blueprint: `thm:physics:phyx_mini_0443:target`.
-/
theorem cooledTankPressureAndAnswer
    (setup : RigidTankAirLineSetup)
    (hFigure : MatchesSuppliedTankAirLineFigure setup)
    (hPhysical : HasPhysicalTankParameters setup)
    (hData : HasSuppliedTankProcessData setup)
    (hLaws : SatisfiesClosedRigidTankIdealGasLaw setup) :
    pressureInMegapascals (setup.stateAt .cooled).pressure = 10 / 3 ∧
      IsUniqueMatchingAnswer setup .D := by
  have hLaw := hLaws.constantVolumeIdealGasLaw .valveClosure .cooled
    (by trivial) (by trivial)
  have hPressure :
      pressureInMegapascals (setup.stateAt .cooled).pressure = 10 / 3 := by
    rw [hData.cooledTemperatureIs300Kelvin,
        hData.temperatureAtValveClosureIs450Kelvin] at hLaw
    have hClosure := hData.pressureAtValveClosureIsFiveMegapascals
    unfold pressureInMegapascals at hClosure ⊢
    norm_num at hClosure hLaw ⊢
    nlinarith
  refine ⟨hPressure, ?_⟩
  constructor
  · norm_num [MatchesDisplayedPressure, displayedPressureInMegapascals,
      hPressure]
  · intro other hOther
    cases other with
    | A =>
        norm_num [MatchesDisplayedPressure, displayedPressureInMegapascals,
          hPressure] at hOther
    | B =>
        norm_num [MatchesDisplayedPressure, displayedPressureInMegapascals,
          hPressure] at hOther
    | C =>
        norm_num [MatchesDisplayedPressure, displayedPressureInMegapascals,
          hPressure] at hOther
    | D => rfl

end PhyXMiniProblems.ProblemPhyXMini0443
