import Mathlib.Data.Real.Basic
import Physlib.Thermodynamics.Temperature.Basic
import Physlib.Thermodynamics.Temperature.TemperatureUnits
import Physlib.Units.WithDim.Pressure

/- USER: The assigned source file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0400

open Dimension

/-!
# Final pressure after two propane tanks are connected

A rigid `1 m³` tank `A` initially contains propane at `100 kPa` and `300 K`.
A rigid `0.5 m³` tank `B` initially contains propane at `250 kPa` and `400 K`.
Opening their connecting valve produces a uniform final state at `325 K`.

Pressure, volume, absolute temperature, and the molar gas constant retain
their physical dimensional roles.  Real numbers below are explicitly named
SI readouts, mole readouts, figure data, or displayed answer values.
-/

/-! ## Dimensionful quantities and calibrated readouts -/

/-- A physical gas volume, carrying the length-cubed dimension. -/
abbrev GasVolume : Type :=
  Dimensionful (WithDim (L𝓭 * L𝓭 * L𝓭) NNReal)

/-!
The molar gas constant with its energy-per-temperature dimension.

Physlib's `Dimension` has no amount-of-substance coordinate.  Its inverse-mole
role is therefore recorded by the type name and by the explicit mole readouts
paired with this quantity in the ideal-gas law below.
-/
abbrev MolarGasConstantQuantity : Type :=
  Dimensionful
    (WithDim (M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹ * Θ𝓭⁻¹) ℝ)

/-- Read a physical gas volume in coherent SI cubic metres. -/
def volumeInCubicMeters (volume : GasVolume) : ℝ :=
  ((volume UnitChoices.SI).val : ℝ)

/-- Read a physical pressure in coherent SI pascals. -/
def pressureInPascals (pressure : DimPressure) : ℝ :=
  (pressure UnitChoices.SI).val

/-- Read a physical pressure in kilopascals. -/
def pressureInKilopascals (pressure : DimPressure) : ℝ :=
  pressureInPascals pressure / 1000

/-!
Read an absolute `Temperature` in kelvins.  The storage scale is explicit
because Physlib's `Temperature` permits an arbitrary zero-preserving unit.
-/
def temperatureInKelvins
    (storageUnit : TemperatureUnit) (temperature : Temperature) : ℝ :=
  let unitRatio : NNReal := storageUnit / TemperatureUnit.kelvin
  temperature.toReal * (unitRatio : ℝ)

/-- Read the molar gas constant in joules per mole-kelvin. -/
def molarGasConstantInJoulesPerMoleKelvin
    (gasConstant : MolarGasConstantQuantity) : ℝ :=
  (gasConstant UnitChoices.SI).val

/-! ## Tanks, gas portions, process stages, and figure vocabulary -/

/-- The tank labels printed in the primary figure. -/
inductive TankLabel where
  | A
  | B
  deriving DecidableEq, Repr

/-- The initially separated state and the final uniform state. -/
inductive ProcessStage where
  | beforeValveOpens
  | finalUniformState
  deriving DecidableEq, Repr

/-- Vertical placement of a tank in the supplied schematic. -/
inductive VerticalPosition where
  | upper
  | lower
  deriving DecidableEq, Repr

/-- Shape in which each rigid tank is drawn. -/
inductive TankShape where
  | horizontalCylinder
  | other
  deriving DecidableEq, Repr

/-- The attachment location of the connecting pipe at a tank. -/
inductive PipeAttachment where
  | top
  | bottom
  | other
  deriving DecidableEq, Repr

/-- The blue fill shades distinguishing the two tanks in the image. -/
inductive TankShade where
  | lightBlue
  | darkBlue
  deriving DecidableEq, Repr

/-- Position of the control valve at a modeled stage. -/
inductive ValvePosition where
  | closed
  | open
  deriving DecidableEq, Repr

/-- Mechanical model stated for both vessels. -/
inductive TankMechanicalModel where
  | rigid
  | deformable
  deriving DecidableEq, Repr

/-- Idealization of the pipe shown between the two tanks. -/
inductive ConnectionModel where
  | pipeWithNegligibleVolume
  | other
  deriving DecidableEq, Repr

/-- Equation-of-state model used for the propane. -/
inductive GasModel where
  | ideal
  | nonideal
  deriving DecidableEq, Repr

/-- Gas species distinguished by the problem statement. -/
inductive GasSpecies where
  | propane
  | other
  deriving DecidableEq, Repr

/-!
A physical gas portion, retaining both its species and its calibrated amount
readout.  The portion itself is not identified with a bare real number.
-/
structure GasPortion where
  species : GasSpecies
  amountInMoles : ℝ

/-!
Labels and geometry read directly from the primary image.  In particular, the
bitmap shows no flow-direction arrow; flow after opening is part of the process
model, not an invented graphical readout.
-/
structure TwoTankValveFigure where
  verticalPosition : TankLabel → VerticalPosition
  tankLabelVisible : TankLabel → Bool
  tankShape : TankLabel → TankShape
  tankShade : TankLabel → TankShade
  pipeAttachment : TankLabel → PipeAttachment
  connectingPipeVisible : Bool
  valveVisible : Bool
  flowArrowVisible : Bool

/-!
The two tanks, their thermodynamic observables at both stages, their propane
portions, and the connecting equipment.  The final pressure is an independent
observable; no numerical answer is stored or defined here.
-/
structure ConnectedPropaneTanks where
  gasModel : GasModel
  tankMechanicalModel : TankLabel → TankMechanicalModel
  tankVolume : TankLabel → GasVolume
  pressureAt : ProcessStage → TankLabel → DimPressure
  temperatureAt : ProcessStage → TankLabel → Temperature
  gasPortionAt : ProcessStage → TankLabel → GasPortion
  molarGasConstant : MolarGasConstantQuantity
  temperatureStorageUnit : TemperatureUnit
  valvePositionAt : ProcessStage → ValvePosition
  connectionModel : ConnectionModel
  connectingPipeVolume : GasVolume
  figure : TwoTankValveFigure

/-! ## Figure evidence, problem data, and governing laws -/

/-!
Primary-image evidence: `A` is the upper light-blue horizontal cylinder and
`B` the lower dark-blue one.  A visible pipe runs from the bottom of `A` to
the top of `B` through a visible valve on the left.
-/
structure MatchesPrimaryFigure (setup : ConnectedPropaneTanks) : Prop where
  tankAIsUpper : setup.figure.verticalPosition .A = .upper
  tankBIsLower : setup.figure.verticalPosition .B = .lower
  bothTankLabelsVisible :
    setup.figure.tankLabelVisible .A = true ∧
      setup.figure.tankLabelVisible .B = true
  bothTanksDrawnAsHorizontalCylinders :
    ∀ tank, setup.figure.tankShape tank = .horizontalCylinder
  tankAIsLightBlue : setup.figure.tankShade .A = .lightBlue
  tankBIsDarkBlue : setup.figure.tankShade .B = .darkBlue
  pipeLeavesBottomOfA : setup.figure.pipeAttachment .A = .bottom
  pipeEntersTopOfB : setup.figure.pipeAttachment .B = .top
  connectingPipeIsVisible : setup.figure.connectingPipeVisible = true
  valveIsVisible : setup.figure.valveVisible = true
  noFlowArrowIsDrawn : setup.figure.flowArrowVisible = false

/-!
Numerical and qualitative data stated in the problem.  These fields specify
the two initial states and the final temperature, but no numerical final
pressure.
-/
structure MatchesProblemStatement (setup : ConnectedPropaneTanks) : Prop where
  propaneUsesIdealGasModel : setup.gasModel = .ideal
  bothTanksAreRigid :
    ∀ tank, setup.tankMechanicalModel tank = .rigid
  allGasPortionsArePropane :
    ∀ stage tank, (setup.gasPortionAt stage tank).species = .propane
  tankAVolumeInCubicMeters :
    volumeInCubicMeters (setup.tankVolume .A) = 1
  tankBVolumeInCubicMeters :
    volumeInCubicMeters (setup.tankVolume .B) = 1 / 2
  tankAInitialPressureInKilopascals :
    pressureInKilopascals (setup.pressureAt .beforeValveOpens .A) = 100
  tankBInitialPressureInKilopascals :
    pressureInKilopascals (setup.pressureAt .beforeValveOpens .B) = 250
  temperatureReadoutsUseKelvins :
    setup.temperatureStorageUnit = TemperatureUnit.kelvin
  tankAInitialTemperatureInKelvins :
    temperatureInKelvins setup.temperatureStorageUnit
        (setup.temperatureAt .beforeValveOpens .A) = 300
  tankBInitialTemperatureInKelvins :
    temperatureInKelvins setup.temperatureStorageUnit
        (setup.temperatureAt .beforeValveOpens .B) = 400
  finalTemperatureInKelvins :
    ∀ tank,
      temperatureInKelvins setup.temperatureStorageUnit
          (setup.temperatureAt .finalUniformState tank) = 325
  valveInitiallyClosed :
    setup.valvePositionAt .beforeValveOpens = .closed
  valveOpenedForFinalState :
    setup.valvePositionAt .finalUniformState = .open
  usesNegligibleVolumeConnectingPipe :
    setup.connectionModel = .pipeWithNegligibleVolume
  connectingPipeVolumeIsNegligible :
    volumeInCubicMeters setup.connectingPipeVolume = 0

/-- Positivity conditions selecting physically meaningful states and data. -/
structure HasPhysicalParameters (setup : ConnectedPropaneTanks) : Prop where
  tankVolumePositive :
    ∀ tank, 0 < volumeInCubicMeters (setup.tankVolume tank)
  pressurePositive :
    ∀ stage tank, 0 < pressureInPascals (setup.pressureAt stage tank)
  absoluteTemperaturePositive :
    ∀ stage tank,
      0 < temperatureInKelvins setup.temperatureStorageUnit
        (setup.temperatureAt stage tank)
  gasAmountPositive :
    ∀ stage tank, 0 < (setup.gasPortionAt stage tank).amountInMoles
  molarGasConstantPositive :
    0 < molarGasConstantInJoulesPerMoleKelvin setup.molarGasConstant

/-!
Macroscopic ideal-gas and closed-system amount-conservation laws.  The SI
readout equation is dimensionally coherent because `Pa · m³ = J`.  Neither
law contains a numerical final pressure.
-/
structure ObeysIdealGasAndAmountConservation
    (setup : ConnectedPropaneTanks) : Prop where
  idealGasLaw :
    ∀ stage tank,
      pressureInPascals (setup.pressureAt stage tank) *
          volumeInCubicMeters (setup.tankVolume tank) =
        (setup.gasPortionAt stage tank).amountInMoles *
          molarGasConstantInJoulesPerMoleKelvin setup.molarGasConstant *
            temperatureInKelvins setup.temperatureStorageUnit
              (setup.temperatureAt stage tank)
  totalPropaneAmountConserved :
    (setup.gasPortionAt .beforeValveOpens .A).amountInMoles +
        (setup.gasPortionAt .beforeValveOpens .B).amountInMoles =
      (setup.gasPortionAt .finalUniformState .A).amountInMoles +
        (setup.gasPortionAt .finalUniformState .B).amountInMoles

/-!
Opening the valve allows mechanical equilibration, so the final uniform state
has one pressure.  This is a qualitative equilibrium law, not the requested
numerical pressure.
-/
structure ReachesUniformPressure (setup : ConnectedPropaneTanks) : Prop where
  finalPressuresEqual :
    pressureInPascals (setup.pressureAt .finalUniformState .A) =
      pressureInPascals (setup.pressureAt .finalUniformState .B)

/-! ## Displayed choices and requested conclusion -/

/-- The common final-pressure readout, taken from tank `A`, in kilopascals. -/
def finalPressureInKilopascals (setup : ConnectedPropaneTanks) : ℝ :=
  pressureInKilopascals (setup.pressureAt .finalUniformState .A)

/-- Labels of the four displayed answer choices. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Kilopascal value printed beside each displayed answer label. -/
def AnswerChoice.pressureInKilopascals : AnswerChoice → ℝ
  | .A => 4000
  | .B => 1399 / 10
  | .C => 154
  | .D => 51 / 5

/-- Answer label recorded by the supplied dataset. -/
def recordedAnswerChoice : AnswerChoice := .B

/-!
Agreement with a displayed pressure rounded to the nearest `0.1 kPa`: the
exact value is strictly within half of one tenth of the displayed value.
-/
def AgreesWithOneDecimalKilopascalRounding
    (exactPressure displayedPressure : ℝ) : Prop :=
  |exactPressure - displayedPressure| < 1 / 20

/-!
Conservation of propane amount and `PV = nRT` give

`p_f = 325 / (1 + 1/2) * (100 * 1 / 300 + 250 * (1/2) / 400)`

and hence the exact result `p_f = 10075/72 kPa`.  This is approximately
`139.9306 kPa`, which rounds to the displayed `139.9 kPa`, answer choice B.
The exact rational equality and the rounding relation are both conclusions;
neither is present in any premise structure above.

Blueprint label: `thm:physics:phyx_mini_0400:target`.
-/
theorem finalPressureInKilopascals_exact_and_matches_recordedAnswerB
    (setup : ConnectedPropaneTanks)
    (_figure : MatchesPrimaryFigure setup)
    (_problem : MatchesProblemStatement setup)
    (_physical : HasPhysicalParameters setup)
    (_laws : ObeysIdealGasAndAmountConservation setup)
    (_uniform : ReachesUniformPressure setup) :
    finalPressureInKilopascals setup = 10075 / 72 ∧
      AgreesWithOneDecimalKilopascalRounding
        (finalPressureInKilopascals setup)
        recordedAnswerChoice.pressureInKilopascals := by
  have hInitialA :=
    _laws.idealGasLaw ProcessStage.beforeValveOpens TankLabel.A
  have hInitialB :=
    _laws.idealGasLaw ProcessStage.beforeValveOpens TankLabel.B
  have hFinalA :=
    _laws.idealGasLaw ProcessStage.finalUniformState TankLabel.A
  have hFinalB :=
    _laws.idealGasLaw ProcessStage.finalUniformState TankLabel.B
  rw [_problem.tankAVolumeInCubicMeters,
      _problem.tankAInitialTemperatureInKelvins] at hInitialA
  rw [_problem.tankBVolumeInCubicMeters,
      _problem.tankBInitialTemperatureInKelvins] at hInitialB
  rw [_problem.tankAVolumeInCubicMeters,
      _problem.finalTemperatureInKelvins TankLabel.A] at hFinalA
  rw [_problem.tankBVolumeInCubicMeters,
      _problem.finalTemperatureInKelvins TankLabel.B] at hFinalB
  have hConservationTimesGasConstant :=
    congrArg
      (fun amount : ℝ =>
        amount *
          molarGasConstantInJoulesPerMoleKelvin setup.molarGasConstant)
      _laws.totalPropaneAmountConserved
  have hInitialPressureA :=
    _problem.tankAInitialPressureInKilopascals
  have hInitialPressureB :=
    _problem.tankBInitialPressureInKilopascals
  unfold pressureInKilopascals at hInitialPressureA hInitialPressureB
  have hExact : finalPressureInKilopascals setup = 10075 / 72 := by
    unfold finalPressureInKilopascals pressureInKilopascals
    nlinarith [_uniform.finalPressuresEqual,
      _physical.molarGasConstantPositive]
  constructor
  · exact hExact
  · rw [hExact]
    norm_num [AgreesWithOneDecimalKilopascalRounding,
      recordedAnswerChoice, AnswerChoice.pressureInKilopascals, abs_of_nonneg]

end PhyXMiniProblems.ProblemPhyXMini0400
