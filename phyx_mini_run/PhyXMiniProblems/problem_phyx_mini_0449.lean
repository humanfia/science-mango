import Mathlib
import Physlib.Thermodynamics.Temperature.Basic
import Physlib.Thermodynamics.Temperature.TemperatureUnits
import Physlib.Units.WithDim.Area
import Physlib.Units.WithDim.Energy
import Physlib.Units.WithDim.Pressure

/- USER: The assigned source file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0449

open Dimension

/-!
# Work done while argon fills a piston-cylinder

A rigid `400 L` tank `A` initially contains argon at `250 kPa` and `30 °C`.
After a valve to piston-cylinder `B` is opened, the same closed inventory of
argon reaches `150 kPa` and `30 °C` throughout. The frictionless piston is
loaded so that `150 kPa` floats it. Thus the piston moves against a constant
load while tank `A` retains its fixed volume.

Pressure, volume, temperature, piston area, piston mass, acceleration, and
work retain physical quantity types. Real numbers below are only coherent-SI
or named-unit readouts and the displayed multiple-choice values.
-/

/-! ## Dimensionful quantities and named-unit readouts -/

/-- A nonnegative physical volume carrying dimension length cubed. -/
abbrev VolumeQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * L𝓭 * L𝓭) NNReal)

/-- A nonnegative physical mass carrying the SI mass dimension. -/
abbrev MassQuantity : Type :=
  Dimensionful (WithDim M𝓭 NNReal)

/-- A nonnegative acceleration magnitude carrying dimension `L T⁻²`. -/
abbrev AccelerationQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * T𝓭⁻¹ * T𝓭⁻¹) NNReal)

/-- Read a physical pressure in coherent SI units (pascals). -/
def pressureInPascals (pressure : DimPressure) : ℝ :=
  (pressure UnitChoices.SI).val

/-- Read a pressure in the kilopascals used in the problem statement. -/
def pressureInKilopascals (pressure : DimPressure) : ℝ :=
  pressureInPascals pressure / 1000

/-- Read a physical volume in coherent SI units (cubic metres). -/
def volumeInCubicMeters (volume : VolumeQuantity) : ℝ :=
  ((volume UnitChoices.SI).val : ℝ)

/-- Read a physical volume in litres. -/
def volumeInLiters (volume : VolumeQuantity) : ℝ :=
  1000 * volumeInCubicMeters volume

/-- Read signed dimensionful energy in coherent SI units (joules). -/
def energyInJoules (energy : DimEnergy) : ℝ :=
  (energy UnitChoices.SI).val

/-- Read signed dimensionful energy in kilojoules. -/
def energyInKilojoules (energy : DimEnergy) : ℝ :=
  energyInJoules energy / 1000

/-- Read a piston face area in square metres. -/
def areaInSquareMeters (area : DimArea) : ℝ :=
  ((area UnitChoices.SI).val : ℝ)

/-- Read a piston mass in kilograms. -/
def massInKilograms (mass : MassQuantity) : ℝ :=
  ((mass UnitChoices.SI).val : ℝ)

/-- Read an acceleration magnitude in metres per second squared. -/
def accelerationInMetersPerSecondSquared
    (acceleration : AccelerationQuantity) : ℝ :=
  ((acceleration UnitChoices.SI).val : ℝ)

/--
Read absolute temperature in kelvins when Physlib's stored magnitude uses the
given zero-preserving temperature unit.
-/
def temperatureInKelvins
    (storageUnit : TemperatureUnit) (temperature : Temperature) : ℝ :=
  let unitRatio : NNReal := storageUnit / TemperatureUnit.kelvin
  temperature.toReal * (unitRatio : ℝ)

/-- Celsius readout, using the exact offset `273.15 K = 5463 / 20 K`. -/
def temperatureInDegreesCelsius
    (storageUnit : TemperatureUnit) (temperature : Temperature) : ℝ :=
  temperatureInKelvins storageUnit temperature - 5463 / 20

/-! ## Apparatus, process roles, and primary-figure vocabulary -/

/-- Chemical identity of the gas occupying the connected apparatus. -/
inductive WorkingGas where
  | argon
  | other
  deriving DecidableEq, Repr

/-- Equation-of-state model used for the argon at the stated conditions. -/
inductive GasEquationOfState where
  | idealGas
  | other
  deriving DecidableEq, Repr

/-- Mechanical behavior of tank `A`. -/
inductive TankWallBehavior where
  | rigid
  | deformable
  deriving DecidableEq, Repr

/-- Friction model for the piston in cylinder `B`. -/
inductive PistonFrictionModel where
  | frictionless
  | frictional
  deriving DecidableEq, Repr

/-- External-load model encountered by the moving piston. -/
inductive PistonLoadRegime where
  | constantPressure
  | variablePressure
  deriving DecidableEq, Repr

/-- Piston positions relevant to the initially empty and final floating states. -/
inductive PistonState where
  | atCylinderBottom
  | floating
  deriving DecidableEq, Repr

/-- The internal valve operation described in the prose. -/
inductive ValveOperation where
  | initiallyClosedThenOpened
  | remainsClosed
  deriving DecidableEq, Repr

/-- Whether the gas inventory can cross the outer boundary of the apparatus. -/
inductive InventoryRegime where
  | closed
  | open
  deriving DecidableEq, Repr

/-- Spatial character of the final thermodynamic state. -/
inductive FinalStateDistribution where
  | uniformAcrossTankAndCylinder
  | nonuniform
  deriving DecidableEq, Repr

/-- Literal symbols visible in the supplied raster. -/
inductive FigureSymbol where
  | argonText
  | tankA
  | pistonCylinderB
  | externalPressureP0
  | gravityG
  deriving DecidableEq, Fintype, Repr

/-- Regions to which the raster's symbols are attached. -/
inductive FigureRegion where
  | tankInterior
  | tankARegion
  | pistonCylinderBRegion
  | abovePiston
  | besideCylinder
  deriving DecidableEq, Repr

/-- Direction of the gravity arrow in the figure. -/
inductive VerticalDirection where
  | upward
  | downward
  deriving DecidableEq, Repr

/-!
Qualitative information represented by the primary figure. It records the
labels `Argon`, `A`, `B`, `P₀`, and `g`, together with the valve connection and
the vertical piston geometry. It contains no work value.
-/
structure TankPistonFigure where
  showsSymbol : FigureSymbol → Bool
  symbolRegion : FigureSymbol → FigureRegion
  tankConnectedToCylinder : Bool
  valveShownInConnection : Bool
  pistonDrawnInsideCylinderB : Bool
  cylinderOpenAbovePiston : Bool
  gravityArrowDirection : VerticalDirection

/-!
Independent physical quantities and qualitative attributes of the transfer.
The work observable and final cylinder volume are fields, not definitions in
terms of the requested answer; their governing relations are assumptions below.
-/
structure ArgonTankPistonSetup where
  workingGas : WorkingGas
  gasEquationOfState : GasEquationOfState
  tankWallBehavior : TankWallBehavior
  pistonFrictionModel : PistonFrictionModel
  pistonLoadRegime : PistonLoadRegime
  initialPistonState : PistonState
  finalPistonState : PistonState
  valveOperation : ValveOperation
  inventoryRegime : InventoryRegime
  finalDistribution : FinalStateDistribution
  tankAVolume : VolumeQuantity
  cylinderBInitialArgonVolume : VolumeQuantity
  cylinderBFinalArgonVolume : VolumeQuantity
  initialTankPressure : DimPressure
  finalUniformPressure : DimPressure
  pistonFloatPressure : DimPressure
  externalPressureP0 : DimPressure
  initialTemperature : Temperature
  finalTemperature : Temperature
  temperatureStorageUnit : TemperatureUnit
  pistonMass : MassQuantity
  pistonFaceArea : DimArea
  gravityAcceleration : AccelerationQuantity
  workDoneByArgon : DimEnergy
  figure : TankPistonFigure

/-! ## Assumptions: prose, readouts, figure evidence, and governing laws -/

/-- Qualitative idealizations stated by the physical scenario. -/
structure MatchesArgonTankPistonScenario
    (setup : ArgonTankPistonSetup) : Prop where
  gasIsArgon : setup.workingGas = .argon
  argonUsesIdealGasModel : setup.gasEquationOfState = .idealGas
  tankAIsRigid : setup.tankWallBehavior = .rigid
  pistonIsFrictionless : setup.pistonFrictionModel = .frictionless
  pistonLoadIsConstant : setup.pistonLoadRegime = .constantPressure
  cylinderBInitiallyEmpty :
    volumeInCubicMeters setup.cylinderBInitialArgonVolume = 0
  pistonInitiallyAtBottom : setup.initialPistonState = .atCylinderBottom
  pistonFinallyFloats : setup.finalPistonState = .floating
  valveIsOpened : setup.valveOperation = .initiallyClosedThenOpened
  argonInventoryIsClosed : setup.inventoryRegime = .closed
  finalStateIsUniform :
    setup.finalDistribution = .uniformAcrossTankAndCylinder

/-!
Numerical readouts supplied by the prose. The two `30 °C` facts make the
transfer isothermal, while the two independent `150 kPa` facts describe the
piston calibration and the eventual uniform gas pressure.
-/
structure MatchesProblemReadouts (setup : ArgonTankPistonSetup) : Prop where
  tankAVolumeIsFourHundredLiters :
    volumeInLiters setup.tankAVolume = 400
  initialTankPressureIsTwoHundredFiftyKilopascals :
    pressureInKilopascals setup.initialTankPressure = 250
  initialTemperatureIsThirtyCelsius :
    temperatureInDegreesCelsius setup.temperatureStorageUnit
        setup.initialTemperature = 30
  pistonFloatPressureIsOneHundredFiftyKilopascals :
    pressureInKilopascals setup.pistonFloatPressure = 150
  finalUniformPressureIsOneHundredFiftyKilopascals :
    pressureInKilopascals setup.finalUniformPressure = 150
  finalTemperatureIsThirtyCelsius :
    temperatureInDegreesCelsius setup.temperatureStorageUnit
        setup.finalTemperature = 30

/-! Primary-image evidence, separated from the numerical prose readouts. -/
structure MatchesSuppliedTankPistonFigure
    (setup : ArgonTankPistonSetup) : Prop where
  everyPrintedSymbolIsShown :
    ∀ symbol, setup.figure.showsSymbol symbol = true
  argonTextLiesInTank :
    setup.figure.symbolRegion .argonText = .tankInterior
  labelALiesOnTankA :
    setup.figure.symbolRegion .tankA = .tankARegion
  labelBLiesOnPistonCylinder :
    setup.figure.symbolRegion .pistonCylinderB = .pistonCylinderBRegion
  pressureP0IsShownAbovePiston :
    setup.figure.symbolRegion .externalPressureP0 = .abovePiston
  gravityGIsShownBesideCylinder :
    setup.figure.symbolRegion .gravityG = .besideCylinder
  tankAndCylinderAreConnected :
    setup.figure.tankConnectedToCylinder = true
  valveIsShownBetweenThem :
    setup.figure.valveShownInConnection = true
  pistonIsDrawnInsideCylinderB :
    setup.figure.pistonDrawnInsideCylinderB = true
  cylinderIsOpenAbovePiston :
    setup.figure.cylinderOpenAbovePiston = true
  gravityArrowPointsDown :
    setup.figure.gravityArrowDirection = .downward

/-- Positivity and nondegeneracy conditions for the physical apparatus. -/
structure HasPhysicalTankPistonParameters
    (setup : ArgonTankPistonSetup) : Prop where
  tankVolumePositive : 0 < volumeInCubicMeters setup.tankAVolume
  initialPressurePositive : 0 < pressureInPascals setup.initialTankPressure
  finalPressurePositive : 0 < pressureInPascals setup.finalUniformPressure
  floatPressurePositive : 0 < pressureInPascals setup.pistonFloatPressure
  externalPressureNonnegative : 0 ≤ pressureInPascals setup.externalPressureP0
  initialAbsoluteTemperaturePositive :
    0 < temperatureInKelvins setup.temperatureStorageUnit setup.initialTemperature
  finalAbsoluteTemperaturePositive :
    0 < temperatureInKelvins setup.temperatureStorageUnit setup.finalTemperature
  pistonMassPositive : 0 < massInKilograms setup.pistonMass
  pistonAreaPositive : 0 < areaInSquareMeters setup.pistonFaceArea
  gravityAccelerationPositive :
    0 < accelerationInMetersPerSecondSquared setup.gravityAcceleration

/-!
The governing physical model consists of four relations:

* fixed-inventory ideal-gas behavior gives the isothermal `pV` invariant for
  the total argon volume in `A` and `B`;
* the calibrated floating pressure balances `P₀` and the piston weight;
* a floating frictionless piston is in pressure equilibrium with the gas; and
* work done by the argon against the constant load is `P_float ΔV_B`.

These relations contain neither the derived final volume `4/15 m³` nor the
requested work `40 kJ`.
-/
structure SatisfiesIdealGasPistonAndWorkLaws
    (setup : ArgonTankPistonSetup) : Prop where
  fixedInventoryIsothermalIdealGasLaw :
    setup.gasEquationOfState = .idealGas →
      setup.inventoryRegime = .closed →
      temperatureInKelvins setup.temperatureStorageUnit
          setup.initialTemperature =
        temperatureInKelvins setup.temperatureStorageUnit
          setup.finalTemperature →
      pressureInPascals setup.initialTankPressure *
          (volumeInCubicMeters setup.tankAVolume +
            volumeInCubicMeters setup.cylinderBInitialArgonVolume) =
        pressureInPascals setup.finalUniformPressure *
          (volumeInCubicMeters setup.tankAVolume +
            volumeInCubicMeters setup.cylinderBFinalArgonVolume)
  pistonFloatForceBalance :
    pressureInPascals setup.pistonFloatPressure *
        areaInSquareMeters setup.pistonFaceArea =
      pressureInPascals setup.externalPressureP0 *
          areaInSquareMeters setup.pistonFaceArea +
        massInKilograms setup.pistonMass *
          accelerationInMetersPerSecondSquared setup.gravityAcceleration
  floatingPistonMechanicalEquilibrium :
    setup.pistonFrictionModel = .frictionless →
      setup.finalPistonState = .floating →
        setup.finalUniformPressure = setup.pistonFloatPressure
  constantLoadBoundaryWork :
    setup.pistonLoadRegime = .constantPressure →
      energyInJoules setup.workDoneByArgon =
        pressureInPascals setup.pistonFloatPressure *
          (volumeInCubicMeters setup.cylinderBFinalArgonVolume -
            volumeInCubicMeters setup.cylinderBInitialArgonVolume)

/-! ## Derived volume, work, and answer metadata -/

/--
The final volume occupied by argon in cylinder `B` is `4/15 m³`. This is a
derived ideal-gas consequence, not a premise of the work theorem.
-/
lemma finalCylinderBVolume_eq_four_fifteenths_cubicMeters
    (setup : ArgonTankPistonSetup)
    (hScenario : MatchesArgonTankPistonScenario setup)
    (hReadouts : MatchesProblemReadouts setup)
    (hPhysical : HasPhysicalTankPistonParameters setup)
    (hLaws : SatisfiesIdealGasPistonAndWorkLaws setup) :
    volumeInCubicMeters setup.cylinderBFinalArgonVolume = 4 / 15 := by
  have hInitialTemperature := hReadouts.initialTemperatureIsThirtyCelsius
  have hFinalTemperature := hReadouts.finalTemperatureIsThirtyCelsius
  simp only [temperatureInDegreesCelsius] at hInitialTemperature hFinalTemperature
  have hGasLaw := hLaws.fixedInventoryIsothermalIdealGasLaw
    (hScenario.argonUsesIdealGasModel) (hScenario.argonInventoryIsClosed)
    (by linarith)
  have hTankVolume := hReadouts.tankAVolumeIsFourHundredLiters
  have hInitialPressure :=
    hReadouts.initialTankPressureIsTwoHundredFiftyKilopascals
  have hFinalPressure :=
    hReadouts.finalUniformPressureIsOneHundredFiftyKilopascals
  norm_num [volumeInLiters] at hTankVolume
  norm_num [pressureInKilopascals] at hInitialPressure hFinalPressure
  rw [hScenario.cylinderBInitiallyEmpty] at hGasLaw
  nlinarith [hGasLaw]

/--
The argon does positive boundary work of exactly `40 kJ` while lifting the
piston. This is the substantive answer requested by the problem.
-/
theorem workDoneByArgon_eq_forty_kilojoules
    (setup : ArgonTankPistonSetup)
    (hScenario : MatchesArgonTankPistonScenario setup)
    (hReadouts : MatchesProblemReadouts setup)
    (hFigure : MatchesSuppliedTankPistonFigure setup)
    (hPhysical : HasPhysicalTankPistonParameters setup)
    (hLaws : SatisfiesIdealGasPistonAndWorkLaws setup) :
    energyInKilojoules setup.workDoneByArgon = 40 := by
  have hFinalVolume := finalCylinderBVolume_eq_four_fifteenths_cubicMeters
    setup hScenario hReadouts hPhysical hLaws
  have hWork :=
    hLaws.constantLoadBoundaryWork hScenario.pistonLoadIsConstant
  have hFloatPressure :=
    hReadouts.pistonFloatPressureIsOneHundredFiftyKilopascals
  norm_num [pressureInKilopascals] at hFloatPressure
  simp only [energyInKilojoules]
  nlinarith [hWork, hFloatPressure, hFinalVolume,
    hScenario.cylinderBInitiallyEmpty]

/-- Labels printed beside the four candidate answers. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Displayed candidate work values, interpreted in kilojoules. -/
def displayedWorkInKilojoules : AnswerChoice → ℝ
  | .A => 60
  | .B => 100
  | .C => 150
  | .D => 40

/-- The source dataset records answer label `D`; this is metadata only. -/
def recordedDatasetAnswer : AnswerChoice := .D

/-- The physically derived work agrees with displayed answer choice `D`. -/
theorem workDoneByArgon_matches_choice_D
    (setup : ArgonTankPistonSetup)
    (hScenario : MatchesArgonTankPistonScenario setup)
    (hReadouts : MatchesProblemReadouts setup)
    (hFigure : MatchesSuppliedTankPistonFigure setup)
    (hPhysical : HasPhysicalTankPistonParameters setup)
    (hLaws : SatisfiesIdealGasPistonAndWorkLaws setup) :
    energyInKilojoules setup.workDoneByArgon =
      displayedWorkInKilojoules .D := by
  simpa [displayedWorkInKilojoules] using
    workDoneByArgon_eq_forty_kilojoules
      setup hScenario hReadouts hFigure hPhysical hLaws

end PhyXMiniProblems.ProblemPhyXMini0449
