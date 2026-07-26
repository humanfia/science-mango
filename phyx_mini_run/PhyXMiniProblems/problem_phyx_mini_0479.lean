import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Physlib.Thermodynamics.Temperature.Basic
import Physlib.Thermodynamics.Temperature.TemperatureUnits
import Physlib.Units.WithDim.Energy
import Physlib.Units.WithDim.Pressure

/- USER: The assigned source file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0479

open Dimension

/-!
# Power output of a three-leg ideal-gas heat engine

The primary pressure--volume diagram shows the clockwise cycle

`1 → 2 → 3 → 1`.

States `1` and `2` lie on the `200 kPa` horizontal line, at volumes
`200 cm³` and `600 cm³`, respectively.  State `3` has volume `600 cm³`.
The leg `1 → 2` is isobaric, `2 → 3` is isochoric, and the curved leg
`3 → 1` follows the isotherm labelled `300 K`.  The monatomic ideal-gas
engine runs at `600 rpm`.

Pressure, volume, temperature, energy, inverse-time rates, and power retain
their physical dimensions.  Real numbers below are named-unit readouts,
dimensionless coupling factors, or displayed answer values.  Work is positive
when done by the gas, and heat is positive when transferred into the gas.
-/

/-! ## Dimensionful quantities and named-unit readouts -/

/-- A nonnegative physical volume carrying dimension `L³`. -/
abbrev VolumeQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * L𝓭 * L𝓭) NNReal)

/-- Shaft rotation rate, carrying inverse-time dimension. -/
abbrev RotationRateQuantity : Type :=
  Dimensionful (WithDim T𝓭⁻¹ NNReal)

/-- Thermodynamic cycle rate, carrying inverse-time dimension. -/
abbrev CycleRateQuantity : Type :=
  Dimensionful (WithDim T𝓭⁻¹ NNReal)

/-- Mechanical power carrying dimension `M L² T⁻³`. -/
abbrev PowerQuantity : Type :=
  Dimensionful
    (WithDim
      (M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹ * T𝓭⁻¹) ℝ)

/-- Read a physical pressure in pascals. -/
def pressureInPascals (pressure : DimPressure) : ℝ :=
  (pressure UnitChoices.SI).val /
    (DimPressure.pascal UnitChoices.SI).val

/-- Read a physical pressure in the kilopascals printed on the vertical axis. -/
def pressureInKilopascals (pressure : DimPressure) : ℝ :=
  pressureInPascals pressure / 1000

/-- Read a physical volume in coherent-SI cubic metres. -/
def volumeInCubicMetres (volume : VolumeQuantity) : ℝ :=
  ((volume UnitChoices.SI).val : ℝ)

/-- Read a physical volume in the cubic centimetres printed on the horizontal axis. -/
def volumeInCubicCentimetres (volume : VolumeQuantity) : ℝ :=
  volumeInCubicMetres volume * 1000000

/-- Read signed heat, work, or internal-energy change in joules. -/
def energyInJoules (energy : DimEnergy) : ℝ :=
  (energy UnitChoices.SI).val /
    (DimEnergy.joule UnitChoices.SI).val

/-- Read an absolute temperature in kelvins from its stated storage unit. -/
def temperatureInKelvins
    (storageUnit : TemperatureUnit) (temperature : Temperature) : ℝ :=
  let unitRatio : NNReal := storageUnit / TemperatureUnit.kelvin
  temperature.toReal * (unitRatio : ℝ)

/-- Read shaft speed in revolutions per SI second. -/
def rotationRateInRevolutionsPerSecond
    (rate : RotationRateQuantity) : ℝ :=
  ((rate UnitChoices.SI).val : ℝ)

/-- Read shaft speed in revolutions per minute. -/
def rotationRateInRevolutionsPerMinute
    (rate : RotationRateQuantity) : ℝ :=
  60 * rotationRateInRevolutionsPerSecond rate

/-- Read thermodynamic cycle rate in cycles per SI second. -/
def cycleRateInHertz (rate : CycleRateQuantity) : ℝ :=
  ((rate UnitChoices.SI).val : ℝ)

/-- Read mechanical power in coherent-SI watts. -/
def powerInWatts (power : PowerQuantity) : ℝ :=
  (power UnitChoices.SI).val

/-! ## Gas, engine-cycle, and primary-figure vocabulary -/

/-- The working-substance model stated in the problem. -/
inductive GasModel where
  | monatomicIdealGas
  deriving DecidableEq, Repr

/-- The thermodynamic role played by the cyclic device. -/
inductive ThermodynamicDeviceRole where
  | heatEngine
  deriving DecidableEq, Repr

/-- The three numbered equilibrium states printed in the diagram. -/
inductive StateLabel where
  | one
  | two
  | three
  deriving DecidableEq, Fintype, Repr

/-- The three directed arrows comprising one traversal of the cycle. -/
inductive CycleLeg where
  | oneToTwo
  | twoToThree
  | threeToOne
  deriving DecidableEq, Fintype, Repr

/-- Initial state of a directed cycle leg. -/
def CycleLeg.initialState : CycleLeg → StateLabel
  | .oneToTwo => .one
  | .twoToThree => .two
  | .threeToOne => .three

/-- Final state of a directed cycle leg. -/
def CycleLeg.finalState : CycleLeg → StateLabel
  | .oneToTwo => .two
  | .twoToThree => .three
  | .threeToOne => .one

/-- Thermodynamic constraint holding along a process leg. -/
inductive ProcessKind where
  | isobaric
  | isochoric
  | isothermal
  deriving DecidableEq, Repr

/-- Geometric appearance of a process leg in the pressure--volume plane. -/
inductive PathGeometry where
  | horizontalSegment
  | verticalSegment
  | curvedSegment
  deriving DecidableEq, Repr

/-- Physical quantity assigned to a plot axis. -/
inductive AxisQuantity where
  | pressure
  | volume
  deriving DecidableEq, Repr

/-- Unit explicitly printed beside a plot axis. -/
inductive AxisUnit where
  | kilopascal
  | cubicCentimetre
  deriving DecidableEq, Repr

/-- Text and tick labels visible in the primary bitmap. -/
inductive FigureLabel where
  | pressureAxisP
  | volumeAxisV
  | originZero
  | pressure100
  | pressure200
  | volume200
  | volume400
  | volume600
  | stateOne
  | stateTwo
  | stateThree
  | isotherm300K
  deriving DecidableEq, Fintype, Repr

/-- A physical equilibrium state of the working gas. -/
structure ThermodynamicState where
  pressure : DimPressure
  volume : VolumeQuantity
  temperature : Temperature

/-!
Qualitative and labelled information transcribed from image `479.png`.
This structure records no work, power, or answer choice.
-/
structure PressureVolumeFigure where
  horizontalAxisQuantity : AxisQuantity
  verticalAxisQuantity : AxisQuantity
  horizontalAxisUnit : AxisUnit
  verticalAxisUnit : AxisUnit
  showsLabel : FigureLabel → Bool
  showsState : StateLabel → Bool
  showsDirectedLeg : CycleLeg → Bool
  directedEndpoints : CycleLeg → StateLabel × StateLabel
  pathGeometry : CycleLeg → PathGeometry
  labelledIsothermTemperature : Temperature

/-!
Independent physical observables for one closed engine cycle.  The requested
power is an independent dimensionful field; its relation to work and cycle
rate is imposed only by the general governing law below.
-/
structure IdealGasHeatEngineCycle where
  gasModel : GasModel
  deviceRole : ThermodynamicDeviceRole
  sameClosedGasSample : Bool
  quasistaticEquilibriumPath : Bool
  temperatureStorageUnit : TemperatureUnit
  stateAt : StateLabel → ThermodynamicState
  processKind : CycleLeg → ProcessKind
  workDoneByGas : CycleLeg → DimEnergy
  heatTransferredIntoGas : CycleLeg → DimEnergy
  internalEnergyChange : CycleLeg → DimEnergy
  shaftRotationRate : RotationRateQuantity
  thermodynamicCycleRate : CycleRateQuantity
  cyclesPerRevolution : ℝ
  powerOutput : PowerQuantity
  figure : PressureVolumeFigure

/-! ## Per-cycle accounting -/

/-- Net work done by the gas in one traversal of `1 → 2 → 3 → 1`. -/
def netWorkDoneByGasInJoules (setup : IdealGasHeatEngineCycle) : ℝ :=
  energyInJoules (setup.workDoneByGas .oneToTwo) +
    energyInJoules (setup.workDoneByGas .twoToThree) +
    energyInJoules (setup.workDoneByGas .threeToOne)

/-! ## Problem data, primary-image readouts, and physical laws -/

/-!
Data and idealized operating assumptions from the prose.  The shaft makes one
traversal of the displayed thermodynamic cycle per revolution; this explicit
coupling is what permits the stated `rpm` to determine a cycle frequency.
No numerical work or power occurs here.
-/
structure MatchesProblemStatement
    (setup : IdealGasHeatEngineCycle) : Prop where
  gasIsMonatomicIdealGas : setup.gasModel = .monatomicIdealGas
  deviceIsHeatEngine : setup.deviceRole = .heatEngine
  sameClosedSample : setup.sameClosedGasSample = true
  pathIsQuasistatic : setup.quasistaticEquilibriumPath = true
  temperatureUnitIsKelvin :
    setup.temperatureStorageUnit = TemperatureUnit.kelvin
  statedShaftSpeedRpm :
    rotationRateInRevolutionsPerMinute setup.shaftRotationRate = 600
  oneCyclePerRevolution : setup.cyclesPerRevolution = 1

/-!
Exact transcription of the pressure--volume bitmap.  The image gives the
three directed legs, the process geometries, the state-1 and state-2 pressure
and volume coordinates, the state-3 volume coordinate, and the `300 K`
isotherm through states `3` and `1`.  It does not give state 3 a numerical
pressure and says nothing about net work or power.
-/
structure MatchesPrimaryPressureVolumeFigure
    (setup : IdealGasHeatEngineCycle) : Prop where
  horizontalAxisIsVolume :
    setup.figure.horizontalAxisQuantity = .volume
  verticalAxisIsPressure :
    setup.figure.verticalAxisQuantity = .pressure
  horizontalAxisUsesCubicCentimetres :
    setup.figure.horizontalAxisUnit = .cubicCentimetre
  verticalAxisUsesKilopascals :
    setup.figure.verticalAxisUnit = .kilopascal
  everyPrintedLabelIsShown :
    ∀ label : FigureLabel, setup.figure.showsLabel label = true
  everyStateIsShown :
    ∀ state : StateLabel, setup.figure.showsState state = true
  everyDirectedLegIsShown :
    ∀ leg : CycleLeg, setup.figure.showsDirectedLeg leg = true
  arrowsFollowCycleOrder : ∀ leg : CycleLeg,
    setup.figure.directedEndpoints leg =
      (leg.initialState, leg.finalState)
  oneToTwoIsHorizontal :
    setup.figure.pathGeometry .oneToTwo = .horizontalSegment
  twoToThreeIsVertical :
    setup.figure.pathGeometry .twoToThree = .verticalSegment
  threeToOneIsCurved :
    setup.figure.pathGeometry .threeToOne = .curvedSegment
  oneToTwoIsIsobaric : setup.processKind .oneToTwo = .isobaric
  twoToThreeIsIsochoric : setup.processKind .twoToThree = .isochoric
  threeToOneIsIsothermal : setup.processKind .threeToOne = .isothermal
  stateOnePressureKilopascals :
    pressureInKilopascals (setup.stateAt .one).pressure = 200
  stateOneVolumeCubicCentimetres :
    volumeInCubicCentimetres (setup.stateAt .one).volume = 200
  stateTwoPressureKilopascals :
    pressureInKilopascals (setup.stateAt .two).pressure = 200
  stateTwoVolumeCubicCentimetres :
    volumeInCubicCentimetres (setup.stateAt .two).volume = 600
  stateThreeVolumeCubicCentimetres :
    volumeInCubicCentimetres (setup.stateAt .three).volume = 600
  labelledIsothermIs300Kelvin :
    temperatureInKelvins setup.temperatureStorageUnit
      setup.figure.labelledIsothermTemperature = 300
  stateOneLiesOnLabelledIsotherm :
    (setup.stateAt .one).temperature =
      setup.figure.labelledIsothermTemperature
  stateThreeLiesOnLabelledIsotherm :
    (setup.stateAt .three).temperature =
      setup.figure.labelledIsothermTemperature
  stateThreeIsDrawnBelowStateTwo :
    pressureInKilopascals (setup.stateAt .three).pressure <
      pressureInKilopascals (setup.stateAt .two).pressure

/-- Positivity and nondegeneracy conditions for the physical branch. -/
structure HasPhysicalThermodynamicParameters
    (setup : IdealGasHeatEngineCycle) : Prop where
  pressurePositive : ∀ state,
    0 < pressureInPascals (setup.stateAt state).pressure
  volumePositive : ∀ state,
    0 < volumeInCubicMetres (setup.stateAt state).volume
  temperaturePositive : ∀ state,
    0 < temperatureInKelvins setup.temperatureStorageUnit
      (setup.stateAt state).temperature
  shaftRatePositive :
    0 < rotationRateInRevolutionsPerSecond setup.shaftRotationRate
  cycleRatePositive :
    0 < cycleRateInHertz setup.thermodynamicCycleRate
  cyclesPerRevolutionPositive : 0 < setup.cyclesPerRevolution
  outputPowerNonnegative : 0 ≤ powerInWatts setup.powerOutput

/-!
Macroscopic governing laws for a fixed sample of monatomic ideal gas:

* the cross-multiplied ideal-gas law expresses `pV/T = constant`;
* monatomic internal energy is `(3/2) pV`, up to a state-independent datum;
* the first law is `Q_into = ΔU + W_by`;
* isobaric, isochoric, and reversible-isothermal boundary-work formulas hold;
* cycle rate is shaft rate times cycles per revolution;
* average output power is net work per cycle times cycles per second.

These are general laws.  No field fixes state 3's pressure, a numerical leg
work, net work, output power, or an answer choice.
-/
structure SatisfiesMonatomicIdealGasEngineLaws
    (setup : IdealGasHeatEngineCycle) : Prop where
  fixedSampleIdealGasLaw : ∀ first second : StateLabel,
    pressureInPascals (setup.stateAt first).pressure *
          volumeInCubicMetres (setup.stateAt first).volume *
          temperatureInKelvins setup.temperatureStorageUnit
            (setup.stateAt second).temperature =
      pressureInPascals (setup.stateAt second).pressure *
          volumeInCubicMetres (setup.stateAt second).volume *
          temperatureInKelvins setup.temperatureStorageUnit
            (setup.stateAt first).temperature
  monatomicInternalEnergyLaw : ∀ leg : CycleLeg,
    energyInJoules (setup.internalEnergyChange leg) =
      (3 / 2 : ℝ) *
        (pressureInPascals
              (setup.stateAt leg.finalState).pressure *
              volumeInCubicMetres
                (setup.stateAt leg.finalState).volume -
          pressureInPascals
              (setup.stateAt leg.initialState).pressure *
              volumeInCubicMetres
                (setup.stateAt leg.initialState).volume)
  firstLaw : ∀ leg : CycleLeg,
    energyInJoules (setup.heatTransferredIntoGas leg) =
      energyInJoules (setup.internalEnergyChange leg) +
        energyInJoules (setup.workDoneByGas leg)
  isobaricPressureAndWorkLaw : ∀ leg : CycleLeg,
    setup.processKind leg = .isobaric →
      (setup.stateAt leg.finalState).pressure =
          (setup.stateAt leg.initialState).pressure ∧
      energyInJoules (setup.workDoneByGas leg) =
        pressureInPascals
            (setup.stateAt leg.initialState).pressure *
          (volumeInCubicMetres
                (setup.stateAt leg.finalState).volume -
            volumeInCubicMetres
                (setup.stateAt leg.initialState).volume)
  isochoricVolumeAndWorkLaw : ∀ leg : CycleLeg,
    setup.processKind leg = .isochoric →
      (setup.stateAt leg.finalState).volume =
          (setup.stateAt leg.initialState).volume ∧
      energyInJoules (setup.workDoneByGas leg) = 0
  isothermalTemperatureAndWorkLaw : ∀ leg : CycleLeg,
    setup.processKind leg = .isothermal →
      (setup.stateAt leg.finalState).temperature =
          (setup.stateAt leg.initialState).temperature ∧
      energyInJoules (setup.workDoneByGas leg) =
        pressureInPascals
            (setup.stateAt leg.initialState).pressure *
          volumeInCubicMetres
            (setup.stateAt leg.initialState).volume *
          Real.log
            (volumeInCubicMetres
                  (setup.stateAt leg.finalState).volume /
              volumeInCubicMetres
                  (setup.stateAt leg.initialState).volume)
  cycleRateFromShaftSpeed :
    cycleRateInHertz setup.thermodynamicCycleRate =
      rotationRateInRevolutionsPerSecond setup.shaftRotationRate *
        setup.cyclesPerRevolution
  outputPowerLaw :
    powerInWatts setup.powerOutput =
      netWorkDoneByGasInJoules setup *
        cycleRateInHertz setup.thermodynamicCycleRate

/-! ## Derived cycle quantities and displayed answer -/

/-!
The ideal-gas and process laws determine the previously unread pressure and
the cycle's work and frequency.  In particular, the three leg works are
`80 J`, `0 J`, and `-40 log 3 J`, giving
`40 (2 - log 3) J` per cycle at `10 cycles/s`.
-/
lemma derivedCycleReadouts
    (setup : IdealGasHeatEngineCycle)
    (_problem : MatchesProblemStatement setup)
    (_figure : MatchesPrimaryPressureVolumeFigure setup)
    (_physical : HasPhysicalThermodynamicParameters setup)
    (_laws : SatisfiesMonatomicIdealGasEngineLaws setup) :
    pressureInKilopascals (setup.stateAt .three).pressure =
        (200 / 3 : ℝ) ∧
      energyInJoules (setup.workDoneByGas .oneToTwo) = 80 ∧
      energyInJoules (setup.workDoneByGas .twoToThree) = 0 ∧
      energyInJoules (setup.workDoneByGas .threeToOne) =
        -(40 * Real.log 3) ∧
      netWorkDoneByGasInJoules setup =
        40 * (2 - Real.log 3) ∧
      cycleRateInHertz setup.thermodynamicCycleRate = 10 := by
  have hPressureOne :
      pressureInPascals (setup.stateAt .one).pressure = 200000 := by
    have h := _figure.stateOnePressureKilopascals
    change
      pressureInPascals (setup.stateAt .one).pressure / 1000 = 200 at h
    linarith
  have hVolumeOne :
      volumeInCubicMetres (setup.stateAt .one).volume = (1 / 5000 : ℝ) := by
    have h := _figure.stateOneVolumeCubicCentimetres
    change
      volumeInCubicMetres (setup.stateAt .one).volume * 1000000 = 200 at h
    norm_num at h ⊢
    linarith
  have hVolumeTwo :
      volumeInCubicMetres (setup.stateAt .two).volume = (3 / 5000 : ℝ) := by
    have h := _figure.stateTwoVolumeCubicCentimetres
    change
      volumeInCubicMetres (setup.stateAt .two).volume * 1000000 = 600 at h
    norm_num at h ⊢
    linarith
  have hVolumeThree :
      volumeInCubicMetres (setup.stateAt .three).volume = (3 / 5000 : ℝ) := by
    have h := _figure.stateThreeVolumeCubicCentimetres
    change
      volumeInCubicMetres (setup.stateAt .three).volume * 1000000 = 600 at h
    norm_num at h ⊢
    linarith
  have hTemperatureOneEqThree :
      (setup.stateAt .one).temperature =
        (setup.stateAt .three).temperature :=
    _figure.stateOneLiesOnLabelledIsotherm.trans
      _figure.stateThreeLiesOnLabelledIsotherm.symm
  have hIdealGas := _laws.fixedSampleIdealGasLaw .one .three
  rw [hTemperatureOneEqThree] at hIdealGas
  have hPressureVolumeThree :
      pressureInPascals (setup.stateAt .three).pressure *
          volumeInCubicMetres (setup.stateAt .three).volume = 40 := by
    have hTemperaturePositive := _physical.temperaturePositive .three
    rw [hPressureOne, hVolumeOne] at hIdealGas
    nlinarith
  have hPressureThree :
      pressureInPascals (setup.stateAt .three).pressure =
        (200000 / 3 : ℝ) := by
    rw [hVolumeThree] at hPressureVolumeThree
    nlinarith
  have hPressureThreeKPa :
      pressureInKilopascals (setup.stateAt .three).pressure =
        (200 / 3 : ℝ) := by
    change
      pressureInPascals (setup.stateAt .three).pressure / 1000 =
        (200 / 3 : ℝ)
    rw [hPressureThree]
    norm_num
  have hWorkOneToTwo :=
    (_laws.isobaricPressureAndWorkLaw .oneToTwo
      _figure.oneToTwoIsIsobaric).2
  dsimp [CycleLeg.initialState, CycleLeg.finalState] at hWorkOneToTwo
  rw [hPressureOne, hVolumeTwo, hVolumeOne] at hWorkOneToTwo
  norm_num at hWorkOneToTwo
  have hWorkTwoToThree :=
    (_laws.isochoricVolumeAndWorkLaw .twoToThree
      _figure.twoToThreeIsIsochoric).2
  have hWorkThreeToOne :=
    (_laws.isothermalTemperatureAndWorkLaw .threeToOne
      _figure.threeToOneIsIsothermal).2
  dsimp [CycleLeg.initialState, CycleLeg.finalState] at hWorkThreeToOne
  rw [hPressureVolumeThree, hVolumeOne, hVolumeThree] at hWorkThreeToOne
  norm_num at hWorkThreeToOne
  rw [one_div, Real.log_inv] at hWorkThreeToOne
  have hWorkThreeToOne' :
      energyInJoules (setup.workDoneByGas .threeToOne) =
        -(40 * Real.log 3) := by
    rw [hWorkThreeToOne]
    ring
  have hNetWork :
      netWorkDoneByGasInJoules setup = 40 * (2 - Real.log 3) := by
    rw [netWorkDoneByGasInJoules, hWorkOneToTwo, hWorkTwoToThree,
      hWorkThreeToOne']
    ring
  have hRotationRate :
      rotationRateInRevolutionsPerSecond setup.shaftRotationRate = 10 := by
    have h := _problem.statedShaftSpeedRpm
    change
      60 * rotationRateInRevolutionsPerSecond setup.shaftRotationRate =
        600 at h
    linarith
  have hCycleRate :
      cycleRateInHertz setup.thermodynamicCycleRate = 10 := by
    rw [_laws.cycleRateFromShaftSpeed, hRotationRate,
      _problem.oneCyclePerRevolution]
    norm_num
  exact
    ⟨hPressureThreeKPa, hWorkOneToTwo, hWorkTwoToThree,
      hWorkThreeToOne', hNetWork, hCycleRate⟩

/-- Labels of the four multiple-choice answers. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Power in watts printed beside each answer choice. -/
def displayedPowerInWatts : AnswerChoice → ℝ
  | .A => 320
  | .B => 340
  | .C => 360
  | .D => 380

/-- Answer label recorded by the source dataset. -/
def recordedAnswerChoice : AnswerChoice := .C

/-- The physical output lies in the nearest-20-watt bin of a displayed choice. -/
def RoundsToDisplayedPower
    (setup : IdealGasHeatEngineCycle) (choice : AnswerChoice) : Prop :=
  |powerInWatts setup.powerOutput - displayedPowerInWatts choice| < 10

/-- One displayed power is strictly closer than every competing choice. -/
def IsUniqueClosestDisplayedPower
    (setup : IdealGasHeatEngineCycle) (choice : AnswerChoice) : Prop :=
  ∀ other, other ≠ choice →
    |powerInWatts setup.powerOutput - displayedPowerInWatts choice| <
      |powerInWatts setup.powerOutput - displayedPowerInWatts other|

/-!
The exact ideal-model power is

`400 (2 - log 3) W ≈ 360.56 W`.

Thus the physical value is not asserted to equal `360 W` exactly; it rounds
to the displayed 20-watt choice C and is uniquely closest to that choice.

This formalizes blueprint label `thm:physics:phyx_mini_0479:target`.
-/
theorem problem_phyx_mini_0479
    (setup : IdealGasHeatEngineCycle)
    (_problem : MatchesProblemStatement setup)
    (_figure : MatchesPrimaryPressureVolumeFigure setup)
    (_physical : HasPhysicalThermodynamicParameters setup)
    (_laws : SatisfiesMonatomicIdealGasEngineLaws setup) :
    powerInWatts setup.powerOutput =
        400 * (2 - Real.log 3) ∧
      RoundsToDisplayedPower setup recordedAnswerChoice ∧
      IsUniqueClosestDisplayedPower setup recordedAnswerChoice := by
  have hDerived :=
    derivedCycleReadouts setup _problem _figure _physical _laws
  have hNetWork := hDerived.2.2.2.2.1
  have hCycleRate := hDerived.2.2.2.2.2
  have hPower :
      powerInWatts setup.powerOutput = 400 * (2 - Real.log 3) := by
    rw [_laws.outputPowerLaw, hNetWork, hCycleRate]
    ring
  have hLogUpper : Real.log 3 < (11 / 10 : ℝ) := by
    rw [Real.log_lt_iff_lt_exp (by norm_num)]
    calc
      (3 : ℝ) <
          ∑ m ∈ Finset.range 6, (11 / 10 : ℝ) ^ m / m.factorial := by
        norm_num [Finset.sum_range_succ, Nat.factorial]
      _ ≤ Real.exp (11 / 10 : ℝ) :=
        Real.sum_le_exp_of_nonneg (by norm_num) 6
  have hExpOneUpper : Real.exp 1 < (27183 / 10000 : ℝ) := by
    have hBound :=
      Real.exp_bound' (x := (1 : ℝ)) (by norm_num) (by norm_num)
        (n := 10) (by norm_num)
    calc
      Real.exp 1 ≤
          (∑ m ∈ Finset.range 10, (1 : ℝ) ^ m / m.factorial) +
            (1 : ℝ) ^ 10 * (10 + 1) / (Nat.factorial 10 * 10) := hBound
      _ < 27183 / 10000 := by
        norm_num [Finset.sum_range_succ, Nat.factorial]
  have hExpSmallUpper :
      Real.exp (39 / 400 : ℝ) < (11025 / 10000 : ℝ) := by
    have hBound :=
      Real.exp_bound' (x := (39 / 400 : ℝ)) (by norm_num)
        (by norm_num) (n := 6) (by norm_num)
    calc
      Real.exp (39 / 400 : ℝ) ≤
          (∑ m ∈ Finset.range 6, (39 / 400 : ℝ) ^ m / m.factorial) +
            (39 / 400 : ℝ) ^ 6 * (6 + 1) /
              (Nat.factorial 6 * 6) := hBound
      _ < 11025 / 10000 := by
        norm_num [Finset.sum_range_succ, Nat.factorial]
  have hLogLower : (439 / 400 : ℝ) < Real.log 3 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num)]
    rw [show (439 / 400 : ℝ) = 1 + 39 / 400 by norm_num, Real.exp_add]
    nlinarith [Real.exp_pos 1, Real.exp_pos (39 / 400 : ℝ)]
  have hPowerLower : 360 < powerInWatts setup.powerOutput := by
    rw [hPower]
    nlinarith
  have hPowerUpper : powerInWatts setup.powerOutput < 361 := by
    rw [hPower]
    nlinarith
  have hRounds :
      RoundsToDisplayedPower setup recordedAnswerChoice := by
    unfold RoundsToDisplayedPower
    simp only [recordedAnswerChoice, displayedPowerInWatts]
    rw [abs_of_pos (by linarith)]
    linarith
  have hClosest :
      IsUniqueClosestDisplayedPower setup recordedAnswerChoice := by
    unfold IsUniqueClosestDisplayedPower
    intro other hOther
    cases other with
    | A =>
        simp only [recordedAnswerChoice, displayedPowerInWatts]
        rw [abs_of_pos (by linarith), abs_of_pos (by linarith)]
        linarith
    | B =>
        simp only [recordedAnswerChoice, displayedPowerInWatts]
        rw [abs_of_pos (by linarith), abs_of_pos (by linarith)]
        linarith
    | C => exact (hOther rfl).elim
    | D =>
        simp only [recordedAnswerChoice, displayedPowerInWatts]
        rw [abs_of_pos (by linarith), abs_of_neg (by linarith)]
        linarith
  exact ⟨hPower, hRounds, hClosest⟩

end PhyXMiniProblems.ProblemPhyXMini0479
