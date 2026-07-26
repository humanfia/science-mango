import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Physlib.Thermodynamics.Temperature.Basic
import Physlib.Units.WithDim.Energy
import Physlib.Units.WithDim.Pressure

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0432

open Dimension

/-!
# Thermal efficiency of a three-leg helium heat-engine cycle

The primary `p`--`V` raster shows the directed cycle `1 → 2 → 3 → 1`.
State `1` is at `(1000 cm³, 1 atm)`, state `2` is at
`(1000 cm³, 5 atm)`, and state `3` is at `(V_max, 1 atm)`.  The first leg is
vertical and isochoric, the curved second leg is explicitly labelled
“Isotherm”, and the horizontal return leg is isobaric.  The working substance
is `120 mg` of helium.

Mass, pressure, volume, heat, work, and internal energy are represented by
unit-independent Physlib quantities.  Real numbers occur only as explicitly
unit-labelled readouts, amount-of-substance and gas-constant readouts, and
dimensionless efficiencies.

Assumption/target split:

* `MatchesProblemScenario` records the helium sample, its mass, the standard
  monatomic ideal-gas model, and the three process kinds;
* `MatchesPrimaryPressureVolumeFigure` records only literal image evidence;
* `HasPhysicalHeatEngineParameters` selects the positive heat-engine branch;
* `SatisfiesIdealMonatomicHeliumCycleLaws` states the ideal-gas, caloric,
  first-law, boundary-work, cycle-accounting, and efficiency laws; and
* the maximum volume, exact efficiency, and closest displayed answer are
  conclusions below, never assumptions or definitions of the physical setup.
-/

/-! ## Dimensionful quantities and calibrated readouts -/

/-- A nonnegative physical mass carrying Physlib's mass dimension. -/
abbrev MassQuantity : Type :=
  Dimensionful (WithDim M𝓭 NNReal)

/-- A nonnegative physical gas volume carrying dimension `length³`. -/
abbrev VolumeQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * L𝓭 * L𝓭) NNReal)

/-- A signed physical pressure.  Positivity is imposed on physical states. -/
abbrev PressureQuantity : Type := DimPressure

/-- A signed heat, work, or internal-energy quantity. -/
abbrev EnergyQuantity : Type := DimEnergy

/-- Coherent-SI mass readout, in kilograms. -/
def massInKilograms (mass : MassQuantity) : ℝ :=
  ((mass UnitChoices.SI).val : ℝ)

/-- Milligram readout used in the problem statement. -/
def massInMilligrams (mass : MassQuantity) : ℝ :=
  10 ^ 6 * massInKilograms mass

/-- Coherent-SI pressure readout, in pascals. -/
def pressureInPascals (pressure : PressureQuantity) : ℝ :=
  (pressure UnitChoices.SI).val

/-- Pressure as a dimensionless multiple of one standard atmosphere. -/
def pressureInAtmospheres (pressure : PressureQuantity) : ℝ :=
  pressureInPascals pressure /
    pressureInPascals DimPressure.standardAtmosphere

/-- Coherent-SI volume readout, in cubic metres. -/
def volumeInCubicMeters (volume : VolumeQuantity) : ℝ :=
  ((volume UnitChoices.SI).val : ℝ)

/-- Cubic-centimetre readout used on the horizontal figure axis. -/
def volumeInCubicCentimeters (volume : VolumeQuantity) : ℝ :=
  10 ^ 6 * volumeInCubicMeters volume

/-- Coherent-SI energy readout, in joules. -/
def energyInJoules (energy : EnergyQuantity) : ℝ :=
  (energy UnitChoices.SI).val

/-- Kelvin readout of Physlib's nonnegative absolute temperature. -/
def temperatureInKelvins (temperature : Temperature) : ℝ :=
  temperature.toReal

/-! ## Gas, state, process, and primary-figure vocabulary -/

/-- The working-gas species stated in the problem. -/
inductive GasSpecies where
  | helium
  deriving DecidableEq, Repr

/-- Molecular model needed for the textbook heat-capacity law. -/
inductive GasModel where
  | monatomicIdealGas
  deriving DecidableEq, Repr

/-- The physical sample used as the engine's working substance. -/
structure WorkingSample where
  species : GasSpecies
  model : GasModel
  mass : MassQuantity

/-- The three numbered equilibrium states printed in the raster. -/
inductive StateLabel where
  | one
  | two
  | three
  deriving DecidableEq, Fintype, Repr

/-- The three directed legs, listed in the arrow order shown in the raster. -/
inductive CycleLeg where
  | oneToTwo
  | twoToThree
  | threeToOne
  deriving DecidableEq, Fintype, Repr

/-- Initial state of each directed cycle leg. -/
def CycleLeg.initialState : CycleLeg → StateLabel
  | .oneToTwo => .one
  | .twoToThree => .two
  | .threeToOne => .three

/-- Final state of each directed cycle leg. -/
def CycleLeg.finalState : CycleLeg → StateLabel
  | .oneToTwo => .two
  | .twoToThree => .three
  | .threeToOne => .one

/-- Thermodynamic classification of each process in the cycle. -/
inductive ProcessKind where
  | isochoric
  | isothermal
  | isobaric
  deriving DecidableEq, Repr

/-- Clockwise orientation of the engine cycle, or its reverse. -/
inductive CycleOrientation where
  | clockwise
  | counterclockwise
  deriving DecidableEq, Repr

/-- Pressure, volume, temperature, and internal energy at one state. -/
structure ThermodynamicState where
  pressure : PressureQuantity
  volume : VolumeQuantity
  temperature : Temperature
  internalEnergy : EnergyQuantity

/-- The two axes of the supplied pressure--volume diagram. -/
inductive FigureAxis where
  | horizontal
  | vertical
  deriving DecidableEq, Repr

/-- Physical quantity assigned to a figure axis. -/
inductive AxisQuantity where
  | volume
  | pressure
  deriving DecidableEq, Repr

/-- Unit text printed beside a figure axis. -/
inductive AxisDisplayUnit where
  | cubicCentimeters
  | atmospheres
  deriving DecidableEq, Repr

/-- Mathematical symbol printed beside a figure axis. -/
inductive AxisSymbol where
  | volumeSymbol
  | pressureSymbol
  deriving DecidableEq, Repr

/-- Geometric appearance of each directed path in the raster. -/
inductive PathShape where
  | vertical
  | curvedDownwardRight
  | horizontal
  deriving DecidableEq, Repr

/-- Direction in which the visible arrowhead points. -/
inductive ArrowDirection where
  | up
  | downAndRight
  | left
  deriving DecidableEq, Repr

/-- Text annotation attached to the curved path. -/
inductive FigureAnnotation where
  | isotherm
  deriving DecidableEq, Repr

/-- Literal labels, ticks, paths, and arrowheads in image `432.png`. -/
structure PressureVolumeFigure where
  axisQuantity : FigureAxis → AxisQuantity
  axisDisplayUnit : FigureAxis → AxisDisplayUnit
  axisSymbol : FigureAxis → AxisSymbol
  pressureTickVisible : ℝ → Bool
  volumeTickVisible : ℝ → Bool
  stateLabelVisible : StateLabel → Bool
  maximumVolumeLabelVisible : Bool
  pathStart : CycleLeg → StateLabel
  pathFinish : CycleLeg → StateLabel
  pathShape : CycleLeg → PathShape
  arrowVisible : CycleLeg → Bool
  arrowDirection : CycleLeg → ArrowDirection
  annotatedLeg : CycleLeg
  annotation : FigureAnnotation

/-!
Independent observables of the physical cycle.  Heat is positive into the
gas and work is positive when done by the gas.  The maximum volume and all
energy transfers are fields of the physical setup, not definitions made from
the requested answer.
-/
structure HeliumHeatEngineCycle where
  sample : WorkingSample
  amountOfSubstanceMoles : ℝ
  molarGasConstantJoulesPerMoleKelvin : ℝ
  stateAt : StateLabel → ThermodynamicState
  processKind : CycleLeg → ProcessKind
  orientation : CycleOrientation
  maximumVolume : VolumeQuantity
  workDoneByGas : CycleLeg → EnergyQuantity
  heatTransferredIntoGas : CycleLeg → EnergyQuantity
  netWorkDoneByGas : EnergyQuantity
  heatInputPerCycle : EnergyQuantity
  thermalEfficiency : ℝ
  figure : PressureVolumeFigure

/-! ## Scenario and primary-figure assumptions -/

/-- Problem prose together with the standard ideal-monatomic helium model. -/
structure MatchesProblemScenario (setup : HeliumHeatEngineCycle) : Prop where
  workingGasIsHelium : setup.sample.species = .helium
  workingGasUsesMonatomicIdealModel :
    setup.sample.model = .monatomicIdealGas
  workingSampleMassIsOneHundredTwentyMilligrams :
    massInMilligrams setup.sample.mass = 120
  firstLegIsIsochoric : setup.processKind .oneToTwo = .isochoric
  secondLegIsIsothermal : setup.processKind .twoToThree = .isothermal
  thirdLegIsIsobaric : setup.processKind .threeToOne = .isobaric
  cycleRunsClockwise : setup.orientation = .clockwise

/-!
Exact transcription of the primary bitmap.  The `V_max` field is identified
with state `3`'s volume, but receives no numerical value in this premise.
-/
structure MatchesPrimaryPressureVolumeFigure
    (setup : HeliumHeatEngineCycle) : Prop where
  horizontalAxisIsVolume :
    setup.figure.axisQuantity .horizontal = .volume
  verticalAxisIsPressure :
    setup.figure.axisQuantity .vertical = .pressure
  horizontalUnitIsCubicCentimeters :
    setup.figure.axisDisplayUnit .horizontal = .cubicCentimeters
  verticalUnitIsAtmospheres :
    setup.figure.axisDisplayUnit .vertical = .atmospheres
  horizontalSymbolIsV :
    setup.figure.axisSymbol .horizontal = .volumeSymbol
  verticalSymbolIsP :
    setup.figure.axisSymbol .vertical = .pressureSymbol
  displayedPressureTicks :
    setup.figure.pressureTickVisible 0 = true ∧
      setup.figure.pressureTickVisible 1 = true ∧
      setup.figure.pressureTickVisible 2 = true ∧
      setup.figure.pressureTickVisible 3 = true ∧
      setup.figure.pressureTickVisible 4 = true ∧
      setup.figure.pressureTickVisible 5 = true
  displayedVolumeTicks :
    setup.figure.volumeTickVisible 0 = true ∧
      setup.figure.volumeTickVisible 1000 = true
  everyStateLabelIsVisible :
    ∀ state, setup.figure.stateLabelVisible state = true
  maximumVolumeLabelIsVisible :
    setup.figure.maximumVolumeLabelVisible = true
  stateOnePressureAtmospheres :
    pressureInAtmospheres (setup.stateAt .one).pressure = 1
  stateOneVolumeCubicCentimeters :
    volumeInCubicCentimeters (setup.stateAt .one).volume = 1000
  stateTwoPressureAtmospheres :
    pressureInAtmospheres (setup.stateAt .two).pressure = 5
  stateTwoVolumeCubicCentimeters :
    volumeInCubicCentimeters (setup.stateAt .two).volume = 1000
  stateThreePressureAtmospheres :
    pressureInAtmospheres (setup.stateAt .three).pressure = 1
  stateThreeVolumeIsMaximum :
    (setup.stateAt .three).volume = setup.maximumVolume
  displayedArrowEndpoints : ∀ leg,
    setup.figure.pathStart leg = leg.initialState ∧
      setup.figure.pathFinish leg = leg.finalState
  everyArrowIsVisible : ∀ leg, setup.figure.arrowVisible leg = true
  firstPathIsVertical :
    setup.figure.pathShape .oneToTwo = .vertical
  secondPathCurvesDownAndRight :
    setup.figure.pathShape .twoToThree = .curvedDownwardRight
  thirdPathIsHorizontal :
    setup.figure.pathShape .threeToOne = .horizontal
  firstArrowPointsUp :
    setup.figure.arrowDirection .oneToTwo = .up
  secondArrowPointsDownAndRight :
    setup.figure.arrowDirection .twoToThree = .downAndRight
  thirdArrowPointsLeft :
    setup.figure.arrowDirection .threeToOne = .left
  isothermAnnotationIsOnSecondLeg :
    setup.figure.annotatedLeg = .twoToThree
  annotationReadsIsotherm : setup.figure.annotation = .isotherm

/-! ## Physical branch and governing thermodynamics -/

/-- Positivity and heat-flow conditions selecting a functioning heat engine. -/
structure HasPhysicalHeatEngineParameters
    (setup : HeliumHeatEngineCycle) : Prop where
  sampleMassPositive : 0 < massInKilograms setup.sample.mass
  amountOfSubstancePositive : 0 < setup.amountOfSubstanceMoles
  molarGasConstantPositive :
    0 < setup.molarGasConstantJoulesPerMoleKelvin
  statePressurePositive : ∀ state,
    0 < pressureInPascals (setup.stateAt state).pressure
  stateVolumePositive : ∀ state,
    0 < volumeInCubicMeters (setup.stateAt state).volume
  stateTemperaturePositive : ∀ state,
    0 < temperatureInKelvins (setup.stateAt state).temperature
  heatInputPositive : 0 < energyInJoules setup.heatInputPerCycle
  heatEntersOnFirstLeg :
    0 < energyInJoules (setup.heatTransferredIntoGas .oneToTwo)
  heatEntersOnSecondLeg :
    0 < energyInJoules (setup.heatTransferredIntoGas .twoToThree)
  heatLeavesOnThirdLeg :
    energyInJoules (setup.heatTransferredIntoGas .threeToOne) < 0

/-!
General governing laws for the fixed sample of ideal monatomic helium:

* `pV = nRT` and `U = (3/2)nRT` at every equilibrium state;
* the first law `ΔU = Q - W_by` on each directed leg;
* zero isochoric work, logarithmic isothermal work, and `p ΔV`
  isobaric work;
* net-work and positive-heat bookkeeping over the closed cycle; and
* the definition `η = W_net / Q_in` when the heat input is nonzero.

No field contains `V_max = 5000 cm³`, the exact efficiency formula, `0.290`,
or answer label D.
-/
structure SatisfiesIdealMonatomicHeliumCycleLaws
    (setup : HeliumHeatEngineCycle) : Prop where
  idealGasLaw : ∀ state,
    pressureInPascals (setup.stateAt state).pressure *
        volumeInCubicMeters (setup.stateAt state).volume =
      setup.amountOfSubstanceMoles *
        setup.molarGasConstantJoulesPerMoleKelvin *
          temperatureInKelvins (setup.stateAt state).temperature
  monatomicInternalEnergy : ∀ state,
    energyInJoules (setup.stateAt state).internalEnergy =
      (3 / 2 : ℝ) * setup.amountOfSubstanceMoles *
        setup.molarGasConstantJoulesPerMoleKelvin *
          temperatureInKelvins (setup.stateAt state).temperature
  firstLawOnEveryLeg : ∀ leg,
    energyInJoules (setup.stateAt leg.finalState).internalEnergy -
        energyInJoules (setup.stateAt leg.initialState).internalEnergy =
      energyInJoules (setup.heatTransferredIntoGas leg) -
        energyInJoules (setup.workDoneByGas leg)
  isochoricFirstLeg :
    (setup.stateAt .one).volume = (setup.stateAt .two).volume
  isothermalSecondLeg :
    (setup.stateAt .two).temperature = (setup.stateAt .three).temperature
  isobaricThirdLeg :
    (setup.stateAt .three).pressure = (setup.stateAt .one).pressure
  isochoricFirstLegWork :
    energyInJoules (setup.workDoneByGas .oneToTwo) = 0
  isothermalSecondLegWork :
    energyInJoules (setup.workDoneByGas .twoToThree) =
      setup.amountOfSubstanceMoles *
        setup.molarGasConstantJoulesPerMoleKelvin *
          temperatureInKelvins (setup.stateAt .two).temperature *
            Real.log
              (volumeInCubicMeters (setup.stateAt .three).volume /
                volumeInCubicMeters (setup.stateAt .two).volume)
  isobaricThirdLegWork :
    energyInJoules (setup.workDoneByGas .threeToOne) =
      pressureInPascals (setup.stateAt .one).pressure *
        (volumeInCubicMeters (setup.stateAt .one).volume -
          volumeInCubicMeters (setup.stateAt .three).volume)
  netWorkAccounting :
    energyInJoules setup.netWorkDoneByGas =
      energyInJoules (setup.workDoneByGas .oneToTwo) +
        energyInJoules (setup.workDoneByGas .twoToThree) +
          energyInJoules (setup.workDoneByGas .threeToOne)
  heatInputAccounting :
    energyInJoules setup.heatInputPerCycle =
      max (energyInJoules (setup.heatTransferredIntoGas .oneToTwo)) 0 +
        max (energyInJoules (setup.heatTransferredIntoGas .twoToThree)) 0 +
          max (energyInJoules (setup.heatTransferredIntoGas .threeToOne)) 0
  efficiencyLaw :
    energyInJoules setup.heatInputPerCycle ≠ 0 →
      setup.thermalEfficiency =
        energyInJoules setup.netWorkDoneByGas /
          energyInJoules setup.heatInputPerCycle

/-! ## Derived volume, energy accounting, and displayed answer -/

/-- The `pV` energy scale at state `1`, expressed in joules. -/
def basePressureVolumeScaleInJoules
    (setup : HeliumHeatEngineCycle) : ℝ :=
  pressureInPascals (setup.stateAt .one).pressure *
    volumeInCubicMeters (setup.stateAt .one).volume

/-!
The isotherm obeys `p₂V₂ = p₃V₃`; the displayed pressure ratio is `5 : 1`
and `V₂ = 1000 cm³`, so the previously unnumbered `V_max` is derived as
`5000 cm³`.
-/
lemma maximumVolumeInCubicCentimeters_eq_fiveThousand
    (setup : HeliumHeatEngineCycle)
    (_scenario : MatchesProblemScenario setup)
    (_figure : MatchesPrimaryPressureVolumeFigure setup)
    (_physical : HasPhysicalHeatEngineParameters setup)
    (_laws : SatisfiesIdealMonatomicHeliumCycleLaws setup) :
    volumeInCubicCentimeters setup.maximumVolume = 5000 := by
  have hStandardAtmosphere :
      pressureInPascals DimPressure.standardAtmosphere = 101325 := by
    norm_num [pressureInPascals, DimPressure.standardAtmosphere,
      CarriesDimension.toDimensionful_apply_apply]
  have hPressureTwo :
      pressureInPascals (setup.stateAt .two).pressure = 506625 := by
    have h := _figure.stateTwoPressureAtmospheres
    rw [pressureInAtmospheres, hStandardAtmosphere] at h
    change pressureInPascals (setup.stateAt .two).pressure / 101325 = 5 at h
    calc
      pressureInPascals (setup.stateAt .two).pressure = 5 * 101325 :=
        (div_eq_iff (by norm_num : (101325 : ℝ) ≠ 0)).mp h
      _ = 506625 := by norm_num
  have hPressureThree :
      pressureInPascals (setup.stateAt .three).pressure = 101325 := by
    have h := _figure.stateThreePressureAtmospheres
    rw [pressureInAtmospheres, hStandardAtmosphere] at h
    change pressureInPascals (setup.stateAt .three).pressure / 101325 = 1 at h
    calc
      pressureInPascals (setup.stateAt .three).pressure = 1 * 101325 :=
        (div_eq_iff (by norm_num : (101325 : ℝ) ≠ 0)).mp h
      _ = 101325 := by norm_num
  have hVolumeTwo :
      volumeInCubicMeters (setup.stateAt .two).volume = 1 / 1000 := by
    have h := _figure.stateTwoVolumeCubicCentimeters
    norm_num [volumeInCubicCentimeters] at h ⊢
    linarith
  have hTemperatureTwoThree :
      temperatureInKelvins (setup.stateAt .two).temperature =
        temperatureInKelvins (setup.stateAt .three).temperature :=
    congrArg temperatureInKelvins _laws.isothermalSecondLeg
  have hPressureVolumeTwoThree :
      pressureInPascals (setup.stateAt .two).pressure *
          volumeInCubicMeters (setup.stateAt .two).volume =
        pressureInPascals (setup.stateAt .three).pressure *
          volumeInCubicMeters (setup.stateAt .three).volume := by
    rw [_laws.idealGasLaw .two, _laws.idealGasLaw .three,
      hTemperatureTwoThree]
  have hVolumeThree :
      volumeInCubicMeters (setup.stateAt .three).volume = 1 / 200 := by
    rw [hPressureTwo, hVolumeTwo, hPressureThree] at hPressureVolumeTwoThree
    norm_num at hPressureVolumeTwoThree ⊢
    linarith
  rw [← _figure.stateThreeVolumeIsMaximum]
  norm_num [volumeInCubicCentimeters, hVolumeThree]

/-!
After deriving `V_max`, the net work is the isothermal expansion work
`5 E₀ log 5` plus the isobaric compression work `-4 E₀`.  Heat enters on
the isochoric leg by `6 E₀` and on the isothermal leg by `5 E₀ log 5`, where
`E₀ = p₁V₁`.  These are consequences of the governing laws, not premises.
-/
lemma netWork_and_heatInput_readouts
    (setup : HeliumHeatEngineCycle)
    (_scenario : MatchesProblemScenario setup)
    (_figure : MatchesPrimaryPressureVolumeFigure setup)
    (_physical : HasPhysicalHeatEngineParameters setup)
    (_laws : SatisfiesIdealMonatomicHeliumCycleLaws setup) :
    energyInJoules setup.netWorkDoneByGas =
        basePressureVolumeScaleInJoules setup *
          (5 * Real.log 5 - 4) ∧
      energyInJoules setup.heatInputPerCycle =
        basePressureVolumeScaleInJoules setup *
          (5 * Real.log 5 + 6) := by
  have hStandardAtmosphere :
      pressureInPascals DimPressure.standardAtmosphere = 101325 := by
    norm_num [pressureInPascals, DimPressure.standardAtmosphere,
      CarriesDimension.toDimensionful_apply_apply]
  have hPressureOne :
      pressureInPascals (setup.stateAt .one).pressure = 101325 := by
    have h := _figure.stateOnePressureAtmospheres
    rw [pressureInAtmospheres, hStandardAtmosphere] at h
    change pressureInPascals (setup.stateAt .one).pressure / 101325 = 1 at h
    calc
      pressureInPascals (setup.stateAt .one).pressure = 1 * 101325 :=
        (div_eq_iff (by norm_num : (101325 : ℝ) ≠ 0)).mp h
      _ = 101325 := by norm_num
  have hPressureTwo :
      pressureInPascals (setup.stateAt .two).pressure = 506625 := by
    have h := _figure.stateTwoPressureAtmospheres
    rw [pressureInAtmospheres, hStandardAtmosphere] at h
    change pressureInPascals (setup.stateAt .two).pressure / 101325 = 5 at h
    calc
      pressureInPascals (setup.stateAt .two).pressure = 5 * 101325 :=
        (div_eq_iff (by norm_num : (101325 : ℝ) ≠ 0)).mp h
      _ = 506625 := by norm_num
  have hPressureThree :
      pressureInPascals (setup.stateAt .three).pressure = 101325 := by
    have h := _figure.stateThreePressureAtmospheres
    rw [pressureInAtmospheres, hStandardAtmosphere] at h
    change pressureInPascals (setup.stateAt .three).pressure / 101325 = 1 at h
    calc
      pressureInPascals (setup.stateAt .three).pressure = 1 * 101325 :=
        (div_eq_iff (by norm_num : (101325 : ℝ) ≠ 0)).mp h
      _ = 101325 := by norm_num
  have hVolumeOne :
      volumeInCubicMeters (setup.stateAt .one).volume = 1 / 1000 := by
    have h := _figure.stateOneVolumeCubicCentimeters
    norm_num [volumeInCubicCentimeters] at h ⊢
    linarith
  have hVolumeTwo :
      volumeInCubicMeters (setup.stateAt .two).volume = 1 / 1000 := by
    have h := _figure.stateTwoVolumeCubicCentimeters
    norm_num [volumeInCubicCentimeters] at h ⊢
    linarith
  have hVolumeThreeCm :=
    maximumVolumeInCubicCentimeters_eq_fiveThousand setup _scenario
      _figure _physical _laws
  have hVolumeThree :
      volumeInCubicMeters (setup.stateAt .three).volume = 1 / 200 := by
    rw [← _figure.stateThreeVolumeIsMaximum] at hVolumeThreeCm
    norm_num [volumeInCubicCentimeters] at hVolumeThreeCm ⊢
    linarith
  have hScale :
      basePressureVolumeScaleInJoules setup = 4053 / 40 := by
    rw [basePressureVolumeScaleInJoules, hPressureOne, hVolumeOne]
    norm_num
  have hWorkOneTwo :
      energyInJoules (setup.workDoneByGas .oneToTwo) = 0 :=
    _laws.isochoricFirstLegWork
  have hWorkTwoThreeLaw := _laws.isothermalSecondLegWork
  rw [← _laws.idealGasLaw .two, hPressureTwo, hVolumeTwo,
    hVolumeThree] at hWorkTwoThreeLaw
  norm_num at hWorkTwoThreeLaw
  have hWorkTwoThree :
      energyInJoules (setup.workDoneByGas .twoToThree) =
        basePressureVolumeScaleInJoules setup * (5 * Real.log 5) := by
    rw [hWorkTwoThreeLaw, hScale]
    ring
  have hWorkThreeOneLaw := _laws.isobaricThirdLegWork
  rw [hPressureOne, hVolumeOne, hVolumeThree] at hWorkThreeOneLaw
  norm_num at hWorkThreeOneLaw
  have hWorkThreeOne :
      energyInJoules (setup.workDoneByGas .threeToOne) =
        -4 * basePressureVolumeScaleInJoules setup := by
    rw [hWorkThreeOneLaw, hScale]
    ring
  have hInternalEnergyPressureVolume (state : StateLabel) :
      energyInJoules (setup.stateAt state).internalEnergy =
        (3 / 2 : ℝ) *
          (pressureInPascals (setup.stateAt state).pressure *
            volumeInCubicMeters (setup.stateAt state).volume) := by
    calc
      energyInJoules (setup.stateAt state).internalEnergy =
          (3 / 2 : ℝ) * setup.amountOfSubstanceMoles *
            setup.molarGasConstantJoulesPerMoleKelvin *
              temperatureInKelvins (setup.stateAt state).temperature :=
        _laws.monatomicInternalEnergy state
      _ = (3 / 2 : ℝ) *
          (setup.amountOfSubstanceMoles *
            setup.molarGasConstantJoulesPerMoleKelvin *
              temperatureInKelvins (setup.stateAt state).temperature) := by
        ring
      _ = (3 / 2 : ℝ) *
          (pressureInPascals (setup.stateAt state).pressure *
            volumeInCubicMeters (setup.stateAt state).volume) := by
        rw [_laws.idealGasLaw state]
  have hInternalEnergyOne :
      energyInJoules (setup.stateAt .one).internalEnergy =
        (3 / 2 : ℝ) * basePressureVolumeScaleInJoules setup := by
    rw [hInternalEnergyPressureVolume .one]
    unfold basePressureVolumeScaleInJoules
    ring
  have hInternalEnergyTwo :
      energyInJoules (setup.stateAt .two).internalEnergy =
        (15 / 2 : ℝ) * basePressureVolumeScaleInJoules setup := by
    rw [hInternalEnergyPressureVolume .two, hPressureTwo, hVolumeTwo, hScale]
    norm_num
  have hInternalEnergyThree :
      energyInJoules (setup.stateAt .three).internalEnergy =
        (15 / 2 : ℝ) * basePressureVolumeScaleInJoules setup := by
    rw [hInternalEnergyPressureVolume .three, hPressureThree, hVolumeThree,
      hScale]
    norm_num
  have hHeatOneTwoLaw := _laws.firstLawOnEveryLeg .oneToTwo
  have hHeatTwoThreeLaw := _laws.firstLawOnEveryLeg .twoToThree
  have hHeatThreeOneLaw := _laws.firstLawOnEveryLeg .threeToOne
  simp only [CycleLeg.initialState, CycleLeg.finalState] at hHeatOneTwoLaw
  simp only [CycleLeg.initialState, CycleLeg.finalState] at hHeatTwoThreeLaw
  simp only [CycleLeg.initialState, CycleLeg.finalState] at hHeatThreeOneLaw
  rw [hInternalEnergyTwo, hInternalEnergyOne, hWorkOneTwo] at hHeatOneTwoLaw
  rw [hInternalEnergyThree, hInternalEnergyTwo, hWorkTwoThree] at hHeatTwoThreeLaw
  rw [hInternalEnergyOne, hInternalEnergyThree, hWorkThreeOne] at hHeatThreeOneLaw
  have hHeatOneTwo :
      energyInJoules (setup.heatTransferredIntoGas .oneToTwo) =
        6 * basePressureVolumeScaleInJoules setup := by
    linarith
  have hHeatTwoThree :
      energyInJoules (setup.heatTransferredIntoGas .twoToThree) =
        basePressureVolumeScaleInJoules setup * (5 * Real.log 5) := by
    linarith
  have hHeatThreeOne :
      energyInJoules (setup.heatTransferredIntoGas .threeToOne) =
        -10 * basePressureVolumeScaleInJoules setup := by
    linarith
  constructor
  · rw [_laws.netWorkAccounting, hWorkOneTwo, hWorkTwoThree,
      hWorkThreeOne]
    ring
  · have hHeatOneTwoNonnegative :
        0 ≤ energyInJoules (setup.heatTransferredIntoGas .oneToTwo) :=
      le_of_lt _physical.heatEntersOnFirstLeg
    have hHeatTwoThreeNonnegative :
        0 ≤ energyInJoules (setup.heatTransferredIntoGas .twoToThree) :=
      le_of_lt _physical.heatEntersOnSecondLeg
    have hHeatThreeOneNonpositive :
        energyInJoules (setup.heatTransferredIntoGas .threeToOne) ≤ 0 :=
      le_of_lt _physical.heatLeavesOnThirdLeg
    rw [_laws.heatInputAccounting,
      max_eq_left hHeatOneTwoNonnegative,
      max_eq_left hHeatTwoThreeNonnegative,
      max_eq_right hHeatThreeOneNonpositive,
      hHeatOneTwo, hHeatTwoThree]
    ring

/-- Labels of the four efficiencies displayed by the source problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Dimensionless efficiency printed beside each answer label. -/
def displayedEfficiency : AnswerChoice → ℝ
  | .A => 4 / 5
  | .B => 101 / 500
  | .C => 427 / 1000
  | .D => 29 / 100

/-- The answer label recorded in the supplied dataset metadata. -/
def recordedDatasetAnswer : AnswerChoice := .D

/-!
A displayed choice is at least as close as every other displayed value to the
calculated efficiency.  This avoids falsely asserting that the exact
logarithmic value is literally the coarse decimal `0.290`.
-/
def IsClosestDisplayedEfficiency
    (efficiency : ℝ) (choice : AnswerChoice) : Prop :=
  ∀ candidate,
    |efficiency - displayedEfficiency choice| ≤
      |efficiency - displayedEfficiency candidate|

/-!
For monatomic ideal helium, the common factor `p₁V₁` cancels between net work
and absorbed heat, leaving

`η = (5 log 5 - 4) / (5 log 5 + 6)`.

This value is closest to the displayed `0.290`, recorded answer D.

Blueprint label: `thm:physics:phyx_mini_0432:target`.
-/
theorem thermalEfficiency_eq_exactValue_and_selectsAnswerD
    (setup : HeliumHeatEngineCycle)
    (_scenario : MatchesProblemScenario setup)
    (_figure : MatchesPrimaryPressureVolumeFigure setup)
    (_physical : HasPhysicalHeatEngineParameters setup)
    (_laws : SatisfiesIdealMonatomicHeliumCycleLaws setup) :
    setup.thermalEfficiency =
        (5 * Real.log 5 - 4) / (5 * Real.log 5 + 6) ∧
      IsClosestDisplayedEfficiency
        setup.thermalEfficiency recordedDatasetAnswer := by
  obtain ⟨hNetWork, hHeatInput⟩ :=
    netWork_and_heatInput_readouts setup _scenario _figure _physical _laws
  have hScalePositive :
      0 < basePressureVolumeScaleInJoules setup := by
    exact mul_pos (_physical.statePressurePositive .one)
      (_physical.stateVolumePositive .one)
  have hLogFivePositive : 0 < Real.log (5 : ℝ) :=
    Real.log_pos (by norm_num)
  have hLogFiveLower : (3 / 2 : ℝ) < Real.log 5 := by
    have hLogTenNinthLower : (1 / 10 : ℝ) < Real.log (10 / 9) := by
      have h := Real.log_lt_sub_one_of_pos
        (by norm_num : (0 : ℝ) < 9 / 10)
        (by norm_num : (9 / 10 : ℝ) ≠ 1)
      rw [show (9 / 10 : ℝ) = (10 / 9 : ℝ)⁻¹ by norm_num,
        Real.log_inv] at h
      norm_num at h ⊢
      linarith
    have hPower : ((10 / 9 : ℝ) ^ 15) < 5 := by norm_num
    have hLogPower :=
      Real.log_lt_log (by positivity : (0 : ℝ) < (10 / 9) ^ 15) hPower
    rw [Real.log_pow] at hLogPower
    norm_num at hLogPower
    nlinarith
  have hLogFiveUpper : Real.log 5 < (9 / 5 : ℝ) := by
    have hExpFifth : (6 / 5 : ℝ) ≤ Real.exp (1 / 5) := by
      have h := Real.add_one_le_exp (1 / 5 : ℝ)
      norm_num at h ⊢
      exact h
    have hPow : (6 / 5 : ℝ) ^ 9 ≤ Real.exp (1 / 5) ^ 9 :=
      pow_le_pow_left₀ (by norm_num) hExpFifth 9
    have hExpNineFifths : (5 : ℝ) < Real.exp (9 / 5) := by
      rw [← Real.exp_nat_mul] at hPow
      norm_num at hPow ⊢
      linarith
    exact
      (Real.log_lt_iff_lt_exp (by norm_num : (0 : ℝ) < 5)).2
        hExpNineFifths
  have hHeatFactorPositive : 0 < 5 * Real.log (5 : ℝ) + 6 := by
    nlinarith
  have hEfficiencyExact :
      setup.thermalEfficiency =
        (5 * Real.log 5 - 4) / (5 * Real.log 5 + 6) := by
    have hEfficiency :=
      _laws.efficiencyLaw (ne_of_gt _physical.heatInputPositive)
    rw [hNetWork, hHeatInput] at hEfficiency
    calc
      setup.thermalEfficiency =
          basePressureVolumeScaleInJoules setup *
              (5 * Real.log 5 - 4) /
            (basePressureVolumeScaleInJoules setup *
              (5 * Real.log 5 + 6)) :=
        hEfficiency
      _ = (5 * Real.log 5 - 4) / (5 * Real.log 5 + 6) :=
        mul_div_mul_left _ _ hScalePositive.ne'
  have hEfficiencyLower :
      (1 / 4 : ℝ) < setup.thermalEfficiency := by
    rw [hEfficiencyExact, lt_div_iff₀ hHeatFactorPositive]
    nlinarith
  have hEfficiencyUpper :
      setup.thermalEfficiency < (1 / 3 : ℝ) := by
    rw [hEfficiencyExact, div_lt_iff₀ hHeatFactorPositive]
    nlinarith
  refine ⟨hEfficiencyExact, ?_⟩
  intro candidate
  cases candidate with
  | A =>
      change
        |setup.thermalEfficiency - (29 / 100 : ℝ)| ≤
          |setup.thermalEfficiency - (4 / 5 : ℝ)|
      rw [abs_of_neg (by nlinarith :
        setup.thermalEfficiency - (4 / 5 : ℝ) < 0), abs_le]
      constructor <;> nlinarith
  | B =>
      change
        |setup.thermalEfficiency - (29 / 100 : ℝ)| ≤
          |setup.thermalEfficiency - (101 / 500 : ℝ)|
      rw [abs_of_pos (by nlinarith :
        0 < setup.thermalEfficiency - (101 / 500 : ℝ)), abs_le]
      constructor <;> nlinarith
  | C =>
      change
        |setup.thermalEfficiency - (29 / 100 : ℝ)| ≤
          |setup.thermalEfficiency - (427 / 1000 : ℝ)|
      rw [abs_of_neg (by nlinarith :
        setup.thermalEfficiency - (427 / 1000 : ℝ) < 0), abs_le]
      constructor <;> nlinarith
  | D => exact le_rfl

end PhyXMiniProblems.ProblemPhyXMini0432
