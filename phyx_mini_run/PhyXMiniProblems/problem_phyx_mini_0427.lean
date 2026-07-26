import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Physlib.Thermodynamics.Temperature.Basic
import Physlib.Thermodynamics.Temperature.TemperatureUnits
import Physlib.Units.WithDim.Energy
import Physlib.Units.WithDim.Pressure

/- USER: The assigned source file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0427

open Dimension

/-!
# Thermal efficiency of a three-leg ideal-gas engine cycle

The primary pressure--volume diagram shows the clockwise cycle

`1 → 2 → 3 → 1`.

State `1` is at `(600 cm³, 1 atm)`, state `2` is at
`(200 cm³, p_max)`, and state `3` is at `(600 cm³, p_max)`.  The curved
compression `1 → 2` is labelled isothermal, `2 → 3` is a horizontal
constant-pressure expansion, and `3 → 1` is a vertical constant-volume
cooling.  The gas has heat-capacity ratio `γ = 1.25`, state `1` has
temperature `300 K`, and the engine runs at `20 cycles/s`.

Pressure, volume, temperature, energy transfer, and cycle rate retain their
physical roles.  Real numbers below are coherent-SI or named-unit readouts,
dimensionless ratios and efficiencies, or displayed answer values.  Work is
positive when done by the gas, and heat is positive when transferred into it.
-/

/-! ## Dimensionful quantities and calibrated readouts -/

/-- A nonnegative physical volume carrying dimension `L³`. -/
abbrev VolumeQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * L𝓭 * L𝓭) NNReal)

/-- A nonnegative cycle rate carrying inverse-time dimension. -/
abbrev CycleRateQuantity : Type :=
  Dimensionful (WithDim T𝓭⁻¹ NNReal)

/-- Read a physical pressure in coherent SI pascals. -/
def pressureInPascals (pressure : DimPressure) : ℝ :=
  (pressure UnitChoices.SI).val

/-- Read a pressure in the atmospheres printed on the vertical axis. -/
def pressureInAtmospheres (pressure : DimPressure) : ℝ :=
  pressureInPascals pressure / 101325

/-- Read a physical volume in coherent SI cubic metres. -/
def volumeInCubicMetres (volume : VolumeQuantity) : ℝ :=
  ((volume UnitChoices.SI).val : ℝ)

/-- Read a volume in the cubic centimetres printed on the horizontal axis. -/
def volumeInCubicCentimetres (volume : VolumeQuantity) : ℝ :=
  volumeInCubicMetres volume * 1000000

/-- Read signed heat, work, or internal-energy change in SI joules. -/
def energyInJoules (energy : DimEnergy) : ℝ :=
  (energy UnitChoices.SI).val

/-- Read an absolute temperature in kelvins from its stated storage unit. -/
def temperatureInKelvin
    (storageUnit : TemperatureUnit) (temperature : Temperature) : ℝ :=
  let unitRatio : NNReal := storageUnit / TemperatureUnit.kelvin
  temperature.toReal * (unitRatio : ℝ)

/-- Read a physical cycle rate in cycles per SI second (hertz). -/
def cycleRateInHertz (rate : CycleRateQuantity) : ℝ :=
  ((rate UnitChoices.SI).val : ℝ)

/-! ## Gas, cycle, and primary-figure vocabulary -/

/-- The working-substance model used for the gas. -/
inductive GasModel where
  | caloricallyPerfectIdealGas
  deriving DecidableEq, Repr

/-- The thermodynamic role played by the cyclic device. -/
inductive ThermodynamicDeviceRole where
  | heatEngine
  deriving DecidableEq, Repr

/-- The three numbered states printed in the supplied diagram. -/
inductive StateLabel where
  | one
  | two
  | three
  deriving DecidableEq, Fintype, Repr

/-- The three directed arrows making up one traversal of the cycle. -/
inductive CycleLeg where
  | oneToTwo
  | twoToThree
  | threeToOne
  deriving DecidableEq, Fintype, Repr

/-- Initial state of each directed process leg. -/
def CycleLeg.initialState : CycleLeg → StateLabel
  | .oneToTwo => .one
  | .twoToThree => .two
  | .threeToOne => .three

/-- Final state of each directed process leg. -/
def CycleLeg.finalState : CycleLeg → StateLabel
  | .oneToTwo => .two
  | .twoToThree => .three
  | .threeToOne => .one

/-- Thermodynamic constraint holding on a process leg. -/
inductive ProcessKind where
  | isothermal
  | isobaric
  | isochoric
  deriving DecidableEq, Repr

/-- Geometric appearance of a process in the pressure--volume plane. -/
inductive PathGeometry where
  | curvedSegment
  | horizontalSegment
  | verticalSegment
  deriving DecidableEq, Repr

/-- Physical quantity assigned to one of the two plot axes. -/
inductive AxisQuantity where
  | pressure
  | volume
  deriving DecidableEq, Repr

/-- Unit explicitly printed beside an axis. -/
inductive AxisUnit where
  | atmosphere
  | cubicCentimetre
  deriving DecidableEq, Repr

/-- Text and numerical labels visible in the primary bitmap. -/
inductive FigureLabel where
  | pressureAxisP
  | volumeAxisV
  | originZero
  | pressureOne
  | pressureMaximum
  | volume200
  | volume400
  | volume600
  | stateOne
  | stateTwo
  | stateThree
  | isotherm
  deriving DecidableEq, Fintype, Repr

/-- A physical equilibrium state of the working gas. -/
structure ThermodynamicState where
  pressure : DimPressure
  volume : VolumeQuantity
  temperature : Temperature

/-!
Qualitative plot data kept separate from the physical state values.  In
particular, this structure records axes, labels, vertices, path shapes, and
arrow directions, but no efficiency or answer choice.
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

/-!
Independent physical observables for one fixed sample of gas.  Work is done
by the gas, heat is transferred into the gas, and internal-energy change is
`U_final - U_initial` on each leg.  The requested efficiency is deliberately
not stored as a field.
-/
structure IdealGasHeatEngineCycle where
  gasModel : GasModel
  deviceRole : ThermodynamicDeviceRole
  sameClosedGasSample : Bool
  quasistaticEquilibriumPath : Bool
  specificHeatRatio : ℝ
  cycleRate : CycleRateQuantity
  temperatureStorageUnit : TemperatureUnit
  stateAt : StateLabel → ThermodynamicState
  processKind : CycleLeg → ProcessKind
  workDoneByGas : CycleLeg → DimEnergy
  heatTransferredIntoGas : CycleLeg → DimEnergy
  internalEnergyChange : CycleLeg → DimEnergy
  figure : PressureVolumeFigure

/-! ## Problem data, primary-image readouts, and physical laws -/

/-!
Numerical data stated in the prose.  The cycle rate is retained even though
thermal efficiency is a per-cycle ratio and hence independent of that rate.
No efficiency or answer value occurs here.
-/
structure MatchesProblemStatement
    (setup : IdealGasHeatEngineCycle) : Prop where
  gasIsCaloricallyPerfectIdealGas :
    setup.gasModel = .caloricallyPerfectIdealGas
  deviceIsHeatEngine : setup.deviceRole = .heatEngine
  sameClosedSample : setup.sameClosedGasSample = true
  pathIsQuasistatic : setup.quasistaticEquilibriumPath = true
  heatCapacityRatio : setup.specificHeatRatio = 5 / 4
  temperatureUnitIsKelvin :
    setup.temperatureStorageUnit = TemperatureUnit.kelvin
  initialTemperatureKelvin :
    temperatureInKelvin setup.temperatureStorageUnit
      (setup.stateAt .one).temperature = 300
  twentyCyclesPerSecond : cycleRateInHertz setup.cycleRate = 20

/-!
Exact transcription of image `427.png`.  The bitmap fixes state `1` at
`(600 cm³, 1 atm)`, state `2` at volume `200 cm³`, state `3` at volume
`600 cm³`, and states `2` and `3` on the common line labelled `p_max`.
The numerical value of `p_max` is not assumed; it must follow from the
isothermal ideal-gas leg.
-/
structure MatchesPrimaryPressureVolumeFigure
    (setup : IdealGasHeatEngineCycle) : Prop where
  horizontalAxisIsVolume :
    setup.figure.horizontalAxisQuantity = .volume
  verticalAxisIsPressure :
    setup.figure.verticalAxisQuantity = .pressure
  horizontalAxisUsesCubicCentimetres :
    setup.figure.horizontalAxisUnit = .cubicCentimetre
  verticalAxisUsesAtmospheres :
    setup.figure.verticalAxisUnit = .atmosphere
  everyPrintedLabelIsShown :
    ∀ label : FigureLabel, setup.figure.showsLabel label = true
  everyStateIsShown :
    ∀ state : StateLabel, setup.figure.showsState state = true
  everyDirectedLegIsShown :
    ∀ leg : CycleLeg, setup.figure.showsDirectedLeg leg = true
  arrowsFollowCycleOrder :
    ∀ leg : CycleLeg,
      setup.figure.directedEndpoints leg =
        (leg.initialState, leg.finalState)
  oneToTwoIsCurved :
    setup.figure.pathGeometry .oneToTwo = .curvedSegment
  twoToThreeIsHorizontal :
    setup.figure.pathGeometry .twoToThree = .horizontalSegment
  threeToOneIsVertical :
    setup.figure.pathGeometry .threeToOne = .verticalSegment
  oneToTwoIsIsothermal :
    setup.processKind .oneToTwo = .isothermal
  twoToThreeIsIsobaric :
    setup.processKind .twoToThree = .isobaric
  threeToOneIsIsochoric :
    setup.processKind .threeToOne = .isochoric
  stateOnePressureAtmospheres :
    pressureInAtmospheres (setup.stateAt .one).pressure = 1
  stateOneVolumeCubicCentimetres :
    volumeInCubicCentimetres (setup.stateAt .one).volume = 600
  stateTwoVolumeCubicCentimetres :
    volumeInCubicCentimetres (setup.stateAt .two).volume = 200
  stateThreeVolumeCubicCentimetres :
    volumeInCubicCentimetres (setup.stateAt .three).volume = 600
  statesTwoAndThreeSharePMax :
    (setup.stateAt .two).pressure = (setup.stateAt .three).pressure
  stateTwoPressureIsDisplayedMaximum :
    ∀ state : StateLabel,
      pressureInAtmospheres (setup.stateAt state).pressure ≤
        pressureInAtmospheres (setup.stateAt .two).pressure

/-- Positivity and nondegeneracy of the physical parameters. -/
structure HasPhysicalThermodynamicParameters
    (setup : IdealGasHeatEngineCycle) : Prop where
  heatCapacityRatioExceedsOne : 1 < setup.specificHeatRatio
  pressurePositive :
    ∀ state, 0 < pressureInPascals (setup.stateAt state).pressure
  volumePositive :
    ∀ state, 0 < volumeInCubicMetres (setup.stateAt state).volume
  temperaturePositive :
    ∀ state,
      0 < temperatureInKelvin setup.temperatureStorageUnit
        (setup.stateAt state).temperature
  cycleRatePositive : 0 < cycleRateInHertz setup.cycleRate

/-!
Macroscopic governing laws for a fixed sample of calorically perfect ideal
gas with constant heat-capacity ratio `γ`.

* the cross-multiplied fixed-sample ideal-gas law expresses `pV/T = const`;
* `ΔU = (p_f V_f - p_i V_i)/(γ - 1)`;
* the first law uses `Q_into = ΔU + W_by`;
* reversible isothermal work is `p_i V_i log(V_f/V_i)`;
* isobaric work is `p(V_f-V_i)`;
* an isochoric leg has zero boundary work.

These are general laws.  No field states `p_max`, any derived state
temperature, a leg's numerical heat/work, net work, total heat input,
efficiency, or answer choice.
-/
structure ObeysCaloricallyPerfectIdealGasLaws
    (setup : IdealGasHeatEngineCycle) : Prop where
  fixedSampleIdealGasLaw : ∀ first second : StateLabel,
    pressureInPascals (setup.stateAt first).pressure *
          volumeInCubicMetres (setup.stateAt first).volume *
          temperatureInKelvin setup.temperatureStorageUnit
            (setup.stateAt second).temperature =
      pressureInPascals (setup.stateAt second).pressure *
          volumeInCubicMetres (setup.stateAt second).volume *
          temperatureInKelvin setup.temperatureStorageUnit
            (setup.stateAt first).temperature
  internalEnergyLaw : ∀ leg : CycleLeg,
    energyInJoules (setup.internalEnergyChange leg) =
      (pressureInPascals
            (setup.stateAt leg.finalState).pressure *
            volumeInCubicMetres
              (setup.stateAt leg.finalState).volume -
          pressureInPascals
            (setup.stateAt leg.initialState).pressure *
            volumeInCubicMetres
              (setup.stateAt leg.initialState).volume) /
        (setup.specificHeatRatio - 1)
  firstLaw : ∀ leg : CycleLeg,
    energyInJoules (setup.heatTransferredIntoGas leg) =
      energyInJoules (setup.internalEnergyChange leg) +
        energyInJoules (setup.workDoneByGas leg)
  isothermalTemperatureAndWorkLaw : ∀ leg : CycleLeg,
    setup.processKind leg = .isothermal →
      temperatureInKelvin setup.temperatureStorageUnit
          (setup.stateAt leg.finalState).temperature =
        temperatureInKelvin setup.temperatureStorageUnit
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

/-! ## Per-cycle energy accounting and displayed answers -/

/-- The `p₁V₁` energy scale of this cycle, expressed in joules. -/
def initialPressureVolumeEnergyInJoules
    (setup : IdealGasHeatEngineCycle) : ℝ :=
  pressureInPascals (setup.stateAt .one).pressure *
    volumeInCubicMetres (setup.stateAt .one).volume

/-- Net work done by the gas in one clockwise traversal of the cycle. -/
def netWorkDoneByGasInJoules (setup : IdealGasHeatEngineCycle) : ℝ :=
  energyInJoules (setup.workDoneByGas .oneToTwo) +
    energyInJoules (setup.workDoneByGas .twoToThree) +
    energyInJoules (setup.workDoneByGas .threeToOne)

/-- Total heat absorbed per cycle, summing the positive parts of signed heat. -/
def totalHeatAbsorbedInJoules (setup : IdealGasHeatEngineCycle) : ℝ :=
  max (energyInJoules (setup.heatTransferredIntoGas .oneToTwo)) 0 +
    max (energyInJoules (setup.heatTransferredIntoGas .twoToThree)) 0 +
    max (energyInJoules (setup.heatTransferredIntoGas .threeToOne)) 0

/-- Dimensionless thermal efficiency `W_net/Q_absorbed` for one cycle. -/
def thermalEfficiency (setup : IdealGasHeatEngineCycle) : ℝ :=
  netWorkDoneByGasInJoules setup / totalHeatAbsorbedInJoules setup

/-- The four answer labels printed in the source problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Dimensionless decimal printed beside each answer label. -/
def displayedEfficiency : AnswerChoice → ℝ
  | .A => 167 / 250
  | .B => 3 / 20
  | .C => 137 / 250
  | .D => 901 / 10000

/-- Answer label recorded in the dataset metadata. -/
def recordedAnswerChoice : AnswerChoice := .D

/-- Agreement with a decimal displayed to four places. -/
def MatchesToNearestTenThousandth
    (setup : IdealGasHeatEngineCycle) (choice : AnswerChoice) : Prop :=
  |thermalEfficiency setup - displayedEfficiency choice| < (1 / 20000 : ℝ)

/-- The specified choice is the unique four-decimal display match. -/
def IsUniqueMatchingDisplayedEfficiency
    (setup : IdealGasHeatEngineCycle) (choice : AnswerChoice) : Prop :=
  MatchesToNearestTenThousandth setup choice ∧
    ∀ other : AnswerChoice,
      MatchesToNearestTenThousandth setup other → other = choice

/-!
The figure and generic laws imply `p_max = 3 atm`, `T₂ = 300 K`, and
`T₃ = 900 K`.  Writing `E₁ = p₁V₁`, the leg heats are
`-E₁ log 3`, `10E₁`, and `-8E₁`, while the works are
`-E₁ log 3`, `2E₁`, and `0`.  These are derived conclusions, not premise
fields.
-/
lemma cycleStateAndEnergyReadouts
    (setup : IdealGasHeatEngineCycle)
    (hProblem : MatchesProblemStatement setup)
    (hFigure : MatchesPrimaryPressureVolumeFigure setup)
    (hPhysical : HasPhysicalThermodynamicParameters setup)
    (hLaws : ObeysCaloricallyPerfectIdealGasLaws setup) :
    pressureInAtmospheres (setup.stateAt .two).pressure = 3 ∧
      pressureInAtmospheres (setup.stateAt .three).pressure = 3 ∧
      temperatureInKelvin setup.temperatureStorageUnit
          (setup.stateAt .two).temperature = 300 ∧
      temperatureInKelvin setup.temperatureStorageUnit
          (setup.stateAt .three).temperature = 900 ∧
      energyInJoules (setup.workDoneByGas .oneToTwo) =
        -(initialPressureVolumeEnergyInJoules setup * Real.log 3) ∧
      energyInJoules (setup.workDoneByGas .twoToThree) =
        2 * initialPressureVolumeEnergyInJoules setup ∧
      energyInJoules (setup.workDoneByGas .threeToOne) = 0 ∧
      energyInJoules (setup.heatTransferredIntoGas .oneToTwo) =
        -(initialPressureVolumeEnergyInJoules setup * Real.log 3) ∧
      energyInJoules (setup.heatTransferredIntoGas .twoToThree) =
        10 * initialPressureVolumeEnergyInJoules setup ∧
      energyInJoules (setup.heatTransferredIntoGas .threeToOne) =
        -(8 * initialPressureVolumeEnergyInJoules setup) := by
  have hp₁ :
      pressureInPascals (setup.stateAt .one).pressure = 101325 := by
    have h := hFigure.stateOnePressureAtmospheres
    norm_num [pressureInAtmospheres] at h ⊢
    linarith
  have hv₁ :
      volumeInCubicMetres (setup.stateAt .one).volume = 3 / 5000 := by
    have h := hFigure.stateOneVolumeCubicCentimetres
    norm_num [volumeInCubicCentimetres] at h ⊢
    linarith
  have hv₂ :
      volumeInCubicMetres (setup.stateAt .two).volume = 1 / 5000 := by
    have h := hFigure.stateTwoVolumeCubicCentimetres
    norm_num [volumeInCubicCentimetres] at h ⊢
    linarith
  have hv₃ :
      volumeInCubicMetres (setup.stateAt .three).volume = 3 / 5000 := by
    have h := hFigure.stateThreeVolumeCubicCentimetres
    norm_num [volumeInCubicCentimetres] at h ⊢
    linarith
  obtain ⟨hT₂T₁, hW₁₂raw⟩ :=
    hLaws.isothermalTemperatureAndWorkLaw .oneToTwo
      hFigure.oneToTwoIsIsothermal
  simp only [CycleLeg.finalState, CycleLeg.initialState] at hT₂T₁ hW₁₂raw
  have hT₂ :
      temperatureInKelvin setup.temperatureStorageUnit
          (setup.stateAt .two).temperature = 300 :=
    hT₂T₁.trans hProblem.initialTemperatureKelvin
  have hp₂ :
      pressureInPascals (setup.stateAt .two).pressure = 303975 := by
    have h := hLaws.fixedSampleIdealGasLaw .one .two
    rw [hp₁, hv₁, hv₂, hT₂, hProblem.initialTemperatureKelvin] at h
    norm_num at h ⊢
    nlinarith [hPhysical.pressurePositive .two]
  have hp₂atm :
      pressureInAtmospheres (setup.stateAt .two).pressure = 3 := by
    norm_num [pressureInAtmospheres, hp₂]
  have hp₂p₃ :
      pressureInPascals (setup.stateAt .two).pressure =
        pressureInPascals (setup.stateAt .three).pressure :=
    congrArg pressureInPascals hFigure.statesTwoAndThreeSharePMax
  have hp₃ :
      pressureInPascals (setup.stateAt .three).pressure = 303975 := by
    linarith
  have hp₃atm :
      pressureInAtmospheres (setup.stateAt .three).pressure = 3 := by
    norm_num [pressureInAtmospheres, hp₃]
  have hT₃ :
      temperatureInKelvin setup.temperatureStorageUnit
          (setup.stateAt .three).temperature = 900 := by
    have h := hLaws.fixedSampleIdealGasLaw .one .three
    rw [hp₁, hv₁, hp₃, hv₃, hProblem.initialTemperatureKelvin] at h
    norm_num at h ⊢
    linarith
  have hE :
      initialPressureVolumeEnergyInJoules setup = 12159 / 200 := by
    norm_num [initialPressureVolumeEnergyInJoules, hp₁, hv₁]
  have hW₁₂ :
      energyInJoules (setup.workDoneByGas .oneToTwo) =
        -(initialPressureVolumeEnergyInJoules setup * Real.log 3) := by
    rw [hp₁, hv₁, hv₂] at hW₁₂raw
    norm_num at hW₁₂raw
    rw [show (1 / 3 : ℝ) = (3 : ℝ)⁻¹ by norm_num, Real.log_inv] at hW₁₂raw
    rw [hW₁₂raw, hE]
    ring
  obtain ⟨_, hW₂₃raw⟩ :=
    hLaws.isobaricPressureAndWorkLaw .twoToThree
      hFigure.twoToThreeIsIsobaric
  simp only [CycleLeg.finalState, CycleLeg.initialState] at hW₂₃raw
  have hW₂₃ :
      energyInJoules (setup.workDoneByGas .twoToThree) =
        2 * initialPressureVolumeEnergyInJoules setup := by
    rw [hp₂, hv₂, hv₃] at hW₂₃raw
    norm_num at hW₂₃raw
    rw [hW₂₃raw, hE]
    norm_num
  obtain ⟨_, hW₃₁⟩ :=
    hLaws.isochoricVolumeAndWorkLaw .threeToOne
      hFigure.threeToOneIsIsochoric
  have hΔU₁₂ :
      energyInJoules (setup.internalEnergyChange .oneToTwo) = 0 := by
    have h := hLaws.internalEnergyLaw .oneToTwo
    simp only [CycleLeg.finalState, CycleLeg.initialState] at h
    rw [hp₂, hv₂, hp₁, hv₁, hProblem.heatCapacityRatio] at h
    norm_num at h ⊢
    exact h
  have hΔU₂₃ :
      energyInJoules (setup.internalEnergyChange .twoToThree) =
        8 * initialPressureVolumeEnergyInJoules setup := by
    have h := hLaws.internalEnergyLaw .twoToThree
    simp only [CycleLeg.finalState, CycleLeg.initialState] at h
    rw [hp₃, hv₃, hp₂, hv₂, hProblem.heatCapacityRatio] at h
    norm_num at h
    rw [h, hE]
    norm_num
  have hΔU₃₁ :
      energyInJoules (setup.internalEnergyChange .threeToOne) =
        -(8 * initialPressureVolumeEnergyInJoules setup) := by
    have h := hLaws.internalEnergyLaw .threeToOne
    simp only [CycleLeg.finalState, CycleLeg.initialState] at h
    rw [hp₁, hv₁, hp₃, hv₃, hProblem.heatCapacityRatio] at h
    norm_num at h
    rw [h, hE]
    norm_num
  have hQ₁₂ :
      energyInJoules (setup.heatTransferredIntoGas .oneToTwo) =
        -(initialPressureVolumeEnergyInJoules setup * Real.log 3) := by
    have h := hLaws.firstLaw .oneToTwo
    rw [hΔU₁₂, hW₁₂] at h
    simpa using h
  have hQ₂₃ :
      energyInJoules (setup.heatTransferredIntoGas .twoToThree) =
        10 * initialPressureVolumeEnergyInJoules setup := by
    have h := hLaws.firstLaw .twoToThree
    rw [hΔU₂₃, hW₂₃] at h
    nlinarith
  have hQ₃₁ :
      energyInJoules (setup.heatTransferredIntoGas .threeToOne) =
        -(8 * initialPressureVolumeEnergyInJoules setup) := by
    have h := hLaws.firstLaw .threeToOne
    rw [hΔU₃₁, hW₃₁, add_zero] at h
    exact h
  exact ⟨hp₂atm, hp₃atm, hT₂, hT₃, hW₁₂, hW₂₃, hW₃₁,
    hQ₁₂, hQ₂₃, hQ₃₁⟩

/-!
The exact ideal-model efficiency is

`(2 - log 3) / 10 ≈ 0.0901388`.

It therefore rounds to `0.0901`, uniquely selecting recorded answer D.  The
rounded decimal is represented by a four-decimal tolerance rather than by an
incorrect exact equality.

This formalizes `thm:physics:phyx_mini_0427:target`.
-/
theorem problem_phyx_mini_0427
    (setup : IdealGasHeatEngineCycle)
    (hProblem : MatchesProblemStatement setup)
    (hFigure : MatchesPrimaryPressureVolumeFigure setup)
    (hPhysical : HasPhysicalThermodynamicParameters setup)
    (hLaws : ObeysCaloricallyPerfectIdealGasLaws setup) :
    thermalEfficiency setup = (2 - Real.log 3) / 10 ∧
      MatchesToNearestTenThousandth setup recordedAnswerChoice ∧
      IsUniqueMatchingDisplayedEfficiency setup recordedAnswerChoice := by
  rcases cycleStateAndEnergyReadouts setup hProblem hFigure hPhysical hLaws with
    ⟨_, _, _, _, hW₁₂, hW₂₃, hW₃₁, hQ₁₂, hQ₂₃, hQ₃₁⟩
  have hEpos : 0 < initialPressureVolumeEnergyInJoules setup := by
    exact mul_pos (hPhysical.pressurePositive .one)
      (hPhysical.volumePositive .one)
  have hlogpos : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hQ₁₂nonpos :
      -(initialPressureVolumeEnergyInJoules setup * Real.log 3) ≤ 0 := by
    exact neg_nonpos.mpr (mul_nonneg hEpos.le hlogpos.le)
  have hQ₂₃nonneg :
      0 ≤ 10 * initialPressureVolumeEnergyInJoules setup := by
    positivity
  have hQ₃₁nonpos :
      -(8 * initialPressureVolumeEnergyInJoules setup) ≤ 0 := by
    exact neg_nonpos.mpr (mul_nonneg (by norm_num) hEpos.le)
  have hNet :
      netWorkDoneByGasInJoules setup =
        initialPressureVolumeEnergyInJoules setup * (2 - Real.log 3) := by
    rw [netWorkDoneByGasInJoules, hW₁₂, hW₂₃, hW₃₁]
    ring
  have hAbsorbed :
      totalHeatAbsorbedInJoules setup =
        10 * initialPressureVolumeEnergyInJoules setup := by
    rw [totalHeatAbsorbedInJoules, hQ₁₂, hQ₂₃, hQ₃₁,
      max_eq_right hQ₁₂nonpos, max_eq_left hQ₂₃nonneg,
      max_eq_right hQ₃₁nonpos]
    ring
  have hEfficiency :
      thermalEfficiency setup = (2 - Real.log 3) / 10 := by
    rw [thermalEfficiency, hNet, hAbsorbed]
    field_simp [ne_of_gt hEpos]
  have hlogBounds :
      (2197 / 2000 : ℝ) < Real.log 3 ∧
        Real.log 3 < (2199 / 2000 : ℝ) := by
    constructor
    · rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 3)]
      rw [show (2197 / 2000 : ℝ) =
          2197 / 4000 + 2197 / 4000 by norm_num, Real.exp_add]
      have hupper := Real.exp_bound' (x := (2197 / 4000 : ℝ))
        (by norm_num) (by norm_num) (n := 8) (by norm_num)
      norm_num [Finset.sum_range_succ, Nat.factorial] at hupper
      have hpos := Real.exp_pos (2197 / 4000 : ℝ)
      nlinarith [sq_nonneg (Real.exp (2197 / 4000 : ℝ))]
    · rw [Real.log_lt_iff_lt_exp (by norm_num : (0 : ℝ) < 3)]
      have hlower := Real.sum_le_exp_of_nonneg
        (show (0 : ℝ) ≤ 2199 / 2000 by norm_num) 10
      norm_num [Finset.sum_range_succ, Nat.factorial] at hlower
      linarith
  have hRecorded :
      MatchesToNearestTenThousandth setup recordedAnswerChoice := by
    rw [MatchesToNearestTenThousandth, hEfficiency]
    change |(2 - Real.log 3) / 10 - 901 / 10000| < (1 / 20000 : ℝ)
    rw [abs_lt]
    constructor <;> nlinarith [hlogBounds.1, hlogBounds.2]
  refine ⟨hEfficiency, hRecorded, hRecorded, ?_⟩
  intro other hOther
  cases other with
  | A =>
      simp only [MatchesToNearestTenThousandth, displayedEfficiency] at hOther
      rw [hEfficiency, abs_lt] at hOther
      norm_num at hOther
      exfalso
      nlinarith [hlogBounds.1]
  | B =>
      simp only [MatchesToNearestTenThousandth, displayedEfficiency] at hOther
      rw [hEfficiency, abs_lt] at hOther
      norm_num at hOther
      exfalso
      nlinarith [hlogBounds.1]
  | C =>
      simp only [MatchesToNearestTenThousandth, displayedEfficiency] at hOther
      rw [hEfficiency, abs_lt] at hOther
      norm_num at hOther
      exfalso
      nlinarith [hlogBounds.1]
  | D =>
      rfl

end PhyXMiniProblems.ProblemPhyXMini0427
