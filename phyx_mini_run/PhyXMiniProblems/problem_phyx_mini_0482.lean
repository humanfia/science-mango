import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Physlib.Thermodynamics.Temperature.Basic
import Physlib.Units.WithDim.Energy
import Physlib.Units.WithDim.Pressure

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0482

open Dimension

/-!
# Efficiency of an isochoric--isothermal--isobaric ideal-gas cycle

The primary pressure--volume image shows the clockwise cycle `1 → 2 → 3 → 1`
with relative state coordinates

* `1 = (V, P, T)`,
* `2 = (V, 2P, 2T)`, and
* `3 = (2V, P, 2T)`.

Thus `1 → 2` is isochoric heating, `2 → 3` is isothermal expansion, and
`3 → 1` is isobaric compression.  The image, rather than the auxiliary
caption's reversed description of the isotherm labels, is treated as primary
evidence.

Pressure, volume, temperature, heat, work, and internal energy are represented
by Physlib quantities carrying their physical roles.  Real numbers below are
SI readouts, the mole and gas-constant readouts, dimensionless ratios, or
displayed efficiencies.

Assumption/target split:

* `MatchesProblemStatement` records the heat-engine role, monatomic ideal-gas
  model, closed directed cycle, three process kinds, and the stated pressure
  changes;
* `MatchesPrimaryPressureVolumeFigure` records axes, symbolic ticks, state
  labels, isotherms, arrows, and the relative `P`, `V`, and `T` readouts;
* `UsesQuasistaticEquilibriumModel` and `HasPhysicalCycleParameters` record
  the modelling regime and the positive physical branch;
* `SatisfiesMonatomicIdealGasCycleLaws` states the ideal-gas, caloric,
  first-law, and boundary-work laws; and
* the energy accounting, exact efficiency, and selected answer C occur only
  as conclusions below.
-/

/-! ## Dimensionful quantities and SI readouts -/

/-- A signed physical volume carrying dimension `length³`. -/
abbrev VolumeQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * L𝓭 * L𝓭) ℝ)

/-- A physical pressure carrying Physlib's pressure dimension. -/
abbrev PressureQuantity : Type := DimPressure

/-- Signed heat, work, or internal energy carrying the energy dimension. -/
abbrev EnergyQuantity : Type := DimEnergy

/-- Coherent-SI volume readout, in cubic metres. -/
def volumeInCubicMeters (volume : VolumeQuantity) : ℝ :=
  (volume UnitChoices.SI).val

/-- Coherent-SI pressure readout, in pascals. -/
def pressureInPascals (pressure : PressureQuantity) : ℝ :=
  (pressure UnitChoices.SI).val /
    (DimPressure.pascal UnitChoices.SI).val

/-- Absolute-temperature readout, in kelvin. -/
def temperatureInKelvins (temperature : Temperature) : ℝ :=
  temperature.toReal

/-- Signed energy readout, in joules. -/
def energyInJoules (energy : EnergyQuantity) : ℝ :=
  (energy UnitChoices.SI).val /
    (DimEnergy.joule UnitChoices.SI).val

/-! ## Cycle, state, and process vocabulary -/

/-- Material model specified for the engine's working gas. -/
inductive GasModel where
  | monatomicIdealGas
  deriving DecidableEq, Repr

/-- Thermodynamic role assigned to the cyclic device. -/
inductive DeviceRole where
  | heatEngine
  deriving DecidableEq, Repr

/-- Equilibrium-path idealization under which a plotted `p`--`V` path fixes work. -/
inductive ProcessRegime where
  | quasistaticEquilibriumPath
  | other
  deriving DecidableEq, Repr

/-- Numerical labels printed beside the three vertices in the figure. -/
inductive StateLabel where
  | one
  | two
  | three
  deriving DecidableEq, Fintype, Repr

/-- Directed process legs in the arrow order shown by the image. -/
inductive CycleLeg where
  | oneToTwo
  | twoToThree
  | threeToOne
  deriving DecidableEq, Fintype, Repr

/-- Initial state of a directed process leg. -/
def CycleLeg.start : CycleLeg → StateLabel
  | .oneToTwo => .one
  | .twoToThree => .two
  | .threeToOne => .three

/-- Final state of a directed process leg. -/
def CycleLeg.finish : CycleLeg → StateLabel
  | .oneToTwo => .two
  | .twoToThree => .three
  | .threeToOne => .one

/-- Thermodynamic character and direction of the three processes. -/
inductive ProcessKind where
  | isochoricHeating
  | isothermalExpansion
  | isobaricCompression
  deriving DecidableEq, Repr

/-- Orientation of the closed path in the pressure--volume plane. -/
inductive CycleOrientation where
  | clockwise
  | counterclockwise
  deriving DecidableEq, Repr

/-- Pressure, volume, absolute temperature, and internal energy at one state. -/
structure ThermodynamicState where
  pressure : PressureQuantity
  volume : VolumeQuantity
  temperature : Temperature
  internalEnergy : EnergyQuantity

/-! ## Primary-figure vocabulary -/

/-- The horizontal and vertical axes of the pressure--volume image. -/
inductive FigureAxis where
  | horizontal
  | vertical
  deriving DecidableEq, Repr

/-- Physical quantity assigned to each figure axis. -/
inductive AxisQuantity where
  | volume
  | pressure
  deriving DecidableEq, Repr

/-- Literal mathematical symbols printed at the ends of the axes. -/
inductive AxisSymbol where
  | V
  | p
  deriving DecidableEq, Repr

/-- Symbolic pressure ticks visible on the vertical axis. -/
inductive PressureTickLabel where
  | zero
  | P
  | twoP
  deriving DecidableEq, Fintype, Repr

/-- Symbolic volume ticks visible on the horizontal axis. -/
inductive VolumeTickLabel where
  | zero
  | V
  | twoV
  deriving DecidableEq, Fintype, Repr

/-- The two dashed isotherm labels visible in the image. -/
inductive IsothermLabel where
  | T
  | twoT
  deriving DecidableEq, Fintype, Repr

/-- Geometric appearance of a directed leg in the plot. -/
inductive PathShape where
  | vertical
  | curvedDownwardRight
  | horizontal
  deriving DecidableEq, Repr

/-- Direction in which a displayed arrowhead points. -/
inductive ArrowDirection where
  | up
  | downAndRight
  | left
  deriving DecidableEq, Repr

/-- Literal visual content of the supplied pressure--volume raster. -/
structure PressureVolumeFigure where
  axisQuantity : FigureAxis → AxisQuantity
  axisSymbol : FigureAxis → AxisSymbol
  pressureTickVisible : PressureTickLabel → Bool
  volumeTickVisible : VolumeTickLabel → Bool
  stateLabelVisible : StateLabel → Bool
  isothermVisible : IsothermLabel → Bool
  stateOnIsotherm : IsothermLabel → StateLabel → Bool
  pathStart : CycleLeg → StateLabel
  pathFinish : CycleLeg → StateLabel
  pathShape : CycleLeg → PathShape
  arrowVisible : CycleLeg → Bool
  arrowDirection : CycleLeg → ArrowDirection

/-!
Independent physical data for the working sample and one traversal of its
cycle.  Heat is positive into the gas and work is positive when done by the
gas.  Reference `P`, `V`, and `T` are the quantities named by the figure.
No net work, heat input, efficiency, or answer choice is stored as a field.
-/
structure HeatEngineCycle where
  gasModel : GasModel
  deviceRole : DeviceRole
  sameClosedSample : Bool
  processRegime : ProcessRegime
  orientation : CycleOrientation
  amountOfSubstanceMoles : ℝ
  molarGasConstantJoulesPerMoleKelvin : ℝ
  referencePressure : PressureQuantity
  referenceVolume : VolumeQuantity
  referenceTemperature : Temperature
  stateAt : StateLabel → ThermodynamicState
  processKind : CycleLeg → ProcessKind
  workDoneByGas : CycleLeg → EnergyQuantity
  heatTransferredIntoGas : CycleLeg → EnergyQuantity
  figure : PressureVolumeFigure

/-! ## Problem-statement and figure/data assumptions -/

/-- The prose description of the closed, directed monatomic-gas engine cycle. -/
structure MatchesProblemStatement (setup : HeatEngineCycle) : Prop where
  gasIsMonatomicIdeal : setup.gasModel = .monatomicIdealGas
  deviceIsHeatEngine : setup.deviceRole = .heatEngine
  usesSameClosedSample : setup.sameClosedSample = true
  firstLegIsIsochoricHeating :
    setup.processKind .oneToTwo = .isochoricHeating
  secondLegIsIsothermalExpansion :
    setup.processKind .twoToThree = .isothermalExpansion
  thirdLegIsIsobaricCompression :
    setup.processKind .threeToOne = .isobaricCompression
  firstStepDoublesPressure :
    pressureInPascals (setup.stateAt .two).pressure =
      2 * pressureInPascals (setup.stateAt .one).pressure
  secondStepRestoresInitialPressure :
    (setup.stateAt .three).pressure = (setup.stateAt .one).pressure
  cycleRunsClockwise : setup.orientation = .clockwise

/-!
Transcription of the primary bitmap.  The scalar coordinate equalities are
calibrated readouts of dimensionful states and reference quantities; none is
an energy, efficiency, or answer value.
-/
structure MatchesPrimaryPressureVolumeFigure
    (setup : HeatEngineCycle) : Prop where
  horizontalAxisIsVolume :
    setup.figure.axisQuantity .horizontal = .volume
  verticalAxisIsPressure :
    setup.figure.axisQuantity .vertical = .pressure
  horizontalAxisSymbolIsV : setup.figure.axisSymbol .horizontal = .V
  verticalAxisSymbolIsP : setup.figure.axisSymbol .vertical = .p
  everyPressureTickIsVisible :
    ∀ tick, setup.figure.pressureTickVisible tick = true
  everyVolumeTickIsVisible :
    ∀ tick, setup.figure.volumeTickVisible tick = true
  everyStateLabelIsVisible :
    ∀ state, setup.figure.stateLabelVisible state = true
  bothIsothermsAreVisible :
    ∀ label, setup.figure.isothermVisible label = true
  stateOneLiesOnTIsotherm :
    setup.figure.stateOnIsotherm .T .one = true
  stateTwoLiesOnTwoTIsotherm :
    setup.figure.stateOnIsotherm .twoT .two = true
  stateThreeLiesOnTwoTIsotherm :
    setup.figure.stateOnIsotherm .twoT .three = true
  stateOneCoordinates :
    pressureInPascals (setup.stateAt .one).pressure =
        pressureInPascals setup.referencePressure ∧
      volumeInCubicMeters (setup.stateAt .one).volume =
        volumeInCubicMeters setup.referenceVolume ∧
      temperatureInKelvins (setup.stateAt .one).temperature =
        temperatureInKelvins setup.referenceTemperature
  stateTwoCoordinates :
    pressureInPascals (setup.stateAt .two).pressure =
        2 * pressureInPascals setup.referencePressure ∧
      volumeInCubicMeters (setup.stateAt .two).volume =
        volumeInCubicMeters setup.referenceVolume ∧
      temperatureInKelvins (setup.stateAt .two).temperature =
        2 * temperatureInKelvins setup.referenceTemperature
  stateThreeCoordinates :
    pressureInPascals (setup.stateAt .three).pressure =
        pressureInPascals setup.referencePressure ∧
      volumeInCubicMeters (setup.stateAt .three).volume =
        2 * volumeInCubicMeters setup.referenceVolume ∧
      temperatureInKelvins (setup.stateAt .three).temperature =
        2 * temperatureInKelvins setup.referenceTemperature
  displayedArrowEndpoints : ∀ leg,
    setup.figure.pathStart leg = leg.start ∧
      setup.figure.pathFinish leg = leg.finish
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

/-! ## Modelling regime, physical branch, and governing laws -/

/-- Quasistatic equilibrium-path model implicit in the displayed `p`--`V` cycle. -/
structure UsesQuasistaticEquilibriumModel
    (setup : HeatEngineCycle) : Prop where
  followsQuasistaticEquilibriumPath :
    setup.processRegime = .quasistaticEquilibriumPath

/-- Positivity assumptions selecting the physical ideal-gas branch. -/
structure HasPhysicalCycleParameters (setup : HeatEngineCycle) : Prop where
  amountOfSubstancePositive : 0 < setup.amountOfSubstanceMoles
  molarGasConstantPositive :
    0 < setup.molarGasConstantJoulesPerMoleKelvin
  referencePressurePositive :
    0 < pressureInPascals setup.referencePressure
  referenceVolumePositive :
    0 < volumeInCubicMeters setup.referenceVolume
  referenceTemperaturePositive :
    0 < temperatureInKelvins setup.referenceTemperature
  statePressurePositive : ∀ state,
    0 < pressureInPascals (setup.stateAt state).pressure
  stateVolumePositive : ∀ state,
    0 < volumeInCubicMeters (setup.stateAt state).volume
  stateTemperaturePositive : ∀ state,
    0 < temperatureInKelvins (setup.stateAt state).temperature

/-!
Unit-aware macroscopic laws for this closed monatomic ideal-gas cycle:

* `pV = nRT` and `U = (3/2)nRT` at each equilibrium state;
* `Q = ΔU + W_by` on every directed leg;
* zero isochoric work;
* logarithmic work `nRT log(V_f/V_i)` on the isothermal expansion; and
* constant-pressure work `p(V_f - V_i)` on the return compression.

The Physlib theorem `IdealGas.ideal_gas_law` is intentionally not used: it is
a unitless statistical-mechanics result with `R = 1`, whereas these laws relate
dimensionful macroscopic state readouts.  No law field fixes net work, heat
input, thermal efficiency, `13.4%`, or answer C.
-/
structure SatisfiesMonatomicIdealGasCycleLaws
    (setup : HeatEngineCycle) : Prop where
  idealGasLaw : ∀ state,
    pressureInPascals (setup.stateAt state).pressure *
        volumeInCubicMeters (setup.stateAt state).volume =
      setup.amountOfSubstanceMoles *
        setup.molarGasConstantJoulesPerMoleKelvin *
          temperatureInKelvins (setup.stateAt state).temperature
  monatomicInternalEnergyLaw : ∀ state,
    energyInJoules (setup.stateAt state).internalEnergy =
      (3 / 2 : ℝ) * setup.amountOfSubstanceMoles *
        setup.molarGasConstantJoulesPerMoleKelvin *
          temperatureInKelvins (setup.stateAt state).temperature
  firstLawOnEveryLeg : ∀ leg,
    energyInJoules (setup.heatTransferredIntoGas leg) =
      energyInJoules (setup.stateAt leg.finish).internalEnergy -
          energyInJoules (setup.stateAt leg.start).internalEnergy +
        energyInJoules (setup.workDoneByGas leg)
  isochoricFirstLegVolume :
    (setup.stateAt .one).volume = (setup.stateAt .two).volume
  isochoricFirstLegWork :
    energyInJoules (setup.workDoneByGas .oneToTwo) = 0
  isothermalSecondLegTemperature :
    (setup.stateAt .two).temperature = (setup.stateAt .three).temperature
  isothermalSecondLegWork :
    energyInJoules (setup.workDoneByGas .twoToThree) =
      setup.amountOfSubstanceMoles *
        setup.molarGasConstantJoulesPerMoleKelvin *
          temperatureInKelvins (setup.stateAt .two).temperature *
            Real.log
              (volumeInCubicMeters (setup.stateAt .three).volume /
                volumeInCubicMeters (setup.stateAt .two).volume)
  isobaricThirdLegPressure :
    (setup.stateAt .three).pressure = (setup.stateAt .one).pressure
  isobaricThirdLegWork :
    energyInJoules (setup.workDoneByGas .threeToOne) =
      pressureInPascals (setup.stateAt .one).pressure *
        (volumeInCubicMeters (setup.stateAt .one).volume -
          volumeInCubicMeters (setup.stateAt .three).volume)

/-! ## Derived cycle accounting and thermal efficiency -/

/-- The positive `pV` energy scale at state `1`, expressed in joules. -/
def basePressureVolumeScaleInJoules (setup : HeatEngineCycle) : ℝ :=
  pressureInPascals (setup.stateAt .one).pressure *
    volumeInCubicMeters (setup.stateAt .one).volume

/-- Net work done by the gas over one complete traversal. -/
def netWorkByGasInJoules (setup : HeatEngineCycle) : ℝ :=
  energyInJoules (setup.workDoneByGas .oneToTwo) +
    energyInJoules (setup.workDoneByGas .twoToThree) +
      energyInJoules (setup.workDoneByGas .threeToOne)

/-- Positive part of a signed heat transfer into the gas. -/
def positiveHeatInJoules (heat : EnergyQuantity) : ℝ :=
  max (energyInJoules heat) 0

/-- Total heat absorbed by the gas during one cycle. -/
def totalHeatInputInJoules (setup : HeatEngineCycle) : ℝ :=
  positiveHeatInJoules (setup.heatTransferredIntoGas .oneToTwo) +
    positiveHeatInJoules (setup.heatTransferredIntoGas .twoToThree) +
      positiveHeatInJoules (setup.heatTransferredIntoGas .threeToOne)

/-- Dimensionless thermal efficiency `W_net / Q_in`. -/
def thermalEfficiency (setup : HeatEngineCycle) : ℝ :=
  netWorkByGasInJoules setup / totalHeatInputInJoules setup

/-!
The governing laws and relative figure coordinates determine all leg energies.
Writing `E₀ = P V`, one obtains

* `W = (0, 2 E₀ log 2, -E₀)`, and
* `Q = (3E₀/2, 2 E₀ log 2, -5E₀/2)`.

These are derived conclusions, not assumptions used to define the setup.
-/
lemma cycleEnergyAccounting
    (setup : HeatEngineCycle)
    (_scenario : MatchesProblemStatement setup)
    (_figure : MatchesPrimaryPressureVolumeFigure setup)
    (_model : UsesQuasistaticEquilibriumModel setup)
    (_physical : HasPhysicalCycleParameters setup)
    (_laws : SatisfiesMonatomicIdealGasCycleLaws setup) :
    energyInJoules (setup.workDoneByGas .oneToTwo) = 0 ∧
      energyInJoules (setup.workDoneByGas .twoToThree) =
        2 * basePressureVolumeScaleInJoules setup * Real.log 2 ∧
      energyInJoules (setup.workDoneByGas .threeToOne) =
        -basePressureVolumeScaleInJoules setup ∧
      energyInJoules (setup.heatTransferredIntoGas .oneToTwo) =
        (3 / 2 : ℝ) * basePressureVolumeScaleInJoules setup ∧
      energyInJoules (setup.heatTransferredIntoGas .twoToThree) =
        2 * basePressureVolumeScaleInJoules setup * Real.log 2 ∧
      energyInJoules (setup.heatTransferredIntoGas .threeToOne) =
        -(5 / 2 : ℝ) * basePressureVolumeScaleInJoules setup ∧
      netWorkByGasInJoules setup =
        basePressureVolumeScaleInJoules setup * (2 * Real.log 2 - 1) ∧
      totalHeatInputInJoules setup =
        basePressureVolumeScaleInJoules setup *
          (2 * Real.log 2 + 3 / 2) := by
  have hT₁ :
      temperatureInKelvins (setup.stateAt .one).temperature =
        temperatureInKelvins setup.referenceTemperature :=
    _figure.stateOneCoordinates.2.2
  have hT₂ :
      temperatureInKelvins (setup.stateAt .two).temperature =
        2 * temperatureInKelvins setup.referenceTemperature :=
    _figure.stateTwoCoordinates.2.2
  have hT₃ :
      temperatureInKelvins (setup.stateAt .three).temperature =
        2 * temperatureInKelvins setup.referenceTemperature :=
    _figure.stateThreeCoordinates.2.2
  have hv₁ :
      volumeInCubicMeters (setup.stateAt .one).volume =
        volumeInCubicMeters setup.referenceVolume :=
    _figure.stateOneCoordinates.2.1
  have hv₂ :
      volumeInCubicMeters (setup.stateAt .two).volume =
        volumeInCubicMeters setup.referenceVolume :=
    _figure.stateTwoCoordinates.2.1
  have hv₃ :
      volumeInCubicMeters (setup.stateAt .three).volume =
        2 * volumeInCubicMeters setup.referenceVolume :=
    _figure.stateThreeCoordinates.2.1
  have hscale :
      basePressureVolumeScaleInJoules setup =
        setup.amountOfSubstanceMoles *
          setup.molarGasConstantJoulesPerMoleKelvin *
            temperatureInKelvins setup.referenceTemperature := by
    simpa [basePressureVolumeScaleInJoules, hT₁] using
      _laws.idealGasLaw .one
  have hscale_pos : 0 < basePressureVolumeScaleInJoules setup := by
    exact mul_pos (_physical.statePressurePositive .one)
      (_physical.stateVolumePositive .one)
  have hvolumeRatio :
      volumeInCubicMeters (setup.stateAt .three).volume /
          volumeInCubicMeters (setup.stateAt .two).volume =
        2 := by
    rw [hv₃, hv₂]
    field_simp [ne_of_gt _physical.referenceVolumePositive]
  have hW₁ :
      energyInJoules (setup.workDoneByGas .oneToTwo) = 0 :=
    _laws.isochoricFirstLegWork
  have hW₂ :
      energyInJoules (setup.workDoneByGas .twoToThree) =
        2 * basePressureVolumeScaleInJoules setup * Real.log 2 := by
    rw [_laws.isothermalSecondLegWork, hT₂, hvolumeRatio]
    calc
      setup.amountOfSubstanceMoles *
              setup.molarGasConstantJoulesPerMoleKelvin *
            (2 * temperatureInKelvins setup.referenceTemperature) *
          Real.log 2 =
          2 *
              (setup.amountOfSubstanceMoles *
                setup.molarGasConstantJoulesPerMoleKelvin *
                  temperatureInKelvins setup.referenceTemperature) *
            Real.log 2 := by ring
      _ = 2 * basePressureVolumeScaleInJoules setup * Real.log 2 := by
        rw [← hscale]
  have hW₃ :
      energyInJoules (setup.workDoneByGas .threeToOne) =
        -basePressureVolumeScaleInJoules setup := by
    rw [_laws.isobaricThirdLegWork, hv₁, hv₃]
    simp only [basePressureVolumeScaleInJoules, hv₁]
    ring
  have hU₁ :
      energyInJoules (setup.stateAt .one).internalEnergy =
        (3 / 2 : ℝ) * basePressureVolumeScaleInJoules setup := by
    rw [_laws.monatomicInternalEnergyLaw, hT₁]
    nlinarith [hscale]
  have hU₂ :
      energyInJoules (setup.stateAt .two).internalEnergy =
        3 * basePressureVolumeScaleInJoules setup := by
    rw [_laws.monatomicInternalEnergyLaw, hT₂]
    nlinarith [hscale]
  have hU₃ :
      energyInJoules (setup.stateAt .three).internalEnergy =
        3 * basePressureVolumeScaleInJoules setup := by
    rw [_laws.monatomicInternalEnergyLaw, hT₃]
    nlinarith [hscale]
  have hQ₁ :
      energyInJoules (setup.heatTransferredIntoGas .oneToTwo) =
        (3 / 2 : ℝ) * basePressureVolumeScaleInJoules setup := by
    rw [_laws.firstLawOnEveryLeg, CycleLeg.start, CycleLeg.finish,
      hU₁, hU₂, hW₁]
    ring
  have hQ₂ :
      energyInJoules (setup.heatTransferredIntoGas .twoToThree) =
        2 * basePressureVolumeScaleInJoules setup * Real.log 2 := by
    simpa [CycleLeg.start, CycleLeg.finish, hU₂, hU₃, hW₂] using
      _laws.firstLawOnEveryLeg .twoToThree
  have hQ₃ :
      energyInJoules (setup.heatTransferredIntoGas .threeToOne) =
        -(5 / 2 : ℝ) * basePressureVolumeScaleInJoules setup := by
    rw [_laws.firstLawOnEveryLeg, CycleLeg.start, CycleLeg.finish,
      hU₁, hU₃, hW₃]
    ring
  have hlog_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hQ₁_pos :
      0 < (3 / 2 : ℝ) * basePressureVolumeScaleInJoules setup := by
    positivity
  have hQ₂_pos :
      0 < 2 * basePressureVolumeScaleInJoules setup * Real.log 2 := by
    positivity
  have hQ₃_nonpos :
      -(5 / 2 : ℝ) * basePressureVolumeScaleInJoules setup ≤ 0 := by
    nlinarith
  have hnet :
      netWorkByGasInJoules setup =
        basePressureVolumeScaleInJoules setup *
          (2 * Real.log 2 - 1) := by
    rw [netWorkByGasInJoules, hW₁, hW₂, hW₃]
    ring
  have hheat :
      totalHeatInputInJoules setup =
        basePressureVolumeScaleInJoules setup *
          (2 * Real.log 2 + 3 / 2) := by
    simp only [totalHeatInputInJoules, positiveHeatInJoules, hQ₁, hQ₂, hQ₃]
    rw [max_eq_left hQ₁_pos.le, max_eq_left hQ₂_pos.le,
      max_eq_right hQ₃_nonpos]
    ring
  exact ⟨hW₁, hW₂, hW₃, hQ₁, hQ₂, hQ₃, hnet, hheat⟩

/-! ## Displayed choices and main target -/

/-- Labels of the four efficiencies displayed by the source problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Dimensionless efficiency printed beside each answer label. -/
def displayedEfficiency : AnswerChoice → ℝ
  | .A => 77 / 500
  | .B => 18 / 125
  | .C => 67 / 500
  | .D => 31 / 250

/-- Answer label recorded in the supplied dataset metadata. -/
def recordedDatasetAnswer : AnswerChoice := .C

/-- A displayed efficiency is at least as close as every other choice. -/
def IsClosestDisplayedEfficiency
    (efficiency : ℝ) (choice : AnswerChoice) : Prop :=
  ∀ candidate,
    |efficiency - displayedEfficiency choice| ≤
      |efficiency - displayedEfficiency candidate|

/-- The specified answer is the unique closest displayed efficiency. -/
def IsUniqueClosestDisplayedEfficiency
    (efficiency : ℝ) (choice : AnswerChoice) : Prop :=
  IsClosestDisplayedEfficiency efficiency choice ∧
    ∀ other,
      IsClosestDisplayedEfficiency efficiency other → other = choice

/-!
For the monatomic ideal gas, the common positive factor `E₀ = PV` cancels:

`η = (2 log 2 - 1) / (2 log 2 + 3/2)
   = (4 log 2 - 2) / (4 log 2 + 3)`.

This is approximately `0.1338`, so the displayed `13.4%` is uniquely closest
and selects the recorded answer C.  The exact value is not identified with the
rounded decimal.

Blueprint label: `thm:physics:phyx_mini_0482:target`.
-/
theorem thermalEfficiency_eq_exactValue_and_selectsAnswerC
    (setup : HeatEngineCycle)
    (_scenario : MatchesProblemStatement setup)
    (_figure : MatchesPrimaryPressureVolumeFigure setup)
    (_model : UsesQuasistaticEquilibriumModel setup)
    (_physical : HasPhysicalCycleParameters setup)
    (_laws : SatisfiesMonatomicIdealGasCycleLaws setup) :
    thermalEfficiency setup =
        (4 * Real.log 2 - 2) / (4 * Real.log 2 + 3) ∧
      IsUniqueClosestDisplayedEfficiency
        (thermalEfficiency setup) recordedDatasetAnswer := by
  rcases cycleEnergyAccounting setup _scenario _figure _model _physical _laws with
    ⟨_, _, _, _, _, _, hnet, hheat⟩
  have hscale_pos : 0 < basePressureVolumeScaleInJoules setup := by
    exact mul_pos (_physical.statePressurePositive .one)
      (_physical.stateVolumePositive .one)
  have hlog_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hden₂ : 0 < 2 * Real.log 2 + 3 / 2 := by positivity
  have hden₄ : 0 < 4 * Real.log 2 + 3 := by positivity
  let η : ℝ := (4 * Real.log 2 - 2) / (4 * Real.log 2 + 3)
  have heff : thermalEfficiency setup = η := by
    rw [thermalEfficiency, hnet, hheat]
    dsimp [η]
    field_simp [ne_of_gt hscale_pos, ne_of_gt hden₂, ne_of_gt hden₄]
    ring
  have hlog_lower : (24 / 35 : ℝ) < Real.log 2 := by
    have h₁ :=
      Real.lt_log_one_add_of_pos (x := (1 / 3 : ℝ)) (by norm_num)
    have h₂ :=
      Real.lt_log_one_add_of_pos (x := (1 / 2 : ℝ)) (by norm_num)
    norm_num at h₁ h₂
    have hsum :
        (24 / 35 : ℝ) < Real.log (4 / 3) + Real.log (3 / 2) := by
      linarith
    rw [← Real.log_mul (by norm_num : (4 / 3 : ℝ) ≠ 0)
      (by norm_num : (3 / 2 : ℝ) ≠ 0)] at hsum
    norm_num at hsum
    exact hsum
  have hlog_upper : Real.log 2 < (7 / 10 : ℝ) := by
    have hbound :=
      Real.exp_bound (x := (-7 / 10 : ℝ)) (n := 6)
        (by norm_num [abs_of_nonpos]) (by norm_num)
    rw [abs_le] at hbound
    rcases hbound with ⟨_, hbound⟩
    norm_num [Finset.sum_range_succ, abs_of_nonpos] at hbound
    have hneg : Real.exp (-7 / 10 : ℝ) < 1 / 2 := by
      linarith
    rw [show (-7 / 10 : ℝ) = -(7 / 10 : ℝ) by norm_num,
      Real.exp_neg] at hneg
    rw [inv_lt_iff_one_lt_mul₀ (Real.exp_pos _)] at hneg
    apply (Real.log_lt_iff_lt_exp (by norm_num : (0 : ℝ) < 2)).2
    linarith
  have hη_lower : (129 / 1000 : ℝ) < η := by
    dsimp [η]
    rw [lt_div_iff₀ hden₄]
    nlinarith
  have hη_upper : η < (139 / 1000 : ℝ) := by
    dsimp [η]
    rw [div_lt_iff₀ hden₄]
    nlinarith
  have hC : |η - 67 / 500| < (1 / 200 : ℝ) := by
    rw [abs_lt]
    constructor <;> norm_num at * <;> linarith
  have hC_lt_A :
      |η - displayedEfficiency .C| < |η - displayedEfficiency .A| := by
    change |η - 67 / 500| < |η - 77 / 500|
    rw [abs_of_neg (by norm_num at *; linarith : η - 77 / 500 < 0)]
    norm_num at *
    linarith
  have hC_lt_B :
      |η - displayedEfficiency .C| < |η - displayedEfficiency .B| := by
    change |η - 67 / 500| < |η - 18 / 125|
    rw [abs_of_neg (by norm_num at *; linarith : η - 18 / 125 < 0)]
    norm_num at *
    linarith
  have hC_lt_D :
      |η - displayedEfficiency .C| < |η - displayedEfficiency .D| := by
    change |η - 67 / 500| < |η - 31 / 250|
    rw [abs_of_pos (by norm_num at *; linarith : 0 < η - 31 / 250)]
    norm_num at *
    linarith
  refine ⟨heff, ?_⟩
  rw [heff]
  change IsUniqueClosestDisplayedEfficiency η .C
  constructor
  · intro candidate
    fin_cases candidate
    · exact hC_lt_A.le
    · exact hC_lt_B.le
    · exact le_rfl
    · exact hC_lt_D.le
  · intro other hother
    fin_cases other
    · exfalso
      exact (not_le_of_gt hC_lt_A) (hother .C)
    · exfalso
      exact (not_le_of_gt hC_lt_B) (hother .C)
    · rfl
    · exfalso
      exact (not_le_of_gt hC_lt_D) (hother .C)

end PhyXMiniProblems.ProblemPhyXMini0482
