import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Physlib.Thermodynamics.Temperature.Basic
import Physlib.Thermodynamics.Temperature.TemperatureUnits
import Physlib.Units.WithDim.Energy
import Physlib.Units.WithDim.Pressure

/- USER: The assigned source file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0434

open Dimension

/-!
# Efficiency of a three-leg diatomic-gas heat engine

The primary pressure-volume bitmap, used in preference to its inconsistent
auxiliary caption, shows the directed cycle

* `1 → 2`: adiabatic compression along a curve;
* `2 → 3`: isobaric expansion at `400 kPa` along a horizontal segment;
* `3 → 1`: isochoric cooling at `V_max` along a vertical segment.

The plotted coordinates are `p₁ = 100 kPa`, `p₂ = p₃ = 400 kPa`,
`V₂ = 1000 cm³`, and `V₁ = V₃ = V_max`.  The working substance is
`0.020 mol` of a diatomic gas.

Pressure, volume, temperature, heat, work, and internal energy are physical
quantities.  Real scalars occur only as explicitly unit-labelled readouts,
dimensionless ratios, and displayed efficiencies.
-/

/-! ## Physical quantities and calibrated readouts -/

/-- Physical gas volume, carrying dimension `L³` and a nonnegative value. -/
abbrev VolumeQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * L𝓭 * L𝓭) NNReal)

/-- Physical gas pressure, represented by Physlib's dimensionful type. -/
abbrev PressureQuantity : Type := DimPressure

/-- Absolute thermodynamic temperature. -/
abbrev TemperatureQuantity : Type := Temperature

/-- Signed heat, work, or internal energy. -/
abbrev EnergyQuantity : Type := DimEnergy

/--
Measurement interface for an abstract amount-of-substance type.  Physlib's
unit system currently has no amount-of-substance base dimension, so the
physical carrier remains abstract and only its calibrated molar readout is
exposed.
-/
structure MolarMeasurement (AmountOfSubstance : Type) where
  inMoles : AmountOfSubstance → ℝ

/-- Read a physical pressure in pascals. -/
def pressureInPascals (pressure : PressureQuantity) : ℝ :=
  (pressure UnitChoices.SI).val

/-- Pressure readout in the kilopascals printed on the vertical axis. -/
def pressureInKilopascals (pressure : PressureQuantity) : ℝ :=
  pressureInPascals pressure / 1000

/-- Read a physical volume in cubic metres. -/
def volumeInCubicMeters (volume : VolumeQuantity) : ℝ :=
  ((volume UnitChoices.SI).val : ℝ)

/-- Volume readout in the cubic centimetres printed on the horizontal axis. -/
def volumeInCubicCentimeters (volume : VolumeQuantity) : ℝ :=
  1000000 * volumeInCubicMeters volume

/-- Read a signed physical energy in joules. -/
def energyInJoules (energy : EnergyQuantity) : ℝ :=
  (energy UnitChoices.SI).val /
    (DimEnergy.joule UnitChoices.SI).val

/-- Convert Physlib's stored absolute temperature to a kelvin readout. -/
def temperatureInKelvins
    (storageUnit : TemperatureUnit) (temperature : TemperatureQuantity) : ℝ :=
  let unitRatio : NNReal := storageUnit / TemperatureUnit.kelvin
  temperature.toReal * (unitRatio : ℝ)

/-! ## Gas, thermodynamic states, cycle legs, and diagram -/

/-- Molecular type of the working substance. -/
inductive MolecularType where
  | monatomic
  | diatomic
  | other
  deriving DecidableEq, Repr

/-- The three numerical state labels printed in the p-V diagram. -/
inductive StateLabel where
  | state1
  | state2
  | state3
  deriving DecidableEq, Fintype, Repr

/-- Directed legs of the closed engine cycle. -/
inductive CycleLeg where
  | oneToTwo
  | twoToThree
  | threeToOne
  deriving DecidableEq, Fintype, Repr

/-- Initial state of each directed cycle leg. -/
def legStart : CycleLeg → StateLabel
  | .oneToTwo => .state1
  | .twoToThree => .state2
  | .threeToOne => .state3

/-- Final state of each directed cycle leg. -/
def legFinish : CycleLeg → StateLabel
  | .oneToTwo => .state2
  | .twoToThree => .state3
  | .threeToOne => .state1

/-- Thermodynamic process classifications used by the cycle. -/
inductive ProcessKind where
  | adiabatic
  | isobaric
  | isochoric
  deriving DecidableEq, Repr

/-- Qualitative shape of a directed segment in the primary bitmap. -/
inductive SegmentShape where
  | curved
  | horizontal
  | vertical
  deriving DecidableEq, Repr

/-- Physical quantity associated with a graph axis. -/
inductive AxisQuantity where
  | volume
  | pressure
  deriving DecidableEq, Repr

/-- Unit printed on the horizontal volume axis. -/
inductive VolumeDisplayUnit where
  | cubicCentimeter
  deriving DecidableEq, Repr

/-- Unit printed on the vertical pressure axis. -/
inductive PressureDisplayUnit where
  | kilopascal
  deriving DecidableEq, Repr

/-- Pressure, volume, and absolute temperature at a labelled state. -/
structure ThermodynamicState where
  pressure : PressureQuantity
  volume : VolumeQuantity
  temperature : TemperatureQuantity

/--
An abstract physical gas sample together with calibrated constitutive
readouts.  Heat capacities are in `J/(mol·K)` and the adiabatic index is
dimensionless.
-/
structure GasSample (AmountOfSubstance : Type) where
  molecularType : MolecularType
  amount : AmountOfSubstance
  amountMeasurement : MolarMeasurement AmountOfSubstance
  molarGasConstantJoulesPerMoleKelvin : ℝ
  molarHeatCapacityAtConstantVolumeJoulesPerMoleKelvin : ℝ
  molarHeatCapacityAtConstantPressureJoulesPerMoleKelvin : ℝ
  adiabaticIndex : ℝ

/-- Molar readout of the working gas amount. -/
def GasSample.amountInMoles {AmountOfSubstance : Type}
    (gas : GasSample AmountOfSubstance) : ℝ :=
  gas.amountMeasurement.inMoles gas.amount

/-- Raw axes, coordinates, labels, arrows, shapes, and annotation in the image. -/
structure PressureVolumeDiagram where
  horizontalAxisQuantity : AxisQuantity
  verticalAxisQuantity : AxisQuantity
  horizontalAxisUnit : VolumeDisplayUnit
  verticalAxisUnit : PressureDisplayUnit
  horizontalAxisMinimumCubicCentimeters : ℝ
  horizontalAxisMaximumCubicCentimeters : ℝ
  verticalAxisMinimumKilopascals : ℝ
  verticalAxisMaximumKilopascals : ℝ
  volumeCoordinateCubicCentimeters : StateLabel → ℝ
  pressureCoordinateKilopascals : StateLabel → ℝ
  vMaxMarkerCubicCentimeters : ℝ
  stateLabelShown : StateLabel → Bool
  arrowStart : CycleLeg → StateLabel
  arrowFinish : CycleLeg → StateLabel
  segmentShape : CycleLeg → SegmentShape
  displayedProcessAnnotation : CycleLeg → Option ProcessKind

/--
The complete heat-engine cycle.  Heat transferred to the gas and work done by
the gas are signed.  Reservoir heats and net work output are positive physical
energy quantities under the physical-domain hypotheses below.
-/
structure HeatEngineSetup (AmountOfSubstance : Type) where
  gas : GasSample AmountOfSubstance
  temperatureStorageUnit : TemperatureUnit
  state : StateLabel → ThermodynamicState
  internalEnergy : StateLabel → EnergyQuantity
  processKind : CycleLeg → ProcessKind
  heatTransferredToGas : CycleLeg → EnergyQuantity
  workDoneByGas : CycleLeg → EnergyQuantity
  heatAbsorbedFromHotReservoir : EnergyQuantity
  heatRejectedToColdReservoir : EnergyQuantity
  netWorkOutput : EnergyQuantity
  thermalEfficiency : ℝ
  figure : PressureVolumeDiagram

/-! ## Scenario and primary-image readouts -/

/--
Facts stated by the prose: a heat-engine cycle with `0.020 mol` of a diatomic
gas and the three indicated process types.  No efficiency value occurs here.
-/
structure MatchesProblemStatement {AmountOfSubstance : Type}
    (setup : HeatEngineSetup AmountOfSubstance) : Prop where
  workingSubstanceIsDiatomic : setup.gas.molecularType = .diatomic
  workingSubstanceAmountMoles : setup.gas.amountInMoles = 1 / 50
  temperaturesStoredInKelvins :
    setup.temperatureStorageUnit = TemperatureUnit.kelvin
  legOneToTwoIsAdiabatic : setup.processKind .oneToTwo = .adiabatic
  legTwoToThreeIsIsobaric : setup.processKind .twoToThree = .isobaric
  legThreeToOneIsIsochoric : setup.processKind .threeToOne = .isochoric

/-!
Primary-image evidence.  In particular, this records a horizontal isobaric
`2 → 3` leg and a vertical isochoric `3 → 1` leg, correcting the reversed
process names in the auxiliary caption.
-/
structure MatchesPrimaryPressureVolumeFigure {AmountOfSubstance : Type}
    (setup : HeatEngineSetup AmountOfSubstance) : Prop where
  horizontalAxisIsVolume : setup.figure.horizontalAxisQuantity = .volume
  verticalAxisIsPressure : setup.figure.verticalAxisQuantity = .pressure
  horizontalAxisUsesCubicCentimeters :
    setup.figure.horizontalAxisUnit = .cubicCentimeter
  verticalAxisUsesKilopascals :
    setup.figure.verticalAxisUnit = .kilopascal
  horizontalAxisRange :
    setup.figure.horizontalAxisMinimumCubicCentimeters = 0 ∧
      setup.figure.horizontalAxisMaximumCubicCentimeters =
        setup.figure.vMaxMarkerCubicCentimeters
  verticalAxisRange :
    setup.figure.verticalAxisMinimumKilopascals = 0 ∧
      setup.figure.verticalAxisMaximumKilopascals = 500
  everyStateLabelIsShown :
    ∀ label : StateLabel, setup.figure.stateLabelShown label = true
  state1Coordinates :
    setup.figure.volumeCoordinateCubicCentimeters .state1 =
        setup.figure.vMaxMarkerCubicCentimeters ∧
      setup.figure.pressureCoordinateKilopascals .state1 = 100
  state2Coordinates :
    setup.figure.volumeCoordinateCubicCentimeters .state2 = 1000 ∧
      setup.figure.pressureCoordinateKilopascals .state2 = 400
  state3Coordinates :
    setup.figure.volumeCoordinateCubicCentimeters .state3 =
        setup.figure.vMaxMarkerCubicCentimeters ∧
      setup.figure.pressureCoordinateKilopascals .state3 = 400
  vMaxLiesToRightOf1000 : 1000 < setup.figure.vMaxMarkerCubicCentimeters
  coordinatesAgreeWithPhysicalStateReadouts :
    ∀ label : StateLabel,
      setup.figure.volumeCoordinateCubicCentimeters label =
          volumeInCubicCentimeters (setup.state label).volume ∧
        setup.figure.pressureCoordinateKilopascals label =
          pressureInKilopascals (setup.state label).pressure
  arrowDirections :
    ∀ leg : CycleLeg,
      setup.figure.arrowStart leg = legStart leg ∧
        setup.figure.arrowFinish leg = legFinish leg
  legOneToTwoIsCurved : setup.figure.segmentShape .oneToTwo = .curved
  legTwoToThreeIsHorizontal :
    setup.figure.segmentShape .twoToThree = .horizontal
  legThreeToOneIsVertical :
    setup.figure.segmentShape .threeToOne = .vertical
  adiabaticLabelOnLegOneToTwo :
    setup.figure.displayedProcessAnnotation .oneToTwo = some .adiabatic
  noProcessLabelOnLegTwoToThree :
    setup.figure.displayedProcessAnnotation .twoToThree = none
  noProcessLabelOnLegThreeToOne :
    setup.figure.displayedProcessAnnotation .threeToOne = none

/-! ## Physical-domain conditions and governing laws -/

/-- Positivity and range conditions selecting a physically operating engine. -/
structure HasPhysicalHeatEngineParameters {AmountOfSubstance : Type}
    (setup : HeatEngineSetup AmountOfSubstance) : Prop where
  amountPositive : 0 < setup.gas.amountInMoles
  gasConstantPositive : 0 < setup.gas.molarGasConstantJoulesPerMoleKelvin
  heatCapacityAtConstantVolumePositive :
    0 < setup.gas.molarHeatCapacityAtConstantVolumeJoulesPerMoleKelvin
  heatCapacityAtConstantPressurePositive :
    0 < setup.gas.molarHeatCapacityAtConstantPressureJoulesPerMoleKelvin
  adiabaticIndexGreaterThanOne : 1 < setup.gas.adiabaticIndex
  pressurePositive : ∀ label : StateLabel,
    0 < pressureInPascals (setup.state label).pressure
  volumePositive : ∀ label : StateLabel,
    0 < volumeInCubicMeters (setup.state label).volume
  absoluteTemperaturePositive : ∀ label : StateLabel,
    0 < temperatureInKelvins setup.temperatureStorageUnit
      (setup.state label).temperature
  heatAbsorbedPositive :
    0 < energyInJoules setup.heatAbsorbedFromHotReservoir
  heatRejectedPositive :
    0 < energyInJoules setup.heatRejectedToColdReservoir
  netWorkOutputPositive : 0 < energyInJoules setup.netWorkOutput
  efficiencyInPhysicalRange :
    0 ≤ setup.thermalEfficiency ∧ setup.thermalEfficiency ≤ 1

/-!
Governing relations for a calorically perfect diatomic ideal gas and this
three-leg cycle.  These fields state constitutive and conservation laws only;
they contain neither `0.15` nor any displayed answer value.
-/
structure SatisfiesDiatomicIdealGasCycleLaws {AmountOfSubstance : Type}
    (setup : HeatEngineSetup AmountOfSubstance) : Prop where
  diatomicConstantVolumeHeatCapacity :
    setup.gas.molarHeatCapacityAtConstantVolumeJoulesPerMoleKelvin =
      (5 / 2) * setup.gas.molarGasConstantJoulesPerMoleKelvin
  diatomicConstantPressureHeatCapacity :
    setup.gas.molarHeatCapacityAtConstantPressureJoulesPerMoleKelvin =
      (7 / 2) * setup.gas.molarGasConstantJoulesPerMoleKelvin
  adiabaticIndexIsHeatCapacityRatio :
    setup.gas.adiabaticIndex =
      setup.gas.molarHeatCapacityAtConstantPressureJoulesPerMoleKelvin /
        setup.gas.molarHeatCapacityAtConstantVolumeJoulesPerMoleKelvin
  idealGasLawAt : ∀ label : StateLabel,
    pressureInPascals (setup.state label).pressure *
        volumeInCubicMeters (setup.state label).volume =
      setup.gas.amountInMoles *
        setup.gas.molarGasConstantJoulesPerMoleKelvin *
          temperatureInKelvins setup.temperatureStorageUnit
            (setup.state label).temperature
  internalEnergyOfDiatomicIdealGasAt : ∀ label : StateLabel,
    energyInJoules (setup.internalEnergy label) =
      setup.gas.amountInMoles *
        setup.gas.molarHeatCapacityAtConstantVolumeJoulesPerMoleKelvin *
          temperatureInKelvins setup.temperatureStorageUnit
            (setup.state label).temperature
  firstLawOnEachLeg : ∀ leg : CycleLeg,
    energyInJoules (setup.internalEnergy (legFinish leg)) -
        energyInJoules (setup.internalEnergy (legStart leg)) =
      energyInJoules (setup.heatTransferredToGas leg) -
        energyInJoules (setup.workDoneByGas leg)
  adiabaticPressureVolumeRelation :
    pressureInPascals (setup.state .state1).pressure /
        pressureInPascals (setup.state .state2).pressure =
      Real.rpow
        (volumeInCubicMeters (setup.state .state2).volume /
          volumeInCubicMeters (setup.state .state1).volume)
        setup.gas.adiabaticIndex
  adiabaticLegTransfersNoHeat :
    energyInJoules (setup.heatTransferredToGas .oneToTwo) = 0
  isobaricPressureRelation :
    (setup.state .state2).pressure = (setup.state .state3).pressure
  isobaricWorkLaw :
    energyInJoules (setup.workDoneByGas .twoToThree) =
      pressureInPascals (setup.state .state2).pressure *
        (volumeInCubicMeters (setup.state .state3).volume -
          volumeInCubicMeters (setup.state .state2).volume)
  isobaricHeatLaw :
    energyInJoules (setup.heatTransferredToGas .twoToThree) =
      setup.gas.amountInMoles *
        setup.gas.molarHeatCapacityAtConstantPressureJoulesPerMoleKelvin *
          (temperatureInKelvins setup.temperatureStorageUnit
              (setup.state .state3).temperature -
            temperatureInKelvins setup.temperatureStorageUnit
              (setup.state .state2).temperature)
  isochoricVolumeRelation :
    (setup.state .state3).volume = (setup.state .state1).volume
  isochoricWorkIsZero :
    energyInJoules (setup.workDoneByGas .threeToOne) = 0
  isochoricHeatLaw :
    energyInJoules (setup.heatTransferredToGas .threeToOne) =
      setup.gas.amountInMoles *
        setup.gas.molarHeatCapacityAtConstantVolumeJoulesPerMoleKelvin *
          (temperatureInKelvins setup.temperatureStorageUnit
              (setup.state .state1).temperature -
            temperatureInKelvins setup.temperatureStorageUnit
              (setup.state .state3).temperature)
  hotReservoirHeatIsLegTwoToThree :
    energyInJoules setup.heatAbsorbedFromHotReservoir =
      energyInJoules (setup.heatTransferredToGas .twoToThree)
  coldReservoirHeatIsRejectedOnLegThreeToOne :
    energyInJoules setup.heatRejectedToColdReservoir =
      -energyInJoules (setup.heatTransferredToGas .threeToOne)
  netWorkIsSumOverCycle :
    energyInJoules setup.netWorkOutput =
      energyInJoules (setup.workDoneByGas .oneToTwo) +
        energyInJoules (setup.workDoneByGas .twoToThree) +
          energyInJoules (setup.workDoneByGas .threeToOne)
  cycleEnergyBalance :
    energyInJoules setup.netWorkOutput =
      energyInJoules setup.heatAbsorbedFromHotReservoir -
        energyInJoules setup.heatRejectedToColdReservoir
  thermalEfficiencyDefinition :
    setup.thermalEfficiency =
      energyInJoules setup.netWorkOutput /
        energyInJoules setup.heatAbsorbedFromHotReservoir

/-! ## Derived relations and final displayed answer -/

/-!
The adiabatic compression and pressure ratio `400/100 = 4` determine the
unlabelled maximum volume.  This is a derived conclusion, not figure data.
-/
lemma vMaxCubicCentimeters_from_adiabatic_compression
    {AmountOfSubstance : Type}
    (setup : HeatEngineSetup AmountOfSubstance)
    (_problem : MatchesProblemStatement setup)
    (_figure : MatchesPrimaryPressureVolumeFigure setup)
    (_physical : HasPhysicalHeatEngineParameters setup)
    (_laws : SatisfiesDiatomicIdealGasCycleLaws setup) :
    setup.figure.vMaxMarkerCubicCentimeters =
      1000 * Real.rpow 4 (5 / 7) := by
  have hp₁ :
      pressureInPascals (setup.state .state1).pressure = 100000 := by
    have hreadout :=
      (_figure.coordinatesAgreeWithPhysicalStateReadouts .state1).2
    have hp₁k := hreadout.symm.trans _figure.state1Coordinates.2
    rw [pressureInKilopascals] at hp₁k
    linarith
  have hp₂ :
      pressureInPascals (setup.state .state2).pressure = 400000 := by
    have hreadout :=
      (_figure.coordinatesAgreeWithPhysicalStateReadouts .state2).2
    have hp₂k := hreadout.symm.trans _figure.state2Coordinates.2
    rw [pressureInKilopascals] at hp₂k
    linarith
  have hv₁ :
      volumeInCubicMeters (setup.state .state1).volume =
        setup.figure.vMaxMarkerCubicCentimeters / 1000000 := by
    have hreadout :=
      (_figure.coordinatesAgreeWithPhysicalStateReadouts .state1).1
    have hv₁cc := hreadout.symm.trans _figure.state1Coordinates.1
    rw [volumeInCubicCentimeters] at hv₁cc
    linarith
  have hv₂ :
      volumeInCubicMeters (setup.state .state2).volume = 1 / 1000 := by
    have hreadout :=
      (_figure.coordinatesAgreeWithPhysicalStateReadouts .state2).1
    have hv₂cc := hreadout.symm.trans _figure.state2Coordinates.1
    rw [volumeInCubicCentimeters] at hv₂cc
    linarith
  have hγ : setup.gas.adiabaticIndex = 7 / 5 := by
    rw [_laws.adiabaticIndexIsHeatCapacityRatio,
      _laws.diatomicConstantPressureHeatCapacity,
      _laws.diatomicConstantVolumeHeatCapacity]
    have hR :
        setup.gas.molarGasConstantJoulesPerMoleKelvin ≠ 0 :=
      ne_of_gt _physical.gasConstantPositive
    field_simp
  have hvmax : 0 < setup.figure.vMaxMarkerCubicCentimeters :=
    lt_trans (by norm_num) _figure.vMaxLiesToRightOf1000
  have hadi := _laws.adiabaticPressureVolumeRelation
  rw [hp₁, hp₂, hv₁, hv₂, hγ] at hadi
  have hratio :
      Real.rpow
          (1000 / setup.figure.vMaxMarkerCubicCentimeters) (7 / 5) =
        1 / 4 := by
    have hbaseRatio :
        1000 / setup.figure.vMaxMarkerCubicCentimeters =
          (1 / 1000) /
            (setup.figure.vMaxMarkerCubicCentimeters / 1000000) := by
      field_simp
      norm_num
    calc
      Real.rpow
          (1000 / setup.figure.vMaxMarkerCubicCentimeters) (7 / 5) =
          Real.rpow
            ((1 / 1000) /
              (setup.figure.vMaxMarkerCubicCentimeters / 1000000)) (7 / 5) :=
        congrArg (fun x : ℝ => Real.rpow x (7 / 5)) hbaseRatio
      _ = 100000 / 400000 := hadi.symm
      _ = 1 / 4 := by norm_num
  have hratio_nonneg :
      0 ≤ 1000 / setup.figure.vMaxMarkerCubicCentimeters := by positivity
  have hroot_nonneg : 0 ≤ Real.rpow 4 (5 / 7) :=
    Real.rpow_nonneg (by norm_num) _
  have hroot_power :
      Real.rpow (Real.rpow 4 (5 / 7)) (7 / 5) = 4 := by
    calc
      Real.rpow (Real.rpow 4 (5 / 7)) (7 / 5) =
          Real.rpow 4 ((5 / 7) * (7 / 5)) :=
        (Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 4) _ _).symm
      _ = 4 := by norm_num
  have hratio_power :
      Real.rpow
          (setup.figure.vMaxMarkerCubicCentimeters / 1000) (7 / 5) =
        4 := by
    rw [show setup.figure.vMaxMarkerCubicCentimeters / 1000 =
      (1000 / setup.figure.vMaxMarkerCubicCentimeters)⁻¹ by
        field_simp]
    calc
      Real.rpow
          (1000 / setup.figure.vMaxMarkerCubicCentimeters)⁻¹ (7 / 5) =
          Real.rpow
            (1000 / setup.figure.vMaxMarkerCubicCentimeters) (-(7 / 5)) :=
        (Real.rpow_neg_eq_inv_rpow _ _).symm
      _ = (Real.rpow
          (1000 / setup.figure.vMaxMarkerCubicCentimeters) (7 / 5))⁻¹ :=
        Real.rpow_neg hratio_nonneg _
      _ = 4 := by rw [hratio]; norm_num
  have hbase :
      setup.figure.vMaxMarkerCubicCentimeters / 1000 =
        Real.rpow 4 (5 / 7) := by
    exact (Real.rpow_left_inj (by positivity) hroot_nonneg
      (by norm_num : (7 / 5 : ℝ) ≠ 0)).mp (hratio_power.trans hroot_power.symm)
  linarith

/-!
Using `Q_in = n C_p (T₃-T₂)`, `Q_out = n C_v (T₃-T₁)`, and the ideal-gas
law gives the exact dimensionless efficiency below.
-/
lemma thermalEfficiency_exact
    {AmountOfSubstance : Type}
    (setup : HeatEngineSetup AmountOfSubstance)
    (_problem : MatchesProblemStatement setup)
    (_figure : MatchesPrimaryPressureVolumeFigure setup)
    (_physical : HasPhysicalHeatEngineParameters setup)
    (_laws : SatisfiesDiatomicIdealGasCycleLaws setup) :
    setup.thermalEfficiency =
      1 - (15 / 28) *
        (Real.rpow 4 (5 / 7) / (Real.rpow 4 (5 / 7) - 1)) := by
  have hp₁ :
      pressureInPascals (setup.state .state1).pressure = 100000 := by
    have hreadout :=
      (_figure.coordinatesAgreeWithPhysicalStateReadouts .state1).2
    have hp₁k := hreadout.symm.trans _figure.state1Coordinates.2
    rw [pressureInKilopascals] at hp₁k
    linarith
  have hp₂ :
      pressureInPascals (setup.state .state2).pressure = 400000 := by
    have hreadout :=
      (_figure.coordinatesAgreeWithPhysicalStateReadouts .state2).2
    have hp₂k := hreadout.symm.trans _figure.state2Coordinates.2
    rw [pressureInKilopascals] at hp₂k
    linarith
  have hp₃ :
      pressureInPascals (setup.state .state3).pressure = 400000 := by
    have hreadout :=
      (_figure.coordinatesAgreeWithPhysicalStateReadouts .state3).2
    have hp₃k := hreadout.symm.trans _figure.state3Coordinates.2
    rw [pressureInKilopascals] at hp₃k
    linarith
  have hv₁ :
      volumeInCubicMeters (setup.state .state1).volume =
        setup.figure.vMaxMarkerCubicCentimeters / 1000000 := by
    have hreadout :=
      (_figure.coordinatesAgreeWithPhysicalStateReadouts .state1).1
    have hv₁cc := hreadout.symm.trans _figure.state1Coordinates.1
    rw [volumeInCubicCentimeters] at hv₁cc
    linarith
  have hv₂ :
      volumeInCubicMeters (setup.state .state2).volume = 1 / 1000 := by
    have hreadout :=
      (_figure.coordinatesAgreeWithPhysicalStateReadouts .state2).1
    have hv₂cc := hreadout.symm.trans _figure.state2Coordinates.1
    rw [volumeInCubicCentimeters] at hv₂cc
    linarith
  have hv₃ :
      volumeInCubicMeters (setup.state .state3).volume =
        setup.figure.vMaxMarkerCubicCentimeters / 1000000 := by
    have hreadout :=
      (_figure.coordinatesAgreeWithPhysicalStateReadouts .state3).1
    have hv₃cc := hreadout.symm.trans _figure.state3Coordinates.1
    rw [volumeInCubicCentimeters] at hv₃cc
    linarith
  have hVmax :=
    vMaxCubicCentimeters_from_adiabatic_compression
      setup _problem _figure _physical _laws
  have hIG₁ := _laws.idealGasLawAt .state1
  have hIG₂ := _laws.idealGasLawAt .state2
  have hIG₃ := _laws.idealGasLawAt .state3
  rw [hp₁, hv₁] at hIG₁
  rw [hp₂, hv₂] at hIG₂
  rw [hp₃, hv₃] at hIG₃
  have hQinRaw := _laws.hotReservoirHeatIsLegTwoToThree
  rw [_laws.isobaricHeatLaw,
    _laws.diatomicConstantPressureHeatCapacity] at hQinRaw
  have hQoutRaw := _laws.coldReservoirHeatIsRejectedOnLegThreeToOne
  rw [_laws.isochoricHeatLaw,
    _laws.diatomicConstantVolumeHeatCapacity] at hQoutRaw
  have hQin :
      energyInJoules setup.heatAbsorbedFromHotReservoir =
        1400 * (Real.rpow 4 (5 / 7) - 1) := by
    rw [hVmax] at hIG₁ hIG₃
    ring_nf at hIG₂ hIG₃ hQinRaw ⊢
    linarith
  have hQout :
      energyInJoules setup.heatRejectedToColdReservoir =
        750 * Real.rpow 4 (5 / 7) := by
    rw [hVmax] at hIG₁
    ring_nf at hIG₁ hIG₃ hQoutRaw ⊢
    linarith
  have hQin_ne :
      energyInJoules setup.heatAbsorbedFromHotReservoir ≠ 0 :=
    ne_of_gt _physical.heatAbsorbedPositive
  have hr_ne : Real.rpow 4 (5 / 7) - 1 ≠ 0 := by
    intro hr
    apply hQin_ne
    rw [hQin, hr]
    norm_num
  rw [_laws.thermalEfficiencyDefinition, _laws.cycleEnergyBalance,
    hQin, hQout]
  field_simp [hr_ne]
  ring

/-- Labels printed beside the four multiple-choice efficiencies. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Dimensionless efficiency printed beside each answer label. -/
def AnswerChoice.efficiencyValue : AnswerChoice → ℝ
  | .A => 8 / 25
  | .B => 4 / 5
  | .C => 29 / 100
  | .D => 3 / 20

/-- Answer label recorded in the dataset metadata. -/
def recordedAnswerChoice : AnswerChoice := .D

/-- Standard half-unit criterion for rounding a real number to two decimals. -/
def RoundsToHundredth (actual displayed : ℝ) : Prop :=
  |actual - displayed| < 1 / 200

/-!
The exact efficiency is approximately `0.14763`, hence it rounds to `0.15`,
the value printed for recorded answer choice D.

Blueprint label: `thm:physics:phyx_mini_0434:target`.
-/
theorem thermalEfficiency_rounds_to_recordedAnswerD
    {AmountOfSubstance : Type}
    (setup : HeatEngineSetup AmountOfSubstance)
    (_problem : MatchesProblemStatement setup)
    (_figure : MatchesPrimaryPressureVolumeFigure setup)
    (_physical : HasPhysicalHeatEngineParameters setup)
    (_laws : SatisfiesDiatomicIdealGasCycleLaws setup) :
    RoundsToHundredth setup.thermalEfficiency
        recordedAnswerChoice.efficiencyValue ∧
      recordedAnswerChoice = .D := by
  constructor
  · rw [thermalEfficiency_exact setup _problem _figure _physical _laws]
    simp only [RoundsToHundredth, recordedAnswerChoice,
      AnswerChoice.efficiencyValue]
    have hr_gt_one : 1 < Real.rpow 4 (5 / 7) :=
      Real.one_lt_rpow (by norm_num) (by norm_num)
    have hrpow7 : (Real.rpow 4 (5 / 7)) ^ 7 = 1024 := by
      calc
        (Real.rpow 4 (5 / 7)) ^ 7 =
            Real.rpow (Real.rpow 4 (5 / 7)) (7 : ℝ) :=
          (Real.rpow_natCast _ _).symm
        _ = Real.rpow 4 ((5 / 7) * 7) :=
          (Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 4) _ _).symm
        _ = 1024 := by norm_num
    have hr_lower : (399 / 149 : ℝ) < Real.rpow 4 (5 / 7) := by
      refine (Real.rpow_lt_rpow_iff (by norm_num) (by positivity)
        (by norm_num : (0 : ℝ) < 7)).mp ?_
      convert
        (show (399 / 149 : ℝ) ^ (7 : ℕ) < 1024 by norm_num) using 1
      · norm_num [Real.rpow_natCast]
      · calc
          Real.rpow (Real.rpow 4 (5 / 7)) (7 : ℝ) =
              (Real.rpow 4 (5 / 7)) ^ (7 : ℕ) :=
            Real.rpow_natCast _ _
          _ = 1024 := hrpow7
    have hr_upper : Real.rpow 4 (5 / 7) < (1183 / 433 : ℝ) := by
      refine (Real.rpow_lt_rpow_iff (by positivity) (by norm_num)
        (by norm_num : (0 : ℝ) < 7)).mp ?_
      convert
        (show 1024 < (1183 / 433 : ℝ) ^ (7 : ℕ) by norm_num) using 1
      · calc
          Real.rpow (Real.rpow 4 (5 / 7)) (7 : ℝ) =
              (Real.rpow 4 (5 / 7)) ^ (7 : ℕ) :=
            Real.rpow_natCast _ _
          _ = 1024 := hrpow7
      · norm_num [Real.rpow_natCast]
    have hden : 0 < Real.rpow 4 (5 / 7) - 1 := by linarith
    have hterm_lt :
        (15 / 28 : ℝ) *
            (Real.rpow 4 (5 / 7) / (Real.rpow 4 (5 / 7) - 1)) <
          171 / 200 := by
      rw [← mul_div_assoc]
      apply (div_lt_iff₀ hden).2
      nlinarith [hr_lower]
    have hterm_gt :
        (169 / 200 : ℝ) <
          (15 / 28) *
            (Real.rpow 4 (5 / 7) / (Real.rpow 4 (5 / 7) - 1)) := by
      rw [← mul_div_assoc]
      apply (lt_div_iff₀ hden).2
      nlinarith [hr_upper]
    rw [abs_lt]
    constructor <;> nlinarith
  · rfl

end PhyXMiniProblems.ProblemPhyXMini0434
