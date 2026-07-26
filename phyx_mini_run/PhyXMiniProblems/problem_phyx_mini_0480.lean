import Mathlib
import Physlib.Thermodynamics.Temperature.Basic
import Physlib.Thermodynamics.Temperature.TemperatureUnits
import Physlib.Units.WithDim.Energy
import Physlib.Units.WithDim.Pressure

/- USER: The assigned source file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0480

open Dimension
open scoped BigOperators

/-!
# Efficiency of a rectangular diatomic-gas heat engine

The primary pressure--volume image shows a clockwise rectangular cycle

* `1 → 2`: isobaric expansion at `3 atm` from `1 m³` to `3 m³`;
* `2 → 3`: isochoric cooling at `3 m³` from `3 atm` to `1 atm`;
* `3 → 4`: isobaric compression at `1 atm` from `3 m³` to `1 m³`;
* `4 → 1`: isochoric heating at `1 m³` from `1 atm` to `3 atm`.

The dashed `300 K` isotherm passes through state `4`.  The working substance
is a diatomic ideal gas.  Pressure, volume, temperature, internal energy,
heat, and work remain physical quantities.  Real numbers below are explicitly
unit-labelled readouts, calibrated constitutive constants, or dimensionless
efficiencies.
-/

/-! ## Dimensionful quantities and named-unit readouts -/

/-- A nonnegative physical volume carrying dimension `L³`. -/
abbrev VolumeQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * L𝓭 * L𝓭) NNReal)

/-- Cubic-metre readout of a physical volume. -/
def volumeInCubicMeters (volume : VolumeQuantity) : ℝ :=
  ((volume UnitChoices.SI).val : ℝ)

/-- Pascal readout of a physical pressure. -/
def pressureInPascals (pressure : DimPressure) : ℝ :=
  (pressure UnitChoices.SI).val /
    (DimPressure.pascal UnitChoices.SI).val

/-- Atmosphere readout of a physical pressure, using `1 atm = 101325 Pa`. -/
def pressureInAtmospheres (pressure : DimPressure) : ℝ :=
  pressureInPascals pressure / 101325

/-- Joule readout of a signed physical energy, heat transfer, or work. -/
def energyInJoules (energy : DimEnergy) : ℝ :=
  (energy UnitChoices.SI).val /
    (DimEnergy.joule UnitChoices.SI).val

/--
Kelvin readout of a Physlib absolute temperature stored in an explicitly
chosen zero-preserving temperature unit.
-/
def temperatureInKelvins
    (storageUnit : TemperatureUnit) (temperature : Temperature) : ℝ :=
  let unitRatio : NNReal := storageUnit / TemperatureUnit.kelvin
  temperature.toReal * (unitRatio : ℝ)

/-! ## Figure labels and directed cycle -/

/-- The four numbered vertices printed on the pressure--volume loop. -/
inductive CycleState where
  | one
  | two
  | three
  | four
  deriving DecidableEq, Fintype, Repr

/-- The four directed sides indicated by arrows in the supplied image. -/
inductive CycleLeg where
  | oneToTwo
  | twoToThree
  | threeToFour
  | fourToOne
  deriving DecidableEq, Fintype, Repr

/-- Initial state of each directed cycle leg. -/
def legSource : CycleLeg → CycleState
  | .oneToTwo => .one
  | .twoToThree => .two
  | .threeToFour => .three
  | .fourToOne => .four

/-- Final state of each directed cycle leg. -/
def legTarget : CycleLeg → CycleState
  | .oneToTwo => .two
  | .twoToThree => .three
  | .threeToFour => .four
  | .fourToOne => .one

/-- Thermodynamic constraint represented by a side of the rectangle. -/
inductive ProcessKind where
  | isobaric
  | isochoric
  deriving DecidableEq, Repr

/-- Geometric orientation of a straight segment in the `p`-`V` plane. -/
inductive SegmentOrientation where
  | horizontal
  | vertical
  deriving DecidableEq, Repr

/-- Process kinds read from the clockwise rectangular path. -/
def displayedProcessKind : CycleLeg → ProcessKind
  | .oneToTwo => .isobaric
  | .twoToThree => .isochoric
  | .threeToFour => .isobaric
  | .fourToOne => .isochoric

/-- Segment orientations read from the primary image. -/
def displayedSegmentOrientation : CycleLeg → SegmentOrientation
  | .oneToTwo => .horizontal
  | .twoToThree => .vertical
  | .threeToFour => .horizontal
  | .fourToOne => .vertical

/-- Physical quantity assigned to one of the plotted axes. -/
inductive AxisQuantity where
  | volume
  | pressure
  deriving DecidableEq, Repr

/-- Unit printed beside the horizontal volume axis. -/
inductive VolumeDisplayUnit where
  | cubicMeter
  deriving DecidableEq, Repr

/-- Unit printed beside the vertical pressure axis. -/
inductive PressureDisplayUnit where
  | atmosphere
  deriving DecidableEq, Repr

/-- Literal annotations whose visibility is evidence from the raster. -/
inductive DiagramLabel where
  | stateOne
  | stateTwo
  | stateThree
  | stateFour
  | pressureOneAtmosphere
  | pressureThreeAtmospheres
  | volumeOneCubicMeter
  | volumeThreeCubicMeters
  | isothermThreeHundredKelvins
  deriving DecidableEq, Fintype, Repr

/-!
The diagram stores literal scalar coordinates in its printed units.  The
physical pressure and volume at each state are separate fields of the engine
and are linked to these coordinates by `MatchesPrimaryPressureVolumeFigure`.
-/
structure PressureVolumeDiagram where
  horizontalAxisQuantity : AxisQuantity
  verticalAxisQuantity : AxisQuantity
  horizontalAxisUnit : VolumeDisplayUnit
  verticalAxisUnit : PressureDisplayUnit
  horizontalAxisMinimumCubicMeters : ℝ
  horizontalAxisMaximumCubicMeters : ℝ
  verticalAxisMinimumAtmospheres : ℝ
  verticalAxisMaximumAtmospheres : ℝ
  volumeCoordinateCubicMeters : CycleState → ℝ
  pressureCoordinateAtmospheres : CycleState → ℝ
  labelVisible : DiagramLabel → Bool
  arrowVisible : CycleLeg → Bool
  arrowStart : CycleLeg → CycleState
  arrowFinish : CycleLeg → CycleState
  segmentOrientation : CycleLeg → SegmentOrientation
  isothermTemperatureKelvins : ℝ
  isothermPassesThrough : CycleState → Bool

/-! ## Gas sample and thermodynamic observables -/

/-- Molecular degrees-of-freedom model specified by the problem. -/
inductive MolecularType where
  | diatomic
  | other
  deriving DecidableEq, Repr

/-- Equation-of-state model for the working substance. -/
inductive GasModel where
  | idealGas
  | other
  deriving DecidableEq, Repr

/-- Role of the cyclic thermodynamic device. -/
inductive ThermodynamicDeviceRole where
  | heatEngine
  | other
  deriving DecidableEq, Repr

/-!
The complete engine setup.  Physlib currently has no amount-of-substance base
dimension, so its carrier remains abstract and only its calibrated mole
readout is real.  Heat is positive into the gas and work is positive when
done by the gas.
-/
structure DiatomicRectangularHeatEngine (AmountOfSubstance : Type) where
  molecularType : MolecularType
  gasModel : GasModel
  deviceRole : ThermodynamicDeviceRole
  amountOfGas : AmountOfSubstance
  amountInMoles : AmountOfSubstance → ℝ
  molarGasConstantJoulesPerMoleKelvin : ℝ
  molarHeatCapacityAtConstantVolumeJoulesPerMoleKelvin : ℝ
  molarHeatCapacityAtConstantPressureJoulesPerMoleKelvin : ℝ
  temperatureStorageUnit : TemperatureUnit
  pressureAt : CycleState → DimPressure
  volumeAt : CycleState → VolumeQuantity
  temperatureAt : CycleState → Temperature
  internalEnergyAt : CycleState → DimEnergy
  workDoneByGasOn : CycleLeg → DimEnergy
  heatTransferredIntoGasOn : CycleLeg → DimEnergy
  processKind : CycleLeg → ProcessKind
  figure : PressureVolumeDiagram

/-- Mole readout of the physical gas sample. -/
def amountOfGasInMoles
    {AmountOfSubstance : Type}
    (setup : DiatomicRectangularHeatEngine AmountOfSubstance) : ℝ :=
  setup.amountInMoles setup.amountOfGas

/-- Kelvin readout of a numbered thermodynamic state. -/
def gasTemperatureInKelvins
    {AmountOfSubstance : Type}
    (setup : DiatomicRectangularHeatEngine AmountOfSubstance)
    (state : CycleState) : ℝ :=
  temperatureInKelvins setup.temperatureStorageUnit
    (setup.temperatureAt state)

/-- Joule readout of the internal energy at a numbered state. -/
def internalEnergyInJoules
    {AmountOfSubstance : Type}
    (setup : DiatomicRectangularHeatEngine AmountOfSubstance)
    (state : CycleState) : ℝ :=
  energyInJoules (setup.internalEnergyAt state)

/-- Signed joule readout of work done by the gas on a directed leg. -/
def workDoneByGasInJoules
    {AmountOfSubstance : Type}
    (setup : DiatomicRectangularHeatEngine AmountOfSubstance)
    (leg : CycleLeg) : ℝ :=
  energyInJoules (setup.workDoneByGasOn leg)

/-- Signed joule readout of heat transferred into the gas on a leg. -/
def heatTransferredIntoGasInJoules
    {AmountOfSubstance : Type}
    (setup : DiatomicRectangularHeatEngine AmountOfSubstance)
    (leg : CycleLeg) : ℝ :=
  energyInJoules (setup.heatTransferredIntoGasOn leg)

/-! ## Assumptions: prose, primary-image evidence, and governing laws -/

/-!
The qualitative facts stated by the problem.  This predicate contains no
efficiency, leg-energy, net-work, heat-input, or answer-choice value.
-/
structure MatchesProblemStatement
    {AmountOfSubstance : Type}
    (setup : DiatomicRectangularHeatEngine AmountOfSubstance) : Prop where
  workingSubstanceIsDiatomic : setup.molecularType = .diatomic
  workingSubstanceIsIdealGas : setup.gasModel = .idealGas
  deviceIsHeatEngine : setup.deviceRole = .heatEngine

/-!
Exact evidence transcribed from the primary raster.  In particular, it fixes
the four `(V,p)` coordinates, clockwise arrows, and the `300 K` isotherm
through state `4`, but contains no thermodynamic efficiency conclusion.
-/
structure MatchesPrimaryPressureVolumeFigure
    {AmountOfSubstance : Type}
    (setup : DiatomicRectangularHeatEngine AmountOfSubstance) : Prop where
  horizontalAxisIsVolume :
    setup.figure.horizontalAxisQuantity = .volume
  verticalAxisIsPressure :
    setup.figure.verticalAxisQuantity = .pressure
  horizontalAxisUsesCubicMeters :
    setup.figure.horizontalAxisUnit = .cubicMeter
  verticalAxisUsesAtmospheres :
    setup.figure.verticalAxisUnit = .atmosphere
  horizontalAxisRange :
    setup.figure.horizontalAxisMinimumCubicMeters = 0 ∧
      setup.figure.horizontalAxisMaximumCubicMeters = 3
  verticalAxisRange :
    setup.figure.verticalAxisMinimumAtmospheres = 0 ∧
      setup.figure.verticalAxisMaximumAtmospheres = 3
  stateOneCoordinates :
    setup.figure.volumeCoordinateCubicMeters .one = 1 ∧
      setup.figure.pressureCoordinateAtmospheres .one = 3
  stateTwoCoordinates :
    setup.figure.volumeCoordinateCubicMeters .two = 3 ∧
      setup.figure.pressureCoordinateAtmospheres .two = 3
  stateThreeCoordinates :
    setup.figure.volumeCoordinateCubicMeters .three = 3 ∧
      setup.figure.pressureCoordinateAtmospheres .three = 1
  stateFourCoordinates :
    setup.figure.volumeCoordinateCubicMeters .four = 1 ∧
      setup.figure.pressureCoordinateAtmospheres .four = 1
  coordinatesRepresentPhysicalStates : ∀ state,
    setup.figure.volumeCoordinateCubicMeters state =
        volumeInCubicMeters (setup.volumeAt state) ∧
      setup.figure.pressureCoordinateAtmospheres state =
        pressureInAtmospheres (setup.pressureAt state)
  everyPrintedLabelIsVisible :
    ∀ label, setup.figure.labelVisible label = true
  everyClockwiseArrowIsVisible :
    ∀ leg, setup.figure.arrowVisible leg = true
  arrowDirections : ∀ leg,
    setup.figure.arrowStart leg = legSource leg ∧
      setup.figure.arrowFinish leg = legTarget leg
  displayedSegmentOrientationsAgree : ∀ leg,
    setup.figure.segmentOrientation leg = displayedSegmentOrientation leg
  displayedProcessKindsAgree : ∀ leg,
    setup.processKind leg = displayedProcessKind leg
  isothermTemperatureIsThreeHundredKelvins :
    setup.figure.isothermTemperatureKelvins = 300
  isothermPassesThroughStateFour :
    setup.figure.isothermPassesThrough .four = true
  temperaturesStoredInKelvins :
    setup.temperatureStorageUnit = TemperatureUnit.kelvin
  stateFourTemperatureAgreesWithIsotherm :
    gasTemperatureInKelvins setup .four =
      setup.figure.isothermTemperatureKelvins

/-- Positivity and nondegeneracy conditions for a physical engine cycle. -/
structure HasPhysicalCycleParameters
    {AmountOfSubstance : Type}
    (setup : DiatomicRectangularHeatEngine AmountOfSubstance) : Prop where
  amountPositive : 0 < amountOfGasInMoles setup
  gasConstantPositive :
    0 < setup.molarGasConstantJoulesPerMoleKelvin
  constantVolumeHeatCapacityPositive :
    0 < setup.molarHeatCapacityAtConstantVolumeJoulesPerMoleKelvin
  constantPressureHeatCapacityPositive :
    0 < setup.molarHeatCapacityAtConstantPressureJoulesPerMoleKelvin
  pressurePositive :
    ∀ state, 0 < pressureInPascals (setup.pressureAt state)
  volumePositive :
    ∀ state, 0 < volumeInCubicMeters (setup.volumeAt state)
  absoluteTemperaturePositive :
    ∀ state, 0 < gasTemperatureInKelvins setup state

/-!
Macroscopic governing laws for a calorically perfect diatomic ideal gas:

* `Cᵥ = (5/2)R` and `Cₚ = (7/2)R`;
* `pV = nRT` and `U = nCᵥT` at every equilibrium state;
* zero boundary work on an isochoric leg;
* `W_by = p(V_f-V_i)` on an isobaric leg;
* `Q_in = U_f-U_i+W_by` on every leg.

These are constitutive and conservation laws.  No field fixes a derived leg
energy, total heat input, net work, efficiency, or answer choice.
-/
structure SatisfiesDiatomicIdealGasCycleLaws
    {AmountOfSubstance : Type}
    (setup : DiatomicRectangularHeatEngine AmountOfSubstance) : Prop where
  diatomicConstantVolumeHeatCapacity :
    setup.molarHeatCapacityAtConstantVolumeJoulesPerMoleKelvin =
      (5 / 2 : ℝ) * setup.molarGasConstantJoulesPerMoleKelvin
  diatomicConstantPressureHeatCapacity :
    setup.molarHeatCapacityAtConstantPressureJoulesPerMoleKelvin =
      (7 / 2 : ℝ) * setup.molarGasConstantJoulesPerMoleKelvin
  idealGasEquation : ∀ state,
    pressureInPascals (setup.pressureAt state) *
        volumeInCubicMeters (setup.volumeAt state) =
      amountOfGasInMoles setup *
        setup.molarGasConstantJoulesPerMoleKelvin *
          gasTemperatureInKelvins setup state
  internalEnergyOfDiatomicIdealGas : ∀ state,
    internalEnergyInJoules setup state =
      amountOfGasInMoles setup *
        setup.molarHeatCapacityAtConstantVolumeJoulesPerMoleKelvin *
          gasTemperatureInKelvins setup state
  isochoricBoundaryWork : ∀ leg,
    setup.processKind leg = .isochoric →
      workDoneByGasInJoules setup leg = 0
  isobaricBoundaryWork : ∀ leg,
    setup.processKind leg = .isobaric →
      workDoneByGasInJoules setup leg =
        pressureInPascals (setup.pressureAt (legSource leg)) *
          (volumeInCubicMeters (setup.volumeAt (legTarget leg)) -
            volumeInCubicMeters (setup.volumeAt (legSource leg)))
  firstLawOnEachLeg : ∀ leg,
    heatTransferredIntoGasInJoules setup leg =
      internalEnergyInJoules setup (legTarget leg) -
        internalEnergyInJoules setup (legSource leg) +
          workDoneByGasInJoules setup leg

/-! ## Derived cycle quantities and answer choices -/

/-- Net work done by the gas over one complete traversal, in joules. -/
def netCycleWorkInJoules
    {AmountOfSubstance : Type}
    (setup : DiatomicRectangularHeatEngine AmountOfSubstance) : ℝ :=
  ∑ leg : CycleLeg, workDoneByGasInJoules setup leg

/-- Total heat entering the gas, obtained by summing positive leg heats. -/
def totalHeatInputInJoules
    {AmountOfSubstance : Type}
    (setup : DiatomicRectangularHeatEngine AmountOfSubstance) : ℝ :=
  ∑ leg : CycleLeg, max (heatTransferredIntoGasInJoules setup leg) 0

/-- Dimensionless thermal efficiency `W_net / Q_in`. -/
def thermalEfficiency
    {AmountOfSubstance : Type}
    (setup : DiatomicRectangularHeatEngine AmountOfSubstance) : ℝ :=
  netCycleWorkInJoules setup / totalHeatInputInJoules setup

/-- Labels of the four printed answer choices. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Dimensionless efficiency printed beside each answer label. -/
def displayedEfficiency : AnswerChoice → ℝ
  | .A => 9 / 100
  | .B => 12 / 100
  | .C => 15 / 100
  | .D => 18 / 100

/-- Answer choice recorded in the supplied dataset metadata. -/
def recordedAnswerChoice : AnswerChoice := .C

/-- Compatibility with an efficiency displayed to the nearest whole percent. -/
def RoundsToDisplayedWholePercent (actual displayed : ℝ) : Prop :=
  |actual - displayed| < 1 / 200

/-!
The state products, diatomic internal-energy law, work laws, and first law
determine every signed leg energy.  The common factor `101325 J` is one
`atm·m³`.  None of these energy values is a premise field.
-/
lemma cycleLegEnergyReadouts
    {AmountOfSubstance : Type}
    (setup : DiatomicRectangularHeatEngine AmountOfSubstance)
    (_problem : MatchesProblemStatement setup)
    (_figure : MatchesPrimaryPressureVolumeFigure setup)
    (_physical : HasPhysicalCycleParameters setup)
    (_laws : SatisfiesDiatomicIdealGasCycleLaws setup) :
    workDoneByGasInJoules setup .oneToTwo = 6 * 101325 ∧
      workDoneByGasInJoules setup .twoToThree = 0 ∧
      workDoneByGasInJoules setup .threeToFour = -2 * 101325 ∧
      workDoneByGasInJoules setup .fourToOne = 0 ∧
      heatTransferredIntoGasInJoules setup .oneToTwo = 21 * 101325 ∧
      heatTransferredIntoGasInJoules setup .twoToThree = -15 * 101325 ∧
      heatTransferredIntoGasInJoules setup .threeToFour = -7 * 101325 ∧
      heatTransferredIntoGasInJoules setup .fourToOne = 5 * 101325 := by
  have hv_one : volumeInCubicMeters (setup.volumeAt .one) = 1 := by
    have h := (_figure.coordinatesRepresentPhysicalStates .one).1
    linarith [_figure.stateOneCoordinates.1]
  have hv_two : volumeInCubicMeters (setup.volumeAt .two) = 3 := by
    have h := (_figure.coordinatesRepresentPhysicalStates .two).1
    linarith [_figure.stateTwoCoordinates.1]
  have hv_three : volumeInCubicMeters (setup.volumeAt .three) = 3 := by
    have h := (_figure.coordinatesRepresentPhysicalStates .three).1
    linarith [_figure.stateThreeCoordinates.1]
  have hv_four : volumeInCubicMeters (setup.volumeAt .four) = 1 := by
    have h := (_figure.coordinatesRepresentPhysicalStates .four).1
    linarith [_figure.stateFourCoordinates.1]

  have hp_one_atm :
      pressureInAtmospheres (setup.pressureAt .one) = 3 := by
    have h := (_figure.coordinatesRepresentPhysicalStates .one).2
    linarith [_figure.stateOneCoordinates.2]
  have hp_two_atm :
      pressureInAtmospheres (setup.pressureAt .two) = 3 := by
    have h := (_figure.coordinatesRepresentPhysicalStates .two).2
    linarith [_figure.stateTwoCoordinates.2]
  have hp_three_atm :
      pressureInAtmospheres (setup.pressureAt .three) = 1 := by
    have h := (_figure.coordinatesRepresentPhysicalStates .three).2
    linarith [_figure.stateThreeCoordinates.2]
  have hp_four_atm :
      pressureInAtmospheres (setup.pressureAt .four) = 1 := by
    have h := (_figure.coordinatesRepresentPhysicalStates .four).2
    linarith [_figure.stateFourCoordinates.2]

  have hp_one :
      pressureInPascals (setup.pressureAt .one) = 3 * 101325 := by
    rw [pressureInAtmospheres] at hp_one_atm
    norm_num at hp_one_atm ⊢
    linarith
  have hp_two :
      pressureInPascals (setup.pressureAt .two) = 3 * 101325 := by
    rw [pressureInAtmospheres] at hp_two_atm
    norm_num at hp_two_atm ⊢
    linarith
  have hp_three :
      pressureInPascals (setup.pressureAt .three) = 1 * 101325 := by
    rw [pressureInAtmospheres] at hp_three_atm
    norm_num at hp_three_atm ⊢
    linarith
  have hp_four :
      pressureInPascals (setup.pressureAt .four) = 1 * 101325 := by
    rw [pressureInAtmospheres] at hp_four_atm
    norm_num at hp_four_atm ⊢
    linarith

  have h_internal_from_pv (state : CycleState) :
      internalEnergyInJoules setup state =
        (5 / 2 : ℝ) * pressureInPascals (setup.pressureAt state) *
          volumeInCubicMeters (setup.volumeAt state) := by
    have h_ideal := _laws.idealGasEquation state
    have h_internal := _laws.internalEnergyOfDiatomicIdealGas state
    rw [_laws.diatomicConstantVolumeHeatCapacity] at h_internal
    nlinarith

  have hU_one := h_internal_from_pv .one
  rw [hp_one, hv_one] at hU_one
  have hU_two := h_internal_from_pv .two
  rw [hp_two, hv_two] at hU_two
  have hU_three := h_internal_from_pv .three
  rw [hp_three, hv_three] at hU_three
  have hU_four := h_internal_from_pv .four
  rw [hp_four, hv_four] at hU_four
  norm_num at hU_one hU_two hU_three hU_four

  have hw_one_two_formula :=
    _laws.isobaricBoundaryWork .oneToTwo (by
      simpa [displayedProcessKind] using
        _figure.displayedProcessKindsAgree .oneToTwo)
  simp only [legSource, legTarget] at hw_one_two_formula
  have hw_one_two :
      workDoneByGasInJoules setup .oneToTwo = 6 * 101325 := by
    rw [hp_one, hv_two, hv_one] at hw_one_two_formula
    norm_num at hw_one_two_formula ⊢
    exact hw_one_two_formula
  have hw_two_three :
      workDoneByGasInJoules setup .twoToThree = 0 :=
    _laws.isochoricBoundaryWork .twoToThree (by
      simpa [displayedProcessKind] using
        _figure.displayedProcessKindsAgree .twoToThree)
  have hw_three_four_formula :=
    _laws.isobaricBoundaryWork .threeToFour (by
      simpa [displayedProcessKind] using
        _figure.displayedProcessKindsAgree .threeToFour)
  simp only [legSource, legTarget] at hw_three_four_formula
  have hw_three_four :
      workDoneByGasInJoules setup .threeToFour = -2 * 101325 := by
    rw [hp_three, hv_four, hv_three] at hw_three_four_formula
    norm_num at hw_three_four_formula ⊢
    exact hw_three_four_formula
  have hw_four_one :
      workDoneByGasInJoules setup .fourToOne = 0 :=
    _laws.isochoricBoundaryWork .fourToOne (by
      simpa [displayedProcessKind] using
        _figure.displayedProcessKindsAgree .fourToOne)

  have hq_one_two := _laws.firstLawOnEachLeg .oneToTwo
  have hq_two_three := _laws.firstLawOnEachLeg .twoToThree
  have hq_three_four := _laws.firstLawOnEachLeg .threeToFour
  have hq_four_one := _laws.firstLawOnEachLeg .fourToOne
  simp only [legSource, legTarget] at hq_one_two hq_two_three hq_three_four hq_four_one
  have hq_one_two_value :
      heatTransferredIntoGasInJoules setup .oneToTwo = 21 * 101325 := by
    rw [hU_two, hU_one, hw_one_two] at hq_one_two
    norm_num at hq_one_two ⊢
    exact hq_one_two
  have hq_two_three_value :
      heatTransferredIntoGasInJoules setup .twoToThree = -15 * 101325 := by
    rw [hU_three, hU_two, hw_two_three] at hq_two_three
    norm_num at hq_two_three ⊢
    exact hq_two_three
  have hq_three_four_value :
      heatTransferredIntoGasInJoules setup .threeToFour = -7 * 101325 := by
    rw [hU_four, hU_three, hw_three_four] at hq_three_four
    norm_num at hq_three_four ⊢
    exact hq_three_four
  have hq_four_one_value :
      heatTransferredIntoGasInJoules setup .fourToOne = 5 * 101325 := by
    rw [hU_one, hU_four, hw_four_one] at hq_four_one
    norm_num at hq_four_one ⊢
    exact hq_four_one

  exact ⟨hw_one_two, hw_two_three, hw_three_four, hw_four_one,
    hq_one_two_value, hq_two_three_value, hq_three_four_value,
    hq_four_one_value⟩

/-!
Consequently the engine does `4 atm·m³` of net work and absorbs
`26 atm·m³` of heat per cycle.  These remain derived conclusions.
-/
lemma netWorkAndHeatInputReadouts
    {AmountOfSubstance : Type}
    (setup : DiatomicRectangularHeatEngine AmountOfSubstance)
    (_problem : MatchesProblemStatement setup)
    (_figure : MatchesPrimaryPressureVolumeFigure setup)
    (_physical : HasPhysicalCycleParameters setup)
    (_laws : SatisfiesDiatomicIdealGasCycleLaws setup) :
    netCycleWorkInJoules setup = 4 * 101325 ∧
      totalHeatInputInJoules setup = 26 * 101325 := by
  rcases cycleLegEnergyReadouts setup _problem _figure _physical _laws with
    ⟨hw12, hw23, hw34, hw41, hq12, hq23, hq34, hq41⟩
  have huniv : (Finset.univ : Finset CycleLeg) =
      {.oneToTwo, .twoToThree, .threeToFour, .fourToOne} := by
    decide
  constructor
  · rw [netCycleWorkInJoules, huniv]
    simp [hw12, hw23, hw34, hw41]
    norm_num
  · rw [totalHeatInputInJoules, huniv]
    simp [hq12, hq23, hq34, hq41]
    norm_num

/-!
The exact efficiency is `4/26 = 2/13 ≈ 0.1538`; hence it rounds to the
displayed `15%`, which is recorded answer choice C.  Neither the exact value
nor the rounding conclusion occurs among the hypotheses.

Blueprint: `thm:physics:phyx_mini_0480:target`.
-/
theorem thermalEfficiency_eq_twoThirteenths_and_rounds_to_choiceC
    {AmountOfSubstance : Type}
    (setup : DiatomicRectangularHeatEngine AmountOfSubstance)
    (_problem : MatchesProblemStatement setup)
    (_figure : MatchesPrimaryPressureVolumeFigure setup)
    (_physical : HasPhysicalCycleParameters setup)
    (_laws : SatisfiesDiatomicIdealGasCycleLaws setup) :
    thermalEfficiency setup = 2 / 13 ∧
      RoundsToDisplayedWholePercent
        (thermalEfficiency setup) (displayedEfficiency .C) := by
  rcases netWorkAndHeatInputReadouts setup _problem _figure _physical _laws with
    ⟨hwork, hheat⟩
  constructor
  · rw [thermalEfficiency, hwork, hheat]
    norm_num
  · rw [RoundsToDisplayedWholePercent, displayedEfficiency,
      thermalEfficiency, hwork, hheat]
    norm_num [abs_of_nonneg, abs_of_nonpos]

end PhyXMiniProblems.ProblemPhyXMini0480
