import Mathlib
import Physlib.Thermodynamics.Temperature.Basic
import Physlib.Thermodynamics.Temperature.TemperatureUnits
import Physlib.Units.WithDim.Energy
import Physlib.Units.WithDim.Pressure

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0430

open Dimension

/-!
# Work and efficiency of a three-leg diatomic-gas heat engine

The primary pressure-volume raster shows the directed cycle
1 to 2 to 3 to 1.  The first leg is vertical and hence isochoric, the second
is the labelled adiabatic expansion, and the third follows the labelled
300 K isotherm back toward the smaller volume.

The marked coordinates are:

* state 1: volume 1000 cubic centimetres, pressure 400 kilopascals;
* state 2: volume 1000 cubic centimetres, pressure not numerically labelled;
* state 3: volume 4000 cubic centimetres, pressure 100 kilopascals.

Thus the auxiliary caption's claim that the first leg is isothermal is not
used.  Physical quantities retain dimensionful types.  Real numbers below
are named unit readouts, dimensionless constants and efficiencies, or
displayed answer data.
-/

/-! ## Dimensionful quantities and named-unit readouts -/

/-- A nonnegative physical volume carrying dimension length cubed. -/
abbrev VolumeQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * L𝓭 * L𝓭) NNReal)

/-- Read a physical pressure in coherent SI pascals. -/
def pressureInPascals (pressure : DimPressure) : ℝ :=
  (pressure UnitChoices.SI).val

/-- Read a physical pressure in the kilopascals printed on the vertical axis. -/
def pressureInKilopascals (pressure : DimPressure) : ℝ :=
  pressureInPascals pressure / 1000

/-- Read a physical volume in coherent SI cubic metres. -/
def volumeInCubicMeters (volume : VolumeQuantity) : ℝ :=
  ((volume UnitChoices.SI).val : ℝ)

/-- Read a physical volume in the cubic centimetres printed on the horizontal axis. -/
def volumeInCubicCentimeters (volume : VolumeQuantity) : ℝ :=
  1000000 * volumeInCubicMeters volume

/-- Read signed physical heat, internal energy, or work in coherent SI joules. -/
def energyInJoules (energy : DimEnergy) : ℝ :=
  (energy UnitChoices.SI).val

/--
Read a stored absolute temperature in kelvin.  Physlib Temperature stores an
absolute nonnegative magnitude in an arbitrary zero-preserving unit, so the
storage unit is retained explicitly by the setup.
-/
def temperatureInKelvin
    (storageUnit : TemperatureUnit) (temperature : Temperature) : ℝ :=
  let unitRatio : NNReal := storageUnit / TemperatureUnit.kelvin
  temperature.toReal * (unitRatio : ℝ)

/-! ## Cycle states, legs, and primary-image vocabulary -/

/-- The three numbered black state points in the supplied raster. -/
inductive CycleState where
  | one
  | two
  | three
  deriving DecidableEq, Fintype, Repr

/-- The three directed legs traversed by the engine. -/
inductive CycleLeg where
  | oneToTwo
  | twoToThree
  | threeToOne
  deriving DecidableEq, Fintype, Repr

/-- Initial endpoint of a directed cycle leg. -/
def legSource : CycleLeg → CycleState
  | .oneToTwo => .one
  | .twoToThree => .two
  | .threeToOne => .three

/-- Final endpoint of a directed cycle leg. -/
def legTarget : CycleLeg → CycleState
  | .oneToTwo => .two
  | .twoToThree => .three
  | .threeToOne => .one

/-- Thermodynamic character of a directed leg. -/
inductive ProcessKind where
  | isochoric
  | adiabatic
  | isothermal
  deriving DecidableEq, Repr

/-- Geometric appearance of a leg in the pressure-volume plane. -/
inductive SegmentShape where
  | verticalSegment
  | curvedSegment
  deriving DecidableEq, Repr

/-- The two displayed graph axes. -/
inductive FigureAxis where
  | horizontal
  | vertical
  deriving DecidableEq, Fintype, Repr

/-- Physical quantity assigned to a graph axis. -/
inductive AxisQuantity where
  | volume
  | pressure
  deriving DecidableEq, Repr

/-- Unit printed beside a graph axis. -/
inductive AxisUnit where
  | cubicCentimeter
  | kilopascal
  deriving DecidableEq, Repr

/-- Process annotations printed next to the two curved legs. -/
inductive ProcessAnnotation where
  | none
  | threeHundredKelvinIsotherm
  | adiabat
  deriving DecidableEq, Repr

/-- Literal labels and numeric ticks visible in the primary raster. -/
inductive FigureLabel where
  | pressureP
  | volumeV
  | pressureUnitKPa
  | volumeUnitCubicCentimeter
  | stateOne
  | stateTwo
  | stateThree
  | pressureOneHundred
  | pressureFourHundred
  | volumeTwoThousand
  | volumeFourThousand
  | threeHundredKelvinIsotherm
  | adiabat
  deriving DecidableEq, Fintype, Repr

/-- The operating role of the cyclic thermodynamic device. -/
inductive ThermodynamicDeviceKind where
  | heatEngine
  | refrigerator
  deriving DecidableEq, Repr

/-- Whether matter crosses the boundary of the working substance. -/
inductive SystemBoundary where
  | closedWorkingSubstance
  | openFlow
  deriving DecidableEq, Repr

/-- Mechanical idealization used to identify boundary work from a pV path. -/
inductive ProcessRegime where
  | quasistaticEquilibrium
  | other
  deriving DecidableEq, Repr

/-- The kind of gas used as the engine's closed working substance. -/
inductive WorkingGasKind where
  | diatomicIdealGas
  | other
  deriving DecidableEq, Repr

/-- One equilibrium state of the working gas. -/
structure ThermodynamicState where
  pressure : DimPressure
  volume : VolumeQuantity
  temperature : Temperature
  internalEnergy : DimEnergy

/--
Qualitative content visible in the supplied pressure-volume raster.  Physical
coordinates are kept in the engine state data and linked to printed ticks by
MatchesSuppliedPressureVolumeFigure.
-/
structure PressureVolumeCycleFigure where
  axisQuantity : FigureAxis → AxisQuantity
  axisUnit : FigureAxis → AxisUnit
  labelShown : FigureLabel → Bool
  statePointShown : CycleState → Bool
  processLegShown : CycleLeg → Bool
  arrowEndpoints : CycleLeg → CycleState × CycleState
  segmentShape : CycleLeg → SegmentShape
  annotation : CycleLeg → ProcessAnnotation

/--
Independent physical observables for one engine cycle.  The amount of
substance remains abstract because Physlib has no amount-of-substance base
dimension; only its explicitly named mole readout is scalar.  No net work,
heat input, efficiency, or answer choice is stored as a field.
-/
structure DiatomicHeatEngineSetup (AmountOfSubstance : Type) where
  deviceKind : ThermodynamicDeviceKind
  systemBoundary : SystemBoundary
  processRegime : ProcessRegime
  workingGasKind : WorkingGasKind
  figure : PressureVolumeCycleFigure
  stateAt : CycleState → ThermodynamicState
  processKind : CycleLeg → ProcessKind
  amountOfGas : AmountOfSubstance
  amountInMoles : AmountOfSubstance → ℝ
  temperatureStorageUnit : TemperatureUnit
  universalGasConstantJoulesPerMoleKelvin : ℝ
  heatCapacityRatio : ℝ
  workDoneByGasOnLeg : CycleLeg → DimEnergy
  heatTransferredIntoGasOnLeg : CycleLeg → DimEnergy

/-- Mole readout of the fixed physical amount of gas. -/
def gasAmountInMoles
    {AmountOfSubstance : Type}
    (setup : DiatomicHeatEngineSetup AmountOfSubstance) : ℝ :=
  setup.amountInMoles setup.amountOfGas

/-- Kelvin readout of the working gas at a numbered cycle state. -/
def stateTemperatureInKelvin
    {AmountOfSubstance : Type}
    (setup : DiatomicHeatEngineSetup AmountOfSubstance)
    (state : CycleState) : ℝ :=
  temperatureInKelvin setup.temperatureStorageUnit
    (setup.stateAt state).temperature

/-- Signed work done by the gas on one directed leg, in joules. -/
def workDoneByGasInJoules
    {AmountOfSubstance : Type}
    (setup : DiatomicHeatEngineSetup AmountOfSubstance)
    (leg : CycleLeg) : ℝ :=
  energyInJoules (setup.workDoneByGasOnLeg leg)

/-- Signed heat transferred into the gas on one directed leg, in joules. -/
def heatTransferredIntoGasInJoules
    {AmountOfSubstance : Type}
    (setup : DiatomicHeatEngineSetup AmountOfSubstance)
    (leg : CycleLeg) : ℝ :=
  energyInJoules (setup.heatTransferredIntoGasOnLeg leg)

/-- Internal-energy readout of the gas at a cycle state, in joules. -/
def internalEnergyInJoules
    {AmountOfSubstance : Type}
    (setup : DiatomicHeatEngineSetup AmountOfSubstance)
    (state : CycleState) : ℝ :=
  energyInJoules (setup.stateAt state).internalEnergy

/-! ## Scenario, primary-image data, and governing laws -/

/--
The prose-level engine model and physical interpretation of each directed leg.
These qualitative premises contain no requested work or efficiency.
-/
structure MatchesDiatomicHeatEngineScenario
    {AmountOfSubstance : Type}
    (setup : DiatomicHeatEngineSetup AmountOfSubstance) : Prop where
  deviceIsHeatEngine : setup.deviceKind = .heatEngine
  workingSubstanceIsClosed : setup.systemBoundary = .closedWorkingSubstance
  gasIsDiatomicIdealGas : setup.workingGasKind = .diatomicIdealGas
  processIsQuasistatic : setup.processRegime = .quasistaticEquilibrium
  firstLegIsIsochoric : setup.processKind .oneToTwo = .isochoric
  secondLegIsAdiabatic : setup.processKind .twoToThree = .adiabatic
  thirdLegIsIsothermal : setup.processKind .threeToOne = .isothermal
  diatomicHeatCapacityRatio : setup.heatCapacityRatio = 7 / 5

/--
Evidence read from the primary image.  It records axes, units, exact printed
coordinates, arrow directions, curve labels, and that the unlabelled state-2
pressure lies above state 1.  No work, heat, or efficiency occurs here.
-/
structure MatchesSuppliedPressureVolumeFigure
    {AmountOfSubstance : Type}
    (setup : DiatomicHeatEngineSetup AmountOfSubstance) : Prop where
  horizontalAxisIsVolume :
    setup.figure.axisQuantity .horizontal = .volume
  verticalAxisIsPressure :
    setup.figure.axisQuantity .vertical = .pressure
  horizontalAxisUsesCubicCentimeters :
    setup.figure.axisUnit .horizontal = .cubicCentimeter
  verticalAxisUsesKilopascals :
    setup.figure.axisUnit .vertical = .kilopascal
  everyPrintedLabelShown :
    ∀ label, setup.figure.labelShown label = true
  everyStatePointShown :
    ∀ state, setup.figure.statePointShown state = true
  everyProcessLegShown :
    ∀ leg, setup.figure.processLegShown leg = true
  arrowsFollowDisplayedCycle : ∀ leg,
    setup.figure.arrowEndpoints leg = (legSource leg, legTarget leg)
  firstLegIsVertical :
    setup.figure.segmentShape .oneToTwo = .verticalSegment
  secondLegIsCurved :
    setup.figure.segmentShape .twoToThree = .curvedSegment
  thirdLegIsCurved :
    setup.figure.segmentShape .threeToOne = .curvedSegment
  firstLegHasNoCurveAnnotation :
    setup.figure.annotation .oneToTwo = .none
  secondLegHasAdiabatLabel :
    setup.figure.annotation .twoToThree = .adiabat
  thirdLegHasThreeHundredKelvinIsothermLabel :
    setup.figure.annotation .threeToOne = .threeHundredKelvinIsotherm
  stateOnePressureKilopascals :
    pressureInKilopascals (setup.stateAt .one).pressure = 400
  stateOneVolumeCubicCentimeters :
    volumeInCubicCentimeters (setup.stateAt .one).volume = 1000
  stateTwoSharesStateOneVolume :
    volumeInCubicCentimeters (setup.stateAt .two).volume = 1000
  stateTwoLiesAboveStateOne :
    pressureInPascals (setup.stateAt .one).pressure <
      pressureInPascals (setup.stateAt .two).pressure
  stateThreePressureKilopascals :
    pressureInKilopascals (setup.stateAt .three).pressure = 100
  stateThreeVolumeCubicCentimeters :
    volumeInCubicCentimeters (setup.stateAt .three).volume = 4000
  isothermTemperatureAtStateOne :
    stateTemperatureInKelvin setup .one = 300
  isothermTemperatureAtStateThree :
    stateTemperatureInKelvin setup .three = 300

/-- Positivity and nondegeneracy conditions for the physical gas cycle. -/
structure HasPhysicalCycleParameters
    {AmountOfSubstance : Type}
    (setup : DiatomicHeatEngineSetup AmountOfSubstance) : Prop where
  pressurePositive : ∀ state,
    0 < pressureInPascals (setup.stateAt state).pressure
  volumePositive : ∀ state,
    0 < volumeInCubicMeters (setup.stateAt state).volume
  absoluteTemperaturePositive : ∀ state,
    0 < stateTemperatureInKelvin setup state
  amountPositive : 0 < gasAmountInMoles setup
  universalGasConstantPositive :
    0 < setup.universalGasConstantJoulesPerMoleKelvin
  heatCapacityRatioGreaterThanOne : 1 < setup.heatCapacityRatio

/--
The governing undergraduate thermodynamics:

* every state obeys the ideal-gas equation in coherent SI readouts;
* a diatomic ideal gas has internal energy five-halves n R T;
* an isochoric leg does no boundary work;
* an adiabatic leg has zero heat transfer and obeys the temperature-volume law;
* quasistatic isothermal work has the standard logarithmic form;
* with heat positive into the gas and work positive by the gas, the first law
  on each leg relates heat, internal-energy change, and work.

These uniform laws state no net cycle work, heat input, efficiency,
approximation, or answer choice.
-/
structure SatisfiesDiatomicIdealGasCycleLaws
    {AmountOfSubstance : Type}
    (setup : DiatomicHeatEngineSetup AmountOfSubstance) : Prop where
  idealGasEquation : ∀ state,
    pressureInPascals (setup.stateAt state).pressure *
        volumeInCubicMeters (setup.stateAt state).volume =
      gasAmountInMoles setup *
        setup.universalGasConstantJoulesPerMoleKelvin *
          stateTemperatureInKelvin setup state
  diatomicInternalEnergy : ∀ state,
    internalEnergyInJoules setup state =
      (5 / 2 : ℝ) * gasAmountInMoles setup *
        setup.universalGasConstantJoulesPerMoleKelvin *
          stateTemperatureInKelvin setup state
  isochoricBoundaryWork : ∀ leg,
    setup.processKind leg = .isochoric →
      workDoneByGasInJoules setup leg = 0
  adiabaticHeatTransfer : ∀ leg,
    setup.processKind leg = .adiabatic →
      heatTransferredIntoGasInJoules setup leg = 0
  adiabaticTemperatureVolumeRelation : ∀ leg,
    setup.processKind leg = .adiabatic →
      stateTemperatureInKelvin setup (legSource leg) *
          Real.rpow
            (volumeInCubicMeters (setup.stateAt (legSource leg)).volume)
            (setup.heatCapacityRatio - 1) =
        stateTemperatureInKelvin setup (legTarget leg) *
          Real.rpow
            (volumeInCubicMeters (setup.stateAt (legTarget leg)).volume)
            (setup.heatCapacityRatio - 1)
  quasistaticIsothermalBoundaryWork : ∀ leg,
    setup.processRegime = .quasistaticEquilibrium →
      setup.processKind leg = .isothermal →
        workDoneByGasInJoules setup leg =
          gasAmountInMoles setup *
            setup.universalGasConstantJoulesPerMoleKelvin *
              stateTemperatureInKelvin setup (legSource leg) *
                Real.log
                  (volumeInCubicMeters
                      (setup.stateAt (legTarget leg)).volume /
                    volumeInCubicMeters
                      (setup.stateAt (legSource leg)).volume)
  firstLawOnEachLeg : ∀ leg,
    heatTransferredIntoGasInJoules setup leg =
      internalEnergyInJoules setup (legTarget leg) -
        internalEnergyInJoules setup (legSource leg) +
          workDoneByGasInJoules setup leg

/-! ## Derived work, heat input, efficiency, and displayed answers -/

/-- Net work done by the gas over the complete directed cycle, in joules. -/
def netCycleWorkInJoules
    {AmountOfSubstance : Type}
    (setup : DiatomicHeatEngineSetup AmountOfSubstance) : ℝ :=
  ∑ leg : CycleLeg, workDoneByGasInJoules setup leg

/--
Total heat input is the sum of positive parts of the three signed leg heats,
so no input leg is selected by definition.
-/
def totalHeatInputInJoules
    {AmountOfSubstance : Type}
    (setup : DiatomicHeatEngineSetup AmountOfSubstance) : ℝ :=
  ∑ leg : CycleLeg, max (heatTransferredIntoGasInJoules setup leg) 0

/-- Dimensionless heat-engine efficiency as net work divided by heat input. -/
def thermalEfficiency
    {AmountOfSubstance : Type}
    (setup : DiatomicHeatEngineSetup AmountOfSubstance) : ℝ :=
  netCycleWorkInJoules setup / totalHeatInputInJoules setup

/-- Labels of the four dimensionless efficiency choices in the source problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Dimensionless efficiency printed beside each answer label. -/
def displayedEfficiency : AnswerChoice → ℝ
  | .A => 0
  | .B => 1
  | .C => 3 / 4
  | .D => 1 / 4

/-- Dataset answer metadata, deliberately not used as a theorem premise. -/
def recordedDatasetAnswer : AnswerChoice := .D

/-- The reported work is the nearest whole number of joules. -/
def RoundsToNearestJoule (actual displayed : ℝ) : Prop :=
  displayed - 1 / 2 ≤ actual ∧ actual < displayed + 1 / 2

/-- The exact efficiency rounds to the displayed value at two decimal places. -/
def RoundsToDisplayedHundredth (actual displayed : ℝ) : Prop :=
  displayed - 1 / 200 ≤ actual ∧ actual < displayed + 1 / 200

/-- A displayed choice agrees with the computed efficiency to two decimal places. -/
def IsRoundedEfficiencyAnswer
    (actual : ℝ) (choice : AnswerChoice) : Prop :=
  RoundsToDisplayedHundredth actual (displayedEfficiency choice)

/-- A choice is the unique displayed efficiency agreeing with the calculation. -/
def IsUniqueRoundedEfficiencyAnswer
    (actual : ℝ) (choice : AnswerChoice) : Prop :=
  IsRoundedEfficiencyAnswer actual choice ∧
    ∀ other, IsRoundedEfficiencyAnswer actual other → other = choice

/--
The two labelled endpoint states have the same coherent pressure-volume
product, namely 400 joules.  This uses only primary-image readouts.
-/
lemma endpointPressureVolumeProducts
    {AmountOfSubstance : Type}
    (setup : DiatomicHeatEngineSetup AmountOfSubstance)
    (hFigure : MatchesSuppliedPressureVolumeFigure setup) :
    pressureInPascals (setup.stateAt .one).pressure *
        volumeInCubicMeters (setup.stateAt .one).volume = 400 ∧
      pressureInPascals (setup.stateAt .three).pressure *
        volumeInCubicMeters (setup.stateAt .three).volume = 400 := by
  constructor
  · have hP := hFigure.stateOnePressureKilopascals
    have hV := hFigure.stateOneVolumeCubicCentimeters
    norm_num [pressureInKilopascals, volumeInCubicCentimeters] at hP hV ⊢
    nlinarith
  · have hP := hFigure.stateThreePressureKilopascals
    have hV := hFigure.stateThreeVolumeCubicCentimeters
    norm_num [pressureInKilopascals, volumeInCubicCentimeters] at hP hV ⊢
    nlinarith

/--
The adiabatic expansion and volume ratio four determine the state-2
temperature for a diatomic gas.
-/
lemma stateTwoTemperatureInKelvin
    {AmountOfSubstance : Type}
    (setup : DiatomicHeatEngineSetup AmountOfSubstance)
    (hScenario : MatchesDiatomicHeatEngineScenario setup)
    (hFigure : MatchesSuppliedPressureVolumeFigure setup)
    (hPhysical : HasPhysicalCycleParameters setup)
    (hLaws : SatisfiesDiatomicIdealGasCycleLaws setup) :
    stateTemperatureInKelvin setup .two =
      300 * Real.rpow 4 (2 / 5 : ℝ) := by
  have hAd :=
    hLaws.adiabaticTemperatureVolumeRelation .twoToThree
      hScenario.secondLegIsAdiabatic
  simp only [legSource, legTarget] at hAd
  have hV2Raw := hFigure.stateTwoSharesStateOneVolume
  have hV3Raw := hFigure.stateThreeVolumeCubicCentimeters
  norm_num [volumeInCubicCentimeters] at hV2Raw hV3Raw
  have hV2 :
      volumeInCubicMeters (setup.stateAt .two).volume = (1 / 1000 : ℝ) := by
    linarith
  have hV3 :
      volumeInCubicMeters (setup.stateAt .three).volume = (1 / 250 : ℝ) := by
    linarith
  rw [hScenario.diatomicHeatCapacityRatio, hV2, hV3,
    hFigure.isothermTemperatureAtStateThree] at hAd
  norm_num at hAd
  rw [show (1 / 250 : ℝ) = 4 * (1 / 1000) by norm_num,
    Real.mul_rpow (by norm_num) (by norm_num)] at hAd
  have hV2Pos := hPhysical.volumePositive .two
  rw [hV2] at hV2Pos
  have hPos : 0 < Real.rpow (1 / 1000 : ℝ) (2 / 5 : ℝ) :=
    Real.rpow_pos_of_pos hV2Pos _
  exact mul_right_cancel₀ (ne_of_gt hPos) (by simpa [mul_assoc] using hAd)

/--
For this cycle the isochoric heat input is
1000 times (four to the two-fifths power minus one) joules.  The adiabatic
expansion converts that internal-energy increase into work, while the 300 K
isothermal compression contributes minus 400 log 4 joules.  Thus the net work
rounds to 187 joules and the exact efficiency rounds uniquely to choice D.

This formalizes theorem label thm:physics:phyx_mini_0430:target.
-/
theorem problem_phyx_mini_0430
    {AmountOfSubstance : Type}
    (setup : DiatomicHeatEngineSetup AmountOfSubstance)
    (hScenario : MatchesDiatomicHeatEngineScenario setup)
    (hFigure : MatchesSuppliedPressureVolumeFigure setup)
    (hPhysical : HasPhysicalCycleParameters setup)
    (hLaws : SatisfiesDiatomicIdealGasCycleLaws setup) :
    totalHeatInputInJoules setup =
        1000 * (Real.rpow 4 (2 / 5 : ℝ) - 1) ∧
      netCycleWorkInJoules setup =
        1000 * (Real.rpow 4 (2 / 5 : ℝ) - 1) - 400 * Real.log 4 ∧
      RoundsToNearestJoule (netCycleWorkInJoules setup) 187 ∧
      thermalEfficiency setup =
        (1000 * (Real.rpow 4 (2 / 5 : ℝ) - 1) - 400 * Real.log 4) /
          (1000 * (Real.rpow 4 (2 / 5 : ℝ) - 1)) ∧
      IsUniqueRoundedEfficiencyAnswer (thermalEfficiency setup) .D := by
  have hPV := endpointPressureVolumeProducts setup hFigure
  have hT2 :=
    stateTwoTemperatureInKelvin setup hScenario hFigure hPhysical hLaws
  have hV1Raw := hFigure.stateOneVolumeCubicCentimeters
  have hV3Raw := hFigure.stateThreeVolumeCubicCentimeters
  norm_num [volumeInCubicCentimeters] at hV1Raw hV3Raw
  have hV1 :
      volumeInCubicMeters (setup.stateAt .one).volume = (1 / 1000 : ℝ) := by
    linarith
  have hV3 :
      volumeInCubicMeters (setup.stateAt .three).volume = (1 / 250 : ℝ) := by
    linarith
  have hNRT := hLaws.idealGasEquation .one
  rw [hPV.1, hFigure.isothermTemperatureAtStateOne] at hNRT
  have hNRT' :
      gasAmountInMoles setup *
          setup.universalGasConstantJoulesPerMoleKelvin * 300 =
        400 :=
    hNRT.symm
  have hU1 : internalEnergyInJoules setup .one = 1000 := by
    rw [hLaws.diatomicInternalEnergy .one,
      hFigure.isothermTemperatureAtStateOne]
    calc
      (5 / 2 : ℝ) * gasAmountInMoles setup *
            setup.universalGasConstantJoulesPerMoleKelvin * 300 =
          (5 / 2 : ℝ) *
            (gasAmountInMoles setup *
              setup.universalGasConstantJoulesPerMoleKelvin * 300) := by
                ring
      _ = (5 / 2 : ℝ) * 400 := by rw [hNRT']
      _ = 1000 := by norm_num
  have hU2 :
      internalEnergyInJoules setup .two =
        1000 * Real.rpow 4 (2 / 5 : ℝ) := by
    rw [hLaws.diatomicInternalEnergy .two, hT2]
    calc
      (5 / 2 : ℝ) * gasAmountInMoles setup *
            setup.universalGasConstantJoulesPerMoleKelvin *
              (300 * Real.rpow 4 (2 / 5 : ℝ)) =
          ((5 / 2 : ℝ) *
              (gasAmountInMoles setup *
                setup.universalGasConstantJoulesPerMoleKelvin * 300)) *
            Real.rpow 4 (2 / 5 : ℝ) := by
              ring
      _ = (5 / 2 : ℝ) * 400 * Real.rpow 4 (2 / 5 : ℝ) := by rw [hNRT']
      _ = 1000 * Real.rpow 4 (2 / 5 : ℝ) := by ring
  have hU3 : internalEnergyInJoules setup .three = 1000 := by
    rw [hLaws.diatomicInternalEnergy .three,
      hFigure.isothermTemperatureAtStateThree]
    calc
      (5 / 2 : ℝ) * gasAmountInMoles setup *
            setup.universalGasConstantJoulesPerMoleKelvin * 300 =
          (5 / 2 : ℝ) *
            (gasAmountInMoles setup *
              setup.universalGasConstantJoulesPerMoleKelvin * 300) := by
                ring
      _ = (5 / 2 : ℝ) * 400 := by rw [hNRT']
      _ = 1000 := by norm_num
  have hW12 :=
    hLaws.isochoricBoundaryWork .oneToTwo hScenario.firstLegIsIsochoric
  have hQ23 :=
    hLaws.adiabaticHeatTransfer .twoToThree hScenario.secondLegIsAdiabatic
  have hFirst23 := hLaws.firstLawOnEachLeg .twoToThree
  simp only [legSource, legTarget] at hFirst23
  have hW23 :
      workDoneByGasInJoules setup .twoToThree =
        1000 * (Real.rpow 4 (2 / 5 : ℝ) - 1) := by
    rw [hQ23, hU3, hU2] at hFirst23
    linarith
  have hW31 :=
    hLaws.quasistaticIsothermalBoundaryWork .threeToOne
      hScenario.processIsQuasistatic hScenario.thirdLegIsIsothermal
  simp only [legSource, legTarget] at hW31
  rw [hV1, hV3, hFigure.isothermTemperatureAtStateThree, hNRT'] at hW31
  norm_num at hW31
  have hLogInv : Real.log (1 / 4 : ℝ) = -Real.log 4 := by
    convert Real.log_inv (4 : ℝ) using 1
    all_goals norm_num
  rw [hLogInv] at hW31
  ring_nf at hW31
  have hAgtOne : 1 < Real.rpow 4 (2 / 5 : ℝ) :=
    Real.one_lt_rpow (by norm_num) (by norm_num)
  have hQ12First := hLaws.firstLawOnEachLeg .oneToTwo
  simp only [legSource, legTarget] at hQ12First
  have hQ12 :
      heatTransferredIntoGasInJoules setup .oneToTwo =
        1000 * (Real.rpow 4 (2 / 5 : ℝ) - 1) := by
    rw [hU2, hU1, hW12] at hQ12First
    linarith
  have hQ12Nonneg :
      0 ≤ heatTransferredIntoGasInJoules setup .oneToTwo := by
    rw [hQ12]
    nlinarith
  have hQ31First := hLaws.firstLawOnEachLeg .threeToOne
  simp only [legSource, legTarget] at hQ31First
  have hQ31 :
      heatTransferredIntoGasInJoules setup .threeToOne =
        -400 * Real.log 4 := by
    rw [hU1, hU3, hW31] at hQ31First
    linarith
  have hLogPos : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hQ31Nonpos :
      heatTransferredIntoGasInJoules setup .threeToOne ≤ 0 := by
    rw [hQ31]
    nlinarith
  have hLegs :
      (Finset.univ : Finset CycleLeg) =
        {.oneToTwo, .twoToThree, .threeToOne} := by
    decide
  have hHeat :
      totalHeatInputInJoules setup =
        1000 * (Real.rpow 4 (2 / 5 : ℝ) - 1) := by
    rw [totalHeatInputInJoules, hLegs]
    simp [hQ12, hQ23, hQ31]
    have hAgtOne' : (1 : ℝ) < (4 : ℝ) ^ (2 / 5 : ℝ) := by
      change 1 < Real.rpow 4 (2 / 5 : ℝ)
      exact hAgtOne
    rw [max_eq_left
      (mul_nonneg (by norm_num) (sub_nonneg.mpr hAgtOne'.le))]
    rw [max_eq_right
      (neg_nonpos.mpr (mul_nonneg (by norm_num) hLogPos.le))]
    ring
  have hNet :
      netCycleWorkInJoules setup =
        1000 * (Real.rpow 4 (2 / 5 : ℝ) - 1) - 400 * Real.log 4 := by
    rw [netCycleWorkInJoules, hLegs]
    simp [hW12, hW23, hW31]
    ring
  have hAPos : 0 < Real.rpow 4 (2 / 5 : ℝ) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hAPowFive : (Real.rpow 4 (2 / 5 : ℝ)) ^ 5 = 16 := by
    have hRoot :
        Real.rpow 4 (2 / 5 : ℝ) = Real.rpow 16 (5 : ℝ)⁻¹ := by
      change (4 : ℝ) ^ (2 / 5 : ℝ) = (16 : ℝ) ^ (5 : ℝ)⁻¹
      rw [show (2 / 5 : ℝ) = 2 * (5 : ℝ)⁻¹ by norm_num,
        Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 4)]
      norm_num
    rw [hRoot]
    exact Real.rpow_inv_natCast_pow (by norm_num) (by norm_num)
  have hALower :
      (17411 / 10000 : ℝ) < Real.rpow 4 (2 / 5 : ℝ) := by
    apply
      (pow_lt_pow_iff_left₀ (by norm_num) hAPos.le
        (by norm_num : 5 ≠ 0)).mp
    rw [hAPowFive]
    norm_num
  have hAUpper :
      Real.rpow 4 (2 / 5 : ℝ) < (17412 / 10000 : ℝ) := by
    apply
      (pow_lt_pow_iff_left₀ hAPos.le (by norm_num)
        (by norm_num : 5 ≠ 0)).mp
    rw [hAPowFive]
    norm_num
  have hLogLower :
      (13862943606 / 10000000000 : ℝ) < Real.log 4 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
    linarith [Real.log_two_gt_d9]
  have hLogUpper :
      Real.log 4 < (13862943616 / 10000000000 : ℝ) := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
    linarith [Real.log_two_lt_d9]
  have hWorkBounds :
      (187 : ℝ) - 1 / 2 ≤
          1000 * (Real.rpow 4 (2 / 5 : ℝ) - 1) - 400 * Real.log 4 ∧
        1000 * (Real.rpow 4 (2 / 5 : ℝ) - 1) - 400 * Real.log 4 <
          (187 : ℝ) + 1 / 2 := by
    constructor
    · nlinarith only [hALower, hLogUpper]
    · nlinarith only [hAUpper, hLogLower]
  have hEfficiency :
      thermalEfficiency setup =
        (1000 * (Real.rpow 4 (2 / 5 : ℝ) - 1) - 400 * Real.log 4) /
          (1000 * (Real.rpow 4 (2 / 5 : ℝ) - 1)) := by
    simp [thermalEfficiency, hHeat, hNet]
  have hHeatPositive :
      0 < 1000 * (Real.rpow 4 (2 / 5 : ℝ) - 1) := by
    nlinarith only [hAgtOne]
  have hEfficiencyBounds :
      (1 / 4 : ℝ) - 1 / 200 ≤ thermalEfficiency setup ∧
        thermalEfficiency setup < (1 / 4 : ℝ) + 1 / 200 := by
    rw [hEfficiency]
    constructor
    · rw [le_div_iff₀ hHeatPositive]
      nlinarith only [hALower, hLogUpper]
    · rw [div_lt_iff₀ hHeatPositive]
      nlinarith only [hAUpper, hLogLower]
  refine ⟨hHeat, hNet, ?_, hEfficiency, ?_⟩
  · simpa [RoundsToNearestJoule, hNet] using hWorkBounds
  · constructor
    · simpa [IsRoundedEfficiencyAnswer, RoundsToDisplayedHundredth,
        displayedEfficiency] using hEfficiencyBounds
    · intro other hOther
      cases other with
      | A =>
          simp [IsRoundedEfficiencyAnswer, RoundsToDisplayedHundredth,
            displayedEfficiency] at hOther
          exfalso
          nlinarith only [hOther, hEfficiencyBounds.1]
      | B =>
          simp [IsRoundedEfficiencyAnswer, RoundsToDisplayedHundredth,
            displayedEfficiency] at hOther
          exfalso
          nlinarith only [hOther, hEfficiencyBounds.2]
      | C =>
          simp [IsRoundedEfficiencyAnswer, RoundsToDisplayedHundredth,
            displayedEfficiency] at hOther
          exfalso
          nlinarith only [hOther, hEfficiencyBounds.2]
      | D => rfl

end PhyXMiniProblems.ProblemPhyXMini0430
