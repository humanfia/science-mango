import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Physlib.Thermodynamics.Temperature.Basic
import Physlib.Units.WithDim.Energy
import Physlib.Units.WithDim.Pressure

/- USER: The assigned source file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0429

open Dimension

/-!
# Efficiency of a diatomic-gas heat-engine cycle

The primary pressure--volume image shows the directed cycle

`1 → 2 → 3 → 1`.

The curved compression `1 → 2` is adiabatic, the curved expansion `2 → 3`
lies on the labelled `400 K` isotherm, and `3 → 1` is a horizontal isobaric
compression at `100 kPa`.  The readable state coordinates are

* state `2`: `(1000 cm³, 400 kPa)`,
* state `3`: `(4000 cm³, 100 kPa)`, and
* state `1`: pressure `100 kPa`, with its volume plotted strictly between
  `2000 cm³` and `3000 cm³` rather than printed numerically.

Pressure, volume, energy, and absolute temperature retain physical types from
Physlib.  Real numbers below are explicitly unit readouts, molar constants,
dimensionless ratios, efficiencies, or displayed answer values.  Work is
positive when done by the gas and heat is positive when transferred into it.
-/

/-! ## Dimensionful quantities and calibrated readouts -/

/-- A nonnegative physical volume carrying the dimension length cubed. -/
abbrev VolumeQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * L𝓭 * L𝓭) NNReal)

/-- Read a dimensionful pressure in coherent SI units (pascals). -/
def pressureInPascals (pressure : DimPressure) : ℝ :=
  (pressure UnitChoices.SI).val

/-- Read pressure in the kilopascals printed on the vertical axis. -/
def pressureInKilopascals (pressure : DimPressure) : ℝ :=
  pressureInPascals pressure / 1000

/-- Read a physical volume in coherent SI units (cubic metres). -/
def volumeInCubicMetres (volume : VolumeQuantity) : ℝ :=
  ((volume UnitChoices.SI).val : ℝ)

/-- Read volume in the cubic centimetres used on the horizontal axis. -/
def volumeInCubicCentimetres (volume : VolumeQuantity) : ℝ :=
  volumeInCubicMetres volume * 1000000

/-- Read a signed physical energy in coherent SI units (joules). -/
def energyInJoules (energy : DimEnergy) : ℝ :=
  (energy UnitChoices.SI).val

/-- Read the absolute-temperature value in kelvins for this calibrated setup. -/
def temperatureInKelvin (temperature : Temperature) : ℝ :=
  temperature.toReal

/-- One `kPa · cm³`, expressed in joules. -/
def joulesPerKilopascalCubicCentimetre : ℝ :=
  1 / 1000

/-! ## Gas, state, cycle, and primary-figure vocabulary -/

/-- The thermodynamic working-substance model stated in the problem. -/
inductive GasModel where
  | idealDiatomic
  deriving DecidableEq, Repr

/-- The role played by the cyclic thermodynamic device. -/
inductive ThermodynamicDeviceRole where
  | heatEngine
  deriving DecidableEq, Repr

/-- The three numbered black points in the supplied diagram. -/
inductive CyclePoint where
  | one
  | two
  | three
  deriving DecidableEq, Fintype, Repr

/-- The three directed arrows forming one traversal of the cycle. -/
inductive CycleLeg where
  | oneToTwo
  | twoToThree
  | threeToOne
  deriving DecidableEq, Fintype, Repr

/-- Initial endpoint of each displayed directed leg. -/
def legStart : CycleLeg → CyclePoint
  | .oneToTwo => .one
  | .twoToThree => .two
  | .threeToOne => .three

/-- Final endpoint of each displayed directed leg. -/
def legFinish : CycleLeg → CyclePoint
  | .oneToTwo => .two
  | .twoToThree => .three
  | .threeToOne => .one

/-- Thermodynamic constraint named by, or inferred directly from, the plot. -/
inductive ProcessKind where
  | adiabatic
  | isothermal
  | isobaric
  deriving DecidableEq, Repr

/-- Geometric appearance of a process leg in the raster. -/
inductive PathGeometry where
  | curved
  | horizontal
  deriving DecidableEq, Repr

/-- Physical quantity assigned to a diagram axis. -/
inductive AxisQuantity where
  | pressure
  | volume
  deriving DecidableEq, Repr

/-- Units printed beside the two axes. -/
inductive AxisUnit where
  | kilopascal
  | cubicCentimetre
  deriving DecidableEq, Repr

/-- Text and numerical labels visible in the primary image. -/
inductive DiagramLabel where
  | pressureSymbolP
  | volumeSymbolV
  | pressure100
  | pressure400
  | volume0
  | volume2000
  | volume4000
  | state1
  | state2
  | state3
  | isotherm400K
  | adiabatic
  deriving DecidableEq, Fintype, Repr

/-- Pressure, volume, temperature, and internal energy at equilibrium. -/
structure ThermodynamicState where
  pressure : DimPressure
  volume : VolumeQuantity
  temperature : Temperature
  internalEnergy : DimEnergy

/-!
The diagram itself: axis assignments, plotted state readouts, directed arrows,
curve classifications, and the two process labels.  Its scalar coordinate
fields are calibrated readouts of dimensionful states, not replacement
physical quantities.
-/
structure PressureVolumeCycleFigure where
  horizontalAxisQuantity : AxisQuantity
  verticalAxisQuantity : AxisQuantity
  horizontalAxisUnit : AxisUnit
  verticalAxisUnit : AxisUnit
  showsLabel : DiagramLabel → Bool
  showsPoint : CyclePoint → Bool
  plottedVolumeCubicCentimetres : CyclePoint → ℝ
  plottedPressureKilopascals : CyclePoint → ℝ
  showsDirectedLeg : CycleLeg → Bool
  directedEndpoints : CycleLeg → CyclePoint × CyclePoint
  pathGeometry : CycleLeg → PathGeometry
  depictedProcessKind : CycleLeg → ProcessKind
  legBearingIsothermLabel : CycleLeg
  displayedIsothermTemperatureKelvin : ℝ
  legBearingAdiabaticLabel : CycleLeg

/-!
Independent observables for the ideal-diatomic-gas cycle.  The requested
efficiency is deliberately not a field: it is defined later from heat and
work readouts.
-/
structure DiatomicHeatEngineCycle where
  gasModel : GasModel
  deviceRole : ThermodynamicDeviceRole
  sameClosedGasSample : Bool
  quasistaticEquilibriumPath : Bool
  amountOfGasMoles : ℝ
  molarGasConstantJoulesPerMoleKelvin : ℝ
  stateAt : CyclePoint → ThermodynamicState
  processKind : CycleLeg → ProcessKind
  workDoneByGas : CycleLeg → DimEnergy
  heatTransferredIntoGas : CycleLeg → DimEnergy
  figure : PressureVolumeCycleFigure

/-- Pressure readout of one physical state in the figure's kilopascals. -/
def statePressureInKilopascals
    (setup : DiatomicHeatEngineCycle) (point : CyclePoint) : ℝ :=
  pressureInKilopascals (setup.stateAt point).pressure

/-- Volume readout of one physical state in the figure's cubic centimetres. -/
def stateVolumeInCubicCentimetres
    (setup : DiatomicHeatEngineCycle) (point : CyclePoint) : ℝ :=
  volumeInCubicCentimetres (setup.stateAt point).volume

/-- Temperature readout of one physical state in kelvins. -/
def stateTemperatureInKelvin
    (setup : DiatomicHeatEngineCycle) (point : CyclePoint) : ℝ :=
  temperatureInKelvin (setup.stateAt point).temperature

/-- Internal-energy readout of one physical state in joules. -/
def stateInternalEnergyInJoules
    (setup : DiatomicHeatEngineCycle) (point : CyclePoint) : ℝ :=
  energyInJoules (setup.stateAt point).internalEnergy

/-! ## Assumptions: scenario, figure data, and governing laws -/

/-- The working substance and operating regime stated or implied by the plot. -/
structure MatchesHeatEngineScenario
    (setup : DiatomicHeatEngineCycle) : Prop where
  gasIsIdealDiatomic : setup.gasModel = .idealDiatomic
  deviceIsHeatEngine : setup.deviceRole = .heatEngine
  sameClosedSample : setup.sameClosedGasSample = true
  pathIsQuasistatic : setup.quasistaticEquilibriumPath = true

/-!
Primary-image evidence.  State `1` has no printed volume value, so only the
strict interval visibly locating it between the `2000` and `3000 cm³` ticks is
recorded.  Its exact volume is a later thermodynamic conclusion.
-/
structure MatchesPrimaryPressureVolumeFigure
    (setup : DiatomicHeatEngineCycle) : Prop where
  horizontalAxisIsVolume : setup.figure.horizontalAxisQuantity = .volume
  verticalAxisIsPressure : setup.figure.verticalAxisQuantity = .pressure
  horizontalAxisUsesCubicCentimetres :
    setup.figure.horizontalAxisUnit = .cubicCentimetre
  verticalAxisUsesKilopascals :
    setup.figure.verticalAxisUnit = .kilopascal
  everyPrintedLabelShown :
    ∀ label : DiagramLabel, setup.figure.showsLabel label = true
  everyStatePointShown :
    ∀ point : CyclePoint, setup.figure.showsPoint point = true
  stateOnePressureCoordinate :
    setup.figure.plottedPressureKilopascals .one = 100
  stateOneVolumeBetweenVisibleTicks :
    2000 < setup.figure.plottedVolumeCubicCentimetres .one ∧
      setup.figure.plottedVolumeCubicCentimetres .one < 3000
  stateTwoCoordinate :
    setup.figure.plottedVolumeCubicCentimetres .two = 1000 ∧
      setup.figure.plottedPressureKilopascals .two = 400
  stateThreeCoordinate :
    setup.figure.plottedVolumeCubicCentimetres .three = 4000 ∧
      setup.figure.plottedPressureKilopascals .three = 100
  plottedCoordinatesRepresentPhysicalStates :
    ∀ point : CyclePoint,
      setup.figure.plottedVolumeCubicCentimetres point =
          stateVolumeInCubicCentimetres setup point ∧
        setup.figure.plottedPressureKilopascals point =
          statePressureInKilopascals setup point
  everyDirectedLegShown :
    ∀ leg : CycleLeg, setup.figure.showsDirectedLeg leg = true
  arrowsFollowOneTwoThreeOneCycle :
    ∀ leg : CycleLeg,
      setup.figure.directedEndpoints leg = (legStart leg, legFinish leg)
  oneToTwoIsCurved : setup.figure.pathGeometry .oneToTwo = .curved
  twoToThreeIsCurved : setup.figure.pathGeometry .twoToThree = .curved
  threeToOneIsHorizontal : setup.figure.pathGeometry .threeToOne = .horizontal
  oneToTwoIsAdiabatic :
    setup.figure.depictedProcessKind .oneToTwo = .adiabatic
  twoToThreeIsIsothermal :
    setup.figure.depictedProcessKind .twoToThree = .isothermal
  threeToOneIsIsobaric :
    setup.figure.depictedProcessKind .threeToOne = .isobaric
  processKindsAgreeWithFigure :
    ∀ leg : CycleLeg,
      setup.processKind leg = setup.figure.depictedProcessKind leg
  isothermLabelIsOnTwoToThree :
    setup.figure.legBearingIsothermLabel = .twoToThree
  isothermLabelReads400Kelvin :
    setup.figure.displayedIsothermTemperatureKelvin = 400
  stateTwoLiesOnLabelledIsotherm :
    stateTemperatureInKelvin setup .two =
      setup.figure.displayedIsothermTemperatureKelvin
  stateThreeLiesOnLabelledIsotherm :
    stateTemperatureInKelvin setup .three =
      setup.figure.displayedIsothermTemperatureKelvin
  adiabaticLabelIsOnOneToTwo :
    setup.figure.legBearingAdiabaticLabel = .oneToTwo

/-- Positivity and nondegeneracy of the physical parameters and states. -/
structure HasPhysicalThermodynamicParameters
    (setup : DiatomicHeatEngineCycle) : Prop where
  amountPositive : 0 < setup.amountOfGasMoles
  gasConstantPositive :
    0 < setup.molarGasConstantJoulesPerMoleKelvin
  pressurePositive :
    ∀ point, 0 < statePressureInKilopascals setup point
  volumePositive :
    ∀ point, 0 < stateVolumeInCubicCentimetres setup point
  temperaturePositive :
    ∀ point, 0 < stateTemperatureInKelvin setup point

/-- `Cᵥ/R` for an ideal diatomic gas with active translational and rotational modes. -/
def diatomicCvOverR : ℝ :=
  5 / 2

/-- `Cₚ/R = Cᵥ/R + 1` for the same ideal diatomic gas. -/
def diatomicCpOverR : ℝ :=
  7 / 2

/-- Heat-capacity ratio `γ = Cₚ/Cᵥ` for the same gas. -/
def diatomicHeatCapacityRatio : ℝ :=
  7 / 5

/-!
The macroscopic laws used to interpret the cycle:

* `pV = nRT` and `U = (5/2)nRT` at each equilibrium state;
* the first law `Q = ΔU + W_by` on every directed leg;
* zero heat and the dimensionless pressure--volume ratio law on an adiabatic
  leg;
* equal endpoint temperatures and logarithmic ideal-gas work on an isothermal
  leg;
* equal endpoint pressures and `p ΔV` boundary work on an isobaric leg.

These are uniform laws for arbitrary state values.  They contain no derived
state-1 volume, cycle heat totals, efficiency, decimal answer, or answer label.
-/
structure SatisfiesIdealDiatomicGasLaws
    (setup : DiatomicHeatEngineCycle) : Prop where
  idealGasLaw : ∀ point : CyclePoint,
    pressureInPascals (setup.stateAt point).pressure *
        volumeInCubicMetres (setup.stateAt point).volume =
      setup.amountOfGasMoles *
        setup.molarGasConstantJoulesPerMoleKelvin *
        stateTemperatureInKelvin setup point
  diatomicInternalEnergyLaw : ∀ point : CyclePoint,
    stateInternalEnergyInJoules setup point =
      diatomicCvOverR * setup.amountOfGasMoles *
        setup.molarGasConstantJoulesPerMoleKelvin *
        stateTemperatureInKelvin setup point
  firstLawOnEachLeg : ∀ leg : CycleLeg,
    energyInJoules (setup.heatTransferredIntoGas leg) =
      stateInternalEnergyInJoules setup (legFinish leg) -
          stateInternalEnergyInJoules setup (legStart leg) +
        energyInJoules (setup.workDoneByGas leg)
  adiabaticLaw : ∀ leg : CycleLeg,
    setup.processKind leg = .adiabatic →
      energyInJoules (setup.heatTransferredIntoGas leg) = 0 ∧
        pressureInPascals (setup.stateAt (legFinish leg)).pressure /
            pressureInPascals (setup.stateAt (legStart leg)).pressure =
          Real.rpow
            (volumeInCubicMetres (setup.stateAt (legStart leg)).volume /
              volumeInCubicMetres (setup.stateAt (legFinish leg)).volume)
            diatomicHeatCapacityRatio
  isothermalLaw : ∀ leg : CycleLeg,
    setup.processKind leg = .isothermal →
      stateTemperatureInKelvin setup (legFinish leg) =
          stateTemperatureInKelvin setup (legStart leg) ∧
        energyInJoules (setup.workDoneByGas leg) =
          setup.amountOfGasMoles *
            setup.molarGasConstantJoulesPerMoleKelvin *
            stateTemperatureInKelvin setup (legStart leg) *
            Real.log
              (volumeInCubicMetres
                    (setup.stateAt (legFinish leg)).volume /
                volumeInCubicMetres
                    (setup.stateAt (legStart leg)).volume)
  isobaricLaw : ∀ leg : CycleLeg,
    setup.processKind leg = .isobaric →
      pressureInPascals (setup.stateAt (legFinish leg)).pressure =
          pressureInPascals (setup.stateAt (legStart leg)).pressure ∧
        energyInJoules (setup.workDoneByGas leg) =
          pressureInPascals (setup.stateAt (legStart leg)).pressure *
            (volumeInCubicMetres
                  (setup.stateAt (legFinish leg)).volume -
              volumeInCubicMetres
                  (setup.stateAt (legStart leg)).volume)

/-! ## Heat accounting, efficiency, and displayed choices -/

/-- Net work done by the gas during one traversal of the three legs. -/
def netWorkByGasInJoules (setup : DiatomicHeatEngineCycle) : ℝ :=
  energyInJoules (setup.workDoneByGas .oneToTwo) +
    energyInJoules (setup.workDoneByGas .twoToThree) +
    energyInJoules (setup.workDoneByGas .threeToOne)

/-- Total absorbed heat: the sum of positive parts of all signed leg heats. -/
def totalHeatInputInJoules (setup : DiatomicHeatEngineCycle) : ℝ :=
  max (energyInJoules (setup.heatTransferredIntoGas .oneToTwo)) 0 +
    max (energyInJoules (setup.heatTransferredIntoGas .twoToThree)) 0 +
    max (energyInJoules (setup.heatTransferredIntoGas .threeToOne)) 0

/-- Dimensionless thermal efficiency `W_net / Q_in`. -/
def thermalEfficiency (setup : DiatomicHeatEngineCycle) : ℝ :=
  netWorkByGasInJoules setup / totalHeatInputInJoules setup

/-- Labels of the four choices printed with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Dimensionless decimal value printed beside each answer label. -/
def displayedEfficiency : AnswerChoice → ℝ
  | .A => 582 / 100
  | .B => 21 / 100
  | .C => 24 / 100
  | .D => 17 / 100

/-- A calculated efficiency rounds to a displayed value at two decimal places. -/
def MatchesToNearestHundredth
    (setup : DiatomicHeatEngineCycle) (choice : AnswerChoice) : Prop :=
  |thermalEfficiency setup - displayedEfficiency choice| < (1 / 200 : ℝ)

/-- The specified answer is the unique displayed two-decimal match. -/
def IsUniqueMatchingDisplayedEfficiency
    (setup : DiatomicHeatEngineCycle) (choice : AnswerChoice) : Prop :=
  MatchesToNearestHundredth setup choice ∧
    ∀ other : AnswerChoice,
      MatchesToNearestHundredth setup other → other = choice

/-!
The adiabatic ratio law fixes the unprinted state-1 volume.  The first law and
the two remaining process laws then give the three signed heats, the absorbed
heat, and the net work.  All quantities in this lemma are conclusions rather
than figure-data or law fields.
-/
lemma derivedStateAndHeatReadouts
    (setup : DiatomicHeatEngineCycle)
    (_scenario : MatchesHeatEngineScenario setup)
    (_figure : MatchesPrimaryPressureVolumeFigure setup)
    (_physical : HasPhysicalThermodynamicParameters setup)
    (_laws : SatisfiesIdealDiatomicGasLaws setup) :
    stateVolumeInCubicCentimetres setup .one =
        1000 * Real.rpow 4 ((5 : ℝ) / 7) ∧
      energyInJoules (setup.heatTransferredIntoGas .oneToTwo) = 0 ∧
      energyInJoules (setup.heatTransferredIntoGas .twoToThree) =
        400 * Real.log 4 ∧
      energyInJoules (setup.heatTransferredIntoGas .threeToOne) =
        diatomicCpOverR *
          (100 * Real.rpow 4 ((5 : ℝ) / 7) - 400) ∧
      totalHeatInputInJoules setup = 400 * Real.log 4 ∧
      netWorkByGasInJoules setup =
        400 * Real.log 4 +
          diatomicCpOverR *
            (100 * Real.rpow 4 ((5 : ℝ) / 7) - 400) := by
  have hprocess₁₂ : setup.processKind .oneToTwo = .adiabatic := by
    rw [_figure.processKindsAgreeWithFigure]
    exact _figure.oneToTwoIsAdiabatic
  have hprocess₂₃ : setup.processKind .twoToThree = .isothermal := by
    rw [_figure.processKindsAgreeWithFigure]
    exact _figure.twoToThreeIsIsothermal
  have hprocess₃₁ : setup.processKind .threeToOne = .isobaric := by
    rw [_figure.processKindsAgreeWithFigure]
    exact _figure.threeToOneIsIsobaric
  have hV₁cc :
      stateVolumeInCubicCentimetres setup .one =
        setup.figure.plottedVolumeCubicCentimetres .one :=
    (_figure.plottedCoordinatesRepresentPhysicalStates .one).1.symm
  have hV₂cc : stateVolumeInCubicCentimetres setup .two = 1000 := by
    calc
      stateVolumeInCubicCentimetres setup .two =
          setup.figure.plottedVolumeCubicCentimetres .two :=
        (_figure.plottedCoordinatesRepresentPhysicalStates .two).1.symm
      _ = 1000 := _figure.stateTwoCoordinate.1
  have hV₃cc : stateVolumeInCubicCentimetres setup .three = 4000 := by
    calc
      stateVolumeInCubicCentimetres setup .three =
          setup.figure.plottedVolumeCubicCentimetres .three :=
        (_figure.plottedCoordinatesRepresentPhysicalStates .three).1.symm
      _ = 4000 := _figure.stateThreeCoordinate.1
  have hP₁kPa : statePressureInKilopascals setup .one = 100 := by
    calc
      statePressureInKilopascals setup .one =
          setup.figure.plottedPressureKilopascals .one :=
        (_figure.plottedCoordinatesRepresentPhysicalStates .one).2.symm
      _ = 100 := _figure.stateOnePressureCoordinate
  have hP₂kPa : statePressureInKilopascals setup .two = 400 := by
    calc
      statePressureInKilopascals setup .two =
          setup.figure.plottedPressureKilopascals .two :=
        (_figure.plottedCoordinatesRepresentPhysicalStates .two).2.symm
      _ = 400 := _figure.stateTwoCoordinate.2
  have hP₃kPa : statePressureInKilopascals setup .three = 100 := by
    calc
      statePressureInKilopascals setup .three =
          setup.figure.plottedPressureKilopascals .three :=
        (_figure.plottedCoordinatesRepresentPhysicalStates .three).2.symm
      _ = 100 := _figure.stateThreeCoordinate.2
  have hV₂m :
      volumeInCubicMetres (setup.stateAt .two).volume = 1 / 1000 := by
    unfold stateVolumeInCubicCentimetres volumeInCubicCentimetres at hV₂cc
    linarith
  have hV₃m :
      volumeInCubicMetres (setup.stateAt .three).volume = 1 / 250 := by
    unfold stateVolumeInCubicCentimetres volumeInCubicCentimetres at hV₃cc
    linarith
  have hP₁Pa :
      pressureInPascals (setup.stateAt .one).pressure = 100000 := by
    unfold statePressureInKilopascals pressureInKilopascals at hP₁kPa
    linarith
  have hP₂Pa :
      pressureInPascals (setup.stateAt .two).pressure = 400000 := by
    unfold statePressureInKilopascals pressureInKilopascals at hP₂kPa
    linarith
  have hP₃Pa :
      pressureInPascals (setup.stateAt .three).pressure = 100000 := by
    unfold statePressureInKilopascals pressureInKilopascals at hP₃kPa
    linarith
  have hV₁m_pos :
      0 < volumeInCubicMetres (setup.stateAt .one).volume := by
    have h := _physical.volumePositive .one
    unfold stateVolumeInCubicCentimetres volumeInCubicCentimetres at h
    norm_num at h
    linarith
  have hvolumeRatio :
      volumeInCubicMetres (setup.stateAt .one).volume /
          volumeInCubicMetres (setup.stateAt .two).volume =
        Real.rpow 4 ((5 : ℝ) / 7) := by
    have hadi := (_laws.adiabaticLaw .oneToTwo hprocess₁₂).2
    simp only [legFinish, legStart] at hadi
    rw [hP₂Pa, hP₁Pa, hV₂m] at hadi
    norm_num [diatomicHeatCapacityRatio] at hadi
    have hratio_nonneg :
        0 ≤
          volumeInCubicMetres (setup.stateAt .one).volume /
            (1 / 1000 : ℝ) := by
      positivity
    rw [hV₂m]
    calc
      volumeInCubicMetres (setup.stateAt .one).volume / (1 / 1000 : ℝ) =
          Real.rpow
            (volumeInCubicMetres (setup.stateAt .one).volume / (1 / 1000 : ℝ))
            (((7 : ℝ) / 5) * ((5 : ℝ) / 7)) := by norm_num
      _ =
          Real.rpow
            (Real.rpow
              (volumeInCubicMetres (setup.stateAt .one).volume / (1 / 1000 : ℝ))
              ((7 : ℝ) / 5))
            ((5 : ℝ) / 7) :=
        Real.rpow_mul hratio_nonneg ((7 : ℝ) / 5) ((5 : ℝ) / 7)
      _ = Real.rpow 4 ((5 : ℝ) / 7) :=
        congrArg (fun x : ℝ => Real.rpow x ((5 : ℝ) / 7)) hadi.symm
  have hV₁m :
      volumeInCubicMetres (setup.stateAt .one).volume =
        Real.rpow 4 ((5 : ℝ) / 7) / 1000 := by
    rw [hV₂m] at hvolumeRatio
    field_simp at hvolumeRatio ⊢
    linarith
  have hV₁cc_exact :
      stateVolumeInCubicCentimetres setup .one =
        1000 * Real.rpow 4 ((5 : ℝ) / 7) := by
    unfold stateVolumeInCubicCentimetres volumeInCubicCentimetres
    rw [hV₁m]
    ring
  have hnRT₁ :
      setup.amountOfGasMoles *
          setup.molarGasConstantJoulesPerMoleKelvin *
          stateTemperatureInKelvin setup .one =
        100 * Real.rpow 4 ((5 : ℝ) / 7) := by
    rw [← _laws.idealGasLaw .one, hP₁Pa, hV₁m]
    ring
  have hnRT₂ :
      setup.amountOfGasMoles *
          setup.molarGasConstantJoulesPerMoleKelvin *
          stateTemperatureInKelvin setup .two =
        400 := by
    rw [← _laws.idealGasLaw .two, hP₂Pa, hV₂m]
    norm_num
  have hnRT₃ :
      setup.amountOfGasMoles *
          setup.molarGasConstantJoulesPerMoleKelvin *
          stateTemperatureInKelvin setup .three =
        400 := by
    rw [← _laws.idealGasLaw .three, hP₃Pa, hV₃m]
    norm_num
  have hU₁ :
      stateInternalEnergyInJoules setup .one =
        diatomicCvOverR * (100 * Real.rpow 4 ((5 : ℝ) / 7)) := by
    rw [_laws.diatomicInternalEnergyLaw .one]
    calc
      diatomicCvOverR * setup.amountOfGasMoles *
            setup.molarGasConstantJoulesPerMoleKelvin *
            stateTemperatureInKelvin setup .one =
          diatomicCvOverR *
            (setup.amountOfGasMoles *
              setup.molarGasConstantJoulesPerMoleKelvin *
              stateTemperatureInKelvin setup .one) := by ring
      _ = diatomicCvOverR * (100 * Real.rpow 4 ((5 : ℝ) / 7)) := by
        rw [hnRT₁]
  have hU₂ :
      stateInternalEnergyInJoules setup .two = diatomicCvOverR * 400 := by
    rw [_laws.diatomicInternalEnergyLaw .two]
    calc
      diatomicCvOverR * setup.amountOfGasMoles *
            setup.molarGasConstantJoulesPerMoleKelvin *
            stateTemperatureInKelvin setup .two =
          diatomicCvOverR *
            (setup.amountOfGasMoles *
              setup.molarGasConstantJoulesPerMoleKelvin *
              stateTemperatureInKelvin setup .two) := by ring
      _ = diatomicCvOverR * 400 := by rw [hnRT₂]
  have hU₃ :
      stateInternalEnergyInJoules setup .three = diatomicCvOverR * 400 := by
    rw [_laws.diatomicInternalEnergyLaw .three]
    calc
      diatomicCvOverR * setup.amountOfGasMoles *
            setup.molarGasConstantJoulesPerMoleKelvin *
            stateTemperatureInKelvin setup .three =
          diatomicCvOverR *
            (setup.amountOfGasMoles *
              setup.molarGasConstantJoulesPerMoleKelvin *
              stateTemperatureInKelvin setup .three) := by ring
      _ = diatomicCvOverR * 400 := by rw [hnRT₃]
  have hQ₁₂ :
      energyInJoules (setup.heatTransferredIntoGas .oneToTwo) = 0 :=
    (_laws.adiabaticLaw .oneToTwo hprocess₁₂).1
  have hW₂₃ :
      energyInJoules (setup.workDoneByGas .twoToThree) =
        400 * Real.log 4 := by
    have hiso := (_laws.isothermalLaw .twoToThree hprocess₂₃).2
    simp only [legFinish, legStart] at hiso
    rw [hV₂m, hV₃m] at hiso
    norm_num at hiso
    calc
      energyInJoules (setup.workDoneByGas .twoToThree) =
          (setup.amountOfGasMoles *
            setup.molarGasConstantJoulesPerMoleKelvin *
            stateTemperatureInKelvin setup .two) * Real.log 4 := hiso
      _ = 400 * Real.log 4 := by rw [hnRT₂]
  have hQ₂₃ :
      energyInJoules (setup.heatTransferredIntoGas .twoToThree) =
        400 * Real.log 4 := by
    have hfirst := _laws.firstLawOnEachLeg .twoToThree
    simp only [legFinish, legStart] at hfirst
    rw [hU₂, hU₃, hW₂₃] at hfirst
    linarith
  have hW₃₁ :
      energyInJoules (setup.workDoneByGas .threeToOne) =
        100 * Real.rpow 4 ((5 : ℝ) / 7) - 400 := by
    have hisob := (_laws.isobaricLaw .threeToOne hprocess₃₁).2
    simp only [legFinish, legStart] at hisob
    rw [hP₃Pa, hV₁m, hV₃m] at hisob
    norm_num at hisob ⊢
    linarith
  have hQ₃₁ :
      energyInJoules (setup.heatTransferredIntoGas .threeToOne) =
        diatomicCpOverR *
          (100 * Real.rpow 4 ((5 : ℝ) / 7) - 400) := by
    have hfirst := _laws.firstLawOnEachLeg .threeToOne
    simp only [legFinish, legStart] at hfirst
    rw [hU₁, hU₃, hW₃₁] at hfirst
    norm_num [diatomicCvOverR, diatomicCpOverR] at hfirst ⊢
    linarith
  have hlog₄_pos : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hrpow_lt_four :
      Real.rpow 4 ((5 : ℝ) / 7) < 4 := by
    exact Real.rpow_lt_self_of_one_lt (by norm_num) (by norm_num)
  have hQ₂₃_pos :
      0 < energyInJoules (setup.heatTransferredIntoGas .twoToThree) := by
    rw [hQ₂₃]
    positivity
  have hQ₃₁_neg :
      energyInJoules (setup.heatTransferredIntoGas .threeToOne) < 0 := by
    have hinner :
        100 * Real.rpow 4 ((5 : ℝ) / 7) - 400 < 0 := by
      nlinarith [hrpow_lt_four]
    rw [hQ₃₁]
    exact mul_neg_of_pos_of_neg (by norm_num [diatomicCpOverR]) hinner
  have htotalHeat :
      totalHeatInputInJoules setup = 400 * Real.log 4 := by
    unfold totalHeatInputInJoules
    rw [max_eq_right hQ₁₂.le, max_eq_left hQ₂₃_pos.le,
      max_eq_right hQ₃₁_neg.le, hQ₂₃]
    simp
  have hnetWork :
      netWorkByGasInJoules setup =
        400 * Real.log 4 +
          diatomicCpOverR *
            (100 * Real.rpow 4 ((5 : ℝ) / 7) - 400) := by
    have hfirst₁₂ := _laws.firstLawOnEachLeg .oneToTwo
    have hfirst₂₃ := _laws.firstLawOnEachLeg .twoToThree
    have hfirst₃₁ := _laws.firstLawOnEachLeg .threeToOne
    simp only [legFinish, legStart] at hfirst₁₂ hfirst₂₃ hfirst₃₁
    unfold netWorkByGasInJoules
    rw [hQ₁₂] at hfirst₁₂
    rw [hQ₂₃] at hfirst₂₃
    rw [hQ₃₁] at hfirst₃₁
    linarith
  exact
    ⟨hV₁cc_exact, hQ₁₂, hQ₂₃, hQ₃₁, htotalHeat, hnetWork⟩

/-!
The exact dimensionless efficiency is

`1 - 7(4 - 4^(5/7)) / (8 log 4) ≈ 0.17429`.

It therefore has the unique two-decimal display `0.17`, answer D.  Neither
this exact expression nor choice D occurs in any premise.

Blueprint label: `thm:physics:phyx_mini_0429:target`.
-/
theorem problem_phyx_mini_0429
    (setup : DiatomicHeatEngineCycle)
    (_scenario : MatchesHeatEngineScenario setup)
    (_figure : MatchesPrimaryPressureVolumeFigure setup)
    (_physical : HasPhysicalThermodynamicParameters setup)
    (_laws : SatisfiesIdealDiatomicGasLaws setup) :
    thermalEfficiency setup =
        1 -
          7 * (4 - Real.rpow 4 ((5 : ℝ) / 7)) /
            (8 * Real.log 4) ∧
      IsUniqueMatchingDisplayedEfficiency setup .D := by
  obtain ⟨_hV₁, _hQ₁₂, _hQ₂₃, _hQ₃₁, hheatInput, hnetWork⟩ :=
    derivedStateAndHeatReadouts setup _scenario _figure _physical _laws
  have hlog₄_pos : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hlog₄_ne : Real.log 4 ≠ 0 := hlog₄_pos.ne'
  have hefficiency :
      thermalEfficiency setup =
        1 -
          7 * (4 - Real.rpow 4 ((5 : ℝ) / 7)) /
            (8 * Real.log 4) := by
    unfold thermalEfficiency
    rw [hheatInput, hnetWork]
    norm_num [diatomicCpOverR]
    field_simp [hlog₄_ne]
    ring
  have hlog₂_lower : (693 / 1000 : ℝ) < Real.log 2 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num)]
    have hbound :=
      Real.exp_bound' (x := (693 / 1000 : ℝ))
        (by norm_num) (by norm_num) (n := 10) (by norm_num)
    norm_num [Finset.sum_range_succ, Nat.factorial] at hbound ⊢
    linarith
  have hlog₂_upper : Real.log 2 < (1387 / 2000 : ℝ) := by
    rw [Real.log_lt_iff_lt_exp (by norm_num)]
    have hbound :=
      Real.sum_le_exp_of_nonneg
        (x := (1387 / 2000 : ℝ)) (by norm_num) 10
    norm_num [Finset.sum_range_succ, Nat.factorial] at hbound ⊢
    linarith
  have hlog₄_eq : Real.log 4 = 2 * Real.log 2 := by
    convert Real.log_pow (2 : ℝ) 2 using 1 <;> norm_num
  have hlog₄_lower : (1386 / 1000 : ℝ) < Real.log 4 := by
    rw [hlog₄_eq]
    linarith
  have hlog₄_upper : Real.log 4 < (1387 / 1000 : ℝ) := by
    rw [hlog₄_eq]
    linarith
  have hrpow_seventh :
      (Real.rpow 4 ((5 : ℝ) / 7)) ^ (7 : ℕ) = 1024 := by
    rw [← Real.rpow_natCast]
    calc
      Real.rpow (Real.rpow 4 ((5 : ℝ) / 7)) (7 : ℝ) =
          Real.rpow 4 (((5 : ℝ) / 7) * 7) :=
        (Real.rpow_mul (show (0 : ℝ) ≤ 4 by norm_num)
          ((5 : ℝ) / 7) 7).symm
      _ = 1024 := by norm_num
  have hrpow_lower :
      (2691 / 1000 : ℝ) < Real.rpow 4 ((5 : ℝ) / 7) := by
    apply
      (pow_lt_pow_iff_left₀ (by norm_num)
        (Real.rpow_pos_of_pos (by norm_num) _).le
        (show (7 : ℕ) ≠ 0 by norm_num)).mp
    change
      (2691 / 1000 : ℝ) ^ (7 : ℕ) <
        (Real.rpow 4 ((5 : ℝ) / 7)) ^ (7 : ℕ)
    rw [hrpow_seventh]
    norm_num
  have hrpow_upper :
      Real.rpow 4 ((5 : ℝ) / 7) < (2692 / 1000 : ℝ) := by
    apply
      (pow_lt_pow_iff_left₀
        (Real.rpow_pos_of_pos (by norm_num) _).le
        (by norm_num) (show (7 : ℕ) ≠ 0 by norm_num)).mp
    change
      (Real.rpow 4 ((5 : ℝ) / 7)) ^ (7 : ℕ) <
      (2692 / 1000 : ℝ) ^ (7 : ℕ)
    rw [hrpow_seventh]
    norm_num
  have hdenominator_pos : 0 < 8 * Real.log 4 := by positivity
  have hcorrection_upper :
      7 * (4 - Real.rpow 4 ((5 : ℝ) / 7)) /
          (8 * Real.log 4) <
        (827 / 1000 : ℝ) := by
    apply (div_lt_iff₀ hdenominator_pos).2
    nlinarith
  have hcorrection_lower :
      (825 / 1000 : ℝ) <
        7 * (4 - Real.rpow 4 ((5 : ℝ) / 7)) /
          (8 * Real.log 4) := by
    apply (lt_div_iff₀ hdenominator_pos).2
    nlinarith
  have hefficiency_lower :
      (173 / 1000 : ℝ) < thermalEfficiency setup := by
    rw [hefficiency]
    linarith
  have hefficiency_upper :
      thermalEfficiency setup < (175 / 1000 : ℝ) := by
    rw [hefficiency]
    linarith
  refine ⟨hefficiency, ?_⟩
  unfold IsUniqueMatchingDisplayedEfficiency
  constructor
  · unfold MatchesToNearestHundredth
    rw [abs_lt]
    norm_num [displayedEfficiency]
    constructor <;> linarith
  · intro other hother
    cases other with
    | A =>
        unfold MatchesToNearestHundredth at hother
        rw [abs_lt] at hother
        norm_num [displayedEfficiency] at hother
        linarith
    | B =>
        unfold MatchesToNearestHundredth at hother
        rw [abs_lt] at hother
        norm_num [displayedEfficiency] at hother
        linarith
    | C =>
        unfold MatchesToNearestHundredth at hother
        rw [abs_lt] at hother
        norm_num [displayedEfficiency] at hother
        linarith
    | D => rfl

end PhyXMiniProblems.ProblemPhyXMini0429
