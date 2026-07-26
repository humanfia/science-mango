import Mathlib
import Physlib.Thermodynamics.Temperature.Basic
import Physlib.Thermodynamics.Temperature.TemperatureUnits
import Physlib.Units.WithDim.Energy
import Physlib.Units.WithDim.Pressure

/- USER: The assigned source file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0425

open Dimension
open scoped BigOperators

/-!
# Thermal efficiency of a rectangular pressure--volume cycle

One mole of a monatomic ideal gas traverses the clockwise rectangular cycle
`1 → 2 → 3 → 4 → 1` in the supplied `p`-`V` diagram.  The vertical legs are
isochoric and the horizontal legs are isobaric.  The primary image gives
`T₁ = 300 K`, a lower pressure of `300 kPa`, `Vmax = 2 Vmin`, and a heat input
of `3750 J` on `1 → 2`.

Pressure, volume, temperature, internal energy, heat, and work remain physical
quantities.  Real numbers below are explicitly named-unit readouts, mole
readouts, dimensionless efficiencies, or displayed answer values.
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

/-- Kilopascal readout of a physical pressure. -/
def pressureInKilopascals (pressure : DimPressure) : ℝ :=
  pressureInPascals pressure / 1000

/-- Joule readout of a signed physical energy, heat transfer, or work. -/
def energyInJoules (energy : DimEnergy) : ℝ :=
  (energy UnitChoices.SI).val /
    (DimEnergy.joule UnitChoices.SI).val

/--
Kelvin readout of a Physlib absolute temperature stored in an explicitly
chosen zero-preserving temperature unit.
-/
def temperatureInKelvin
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

/-- Initial state of each directed leg. -/
def legSource : CycleLeg → CycleState
  | .oneToTwo => .one
  | .twoToThree => .two
  | .threeToFour => .three
  | .fourToOne => .four

/-- Final state of each directed leg. -/
def legTarget : CycleLeg → CycleState
  | .oneToTwo => .two
  | .twoToThree => .three
  | .threeToFour => .four
  | .fourToOne => .one

/-- Thermodynamic constraint represented by a side of the rectangle. -/
inductive ProcessKind where
  | isochoric
  | isobaric
  deriving DecidableEq, Repr

/-- Geometric orientation of a straight segment in the `p`-`V` plane. -/
inductive SegmentOrientation where
  | vertical
  | horizontal
  deriving DecidableEq, Repr

/-- Process kinds read from the primary image. -/
def displayedProcessKind : CycleLeg → ProcessKind
  | .oneToTwo => .isochoric
  | .twoToThree => .isobaric
  | .threeToFour => .isochoric
  | .fourToOne => .isobaric

/-- Segment orientations read from the primary image. -/
def displayedSegmentOrientation : CycleLeg → SegmentOrientation
  | .oneToTwo => .vertical
  | .twoToThree => .horizontal
  | .threeToFour => .vertical
  | .fourToOne => .horizontal

/-- Physical quantity assigned to one of the two plotted axes. -/
inductive AxisQuantity where
  | volumeV
  | pressureP
  deriving DecidableEq, Repr

/-- Pressure unit printed beside the vertical axis. -/
inductive PressureDisplayUnit where
  | kilopascal
  deriving DecidableEq, Repr

/-- Literal labels and numeric annotations visible in the primary image. -/
inductive DiagramLabel where
  | stateOne
  | stateTwo
  | stateThree
  | stateFour
  | pressureMaximum
  | pressureThreeHundred
  | volumeMinimum
  | volumeMaximumEqualsTwiceMinimum
  | temperatureOneEqualsThreeHundredKelvin
  | heatInputThreeThousandSevenHundredFiftyJoules
  deriving DecidableEq, Fintype, Repr

/-- The rectangular pressure--volume diagram and its physical coordinates. -/
structure RectangularPVCycleFigure where
  minimumVolume : VolumeQuantity
  maximumVolume : VolumeQuantity
  lowerPressure : DimPressure
  maximumPressure : DimPressure
  volumeAt : CycleState → VolumeQuantity
  pressureAt : CycleState → DimPressure
  horizontalAxisQuantity : AxisQuantity
  verticalAxisQuantity : AxisQuantity
  pressureDisplayUnit : PressureDisplayUnit
  labelVisible : DiagramLabel → Bool
  arrowVisible : CycleLeg → Bool
  legDrawnStraight : CycleLeg → Bool

/-! ## Gas sample and thermodynamic observables -/

/-- Material model specified in the problem. -/
inductive GasModel where
  | monatomicIdealGas
  | other
  deriving DecidableEq, Repr

/-- Role of the cyclic thermodynamic device. -/
inductive ThermodynamicDeviceRole where
  | heatEngine
  | other
  deriving DecidableEq, Repr

/-!
The working gas, its diagram, and its state and process observables.  Amount
of substance is kept abstract; only the explicitly named mole readout is a
real number because Physlib's unit dimensions do not include amount of
substance.  Heat is positive into the gas and work is positive when done by
the gas.
-/
structure MonatomicRectangularHeatEngine (AmountOfSubstance : Type) where
  gasModel : GasModel
  deviceRole : ThermodynamicDeviceRole
  amountOfGas : AmountOfSubstance
  amountInMoles : AmountOfSubstance → ℝ
  figure : RectangularPVCycleFigure
  temperatureAt : CycleState → Temperature
  temperatureStorageUnit : TemperatureUnit
  universalGasConstantJoulesPerMoleKelvin : ℝ
  internalEnergyAt : CycleState → DimEnergy
  workDoneByGasOn : CycleLeg → DimEnergy
  heatTransferredIntoGasOn : CycleLeg → DimEnergy
  processKind : CycleLeg → ProcessKind
  segmentOrientation : CycleLeg → SegmentOrientation

/-- Mole readout of the physical gas sample. -/
def amountOfGasInMoles
    {AmountOfSubstance : Type}
    (setup : MonatomicRectangularHeatEngine AmountOfSubstance) : ℝ :=
  setup.amountInMoles setup.amountOfGas

/-- Kelvin readout at a numbered state. -/
def gasTemperatureInKelvin
    {AmountOfSubstance : Type}
    (setup : MonatomicRectangularHeatEngine AmountOfSubstance)
    (state : CycleState) : ℝ :=
  temperatureInKelvin setup.temperatureStorageUnit
    (setup.temperatureAt state)

/-- Joule readout of the internal energy at a numbered state. -/
def internalEnergyInJoules
    {AmountOfSubstance : Type}
    (setup : MonatomicRectangularHeatEngine AmountOfSubstance)
    (state : CycleState) : ℝ :=
  energyInJoules (setup.internalEnergyAt state)

/-- Signed joule readout of work done by the gas on a directed leg. -/
def workDoneByGasInJoules
    {AmountOfSubstance : Type}
    (setup : MonatomicRectangularHeatEngine AmountOfSubstance)
    (leg : CycleLeg) : ℝ :=
  energyInJoules (setup.workDoneByGasOn leg)

/-- Signed joule readout of heat transferred into the gas on a leg. -/
def heatTransferredIntoGasInJoules
    {AmountOfSubstance : Type}
    (setup : MonatomicRectangularHeatEngine AmountOfSubstance)
    (leg : CycleLeg) : ℝ :=
  energyInJoules (setup.heatTransferredIntoGasOn leg)

/-! ## Assumptions: prose data, figure readouts, and governing laws -/

/-!
The data stated in the prose.  This records the measured heat supplied on
`1 → 2`, but neither net work, total heat input, nor thermal efficiency.
-/
structure MatchesProblemStatement
    {AmountOfSubstance : Type}
    (setup : MonatomicRectangularHeatEngine AmountOfSubstance) : Prop where
  gasIsMonatomicIdeal : setup.gasModel = .monatomicIdealGas
  deviceIsHeatEngine : setup.deviceRole = .heatEngine
  amountIsOneMole : amountOfGasInMoles setup = 1
  heatInputOnOneToTwoIs3750Joules :
    heatTransferredIntoGasInJoules setup .oneToTwo = 3750

/-!
Exact transcription of the primary bitmap: clockwise arrows around a
rectangle, vertical isochoric legs, horizontal isobaric legs, lower pressure
`300 kPa`, `T₁ = 300 K`, and `Vmax = 2 Vmin`.  The value of `pmax` is not
given here and must be derived from the heating process.
-/
structure MatchesPrimaryPVDiagram
    {AmountOfSubstance : Type}
    (setup : MonatomicRectangularHeatEngine AmountOfSubstance) : Prop where
  horizontalAxisIsVolume :
    setup.figure.horizontalAxisQuantity = .volumeV
  verticalAxisIsPressure :
    setup.figure.verticalAxisQuantity = .pressureP
  pressureAxisUsesKilopascals :
    setup.figure.pressureDisplayUnit = .kilopascal
  everyPrintedLabelIsVisible :
    ∀ label, setup.figure.labelVisible label = true
  everyClockwiseArrowIsVisible :
    ∀ leg, setup.figure.arrowVisible leg = true
  everyLegIsStraight :
    ∀ leg, setup.figure.legDrawnStraight leg = true
  displayedProcessKindsAgree :
    ∀ leg, setup.processKind leg = displayedProcessKind leg
  displayedSegmentOrientationsAgree :
    ∀ leg, setup.segmentOrientation leg = displayedSegmentOrientation leg
  stateOneVolumeIsMinimum :
    setup.figure.volumeAt .one = setup.figure.minimumVolume
  stateTwoVolumeIsMinimum :
    setup.figure.volumeAt .two = setup.figure.minimumVolume
  stateThreeVolumeIsMaximum :
    setup.figure.volumeAt .three = setup.figure.maximumVolume
  stateFourVolumeIsMaximum :
    setup.figure.volumeAt .four = setup.figure.maximumVolume
  stateOnePressureIsLower :
    setup.figure.pressureAt .one = setup.figure.lowerPressure
  stateTwoPressureIsMaximum :
    setup.figure.pressureAt .two = setup.figure.maximumPressure
  stateThreePressureIsMaximum :
    setup.figure.pressureAt .three = setup.figure.maximumPressure
  stateFourPressureIsLower :
    setup.figure.pressureAt .four = setup.figure.lowerPressure
  maximumVolumeIsTwiceMinimum :
    volumeInCubicMeters setup.figure.maximumVolume =
      2 * volumeInCubicMeters setup.figure.minimumVolume
  lowerPressureIs300Kilopascals :
    pressureInKilopascals setup.figure.lowerPressure = 300
  temperatureIsStoredInKelvin :
    setup.temperatureStorageUnit = TemperatureUnit.kelvin
  stateOneTemperatureIs300Kelvin :
    gasTemperatureInKelvin setup .one = 300

/-!
The standard classroom SI calibration `R = 8.31 J/(mol K)` used at the
precision of the problem data and answer choices.  It is an independent
physical-constant readout, not an efficiency assumption.
-/
structure UsesClassroomSIGasConstant
    {AmountOfSubstance : Type}
    (setup : MonatomicRectangularHeatEngine AmountOfSubstance) : Prop where
  gasConstantReadout :
    setup.universalGasConstantJoulesPerMoleKelvin = 831 / 100

/-- Positivity and nondegeneracy conditions for a physical engine cycle. -/
structure HasPhysicalCycleParameters
    {AmountOfSubstance : Type}
    (setup : MonatomicRectangularHeatEngine AmountOfSubstance) : Prop where
  amountPositive : 0 < amountOfGasInMoles setup
  gasConstantPositive :
    0 < setup.universalGasConstantJoulesPerMoleKelvin
  pressurePositive :
    ∀ state, 0 < pressureInPascals (setup.figure.pressureAt state)
  volumePositive :
    ∀ state, 0 < volumeInCubicMeters (setup.figure.volumeAt state)
  absoluteTemperaturePositive :
    ∀ state, 0 < gasTemperatureInKelvin setup state
  pressureLevelsDistinct :
    pressureInPascals setup.figure.lowerPressure <
      pressureInPascals setup.figure.maximumPressure
  volumeLevelsDistinct :
    volumeInCubicMeters setup.figure.minimumVolume <
      volumeInCubicMeters setup.figure.maximumVolume

/-!
Macroscopic governing laws for the monatomic ideal-gas cycle:

* `p V = n R T` at each equilibrium state;
* `U = (3/2) n R T` for a monatomic ideal gas;
* zero boundary work on an isochoric leg;
* `W_by = p (V_f - V_i)` on an isobaric leg;
* `Q_in = U_f - U_i + W_by` on every leg.

These laws are general relations.  No field fixes a leg-energy result other
than the measured `1 → 2` heat, net cycle work, total heat input, efficiency,
or answer choice.
-/
structure SatisfiesMonatomicIdealGasLaws
    {AmountOfSubstance : Type}
    (setup : MonatomicRectangularHeatEngine AmountOfSubstance) : Prop where
  idealGasEquation : ∀ state,
    pressureInPascals (setup.figure.pressureAt state) *
        volumeInCubicMeters (setup.figure.volumeAt state) =
      amountOfGasInMoles setup *
        setup.universalGasConstantJoulesPerMoleKelvin *
          gasTemperatureInKelvin setup state
  monatomicInternalEnergy : ∀ state,
    internalEnergyInJoules setup state =
      (3 / 2 : ℝ) * amountOfGasInMoles setup *
        setup.universalGasConstantJoulesPerMoleKelvin *
          gasTemperatureInKelvin setup state
  isochoricBoundaryWork : ∀ leg,
    setup.processKind leg = .isochoric →
      workDoneByGasInJoules setup leg = 0
  isobaricBoundaryWork : ∀ leg,
    setup.processKind leg = .isobaric →
      workDoneByGasInJoules setup leg =
        pressureInPascals (setup.figure.pressureAt (legSource leg)) *
          (volumeInCubicMeters (setup.figure.volumeAt (legTarget leg)) -
            volumeInCubicMeters (setup.figure.volumeAt (legSource leg)))
  firstLawOnEachLeg : ∀ leg,
    heatTransferredIntoGasInJoules setup leg =
      internalEnergyInJoules setup (legTarget leg) -
        internalEnergyInJoules setup (legSource leg) +
          workDoneByGasInJoules setup leg

/-! ## Derived cycle quantities and answer choices -/

/-- Net work done by the gas over one complete traversal, in joules. -/
def netCycleWorkInJoules
    {AmountOfSubstance : Type}
    (setup : MonatomicRectangularHeatEngine AmountOfSubstance) : ℝ :=
  ∑ leg : CycleLeg, workDoneByGasInJoules setup leg

/-- Total heat entering the gas, obtained by summing positive leg heats. -/
def totalHeatInputInJoules
    {AmountOfSubstance : Type}
    (setup : MonatomicRectangularHeatEngine AmountOfSubstance) : ℝ :=
  ∑ leg : CycleLeg, max (heatTransferredIntoGasInJoules setup leg) 0

/-- Dimensionless thermal efficiency `W_net / Q_in`. -/
def thermalEfficiency
    {AmountOfSubstance : Type}
    (setup : MonatomicRectangularHeatEngine AmountOfSubstance) : ℝ :=
  netCycleWorkInJoules setup / totalHeatInputInJoules setup

/-- Labels of the four printed answer choices. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Fractional efficiency printed beside each answer label. -/
def displayedEfficiency : AnswerChoice → ℝ
  | .A => 46 / 100
  | .B => 40 / 100
  | .C => 67 / 100
  | .D => 15 / 100

/-- Answer choice recorded in the supplied dataset metadata. -/
def recordedAnswerChoice : AnswerChoice := .D

/-- Compatibility with an efficiency displayed to the nearest hundredth. -/
def RoundsToDisplayedHundredth
    (actual displayed : ℝ) : Prop :=
  |actual - displayed| < 1 / 200

/-!
The governing laws and source data determine all signed leg energies.  This
is an intermediate derived result; none of these values is a premise field.
-/
lemma cycleLegEnergyReadouts
    {AmountOfSubstance : Type}
    (setup : MonatomicRectangularHeatEngine AmountOfSubstance)
    (h_problem : MatchesProblemStatement setup)
    (h_figure : MatchesPrimaryPVDiagram setup)
    (h_constant : UsesClassroomSIGasConstant setup)
    (h_physical : HasPhysicalCycleParameters setup)
    (h_laws : SatisfiesMonatomicIdealGasLaws setup) :
    workDoneByGasInJoules setup .oneToTwo = 0 ∧
      workDoneByGasInJoules setup .twoToThree = 4993 ∧
      workDoneByGasInJoules setup .threeToFour = 0 ∧
      workDoneByGasInJoules setup .fourToOne = -2493 ∧
      heatTransferredIntoGasInJoules setup .oneToTwo = 3750 ∧
      heatTransferredIntoGasInJoules setup .twoToThree = 24965 / 2 ∧
      heatTransferredIntoGasInJoules setup .threeToFour = -7500 ∧
      heatTransferredIntoGasInJoules setup .fourToOne = -12465 / 2 := by
  have h_internal_from_pv (state : CycleState) :
      internalEnergyInJoules setup state =
        (3 / 2 : ℝ) *
          pressureInPascals (setup.figure.pressureAt state) *
            volumeInCubicMeters (setup.figure.volumeAt state) := by
    have h_ideal := h_laws.idealGasEquation state
    have h_internal := h_laws.monatomicInternalEnergy state
    nlinarith

  have hpv_one := h_laws.idealGasEquation .one
  rw [h_figure.stateOnePressureIsLower,
    h_figure.stateOneVolumeIsMinimum,
    h_problem.amountIsOneMole,
    h_constant.gasConstantReadout,
    h_figure.stateOneTemperatureIs300Kelvin] at hpv_one
  norm_num at hpv_one

  have hU_one := h_internal_from_pv .one
  rw [h_figure.stateOnePressureIsLower,
    h_figure.stateOneVolumeIsMinimum] at hU_one
  have hU_two := h_internal_from_pv .two
  rw [h_figure.stateTwoPressureIsMaximum,
    h_figure.stateTwoVolumeIsMinimum] at hU_two
  have hU_three := h_internal_from_pv .three
  rw [h_figure.stateThreePressureIsMaximum,
    h_figure.stateThreeVolumeIsMaximum] at hU_three
  have hU_four := h_internal_from_pv .four
  rw [h_figure.stateFourPressureIsLower,
    h_figure.stateFourVolumeIsMaximum] at hU_four

  have hw_one_two :
      workDoneByGasInJoules setup .oneToTwo = 0 :=
    h_laws.isochoricBoundaryWork .oneToTwo (by
      simpa [displayedProcessKind] using
        h_figure.displayedProcessKindsAgree .oneToTwo)
  have hw_three_four :
      workDoneByGasInJoules setup .threeToFour = 0 :=
    h_laws.isochoricBoundaryWork .threeToFour (by
      simpa [displayedProcessKind] using
        h_figure.displayedProcessKindsAgree .threeToFour)

  have hpv_two :
      pressureInPascals setup.figure.maximumPressure *
          volumeInCubicMeters setup.figure.minimumVolume =
        4993 := by
    have hq_one_two := h_laws.firstLawOnEachLeg .oneToTwo
    simp only [legSource, legTarget] at hq_one_two
    nlinarith [h_problem.heatInputOnOneToTwoIs3750Joules]

  have hw_two_three_formula :=
    h_laws.isobaricBoundaryWork .twoToThree (by
      simpa [displayedProcessKind] using
        h_figure.displayedProcessKindsAgree .twoToThree)
  simp only [legSource, legTarget] at hw_two_three_formula
  rw [h_figure.stateTwoPressureIsMaximum,
    h_figure.stateThreeVolumeIsMaximum,
    h_figure.stateTwoVolumeIsMinimum,
    h_figure.maximumVolumeIsTwiceMinimum] at hw_two_three_formula
  have hw_two_three :
      workDoneByGasInJoules setup .twoToThree = 4993 := by
    nlinarith

  have hw_four_one_formula :=
    h_laws.isobaricBoundaryWork .fourToOne (by
      simpa [displayedProcessKind] using
        h_figure.displayedProcessKindsAgree .fourToOne)
  simp only [legSource, legTarget] at hw_four_one_formula
  rw [h_figure.stateFourPressureIsLower,
    h_figure.stateOneVolumeIsMinimum,
    h_figure.stateFourVolumeIsMaximum,
    h_figure.maximumVolumeIsTwiceMinimum] at hw_four_one_formula
  have hw_four_one :
      workDoneByGasInJoules setup .fourToOne = -2493 := by
    nlinarith

  rw [h_figure.maximumVolumeIsTwiceMinimum] at hU_three hU_four
  have hU_one_value :
      internalEnergyInJoules setup .one = 7479 / 2 := by
    nlinarith
  have hU_two_value :
      internalEnergyInJoules setup .two = 14979 / 2 := by
    nlinarith
  have hU_three_value :
      internalEnergyInJoules setup .three = 14979 := by
    nlinarith
  have hU_four_value :
      internalEnergyInJoules setup .four = 7479 := by
    nlinarith

  have hq_two_three := h_laws.firstLawOnEachLeg .twoToThree
  have hq_three_four := h_laws.firstLawOnEachLeg .threeToFour
  have hq_four_one := h_laws.firstLawOnEachLeg .fourToOne
  simp only [legSource, legTarget] at hq_two_three hq_three_four hq_four_one
  have hq_two_three_value :
      heatTransferredIntoGasInJoules setup .twoToThree = 24965 / 2 := by
    nlinarith
  have hq_three_four_value :
      heatTransferredIntoGasInJoules setup .threeToFour = -7500 := by
    nlinarith
  have hq_four_one_value :
      heatTransferredIntoGasInJoules setup .fourToOne = -12465 / 2 := by
    nlinarith

  exact ⟨hw_one_two, hw_two_three, hw_three_four, hw_four_one,
    h_problem.heatInputOnOneToTwoIs3750Joules, hq_two_three_value,
    hq_three_four_value, hq_four_one_value⟩

/-!
Consequently the engine does `2500 J` of net work and absorbs
`32465/2 J` of heat per cycle.  These are conclusions used by the final
efficiency theorem.
-/
lemma netWorkAndHeatInputReadouts
    {AmountOfSubstance : Type}
    (setup : MonatomicRectangularHeatEngine AmountOfSubstance)
    (h_problem : MatchesProblemStatement setup)
    (h_figure : MatchesPrimaryPVDiagram setup)
    (h_constant : UsesClassroomSIGasConstant setup)
    (h_physical : HasPhysicalCycleParameters setup)
    (h_laws : SatisfiesMonatomicIdealGasLaws setup) :
    netCycleWorkInJoules setup = 2500 ∧
      totalHeatInputInJoules setup = 32465 / 2 := by
  rcases cycleLegEnergyReadouts setup h_problem h_figure h_constant
      h_physical h_laws with
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
The exact efficiency in the stated `R = 8.31 J/(mol K)` classroom model is
`1000/6493 ≈ 0.154`.  It therefore rounds to the displayed value `0.15`,
which is recorded answer choice D.  Neither the exact efficiency nor the
rounding conclusion occurs among the hypotheses.

Blueprint: `thm:physics:phyx_mini_0425:target`.
-/
theorem thermalEfficiency_eq_answerChoiceD
    {AmountOfSubstance : Type}
    (setup : MonatomicRectangularHeatEngine AmountOfSubstance)
    (h_problem : MatchesProblemStatement setup)
    (h_figure : MatchesPrimaryPVDiagram setup)
    (h_constant : UsesClassroomSIGasConstant setup)
    (h_physical : HasPhysicalCycleParameters setup)
    (h_laws : SatisfiesMonatomicIdealGasLaws setup) :
    thermalEfficiency setup = 1000 / 6493 ∧
      RoundsToDisplayedHundredth
        (thermalEfficiency setup) (displayedEfficiency .D) ∧
      recordedAnswerChoice = .D := by
  rcases netWorkAndHeatInputReadouts setup h_problem h_figure h_constant
      h_physical h_laws with
    ⟨hwork, hheat⟩
  refine ⟨?_, ?_, rfl⟩
  · rw [thermalEfficiency, hwork, hheat]
    norm_num
  · rw [RoundsToDisplayedHundredth, displayedEfficiency,
      thermalEfficiency, hwork, hheat]
    norm_num [abs_of_nonneg, abs_of_nonpos]

end PhyXMiniProblems.ProblemPhyXMini0425
