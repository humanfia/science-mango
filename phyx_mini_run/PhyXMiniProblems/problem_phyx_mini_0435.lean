import Mathlib
import Physlib.Thermodynamics.Temperature.Basic
import Physlib.Thermodynamics.Temperature.TemperatureUnits
import Physlib.Units.WithDim.Energy
import Physlib.Units.WithDim.Pressure

/- USER: The assigned source file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0435

open Dimension

/-!
# Hot-reservoir heat for a reversed rectangular `pV` cycle

The primary bitmap shows the counter-clockwise traversal
`2 → 1 → 4 → 3 → 2` of a rectangle.  Its vertices have volumes `1 m³` and
`3 m³`, pressures `1 atm` and `3 atm`, and the dashed isotherms identify
`T₂ = 2700 K` and `T₄ = 300 K`.

The working gas is represented by dimensionful pressure, volume, and energy
quantities and by Physlib's absolute `Temperature`.  Real numbers below occur
only as named-unit readouts, dimensionless constitutive coefficients, and
displayed multiple-choice values.

The source does not identify the gas or state its constant-volume heat
capacity.  The governing-law predicate therefore models a calorically ideal
gas with an unspecified positive sample heat capacity.  This suffices to
derive an exact symbolic value of `Q_H`, but not one of the displayed numbers.

Assumption/target split:

* `MatchesProblemAndPrimaryFigure` records only prose and bitmap data;
* `SatisfiesIdealGasLaws` states the ideal-gas, internal-energy,
  boundary-work, and first-law relations while leaving the heat capacity free;
* the signed leg heats and the positive hot-reservoir heat `Q_H` occur only as
  symbolic conclusions below;
* answer D is retained only as dataset metadata, and the difference from its
  displayed value is characterized exactly rather than asserted to vanish.
-/

/-! ## Dimensionful quantities and calibrated readouts -/

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

/-- Standard-atmosphere readout of a physical pressure. -/
def pressureInAtmospheres (pressure : DimPressure) : ℝ :=
  (pressure UnitChoices.SI).val /
    (DimPressure.standardAtmosphere UnitChoices.SI).val

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

/-- Physlib's standard-atmosphere unit has the exact SI value `101325 Pa`. -/
lemma standardAtmosphereInPascals :
    pressureInPascals DimPressure.standardAtmosphere = 101325 := by
  sorry

/-! ## Figure labels, axes, and reverse traversal -/

/-- The four numbered states printed on the rectangular cycle. -/
inductive CycleState where
  | one
  | two
  | three
  | four
  deriving DecidableEq, Fintype, Repr

/-- The four directed legs, in the counter-clockwise order shown. -/
inductive CycleLeg where
  | twoToOne
  | oneToFour
  | fourToThree
  | threeToTwo
  deriving DecidableEq, Fintype, Repr

/-- Initial state of a directed reverse-cycle leg. -/
def legSource : CycleLeg → CycleState
  | .twoToOne => .two
  | .oneToFour => .one
  | .fourToThree => .four
  | .threeToTwo => .three

/-- Final state of a directed reverse-cycle leg. -/
def legTarget : CycleLeg → CycleState
  | .twoToOne => .one
  | .oneToFour => .four
  | .fourToThree => .three
  | .threeToTwo => .two

/-- Thermodynamic constraint represented by a side of the rectangle. -/
inductive ProcessKind where
  | isobaric
  | isochoric
  deriving DecidableEq, Repr

/-- Process kind read from the horizontal or vertical geometry of each leg. -/
def displayedProcessKind : CycleLeg → ProcessKind
  | .twoToOne => .isobaric
  | .oneToFour => .isochoric
  | .fourToThree => .isobaric
  | .threeToTwo => .isochoric

/-- The two Cartesian axes in the supplied diagram. -/
inductive FigureAxis where
  | horizontal
  | vertical
  deriving DecidableEq, Repr

/-- Physical quantity assigned to a diagram axis. -/
inductive AxisQuantity where
  | volume
  | pressure
  deriving DecidableEq, Repr

/-- Units printed next to the axes in the bitmap. -/
inductive AxisDisplayUnit where
  | cubicMeter
  | standardAtmosphere
  deriving DecidableEq, Repr

/-- Direction of a visible arrowhead on one side of the rectangle. -/
inductive ArrowDirection where
  | left
  | down
  | right
  | up
  deriving DecidableEq, Repr

/-- Arrow direction visible on each reverse-cycle leg. -/
def displayedArrowDirection : CycleLeg → ArrowDirection
  | .twoToOne => .left
  | .oneToFour => .down
  | .fourToThree => .right
  | .threeToTwo => .up

/-- Orientation of the closed path in the `pV` plane. -/
inductive CycleOrientation where
  | clockwise
  | counterclockwise
  deriving DecidableEq, Repr

/-- The two dashed temperature annotations in the primary bitmap. -/
inductive IsothermLabel where
  | twoThousandSevenHundredKelvin
  | threeHundredKelvin
  deriving DecidableEq, Fintype, Repr

/-- Literal geometric and physical content of the supplied `pV` diagram. -/
structure PressureVolumeCycleFigure where
  volumeAt : CycleState → VolumeQuantity
  pressureAt : CycleState → DimPressure
  axisQuantity : FigureAxis → AxisQuantity
  axisDisplayUnit : FigureAxis → AxisDisplayUnit
  vertexVisible : CycleState → Bool
  arrowVisible : CycleLeg → Bool
  arrowDirection : CycleLeg → ArrowDirection
  legDrawnStraight : CycleLeg → Bool
  isothermLabelVisible : IsothermLabel → Bool
  isothermPassesThrough : IsothermLabel → CycleState → Bool

/-! ## Thermodynamic system and observables -/

/-- Physical role of the device after the stated reversal. -/
inductive ThermodynamicDeviceRole where
  | reversedHeatPump
  | other
  deriving DecidableEq, Repr

/-- Constitutive class of the working gas. -/
inductive GasModel where
  | idealGas
  | other
  deriving DecidableEq, Repr

/-!
The reverse-cycle device and its physical observables.  Heat is positive into
the gas and boundary work is positive when done by the gas.  The scalar
`sampleGasConstantJoulesPerKelvin` is the SI readout of `nR` for the complete
gas sample, whose amount is not supplied separately in the source.  The
constant-volume heat capacity is retained as a separate SI readout because
the source does not state it and hence does not determine a numerical heat.
-/
structure ReversedRectangularIdealGasCycle where
  deviceRole : ThermodynamicDeviceRole
  gasModel : GasModel
  figure : PressureVolumeCycleFigure
  temperatureAt : CycleState → Temperature
  temperatureStorageUnit : TemperatureUnit
  sampleGasConstantJoulesPerKelvin : ℝ
  constantVolumeHeatCapacityJoulesPerKelvin : ℝ
  internalEnergyAt : CycleState → DimEnergy
  workDoneByGasOn : CycleLeg → DimEnergy
  heatTransferredIntoGasOn : CycleLeg → DimEnergy
  orientation : CycleOrientation

/-- Kelvin readout at a numbered state. -/
def gasTemperatureInKelvin
    (setup : ReversedRectangularIdealGasCycle) (state : CycleState) : ℝ :=
  temperatureInKelvin setup.temperatureStorageUnit
    (setup.temperatureAt state)

/-- Joule readout of internal energy at a numbered state. -/
def internalEnergyInJoules
    (setup : ReversedRectangularIdealGasCycle) (state : CycleState) : ℝ :=
  energyInJoules (setup.internalEnergyAt state)

/-- Signed joule readout of boundary work done by the gas on a leg. -/
def workDoneByGasInJoules
    (setup : ReversedRectangularIdealGasCycle) (leg : CycleLeg) : ℝ :=
  energyInJoules (setup.workDoneByGasOn leg)

/-- Signed joule readout of heat transferred into the gas on a leg. -/
def heatTransferredIntoGasInJoules
    (setup : ReversedRectangularIdealGasCycle) (leg : CycleLeg) : ℝ :=
  energyInJoules (setup.heatTransferredIntoGasOn leg)

/-! ## Source data, figure readouts, and governing laws -/

/-!
Exact transcription of the prose and primary bitmap.  The dashed `2700 K`
curve visibly meets state 2 and the dashed `300 K` curve visibly meets state
4; the auxiliary caption's claim that each passes through two vertices is not
used because the bitmap is designated as primary evidence.
-/
structure MatchesProblemAndPrimaryFigure
    (setup : ReversedRectangularIdealGasCycle) : Prop where
  deviceIsOperatedInReverse :
    setup.deviceRole = .reversedHeatPump
  traversalIsCounterclockwise :
    setup.orientation = .counterclockwise
  horizontalAxisIsVolume :
    setup.figure.axisQuantity .horizontal = .volume
  verticalAxisIsPressure :
    setup.figure.axisQuantity .vertical = .pressure
  horizontalAxisUsesCubicMeters :
    setup.figure.axisDisplayUnit .horizontal = .cubicMeter
  verticalAxisUsesAtmospheres :
    setup.figure.axisDisplayUnit .vertical = .standardAtmosphere
  everyVertexIsVisible :
    ∀ state, setup.figure.vertexVisible state = true
  everyReverseArrowIsVisible :
    ∀ leg, setup.figure.arrowVisible leg = true
  arrowDirectionsAgreeWithBitmap :
    ∀ leg, setup.figure.arrowDirection leg = displayedArrowDirection leg
  everyLegIsStraight :
    ∀ leg, setup.figure.legDrawnStraight leg = true
  everyIsothermLabelIsVisible :
    ∀ label, setup.figure.isothermLabelVisible label = true
  hotIsothermPassesThroughStateTwo :
    setup.figure.isothermPassesThrough
      .twoThousandSevenHundredKelvin .two = true
  coldIsothermPassesThroughStateFour :
    setup.figure.isothermPassesThrough .threeHundredKelvin .four = true
  stateOneVolumeIsOneCubicMeter :
    volumeInCubicMeters (setup.figure.volumeAt .one) = 1
  stateTwoVolumeIsThreeCubicMeters :
    volumeInCubicMeters (setup.figure.volumeAt .two) = 3
  stateThreeVolumeIsThreeCubicMeters :
    volumeInCubicMeters (setup.figure.volumeAt .three) = 3
  stateFourVolumeIsOneCubicMeter :
    volumeInCubicMeters (setup.figure.volumeAt .four) = 1
  stateOnePressureIsThreeAtmospheres :
    pressureInAtmospheres (setup.figure.pressureAt .one) = 3
  stateTwoPressureIsThreeAtmospheres :
    pressureInAtmospheres (setup.figure.pressureAt .two) = 3
  stateThreePressureIsOneAtmosphere :
    pressureInAtmospheres (setup.figure.pressureAt .three) = 1
  stateFourPressureIsOneAtmosphere :
    pressureInAtmospheres (setup.figure.pressureAt .four) = 1
  temperatureIsStoredInKelvin :
    setup.temperatureStorageUnit = TemperatureUnit.kelvin
  stateTwoTemperatureIs2700Kelvin :
    gasTemperatureInKelvin setup .two = 2700
  stateFourTemperatureIs300Kelvin :
    gasTemperatureInKelvin setup .four = 300

/-- Positivity and nondegeneracy conditions for a physical gas cycle. -/
structure HasPhysicalCycleParameters
    (setup : ReversedRectangularIdealGasCycle) : Prop where
  sampleGasConstantPositive :
    0 < setup.sampleGasConstantJoulesPerKelvin
  constantVolumeHeatCapacityPositive :
    0 < setup.constantVolumeHeatCapacityJoulesPerKelvin
  pressurePositive :
    ∀ state, 0 < pressureInPascals (setup.figure.pressureAt state)
  volumePositive :
    ∀ state, 0 < volumeInCubicMeters (setup.figure.volumeAt state)
  absoluteTemperaturePositive :
    ∀ state, 0 < gasTemperatureInKelvin setup state

/-!
Macroscopic governing laws for the chosen ideal-gas model:

* `pV = (nR)T` at each equilibrium state;
* `U = C_V T` for the separately modeled constant-volume heat capacity;
* zero boundary work on an isochoric leg;
* `W_by = p(V_f - V_i)` on an isobaric leg;
* `Q_in = U_f - U_i + W_by` on every directed leg.

No field specifies a signed leg heat, total hot-side heat, or answer choice.
-/
structure SatisfiesIdealGasLaws
    (setup : ReversedRectangularIdealGasCycle) : Prop where
  gasModelIsIdealGas :
    setup.gasModel = .idealGas
  idealGasEquation : ∀ state,
    pressureInPascals (setup.figure.pressureAt state) *
        volumeInCubicMeters (setup.figure.volumeAt state) =
      setup.sampleGasConstantJoulesPerKelvin *
        gasTemperatureInKelvin setup state
  internalEnergyEquation : ∀ state,
    internalEnergyInJoules setup state =
      setup.constantVolumeHeatCapacityJoulesPerKelvin *
        gasTemperatureInKelvin setup state
  isochoricBoundaryWork : ∀ leg,
    displayedProcessKind leg = .isochoric →
      workDoneByGasInJoules setup leg = 0
  isobaricBoundaryWork : ∀ leg,
    displayedProcessKind leg = .isobaric →
      workDoneByGasInJoules setup leg =
        pressureInPascals (setup.figure.pressureAt (legSource leg)) *
          (volumeInCubicMeters (setup.figure.volumeAt (legTarget leg)) -
            volumeInCubicMeters (setup.figure.volumeAt (legSource leg)))
  firstLawOnEachLeg : ∀ leg,
    heatTransferredIntoGasInJoules setup leg =
      internalEnergyInJoules setup (legTarget leg) -
        internalEnergyInJoules setup (legSource leg) +
          workDoneByGasInJoules setup leg

/-! ## Derived heat and work quantities -/

/-!
Positive heat delivered by the gas to the hot reservoir.  The two legs on
which heat leaves the gas are `2 → 1` and `1 → 4`, so the sign is reversed.
This definition contains no numerical answer.
-/
def hotReservoirHeatInJoules
    (setup : ReversedRectangularIdealGasCycle) : ℝ :=
  -(heatTransferredIntoGasInJoules setup .twoToOne +
    heatTransferredIntoGasInJoules setup .oneToFour)

/-- Positive heat absorbed by the gas on the low-temperature side. -/
def coldReservoirHeatInJoules
    (setup : ReversedRectangularIdealGasCycle) : ℝ :=
  heatTransferredIntoGasInJoules setup .fourToThree +
    heatTransferredIntoGasInJoules setup .threeToTwo

/-- Positive work supplied to drive one traversal of the reverse cycle. -/
def cycleWorkInputInJoules
    (setup : ReversedRectangularIdealGasCycle) : ℝ :=
  -(workDoneByGasInJoules setup .twoToOne +
    workDoneByGasInJoules setup .oneToFour +
    workDoneByGasInJoules setup .fourToThree +
    workDoneByGasInJoules setup .threeToTwo)

/-! ## Answer choices -/

/-- Labels of the four displayed answers. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Joule value printed beside each answer label. -/
def displayedHotReservoirHeatInJoules : AnswerChoice → ℝ
  | .A => 222800
  | .B => 2633000
  | .C => 1519000
  | .D => 2228000

/-- Answer label recorded by the supplied dataset. -/
def recordedAnswerChoice : AnswerChoice := .D

/-! ## Derived statements -/

/--
The two labeled isotherms and the ideal-gas law determine the sample's `nR`
readout and the two unlabeled vertex temperatures.
-/
lemma sampleGasConstantAndUnlabeledTemperatures
    (setup : ReversedRectangularIdealGasCycle)
    (h_figure : MatchesProblemAndPrimaryFigure setup)
    (h_physical : HasPhysicalCycleParameters setup)
    (h_laws : SatisfiesIdealGasLaws setup) :
    setup.sampleGasConstantJoulesPerKelvin = 1351 / 4 ∧
      gasTemperatureInKelvin setup .one = 900 ∧
      gasTemperatureInKelvin setup .three = 900 := by
  sorry

/--
The governing laws determine each signed work and heat transfer.  These
values are conclusions and do not occur in any premise structure.
-/
lemma reversedCycleLegEnergyReadouts
    (setup : ReversedRectangularIdealGasCycle)
    (h_figure : MatchesProblemAndPrimaryFigure setup)
    (h_physical : HasPhysicalCycleParameters setup)
    (h_laws : SatisfiesIdealGasLaws setup) :
    workDoneByGasInJoules setup .twoToOne = -607950 ∧
      workDoneByGasInJoules setup .oneToFour = 0 ∧
      workDoneByGasInJoules setup .fourToThree = 202650 ∧
      workDoneByGasInJoules setup .threeToTwo = 0 ∧
      heatTransferredIntoGasInJoules setup .twoToOne =
        -1800 * setup.constantVolumeHeatCapacityJoulesPerKelvin - 607950 ∧
      heatTransferredIntoGasInJoules setup .oneToFour =
        -600 * setup.constantVolumeHeatCapacityJoulesPerKelvin ∧
      heatTransferredIntoGasInJoules setup .fourToThree =
        600 * setup.constantVolumeHeatCapacityJoulesPerKelvin + 202650 ∧
      heatTransferredIntoGasInJoules setup .threeToTwo =
        1800 * setup.constantVolumeHeatCapacityJoulesPerKelvin := by
  sorry

/--
Symbolic SI heat readouts and the exact reversed-cycle balance
`Q_H = Q_C + W_in`.  The unspecified sample heat capacity remains visible.
-/
lemma reversedCycleHeatAndWorkReadouts
    (setup : ReversedRectangularIdealGasCycle)
    (h_figure : MatchesProblemAndPrimaryFigure setup)
    (h_physical : HasPhysicalCycleParameters setup)
    (h_laws : SatisfiesIdealGasLaws setup) :
    hotReservoirHeatInJoules setup =
        2400 * setup.constantVolumeHeatCapacityJoulesPerKelvin + 607950 ∧
      coldReservoirHeatInJoules setup =
        2400 * setup.constantVolumeHeatCapacityJoulesPerKelvin + 202650 ∧
      cycleWorkInputInJoules setup = 405300 ∧
      hotReservoirHeatInJoules setup =
        coldReservoirHeatInJoules setup + cycleWorkInputInJoules setup := by
  sorry

/-!
The source-supported result is the symbolic relation
`Q_H = 2400 C_V + 607950 J`.  The source separately records answer D, but does
not supply `C_V`; consequently the exact difference from D's displayed value
is stated as a function of the free heat capacity, not set equal to zero.

The declaration name is retained for blueprint stability even though the
repaired statement no longer claims that the source data determine D.

Blueprint: `thm:physics:phyx_mini_0435:target`.
-/
theorem hotReservoirHeat_matches_recordedAnswerD
    (setup : ReversedRectangularIdealGasCycle)
    (h_figure : MatchesProblemAndPrimaryFigure setup)
    (h_physical : HasPhysicalCycleParameters setup)
    (h_laws : SatisfiesIdealGasLaws setup) :
    hotReservoirHeatInJoules setup =
        2400 * setup.constantVolumeHeatCapacityJoulesPerKelvin + 607950 ∧
      recordedAnswerChoice = .D ∧
      hotReservoirHeatInJoules setup -
          displayedHotReservoirHeatInJoules recordedAnswerChoice =
        2400 * setup.constantVolumeHeatCapacityJoulesPerKelvin - 1620050 := by
  sorry

end PhyXMiniProblems.ProblemPhyXMini0435
