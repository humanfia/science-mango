import Mathlib
import Physlib.Thermodynamics.Temperature.Basic
import Physlib.Thermodynamics.Temperature.TemperatureUnits
import Physlib.Units.WithDim.Energy
import Physlib.Units.WithDim.Pressure

/- USER: The assigned source file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0411

open Dimension

/-!
# Heat transferred during an isochoric step of a monatomic ideal gas

The primary image is a pressure--volume diagram with states `1`, `2`, and
`3`.  Its axes are pressure in atmospheres and volume in cubic centimetres.
The plotted process goes from `(800 cm³, 4 atm)` to `(1600 cm³, 4 atm)` and
then vertically to `(1600 cm³, 2 atm)`.

Pressure, energy, and absolute temperature use Physlib physical-quantity
types.  Physlib has no named volume type or amount-of-substance dimension, so
volume is represented as nonnegative dimensionful length cubed, while amount
of substance is an abstract carrier equipped with a mole readout.  Real
numbers occur only as calibrated unit readouts, the gas constant's calibrated
value, and displayed multiple-choice values.
-/

/-! ## Dimensionful quantities and calibrated unit readouts -/

/-- A nonnegative physical volume with dimension length cubed. -/
abbrev VolumeQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * L𝓭 * L𝓭) NNReal)

/-!
An abstract physical amount-of-substance carrier with a calibrated mole
readout.  This keeps the gas amount distinct from a bare scalar.
-/
structure AmountOfSubstanceScale where
  Quantity : Type
  inMoles : Quantity → ℝ

/-- Read a physical pressure in coherent SI units (pascals). -/
def pressureInPascals (pressure : DimPressure) : ℝ :=
  (pressure UnitChoices.SI).val

/-- The SI readout of Physlib's physical standard-atmosphere constant. -/
def standardAtmosphereInPascals : ℝ :=
  pressureInPascals DimPressure.standardAtmosphere

/-- Read a physical pressure in standard atmospheres. -/
def pressureInAtmospheres (pressure : DimPressure) : ℝ :=
  pressureInPascals pressure / standardAtmosphereInPascals

/-- Read a physical volume in coherent SI units (cubic metres). -/
def volumeInCubicMetres (volume : VolumeQuantity) : ℝ :=
  ((volume UnitChoices.SI).val : ℝ)

/-- Read a physical volume in cubic centimetres. -/
def volumeInCubicCentimetres (volume : VolumeQuantity) : ℝ :=
  volumeInCubicMetres volume * 1000000

/-- Read a signed physical energy in coherent SI units (joules). -/
def energyInJoules (energy : DimEnergy) : ℝ :=
  (energy UnitChoices.SI).val

/-!
Read an absolute temperature in kelvin, accounting for the zero-preserving
unit in which a Physlib `Temperature` value is stored.
-/
def temperatureInKelvin
    (storageUnit : TemperatureUnit) (temperature : Temperature) : ℝ :=
  let unitRatio : NNReal := storageUnit / TemperatureUnit.kelvin
  temperature.toReal * (unitRatio : ℝ)

/-!
Physlib defines `DimPressure.standardAtmosphere` to be exactly `101325 Pa`.
This helper exposes that library-unit fact to the later scalar calculation.
-/
theorem standardAtmosphereInPascals_eq :
    standardAtmosphereInPascals = 101325 := by
  simp [standardAtmosphereInPascals, pressureInPascals,
    DimPressure.standardAtmosphere, CarriesDimension.toDimensionful_apply_apply]

/-! ## States, depicted steps, and figure geometry -/

/-- The three numbered equilibrium states drawn on the diagram. -/
inductive StateLabel where
  | one
  | two
  | three
  deriving DecidableEq, Fintype, Repr

/-- The two directed process segments shown by arrows. -/
inductive ProcessStep where
  | oneToTwo
  | twoToThree
  deriving DecidableEq, Fintype, Repr

/-- The thermodynamic constraint imposed along a depicted process step. -/
inductive ProcessKind where
  | isobaric
  | isochoric
  deriving DecidableEq, Repr

/-- The geometric shape of a process step in the primary `p`--`V` image. -/
inductive PathGeometry where
  | horizontal
  | vertical
  deriving DecidableEq, Repr

/-- The physical quantity and unit named on a diagram axis. -/
inductive AxisQuantity where
  | volumeInCubicCentimetres
  | pressureInAtmospheres
  deriving DecidableEq, Repr

/-- The initial state of each directed process segment. -/
def ProcessStep.startState : ProcessStep → StateLabel
  | .oneToTwo => .one
  | .twoToThree => .two

/-- The final state of each directed process segment. -/
def ProcessStep.endState : ProcessStep → StateLabel
  | .oneToTwo => .two
  | .twoToThree => .three

/-!
The quantitative and directed geometry displayed by the supplied `p`--`V`
figure.  Coordinates are calibrated scalar readouts in the units printed on
the axes, rather than physical quantities in their own right.
-/
structure PressureVolumeFigure where
  horizontalAxis : AxisQuantity
  verticalAxis : AxisQuantity
  pressureCoordinateAtmospheres : StateLabel → ℝ
  volumeCoordinateCubicCentimetres : StateLabel → ℝ
  arrowShown : ProcessStep → Bool
  arrowStart : ProcessStep → StateLabel
  arrowEnd : ProcessStep → StateLabel
  pathGeometry : ProcessStep → PathGeometry

/-! ## Gas states and the modeled experiment -/

/-- The gas model stated in the problem. -/
inductive GasModel where
  | monatomicIdeal
  | other
  deriving DecidableEq, Repr

/-!
A thermodynamic state of the sample.  Pressure, volume, absolute temperature,
and internal energy remain distinct physical quantities.
-/
structure GasState where
  pressure : DimPressure
  volume : VolumeQuantity
  temperature : Temperature
  internalEnergy : DimEnergy

/-!
The gas sample and the two-step process.  Heat is positive when transferred
to the gas, while boundary work is positive when done by the gas.
-/
structure MonatomicGasProcess (amountScale : AmountOfSubstanceScale) where
  figure : PressureVolumeFigure
  stateAt : StateLabel → GasState
  gasAmount : amountScale.Quantity
  gasModel : GasModel
  temperatureStorageUnit : TemperatureUnit
  universalGasConstantJoulesPerMoleKelvin : ℝ
  processKind : ProcessStep → ProcessKind
  heatTransferredToGas : ProcessStep → DimEnergy
  boundaryWorkDoneByGas : ProcessStep → DimEnergy

/-! ## Figure readouts and problem data -/

/-!
Facts read directly from the primary raster, including both axis labels, all
three plotted coordinates, both path shapes, and the directions of the two
arrows.  The fields also state that the plotted coordinates are calibrated
readouts of the modeled physical states.  No heat value occurs here.
-/
structure MatchesSuppliedFigure
    {amountScale : AmountOfSubstanceScale}
    (process : MonatomicGasProcess amountScale) : Prop where
  horizontalAxisIsVolume :
    process.figure.horizontalAxis = .volumeInCubicCentimetres
  verticalAxisIsPressure :
    process.figure.verticalAxis = .pressureInAtmospheres
  stateOneVolumeCoordinate :
    process.figure.volumeCoordinateCubicCentimetres .one = 800
  stateOnePressureCoordinate :
    process.figure.pressureCoordinateAtmospheres .one = 4
  stateTwoVolumeCoordinate :
    process.figure.volumeCoordinateCubicCentimetres .two = 1600
  stateTwoPressureCoordinate :
    process.figure.pressureCoordinateAtmospheres .two = 4
  stateThreeVolumeCoordinate :
    process.figure.volumeCoordinateCubicCentimetres .three = 1600
  stateThreePressureCoordinate :
    process.figure.pressureCoordinateAtmospheres .three = 2
  everyArrowShown : ∀ step, process.figure.arrowShown step = true
  arrowsHaveDepictedStart : ∀ step,
    process.figure.arrowStart step = step.startState
  arrowsHaveDepictedEnd : ∀ step,
    process.figure.arrowEnd step = step.endState
  firstPathIsHorizontal :
    process.figure.pathGeometry .oneToTwo = .horizontal
  secondPathIsVertical :
    process.figure.pathGeometry .twoToThree = .vertical
  pressureReadoutMatchesFigure : ∀ state,
    pressureInAtmospheres (process.stateAt state).pressure =
      process.figure.pressureCoordinateAtmospheres state
  volumeReadoutMatchesFigure : ∀ state,
    volumeInCubicCentimetres (process.stateAt state).volume =
      process.figure.volumeCoordinateCubicCentimetres state

/-!
The prose data: the sample contains `0.10 mol` of a monatomic ideal gas.
The process-kind fields give the standard thermodynamic interpretation of the
horizontal and vertical paths in the supplied pressure--volume diagram.
Positivity fields express ordinary nondegeneracy of the calibrated model.
-/
structure MatchesProblemScenario
    {amountScale : AmountOfSubstanceScale}
    (process : MonatomicGasProcess amountScale) : Prop where
  amountIsPointOneMole : amountScale.inMoles process.gasAmount = 1 / 10
  gasIsMonatomicIdeal : process.gasModel = .monatomicIdeal
  temperatureUnitIsKelvin :
    process.temperatureStorageUnit = TemperatureUnit.kelvin
  firstStepIsIsobaric : process.processKind .oneToTwo = .isobaric
  secondStepIsIsochoric : process.processKind .twoToThree = .isochoric
  amountPositive : 0 < amountScale.inMoles process.gasAmount
  gasConstantPositive :
    0 < process.universalGasConstantJoulesPerMoleKelvin
  everyPressurePositive : ∀ state,
    0 < pressureInPascals (process.stateAt state).pressure
  everyVolumePositive : ∀ state,
    0 < volumeInCubicMetres (process.stateAt state).volume
  everyAbsoluteTemperaturePositive : ∀ state,
    0 < temperatureInKelvin process.temperatureStorageUnit
      (process.stateAt state).temperature

/-! ## Governing thermodynamic laws -/

/-!
The physical laws used to determine the heat transfer:

* `PV = nRT` in coherent SI readouts at every equilibrium state;
* `ΔU = (3/2)nRΔT` for a monatomic ideal gas;
* `ΔU = Q - W_by` for each depicted process segment;
* a process explicitly identified as isochoric has zero boundary work.

These are general laws over the modeled states and steps.  In particular,
none states the requested numerical heat for `2 → 3` or selects an answer.
-/
structure SatisfiesMonatomicIdealGasPhysics
    {amountScale : AmountOfSubstanceScale}
    (process : MonatomicGasProcess amountScale) : Prop where
  idealGasLaw : ∀ state,
    pressureInPascals (process.stateAt state).pressure *
        volumeInCubicMetres (process.stateAt state).volume =
      amountScale.inMoles process.gasAmount *
        process.universalGasConstantJoulesPerMoleKelvin *
          temperatureInKelvin process.temperatureStorageUnit
            (process.stateAt state).temperature
  monatomicInternalEnergyDifference : ∀ initial final,
    energyInJoules (process.stateAt final).internalEnergy -
        energyInJoules (process.stateAt initial).internalEnergy =
      (3 / 2 : ℝ) * amountScale.inMoles process.gasAmount *
        process.universalGasConstantJoulesPerMoleKelvin *
          (temperatureInKelvin process.temperatureStorageUnit
              (process.stateAt final).temperature -
            temperatureInKelvin process.temperatureStorageUnit
              (process.stateAt initial).temperature)
  firstLaw : ∀ step,
    energyInJoules (process.stateAt step.endState).internalEnergy -
        energyInJoules (process.stateAt step.startState).internalEnergy =
      energyInJoules (process.heatTransferredToGas step) -
        energyInJoules (process.boundaryWorkDoneByGas step)
  isochoricBoundaryWork : ∀ step,
    process.processKind step = .isochoric →
      energyInJoules (process.boundaryWorkDoneByGas step) = 0

/-! ## Requested heat and answer-choice metadata -/

/-- Heat transferred to the gas during the depicted process `2 → 3`. -/
def heatDuringProcessTwoToThreeInJoules
    {amountScale : AmountOfSubstanceScale}
    (process : MonatomicGasProcess amountScale) : ℝ :=
  energyInJoules (process.heatTransferredToGas .twoToThree)

/-- Labels of the four heat-energy choices printed with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- The heat in joules printed beside each answer label. -/
def displayedHeatInJoules : AnswerChoice → ℝ
  | .A => 488
  | .B => -815
  | .C => -488
  | .D => 0

/-!
A choice is selected by the usual closest-listed-value interpretation.  This
is needed because the coherent standard-atmosphere conversion gives an exact
heat of `-486.36 J`, while the displayed answer is `-488 J`.
-/
def IsClosestDisplayedHeat
    {amountScale : AmountOfSubstanceScale}
    (process : MonatomicGasProcess amountScale)
    (choice : AnswerChoice) : Prop :=
  ∀ other : AnswerChoice,
    |heatDuringProcessTwoToThreeInJoules process -
        displayedHeatInJoules choice| ≤
      |heatDuringProcessTwoToThreeInJoules process -
        displayedHeatInJoules other|

/-!
During `2 → 3`, the volume is fixed at `1600 cm³` while pressure falls from
`4 atm` to `2 atm`, so boundary work is zero.  Combining `PV = nRT` with
`ΔU = (3/2)nRΔT` and the first law gives

`Q₂₃ = (3/2)(0.0016 m³)(-2 · 101325 Pa) = -12159/25 J = -486.36 J`.

Consequently `-488 J`, choice `C`, is the uniquely closest displayed answer.
Neither the exact heat nor the selected answer is present in any premise.

Blueprint: `thm:physics:phyx_mini_0411:target`.
-/
theorem heat_transferred_during_isochoric_process_two_to_three
    {amountScale : AmountOfSubstanceScale}
    (process : MonatomicGasProcess amountScale)
    (hFigure : MatchesSuppliedFigure process)
    (hScenario : MatchesProblemScenario process)
    (hPhysics : SatisfiesMonatomicIdealGasPhysics process) :
    heatDuringProcessTwoToThreeInJoules process = (-12159 / 25 : ℝ) ∧
      ∀ choice : AnswerChoice,
        IsClosestDisplayedHeat process choice ↔ choice = .C := by
  have hpTwoAtmospheres :
      pressureInAtmospheres (process.stateAt .two).pressure = 4 := by
    calc
      pressureInAtmospheres (process.stateAt .two).pressure =
          process.figure.pressureCoordinateAtmospheres .two :=
        hFigure.pressureReadoutMatchesFigure .two
      _ = 4 := hFigure.stateTwoPressureCoordinate
  have hpThreeAtmospheres :
      pressureInAtmospheres (process.stateAt .three).pressure = 2 := by
    calc
      pressureInAtmospheres (process.stateAt .three).pressure =
          process.figure.pressureCoordinateAtmospheres .three :=
        hFigure.pressureReadoutMatchesFigure .three
      _ = 2 := hFigure.stateThreePressureCoordinate
  have hvTwoCubicCentimetres :
      volumeInCubicCentimetres (process.stateAt .two).volume = 1600 := by
    calc
      volumeInCubicCentimetres (process.stateAt .two).volume =
          process.figure.volumeCoordinateCubicCentimetres .two :=
        hFigure.volumeReadoutMatchesFigure .two
      _ = 1600 := hFigure.stateTwoVolumeCoordinate
  have hvThreeCubicCentimetres :
      volumeInCubicCentimetres (process.stateAt .three).volume = 1600 := by
    calc
      volumeInCubicCentimetres (process.stateAt .three).volume =
          process.figure.volumeCoordinateCubicCentimetres .three :=
        hFigure.volumeReadoutMatchesFigure .three
      _ = 1600 := hFigure.stateThreeVolumeCoordinate
  have hpTwo :
      pressureInPascals (process.stateAt .two).pressure = 405300 := by
    rw [pressureInAtmospheres, standardAtmosphereInPascals_eq] at hpTwoAtmospheres
    linarith
  have hpThree :
      pressureInPascals (process.stateAt .three).pressure = 202650 := by
    rw [pressureInAtmospheres, standardAtmosphereInPascals_eq] at hpThreeAtmospheres
    linarith
  have hvTwo :
      volumeInCubicMetres (process.stateAt .two).volume = (1 / 625 : ℝ) := by
    rw [volumeInCubicCentimetres] at hvTwoCubicCentimetres
    norm_num at hvTwoCubicCentimetres ⊢
    linarith
  have hvThree :
      volumeInCubicMetres (process.stateAt .three).volume = (1 / 625 : ℝ) := by
    rw [volumeInCubicCentimetres] at hvThreeCubicCentimetres
    norm_num at hvThreeCubicCentimetres ⊢
    linarith
  have hIdealTwo := hPhysics.idealGasLaw .two
  have hIdealThree := hPhysics.idealGasLaw .three
  rw [hpTwo, hvTwo] at hIdealTwo
  rw [hpThree, hvThree] at hIdealThree
  norm_num at hIdealTwo hIdealThree
  have hInternalEnergy :=
    hPhysics.monatomicInternalEnergyDifference StateLabel.two StateLabel.three
  have hInternalEnergyValue :
      energyInJoules (process.stateAt .three).internalEnergy -
          energyInJoules (process.stateAt .two).internalEnergy =
        (-12159 / 25 : ℝ) := by
    ring_nf at hIdealTwo hIdealThree hInternalEnergy ⊢
    linarith
  have hZeroWork :
      energyInJoules (process.boundaryWorkDoneByGas .twoToThree) = 0 := by
    exact hPhysics.isochoricBoundaryWork .twoToThree
      hScenario.secondStepIsIsochoric
  have hFirstLaw := hPhysics.firstLaw .twoToThree
  simp only [ProcessStep.startState, ProcessStep.endState] at hFirstLaw
  have hHeat :
      heatDuringProcessTwoToThreeInJoules process = (-12159 / 25 : ℝ) := by
    unfold heatDuringProcessTwoToThreeInJoules
    linarith
  refine ⟨hHeat, ?_⟩
  intro choice
  constructor
  · intro hClosest
    unfold IsClosestDisplayedHeat at hClosest
    cases choice with
    | A =>
        have h := hClosest .C
        norm_num [hHeat, displayedHeatInJoules] at h
    | B =>
        have h := hClosest .C
        norm_num [hHeat, displayedHeatInJoules] at h
    | C => rfl
    | D =>
        have h := hClosest .C
        norm_num [hHeat, displayedHeatInJoules] at h
  · intro hChoice
    subst choice
    unfold IsClosestDisplayedHeat
    intro other
    rw [hHeat]
    cases other <;> norm_num [displayedHeatInJoules]

end PhyXMiniProblems.ProblemPhyXMini0411
