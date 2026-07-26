import Mathlib
import Physlib.Thermodynamics.Temperature.Basic
import Physlib.Thermodynamics.Temperature.TemperatureUnits
import Physlib.Units.WithDim.Energy
import Physlib.Units.WithDim.Pressure

/- USER: The assigned source file did not exist when this autoformalization task began. -/

/-!
# Heat supplied during an isobaric expansion of nitrogen

This file formalizes problem `phyx_mini_0409`.  The primary pressure-volume
diagram contains two processes for `0.10 mol` of nitrogen:

* process `A` is the vertical path from `(2000 cm³, 3 atm)` to
  `(2000 cm³, 1 atm)`;
* process `B` is the horizontal expansion from `(1000 cm³, 2 atm)` to
  `(3000 cm³, 2 atm)`.

The problem asks for the heat entering the gas on process `B`.  Pressure,
volume, internal energy, work, and heat retain physical dimensions.  Real
numbers occur only as explicitly unit-labelled readouts, amounts measured in
moles, a molar-gas-constant readout, and displayed answer values.

The auxiliary prose caption interchanges the labels and misreads endpoints;
the declarations below follow the bitmap, which the source designates as the
primary evidence.
-/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0409

open Dimension

/-! ## Dimensionful quantities and named-unit readouts -/

/-- A nonnegative thermodynamic volume carrying physical dimension `length³`. -/
abbrev VolumeQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * L𝓭 * L𝓭) NNReal)

/-- Thermodynamic pressure, using Physlib's dimensionful pressure type. -/
abbrev PressureQuantity : Type := DimPressure

/-- Signed internal energy, work, or heat, using Physlib's energy type. -/
abbrev EnergyQuantity : Type := DimEnergy

/-- Coherent SI cubic-metre readout of a physical volume. -/
def volumeInCubicMeters (volume : VolumeQuantity) : ℝ :=
  ((volume UnitChoices.SI).val : ℝ)

/-- Cubic-centimetre readout used on the horizontal axis of the bitmap. -/
def volumeInCubicCentimeters (volume : VolumeQuantity) : ℝ :=
  10 ^ 6 * volumeInCubicMeters volume

/-- Pascal readout of a physical pressure. -/
def pressureInPascals (pressure : PressureQuantity) : ℝ :=
  (pressure UnitChoices.SI).val /
    (DimPressure.pascal UnitChoices.SI).val

/-- Standard-atmosphere readout used on the vertical axis of the bitmap. -/
def pressureInAtmospheres (pressure : PressureQuantity) : ℝ :=
  (pressure UnitChoices.SI).val /
    (DimPressure.standardAtmosphere UnitChoices.SI).val

/-- Joule readout of a signed physical energy quantity. -/
def energyInJoules (energy : EnergyQuantity) : ℝ :=
  (energy UnitChoices.SI).val /
    (DimEnergy.joule UnitChoices.SI).val

/-- Kelvin readout of a stored Physlib absolute temperature. -/
def temperatureInKelvins
    (storageUnit : TemperatureUnit) (temperature : Temperature) : ℝ :=
  let unitRatio : NNReal := storageUnit / TemperatureUnit.kelvin
  temperature.toReal * (unitRatio : ℝ)

/-! ## Gas, thermodynamic states, and process labels -/

/-- Chemical species of the working gas. -/
inductive GasSpecies where
  | nitrogen
  deriving DecidableEq, Repr

/-- Molecular model used for the room-temperature nitrogen sample. -/
inductive MolecularModel where
  | idealDiatomicGas
  deriving DecidableEq, Repr

/-!
The scalar fields are explicitly SI/mole readouts.  They do not replace the
gas sample by a bare real number; Physlib's dimension system currently has no
base dimension for amount of substance.
-/
structure GasSample where
  species : GasSpecies
  molecularModel : MolecularModel
  amountOfGasMoles : ℝ
  molarGasConstantJoulesPerMoleKelvin : ℝ

/-- The two process labels printed next to the arrows in the bitmap. -/
inductive ProcessLabel where
  | A
  | B
  deriving DecidableEq, Fintype, Repr

/-- The initial and final state labels printed at each path's endpoints. -/
inductive EndpointLabel where
  | i
  | f
  deriving DecidableEq, Fintype, Repr

/-- Thermodynamic observables at one labelled equilibrium state. -/
structure ThermodynamicState where
  pressure : PressureQuantity
  volume : VolumeQuantity
  temperature : Temperature
  internalEnergy : EnergyQuantity

/-- Constraint defining each of the two straight processes. -/
inductive ProcessKind where
  | constantVolume
  | constantPressure
  deriving DecidableEq, Repr

/-- Direction of the arrow along a depicted process. -/
inductive ProcessDirection where
  | pressureDecrease
  | volumeExpansion
  deriving DecidableEq, Repr

/-! ## Primary-figure vocabulary -/

/-- The two Cartesian axes in the pressure-volume diagram. -/
inductive FigureAxis where
  | horizontal
  | vertical
  deriving DecidableEq, Fintype, Repr

/-- Physical quantity assigned to a diagram axis. -/
inductive AxisQuantity where
  | volume
  | pressure
  deriving DecidableEq, Repr

/-- Unit printed beside a diagram axis. -/
inductive AxisDisplayUnit where
  | cubicCentimeters
  | atmospheres
  deriving DecidableEq, Repr

/-- Literal physical symbol printed beside a diagram axis. -/
inductive AxisSymbol where
  | V
  | p
  deriving DecidableEq, Repr

/-- Geometry of one directed line segment in the `p`-`V` plane. -/
inductive PathGeometry where
  | verticalStraightSegment
  | horizontalStraightSegment
  deriving DecidableEq, Repr

/-!
Structured transcription of image `409.png`.  The numeric axis bounds and
plotted points are read in the display unit assigned to the corresponding
axis; the match predicate below supplies their exact values.
-/
structure PressureVolumeFigure where
  axisQuantity : FigureAxis → AxisQuantity
  axisDisplayUnit : FigureAxis → AxisDisplayUnit
  axisSymbol : FigureAxis → AxisSymbol
  axisMinimum : FigureAxis → ℝ
  axisMaximum : FigureAxis → ℝ
  processLabelVisible : ProcessLabel → Bool
  endpointLabelVisible : ProcessLabel → EndpointLabel → Bool
  plottedPressure : ProcessLabel → EndpointLabel → PressureQuantity
  plottedVolume : ProcessLabel → EndpointLabel → VolumeQuantity
  pathStart : ProcessLabel → EndpointLabel
  pathFinish : ProcessLabel → EndpointLabel
  pathGeometry : ProcessLabel → PathGeometry
  directionArrowShown : ProcessLabel → Bool

/-!
The common gas sample, its states along both depicted processes, signed
energy transfers, and the primary figure.  Positive heat and work use the
convention "into the gas" and "done by the gas", respectively.  No numerical
heat answer is stored in this setup.
-/
structure NitrogenProcessSetup where
  sample : GasSample
  state : ProcessLabel → EndpointLabel → ThermodynamicState
  temperatureStorageUnit : TemperatureUnit
  processKind : ProcessLabel → ProcessKind
  processDirection : ProcessLabel → ProcessDirection
  workDoneByGas : ProcessLabel → EnergyQuantity
  heatTransferredIntoGas : ProcessLabel → EnergyQuantity
  queriedProcess : ProcessLabel
  figure : PressureVolumeFigure

/-! ## Problem data and primary-image readouts -/

/-!
Exact transcription of the prose and primary bitmap.  In particular, the
bitmap—not the inconsistent auxiliary caption—shows process `B` running
horizontally from `(1000 cm³, 2 atm)` to `(3000 cm³, 2 atm)`.  No heat,
work, internal-energy, or answer-choice value occurs in these fields.
-/
structure MatchesProblemAndPrimaryFigure
    (setup : NitrogenProcessSetup) : Prop where
  gasSpeciesIsNitrogen : setup.sample.species = .nitrogen
  gasModelIsIdealDiatomic :
    setup.sample.molecularModel = .idealDiatomicGas
  amountOfNitrogenMoles : setup.sample.amountOfGasMoles = 1 / 10
  queriedProcessIsB : setup.queriedProcess = .B
  horizontalAxisIsVolume :
    setup.figure.axisQuantity .horizontal = .volume
  verticalAxisIsPressure :
    setup.figure.axisQuantity .vertical = .pressure
  horizontalAxisUnitIsCubicCentimeters :
    setup.figure.axisDisplayUnit .horizontal = .cubicCentimeters
  verticalAxisUnitIsAtmospheres :
    setup.figure.axisDisplayUnit .vertical = .atmospheres
  horizontalAxisSymbolIsV : setup.figure.axisSymbol .horizontal = .V
  verticalAxisSymbolIsP : setup.figure.axisSymbol .vertical = .p
  horizontalAxisStartsAtZero : setup.figure.axisMinimum .horizontal = 0
  horizontalAxisEndsAtThreeThousand :
    setup.figure.axisMaximum .horizontal = 3000
  verticalAxisStartsAtZero : setup.figure.axisMinimum .vertical = 0
  verticalAxisEndsAtThree : setup.figure.axisMaximum .vertical = 3
  processLabelsVisible : ∀ process,
    setup.figure.processLabelVisible process = true
  endpointLabelsVisible : ∀ process endpoint,
    setup.figure.endpointLabelVisible process endpoint = true
  plottedCoordinatesAreGasStates : ∀ process endpoint,
    setup.figure.plottedPressure process endpoint =
        (setup.state process endpoint).pressure ∧
      setup.figure.plottedVolume process endpoint =
        (setup.state process endpoint).volume
  processAInitialPressureAtmospheres :
    pressureInAtmospheres (setup.figure.plottedPressure .A .i) = 3
  processAFinalPressureAtmospheres :
    pressureInAtmospheres (setup.figure.plottedPressure .A .f) = 1
  processAInitialVolumeCubicCentimeters :
    volumeInCubicCentimeters (setup.figure.plottedVolume .A .i) = 2000
  processAFinalVolumeCubicCentimeters :
    volumeInCubicCentimeters (setup.figure.plottedVolume .A .f) = 2000
  processBInitialPressureAtmospheres :
    pressureInAtmospheres (setup.figure.plottedPressure .B .i) = 2
  processBFinalPressureAtmospheres :
    pressureInAtmospheres (setup.figure.plottedPressure .B .f) = 2
  processBInitialVolumeCubicCentimeters :
    volumeInCubicCentimeters (setup.figure.plottedVolume .B .i) = 1000
  processBFinalVolumeCubicCentimeters :
    volumeInCubicCentimeters (setup.figure.plottedVolume .B .f) = 3000
  pathsStartAtI : ∀ process, setup.figure.pathStart process = .i
  pathsFinishAtF : ∀ process, setup.figure.pathFinish process = .f
  processAPathIsVertical :
    setup.figure.pathGeometry .A = .verticalStraightSegment
  processBPathIsHorizontal :
    setup.figure.pathGeometry .B = .horizontalStraightSegment
  directionArrowsAreShown : ∀ process,
    setup.figure.directionArrowShown process = true
  processAIsIsochoric : setup.processKind .A = .constantVolume
  processADecreasesPressure :
    setup.processDirection .A = .pressureDecrease
  processBIsIsobaric : setup.processKind .B = .constantPressure
  processBIsAnExpansion : setup.processDirection .B = .volumeExpansion

/-! ## Physical-domain conditions and governing laws -/

/-- Positivity conditions selecting physically meaningful gas parameters. -/
structure HasPhysicalNitrogenParameters
    (setup : NitrogenProcessSetup) : Prop where
  amountOfGasPositive : 0 < setup.sample.amountOfGasMoles
  molarGasConstantPositive :
    0 < setup.sample.molarGasConstantJoulesPerMoleKelvin
  pressurePositive : ∀ process endpoint,
    0 < pressureInPascals (setup.state process endpoint).pressure
  volumePositive : ∀ process endpoint,
    0 < volumeInCubicMeters (setup.state process endpoint).volume
  absoluteTemperaturePositive : ∀ process endpoint,
    0 < temperatureInKelvins setup.temperatureStorageUnit
      (setup.state process endpoint).temperature

/-!
Macroscopic laws for the common ideal-diatomic nitrogen sample:

* `pV = nRT` at every labelled equilibrium state;
* `U = (5/2)nRT` for five active translational/rotational degrees of freedom;
* zero boundary work on an isochore and `W_by = p(V_f - V_i)` on an isobar;
* `Q_in = ΔU + W_by`, the closed-system first law with the stated signs.

These are general relations over the setup's physical variables.  They contain
neither `1418.55 J`, the displayed `1400 J`, nor an answer label.
-/
structure SatisfiesIdealDiatomicNitrogenLaws
    (setup : NitrogenProcessSetup) : Prop where
  idealGasEquation : ∀ process endpoint,
    pressureInPascals (setup.state process endpoint).pressure *
        volumeInCubicMeters (setup.state process endpoint).volume =
      setup.sample.amountOfGasMoles *
        setup.sample.molarGasConstantJoulesPerMoleKelvin *
        temperatureInKelvins setup.temperatureStorageUnit
          (setup.state process endpoint).temperature
  diatomicInternalEnergy : ∀ process endpoint,
    energyInJoules (setup.state process endpoint).internalEnergy =
      (5 / 2 : ℝ) * setup.sample.amountOfGasMoles *
        setup.sample.molarGasConstantJoulesPerMoleKelvin *
        temperatureInKelvins setup.temperatureStorageUnit
          (setup.state process endpoint).temperature
  isochoricBoundaryWork : ∀ process,
    setup.processKind process = .constantVolume →
      energyInJoules (setup.workDoneByGas process) = 0
  isobaricBoundaryWork : ∀ process,
    setup.processKind process = .constantPressure →
      energyInJoules (setup.workDoneByGas process) =
        pressureInPascals (setup.state process .i).pressure *
          (volumeInCubicMeters (setup.state process .f).volume -
            volumeInCubicMeters (setup.state process .i).volume)
  firstLaw : ∀ process,
    energyInJoules (setup.heatTransferredIntoGas process) =
      energyInJoules (setup.state process .f).internalEnergy -
        energyInJoules (setup.state process .i).internalEnergy +
        energyInJoules (setup.workDoneByGas process)

/-! ## Derived heat and multiple-choice conclusion -/

/-- Labels printed beside the four multiple-choice answers. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Heat-into-gas readout in joules printed beside each answer label. -/
def displayedHeatInJoules : AnswerChoice → ℝ
  | .A => 700
  | .B => 1000
  | .C => 1400
  | .D => -1400

/-- Answer label recorded in the dataset metadata. -/
def recordedAnswerChoice : AnswerChoice := .C

/-- The exact heat lies within half of `100 J` of the displayed choice. -/
def RoundsToDisplayedHundredJoules
    (actualHeatInJoules : ℝ) (choice : AnswerChoice) : Prop :=
  |actualHeatInJoules - displayedHeatInJoules choice| < 50

/-- The selected display is closer to the exact heat than every alternative. -/
def IsUniqueClosestDisplayedHeat
    (actualHeatInJoules : ℝ) (choice : AnswerChoice) : Prop :=
  ∀ other : AnswerChoice, other ≠ choice →
    |actualHeatInJoules - displayedHeatInJoules choice| <
      |actualHeatInJoules - displayedHeatInJoules other|

/-!
The figure readouts and governing laws give

`Q_B = (7/2) p ΔV = (7/2)(2 atm)(2000 cm³) = 1418.55 J`.

This intermediate exact value is a conclusion, not an assumption field.
-/
lemma processB_heat_exact
    (setup : NitrogenProcessSetup)
    (_problem : MatchesProblemAndPrimaryFigure setup)
    (_laws : SatisfiesIdealDiatomicNitrogenLaws setup) :
    energyInJoules (setup.heatTransferredIntoGas .B) =
      (28371 / 20 : ℝ) := by
  have hPressureInitialAtmospheres :
      pressureInAtmospheres (setup.state .B .i).pressure = 2 := by
    rw [← (_problem.plottedCoordinatesAreGasStates .B .i).1]
    exact _problem.processBInitialPressureAtmospheres
  have hPressureFinalAtmospheres :
      pressureInAtmospheres (setup.state .B .f).pressure = 2 := by
    rw [← (_problem.plottedCoordinatesAreGasStates .B .f).1]
    exact _problem.processBFinalPressureAtmospheres
  have hVolumeInitialCubicCentimeters :
      volumeInCubicCentimeters (setup.state .B .i).volume = 1000 := by
    rw [← (_problem.plottedCoordinatesAreGasStates .B .i).2]
    exact _problem.processBInitialVolumeCubicCentimeters
  have hVolumeFinalCubicCentimeters :
      volumeInCubicCentimeters (setup.state .B .f).volume = 3000 := by
    rw [← (_problem.plottedCoordinatesAreGasStates .B .f).2]
    exact _problem.processBFinalVolumeCubicCentimeters
  have hPressureInitialPascals :
      pressureInPascals (setup.state .B .i).pressure = 202650 := by
    unfold pressureInAtmospheres at hPressureInitialAtmospheres
    unfold pressureInPascals
    norm_num [DimPressure.standardAtmosphere, DimPressure.pascal,
      CarriesDimension.toDimensionful_apply_apply] at hPressureInitialAtmospheres ⊢
    linarith
  have hPressureFinalPascals :
      pressureInPascals (setup.state .B .f).pressure = 202650 := by
    unfold pressureInAtmospheres at hPressureFinalAtmospheres
    unfold pressureInPascals
    norm_num [DimPressure.standardAtmosphere, DimPressure.pascal,
      CarriesDimension.toDimensionful_apply_apply] at hPressureFinalAtmospheres ⊢
    linarith
  have hVolumeInitialCubicMeters :
      volumeInCubicMeters (setup.state .B .i).volume = (1 / 1000 : ℝ) := by
    unfold volumeInCubicCentimeters at hVolumeInitialCubicCentimeters
    norm_num at hVolumeInitialCubicCentimeters ⊢
    linarith
  have hVolumeFinalCubicMeters :
      volumeInCubicMeters (setup.state .B .f).volume = (3 / 1000 : ℝ) := by
    unfold volumeInCubicCentimeters at hVolumeFinalCubicCentimeters
    norm_num at hVolumeFinalCubicCentimeters ⊢
    linarith
  have hIdealInitial := _laws.idealGasEquation .B .i
  have hIdealFinal := _laws.idealGasEquation .B .f
  have hInternalEnergyInitial := _laws.diatomicInternalEnergy .B .i
  have hInternalEnergyFinal := _laws.diatomicInternalEnergy .B .f
  have hWork :=
    _laws.isobaricBoundaryWork .B _problem.processBIsIsobaric
  have hFirstLaw := _laws.firstLaw .B
  rw [hPressureInitialPascals, hVolumeInitialCubicMeters] at hIdealInitial
  rw [hPressureFinalPascals, hVolumeFinalCubicMeters] at hIdealFinal
  rw [hPressureInitialPascals, hVolumeInitialCubicMeters,
    hVolumeFinalCubicMeters] at hWork
  norm_num at hIdealInitial hIdealFinal hWork
  nlinarith [hIdealInitial, hIdealFinal, hInternalEnergyInitial,
    hInternalEnergyFinal, hWork, hFirstLaw]

/-!
Thus the required heat is exactly `1418.55 J`; it rounds to and uniquely
selects the displayed `1400 J`, answer C.

Blueprint label: `thm:physics:phyx_mini_0409:target`.
-/
theorem heat_required_for_process_B_is_answer_C
    (setup : NitrogenProcessSetup)
    (_problem : MatchesProblemAndPrimaryFigure setup)
    (_physical : HasPhysicalNitrogenParameters setup)
    (_laws : SatisfiesIdealDiatomicNitrogenLaws setup) :
    energyInJoules (setup.heatTransferredIntoGas .B) =
        (28371 / 20 : ℝ) ∧
      RoundsToDisplayedHundredJoules
        (energyInJoules (setup.heatTransferredIntoGas .B))
        recordedAnswerChoice ∧
      IsUniqueClosestDisplayedHeat
        (energyInJoules (setup.heatTransferredIntoGas .B))
        recordedAnswerChoice := by
  have hHeat := processB_heat_exact setup _problem _laws
  refine ⟨hHeat, ?_, ?_⟩
  · rw [hHeat]
    norm_num [RoundsToDisplayedHundredJoules, recordedAnswerChoice,
      displayedHeatInJoules, abs_of_nonneg]
  · rw [hHeat]
    intro other hOther
    fin_cases other <;>
      norm_num [IsUniqueClosestDisplayedHeat, recordedAnswerChoice,
        displayedHeatInJoules, abs_of_nonneg, abs_of_nonpos] at *

end PhyXMiniProblems.ProblemPhyXMini0409
