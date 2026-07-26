import Mathlib
import Physlib.Thermodynamics.Temperature.Basic
import Physlib.Thermodynamics.Temperature.TemperatureUnits
import Physlib.Units.WithDim.Energy
import Physlib.Units.WithDim.Pressure

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0495

open Dimension

/-!
# Internal-energy change for a two-step monatomic ideal-gas process

The supplied pressure--volume raster shows state `1` at
`(2.00 m^3, 425 Pa)` and state `2` at `(8.00 m^3, 425 Pa)`.  The question
asks for the internal-energy change of `1.75 mol` of a monatomic ideal gas
along the named two-step process B from state `1` to state `2`.

Pressure, volume, temperature, and internal energy retain physical quantity
types.  Real numbers below are calibrated readouts in named SI units,
dimensionless ratios, diagram coordinates, or displayed answer values.
-/

/-! ## Physical quantities and calibrated readouts -/

/-- A nonnegative physical volume carrying dimension length cubed. -/
abbrev VolumeQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * L𝓭 * L𝓭) NNReal)

/-!
An abstract amount-of-substance carrier with a mole readout.  Physlib has no
named dimensionful amount-of-substance type or mole unit suitable for this
macroscopic gas sample.
-/
structure AmountOfSubstanceScale where
  Quantity : Type
  inMoles : Quantity → ℝ

/-!
An abstract carrier for the universal gas constant, equipped with its
joule-per-mole-kelvin readout.
-/
structure MolarThermalCoefficientScale where
  Quantity : Type
  inJoulesPerMoleKelvin : Quantity → ℝ

/-- Read a physical pressure in coherent SI pascals (`N/m^2`). -/
def pressureInPascals (pressure : DimPressure) : ℝ :=
  (pressure UnitChoices.SI).val

/-- Read a physical volume in coherent SI cubic metres. -/
def volumeInCubicMetres (volume : VolumeQuantity) : ℝ :=
  ((volume UnitChoices.SI).val : ℝ)

/-- Read physical internal energy in coherent SI joules. -/
def energyInJoules (energy : DimEnergy) : ℝ :=
  (energy UnitChoices.SI).val

/-- Read an absolute temperature in kelvins from its zero-preserving unit. -/
def temperatureInKelvins
    (storageUnit : TemperatureUnit) (temperature : Temperature) : ℝ :=
  let unitRatio : NNReal := storageUnit / TemperatureUnit.kelvin
  temperature.toReal * (unitRatio : ℝ)

/-! ## States, the two-step route B, and the supplied figure -/

/-- Nodes encountered along process B; only the endpoints are labelled. -/
inductive ProcessPoint where
  | stateOne
  | intermediateB
  | stateTwo
  deriving DecidableEq, Fintype, Repr

/-- The two consecutive legs that constitute process B. -/
inductive ProcessBStep where
  | first
  | second
  deriving DecidableEq, Fintype, Repr

/-- Initial node of each step of process B. -/
def processBStepStart : ProcessBStep → ProcessPoint
  | .first => .stateOne
  | .second => .intermediateB

/-- Final node of each step of process B. -/
def processBStepFinish : ProcessBStep → ProcessPoint
  | .first => .intermediateB
  | .second => .stateTwo

/-- The named process selected by the question. -/
inductive ProcessName where
  | B
  | other
  deriving DecidableEq, Repr

/-- A pressure--volume--temperature equilibrium state of the gas. -/
structure EquilibriumGasState where
  pressure : DimPressure
  volume : VolumeQuantity
  temperature : Temperature

/-- The two coordinate axes in the pressure--volume raster. -/
inductive DiagramAxis where
  | horizontal
  | vertical
  deriving DecidableEq, Fintype, Repr

/-- The physical quantity plotted on a diagram axis. -/
inductive AxisQuantity where
  | volume
  | pressure
  deriving DecidableEq, Repr

/-- Units printed beside the two axes. -/
inductive AxisUnit where
  | cubicMetre
  | pascal
  deriving DecidableEq, Repr

/-- The two red points labelled `1` and `2` in the raster. -/
inductive FigurePoint where
  | one
  | two
  deriving DecidableEq, Fintype, Repr

/-- Process node represented by a labelled red point. -/
def figurePointProcessPoint : FigurePoint → ProcessPoint
  | .one => .stateOne
  | .two => .stateTwo

/-!
Primary-image content.  The source raster shows the two endpoint points but
does not draw the two legs or the intermediate point of process B.
-/
structure PressureVolumeDiagram where
  axisQuantity : DiagramAxis → AxisQuantity
  axisUnit : DiagramAxis → AxisUnit
  volumeTickCoordinates : List ℝ
  pressureTickCoordinates : List ℝ
  showsPointLabel : FigurePoint → Bool
  pointLabelText : FigurePoint → String
  pointVolumeCoordinate : FigurePoint → ℝ
  pointPressureCoordinate : FigurePoint → ℝ
  showsProcessBPath : Bool

/-- Constitutive model stipulated in the problem. -/
inductive GasModel where
  | monatomicIdealGas
  | other
  deriving DecidableEq, Repr

/-!
Independent physical data.  No internal-energy change, displayed answer, or
answer-choice label is stored in the setup.
-/
structure IdealGasProcessSetup
    (amountScale : AmountOfSubstanceScale)
    (thermalScale : MolarThermalCoefficientScale) where
  gasModel : GasModel
  sameClosedGasSample : Bool
  selectedProcess : ProcessName
  amountOfGas : amountScale.Quantity
  universalGasConstant : thermalScale.Quantity
  temperatureStorageUnit : TemperatureUnit
  stateAt : ProcessPoint → EquilibriumGasState
  internalEnergyAt : ProcessPoint → DimEnergy
  figure : PressureVolumeDiagram

/-- Mole readout of the fixed gas sample. -/
def amountOfGasInMoles
    {amountScale : AmountOfSubstanceScale}
    {thermalScale : MolarThermalCoefficientScale}
    (setup : IdealGasProcessSetup amountScale thermalScale) : ℝ :=
  amountScale.inMoles setup.amountOfGas

/-- Pascal readout of pressure at a process node. -/
def statePressureInPascals
    {amountScale : AmountOfSubstanceScale}
    {thermalScale : MolarThermalCoefficientScale}
    (setup : IdealGasProcessSetup amountScale thermalScale)
    (point : ProcessPoint) : ℝ :=
  pressureInPascals (setup.stateAt point).pressure

/-- Cubic-metre readout of volume at a process node. -/
def stateVolumeInCubicMetres
    {amountScale : AmountOfSubstanceScale}
    {thermalScale : MolarThermalCoefficientScale}
    (setup : IdealGasProcessSetup amountScale thermalScale)
    (point : ProcessPoint) : ℝ :=
  volumeInCubicMetres (setup.stateAt point).volume

/-- Kelvin readout of absolute temperature at a process node. -/
def stateTemperatureInKelvins
    {amountScale : AmountOfSubstanceScale}
    {thermalScale : MolarThermalCoefficientScale}
    (setup : IdealGasProcessSetup amountScale thermalScale)
    (point : ProcessPoint) : ℝ :=
  temperatureInKelvins setup.temperatureStorageUnit
    (setup.stateAt point).temperature

/-- Joule readout of internal energy at a process node. -/
def internalEnergyInJoules
    {amountScale : AmountOfSubstanceScale}
    {thermalScale : MolarThermalCoefficientScale}
    (setup : IdealGasProcessSetup amountScale thermalScale)
    (point : ProcessPoint) : ℝ :=
  energyInJoules (setup.internalEnergyAt point)

/-!
Change in internal energy along process B.  This is the endpoint difference
because internal energy is a state function; the intermediate path geometry
does not enter this definition.
-/
def internalEnergyChangeForProcessBInJoules
    {amountScale : AmountOfSubstanceScale}
    {thermalScale : MolarThermalCoefficientScale}
    (setup : IdealGasProcessSetup amountScale thermalScale) : ℝ :=
  internalEnergyInJoules setup (processBStepFinish .second) -
    internalEnergyInJoules setup (processBStepStart .first)

/-! ## Assumptions: scenario, readouts, figure evidence, and laws -/

/-- Qualitative scenario facts stated by the question. -/
structure MatchesMonatomicIdealGasScenario
    {amountScale : AmountOfSubstanceScale}
    {thermalScale : MolarThermalCoefficientScale}
    (setup : IdealGasProcessSetup amountScale thermalScale) : Prop where
  gasIsMonatomicIdeal : setup.gasModel = .monatomicIdealGas
  oneFixedClosedSample : setup.sameClosedGasSample = true
  requestedProcessIsB : setup.selectedProcess = .B

/-!
Numerical readouts given in the prose.  They contain no internal-energy
change or answer-choice value.
-/
structure MatchesProblemStatementReadouts
    {amountScale : AmountOfSubstanceScale}
    {thermalScale : MolarThermalCoefficientScale}
    (setup : IdealGasProcessSetup amountScale thermalScale) : Prop where
  amountIsOnePointSevenFiveMoles :
    amountOfGasInMoles setup = (7 / 4 : ℝ)
  stateOnePressureIsFourHundredTwentyFivePascals :
    statePressureInPascals setup .stateOne = 425
  stateTwoPressureIsFourHundredTwentyFivePascals :
    statePressureInPascals setup .stateTwo = 425
  stateOneVolumeIsTwoCubicMetres :
    stateVolumeInCubicMetres setup .stateOne = 2
  stateTwoVolumeIsEightCubicMetres :
    stateVolumeInCubicMetres setup .stateTwo = 8

/-!
Facts read from the supplied raster, including its axis ticks and endpoint
labels.  The absent process-path drawing is recorded explicitly so no path
geometry is inferred from the image.
-/
structure MatchesSuppliedPVDiagram
    {amountScale : AmountOfSubstanceScale}
    {thermalScale : MolarThermalCoefficientScale}
    (setup : IdealGasProcessSetup amountScale thermalScale) : Prop where
  horizontalAxisIsVolume :
    setup.figure.axisQuantity .horizontal = .volume
  verticalAxisIsPressure :
    setup.figure.axisQuantity .vertical = .pressure
  horizontalAxisUsesCubicMetres :
    setup.figure.axisUnit .horizontal = .cubicMetre
  verticalAxisUsesPascals :
    setup.figure.axisUnit .vertical = .pascal
  volumeTicksShown :
    setup.figure.volumeTickCoordinates = [0, 2, 4, 6, 8, 10]
  pressureTicksShown :
    setup.figure.pressureTickCoordinates = [0, 100, 200, 300, 400, 500]
  bothPointLabelsShown :
    ∀ point, setup.figure.showsPointLabel point = true
  pointOneLabelText : setup.figure.pointLabelText .one = "1"
  pointTwoLabelText : setup.figure.pointLabelText .two = "2"
  pointCoordinatesMatchPhysicalStates :
    ∀ point,
      setup.figure.pointVolumeCoordinate point =
          stateVolumeInCubicMetres setup (figurePointProcessPoint point) ∧
        setup.figure.pointPressureCoordinate point =
          statePressureInPascals setup (figurePointProcessPoint point)
  processBPathIsNotDrawn : setup.figure.showsProcessBPath = false

/-- Positivity and nondegeneracy of the physical gas parameters. -/
structure HasPhysicalGasParameters
    {amountScale : AmountOfSubstanceScale}
    {thermalScale : MolarThermalCoefficientScale}
    (setup : IdealGasProcessSetup amountScale thermalScale) : Prop where
  amountPositive : 0 < amountOfGasInMoles setup
  universalGasConstantPositive :
    0 < thermalScale.inJoulesPerMoleKelvin setup.universalGasConstant
  pressurePositive :
    ∀ point, 0 < statePressureInPascals setup point
  volumePositive :
    ∀ point, 0 < stateVolumeInCubicMetres setup point
  absoluteTemperaturePositive :
    ∀ point, 0 < stateTemperatureInKelvins setup point

/-!
Governing laws for a fixed monatomic ideal gas.  They state `PV = nRT` and
`U = (3/2)nRT` at every equilibrium process node and contain no numerical
internal-energy change or displayed answer.
-/
structure SatisfiesMonatomicIdealGasLaws
    {amountScale : AmountOfSubstanceScale}
    {thermalScale : MolarThermalCoefficientScale}
    (setup : IdealGasProcessSetup amountScale thermalScale) : Prop where
  idealGasEquation :
    ∀ point,
      statePressureInPascals setup point *
          stateVolumeInCubicMetres setup point =
        amountOfGasInMoles setup *
          thermalScale.inJoulesPerMoleKelvin setup.universalGasConstant *
            stateTemperatureInKelvins setup point
  monatomicInternalEnergyEquation :
    ∀ point,
      internalEnergyInJoules setup point =
        (3 / 2 : ℝ) * amountOfGasInMoles setup *
          thermalScale.inJoulesPerMoleKelvin setup.universalGasConstant *
            stateTemperatureInKelvins setup point

/-! ## Displayed answers and formalization target -/

/-- Labels of the four displayed multiple-choice answers. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Energy change in joules printed beside each answer label. -/
def displayedInternalEnergyChangeInJoules : AnswerChoice → ℝ
  | .A => 4130
  | .B => 3230
  | .C => 3530
  | .D => 3830

/-- The source dataset's recorded label, retained only as metadata. -/
def recordedDatasetAnswer : AnswerChoice := .D

/-!
`displayed` is the nearest multiple-of-ten presentation of `exact`, using a
left-closed, right-open ten-joule bin (the usual half-up convention).
-/
def RoundsToNearestTenJoules (exact displayed : ℝ) : Prop :=
  displayed - 5 ≤ exact ∧ exact < displayed + 5

/-- A displayed choice agrees with the exact process-B energy change. -/
def MatchesDisplayedInternalEnergyChange
    {amountScale : AmountOfSubstanceScale}
    {thermalScale : MolarThermalCoefficientScale}
    (setup : IdealGasProcessSetup amountScale thermalScale)
    (choice : AnswerChoice) : Prop :=
  RoundsToNearestTenJoules
    (internalEnergyChangeForProcessBInJoules setup)
    (displayedInternalEnergyChangeInJoules choice)

/-!
For a monatomic ideal gas, `U = (3/2)PV` at each endpoint.  Hence process B
has exact change

`(3/2) * 425 Pa * (8 - 2) m^3 = 3825 J`,

which is displayed as `3830 J`; therefore D is the unique matching choice.
All three facts remain conclusions.

Blueprint: `thm:physics:phyx_mini_0495:target`.
-/
theorem problem_phyx_mini_0495
    {amountScale : AmountOfSubstanceScale}
    {thermalScale : MolarThermalCoefficientScale}
    (setup : IdealGasProcessSetup amountScale thermalScale)
    (hScenario : MatchesMonatomicIdealGasScenario setup)
    (hData : MatchesProblemStatementReadouts setup)
    (hFigure : MatchesSuppliedPVDiagram setup)
    (hPhysical : HasPhysicalGasParameters setup)
    (hLaws : SatisfiesMonatomicIdealGasLaws setup) :
    internalEnergyChangeForProcessBInJoules setup = 3825 ∧
      RoundsToNearestTenJoules
        (internalEnergyChangeForProcessBInJoules setup) 3830 ∧
      ∀ choice : AnswerChoice,
        MatchesDisplayedInternalEnergyChange setup choice ↔ choice = .D := by
  have hStateOneEnergy :
      internalEnergyInJoules setup .stateOne = 1275 := by
    have hIdealGas := hLaws.idealGasEquation .stateOne
    have hInternalEnergy :=
      hLaws.monatomicInternalEnergyEquation .stateOne
    rw [hData.stateOnePressureIsFourHundredTwentyFivePascals,
      hData.stateOneVolumeIsTwoCubicMetres] at hIdealGas
    nlinarith
  have hStateTwoEnergy :
      internalEnergyInJoules setup .stateTwo = 5100 := by
    have hIdealGas := hLaws.idealGasEquation .stateTwo
    have hInternalEnergy :=
      hLaws.monatomicInternalEnergyEquation .stateTwo
    rw [hData.stateTwoPressureIsFourHundredTwentyFivePascals,
      hData.stateTwoVolumeIsEightCubicMetres] at hIdealGas
    nlinarith
  have hExact :
      internalEnergyChangeForProcessBInJoules setup = 3825 := by
    change
      internalEnergyInJoules setup .stateTwo -
          internalEnergyInJoules setup .stateOne =
        3825
    norm_num [hStateOneEnergy, hStateTwoEnergy]
  refine ⟨hExact, ?_, ?_⟩
  · rw [hExact]
    norm_num [RoundsToNearestTenJoules]
  · intro choice
    cases choice <;>
      simp [MatchesDisplayedInternalEnergyChange,
        displayedInternalEnergyChangeInJoules, RoundsToNearestTenJoules,
        hExact] <;>
      norm_num

end PhyXMiniProblems.ProblemPhyXMini0495
