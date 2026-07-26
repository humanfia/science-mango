import Mathlib
import Physlib.Thermodynamics.Temperature.Basic
import Physlib.Units.WithDim.Energy
import Physlib.Units.WithDim.Pressure

/- USER: The assigned source file did not exist when this autoformalization task began. -/

/-!
# Heat transferred along a straight pressure--volume path

The primary figure shows `0.015 mol` of hydrogen following the straight
pressure--volume path

* `i = (100 cm³, 4 atm)`,
* `f = (300 cm³, 1 atm)`.

The bitmap, rather than its auxiliary caption, is the source for the final
volume `300 cm³`.  Pressure, volume, temperature, internal energy, heat, and
work remain physical quantities.  Real numbers below occur only as readouts
in named units, dimensionless path parameters, effective degrees of freedom,
or displayed multiple-choice values.

The recorded answer `36 J` corresponds to the textbook effective model
`C_V = (3/2) R`.  With the exact standard atmosphere conversion, that model
gives `28371/800 J = 35.46375 J`; the theorem therefore identifies `36 J` as
the unique closest displayed choice rather than asserting a false exact
equality.
-/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0413

open Dimension

/-! ## Dimensionful quantities and named-unit readouts -/

/-- A nonnegative physical gas volume, carrying dimension `length³`. -/
abbrev VolumeQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * L𝓭 * L𝓭) NNReal)

/-- Energy per mole per kelvin, with the mole count represented by a named readout. -/
abbrev MolarEnergyPerKelvin : Type :=
  Dimensionful
    (WithDim (M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹ * Θ𝓭⁻¹) ℝ)

/-- Coherent-SI cubic-metre readout of a physical volume. -/
def volumeInCubicMeters (volume : VolumeQuantity) : ℝ :=
  ((volume UnitChoices.SI).val : ℝ)

/-- Cubic-centimetre readout used on the horizontal axis, `1 m³ = 10⁶ cm³`. -/
def volumeInCubicCentimeters (volume : VolumeQuantity) : ℝ :=
  10 ^ 6 * volumeInCubicMeters volume

/-- Pascal readout of a physical pressure. -/
def pressureInPascals (pressure : DimPressure) : ℝ :=
  (pressure UnitChoices.SI).val /
    (DimPressure.pascal UnitChoices.SI).val

/-- Pressure readout as a multiple of Physlib's standard atmosphere. -/
def pressureInAtmospheres (pressure : DimPressure) : ℝ :=
  pressureInPascals pressure /
    pressureInPascals DimPressure.standardAtmosphere

/-- Joule readout of a signed physical energy. -/
def energyInJoules (energy : DimEnergy) : ℝ :=
  (energy UnitChoices.SI).val /
    (DimEnergy.joule UnitChoices.SI).val

/-- Kelvin readout of Physlib's absolute-temperature object. -/
def temperatureInKelvins (temperature : Temperature) : ℝ :=
  temperature.toReal

/-- Joules-per-mole-kelvin readout of a molar energy-per-temperature quantity. -/
def molarEnergyPerKelvinInSI (quantity : MolarEnergyPerKelvin) : ℝ :=
  (quantity UnitChoices.SI).val

/-! ## Gas, thermodynamic states, and primary-figure vocabulary -/

/-- Chemical species named by the problem statement. -/
inductive GasSpecies where
  | hydrogen
  deriving DecidableEq, Repr

/-- Equation-of-state model used in the intended calculation. -/
inductive EquationOfStateModel where
  | idealGas
  | other
  deriving DecidableEq, Repr

/-!
The gas sample is a physical object with chemical and modeling roles.
`amountInMoles` is an explicitly unit-labelled scalar readout, not a scalar
replacement for the sample.
-/
structure GasSample where
  species : GasSpecies
  equationOfStateModel : EquationOfStateModel
  amountInMoles : ℝ

/-- The two endpoint labels printed in the pressure--volume diagram. -/
inductive StateLabel where
  | i
  | f
  deriving DecidableEq, Fintype, Repr

/-- One equilibrium state of the gas, including its state-function energy. -/
structure ThermodynamicState where
  pressure : DimPressure
  volume : VolumeQuantity
  temperature : Temperature
  internalEnergy : DimEnergy

/-- The two axes visible in the supplied bitmap. -/
inductive FigureAxis where
  | horizontal
  | vertical
  deriving DecidableEq, Fintype, Repr

/-- Physical quantity assigned to a diagram axis. -/
inductive AxisQuantity where
  | volume
  | pressure
  deriving DecidableEq, Repr

/-- Unit text printed beside a diagram axis. -/
inductive AxisDisplayUnit where
  | cubicCentimeters
  | standardAtmospheres
  deriving DecidableEq, Repr

/-- Literal state label printed next to a plotted endpoint. -/
inductive FigurePointLabel where
  | i
  | f
  deriving DecidableEq, Fintype, Repr

/-- Geometry of the only process path visible in the figure. -/
inductive PathGeometry where
  | straightSegment
  deriving DecidableEq, Repr

/-!
Scalar coordinate fields are literal readouts from the axes.  They are linked
to dimensionful thermodynamic states by `MatchesPrimaryFigure` below.
-/
structure PressureVolumeDiagram where
  axisQuantity : FigureAxis → AxisQuantity
  axisDisplayUnit : FigureAxis → AxisDisplayUnit
  axisMinimum : FigureAxis → ℝ
  axisMaximum : FigureAxis → ℝ
  pointVolumeCubicCentimeters : StateLabel → ℝ
  pointPressureAtmospheres : StateLabel → ℝ
  pointLabelShown : FigurePointLabel → Bool
  pathGeometry : PathGeometry
  arrowShown : Bool
  arrowStart : StateLabel
  arrowFinish : StateLabel

/-!
The independent physical setup.  Heat is positive into the gas and work is
positive when done by the gas.  Neither energy field is defined from the
recorded answer.
-/
structure HydrogenStraightPVProcess where
  gas : GasSample
  state : StateLabel → ThermodynamicState
  stateAlongPath : ℝ → ThermodynamicState
  molarGasConstant : MolarEnergyPerKelvin
  molarHeatCapacityAtConstantVolume : MolarEnergyPerKelvin
  workDoneByGas : DimEnergy
  heatTransferredToGas : DimEnergy
  figure : PressureVolumeDiagram

/-! ## Problem data and primary-image evidence -/

/-- Prose data and the ideal-gas equation-of-state choice, without a heat answer. -/
structure MatchesProblemDescription
    (setup : HydrogenStraightPVProcess) : Prop where
  workingSubstanceIsHydrogen : setup.gas.species = .hydrogen
  idealGasModelSelected : setup.gas.equationOfStateModel = .idealGas
  amountOfGasInMoles : setup.gas.amountInMoles = (15 / 1000 : ℝ)

/-!
Exact evidence transcribed from the primary bitmap `phyx_data/test_image/413.png`.
In particular, the plotted final volume is `300 cm³`; the auxiliary caption's
approximately `250 cm³` statement is not used.
-/
structure MatchesPrimaryFigure
    (setup : HydrogenStraightPVProcess) : Prop where
  horizontalAxisIsVolume :
    setup.figure.axisQuantity .horizontal = .volume
  verticalAxisIsPressure :
    setup.figure.axisQuantity .vertical = .pressure
  horizontalAxisUsesCubicCentimeters :
    setup.figure.axisDisplayUnit .horizontal = .cubicCentimeters
  verticalAxisUsesAtmospheres :
    setup.figure.axisDisplayUnit .vertical = .standardAtmospheres
  horizontalAxisRange :
    setup.figure.axisMinimum .horizontal = 0 ∧
      setup.figure.axisMaximum .horizontal = 300
  verticalAxisRange :
    setup.figure.axisMinimum .vertical = 0 ∧
      setup.figure.axisMaximum .vertical = 4
  initialCoordinate :
    setup.figure.pointVolumeCubicCentimeters .i = 100 ∧
      setup.figure.pointPressureAtmospheres .i = 4
  finalCoordinate :
    setup.figure.pointVolumeCubicCentimeters .f = 300 ∧
      setup.figure.pointPressureAtmospheres .f = 1
  coordinatesRepresentPhysicalStates :
    ∀ label : StateLabel,
      setup.figure.pointVolumeCubicCentimeters label =
          volumeInCubicCentimeters (setup.state label).volume ∧
        setup.figure.pointPressureAtmospheres label =
          pressureInAtmospheres (setup.state label).pressure
  everyEndpointLabelShown :
    ∀ label : FigurePointLabel, setup.figure.pointLabelShown label = true
  pathIsStraight : setup.figure.pathGeometry = .straightSegment
  directedArrowShown : setup.figure.arrowShown = true
  arrowStartsAtI : setup.figure.arrowStart = .i
  arrowFinishesAtF : setup.figure.arrowFinish = .f

/-! ## Physical domain, model calibration, and governing laws -/

/-- Positivity conditions selecting physically meaningful gas states. -/
structure HasPhysicalProcessParameters
    (setup : HydrogenStraightPVProcess) : Prop where
  amountPositive : 0 < setup.gas.amountInMoles
  gasConstantPositive :
    0 < molarEnergyPerKelvinInSI setup.molarGasConstant
  heatCapacityPositive :
    0 < molarEnergyPerKelvinInSI
      setup.molarHeatCapacityAtConstantVolume
  pressurePositive :
    ∀ label, 0 < pressureInPascals (setup.state label).pressure
  volumePositive :
    ∀ label, 0 < volumeInCubicMeters (setup.state label).volume
  temperaturePositive :
    ∀ label, 0 < temperatureInKelvins (setup.state label).temperature

/-!
The textbook calibration implicit in the recorded `36 J` answer: the molar
gas constant is `8.314 J mol⁻¹ K⁻¹`, and the effective constant-volume heat
capacity retains three quadratic degrees of freedom, `C_V = (3/2) R`.
This assumption is explicit because ordinary molecular hydrogen at room
temperature would instead normally use `C_V = (5/2) R`.
-/
structure UsesThreeDegreeIdealGasCalibration
    (setup : HydrogenStraightPVProcess) : Prop where
  standardMolarGasConstant :
    molarEnergyPerKelvinInSI setup.molarGasConstant = (4157 / 500 : ℝ)
  threeDegreeHeatCapacity :
    molarEnergyPerKelvinInSI
        setup.molarHeatCapacityAtConstantVolume =
      (3 / 2 : ℝ) * molarEnergyPerKelvinInSI setup.molarGasConstant

/-!
The straight path is affinely parametrized by `t ∈ [0,1]`.  For a straight
pressure trace, the quasistatic boundary work `∫ p dV` is the trapezoid area,
average endpoint pressure times the volume change.  These are generic process
laws and contain no numerical heat value.
-/
structure SatisfiesStraightPVPathAndWorkLaw
    (setup : HydrogenStraightPVProcess) : Prop where
  pathStartsAtInitialState : setup.stateAlongPath 0 = setup.state .i
  pathFinishesAtFinalState : setup.stateAlongPath 1 = setup.state .f
  affineVolume :
    ∀ parameter ∈ Set.Icc (0 : ℝ) 1,
      volumeInCubicMeters (setup.stateAlongPath parameter).volume =
        (1 - parameter) * volumeInCubicMeters (setup.state .i).volume +
          parameter * volumeInCubicMeters (setup.state .f).volume
  affinePressure :
    ∀ parameter ∈ Set.Icc (0 : ℝ) 1,
      pressureInPascals (setup.stateAlongPath parameter).pressure =
        (1 - parameter) * pressureInPascals (setup.state .i).pressure +
          parameter * pressureInPascals (setup.state .f).pressure
  straightPathBoundaryWork :
    setup.figure.pathGeometry = .straightSegment →
      energyInJoules setup.workDoneByGas =
        (pressureInPascals (setup.state .i).pressure +
            pressureInPascals (setup.state .f).pressure) / 2 *
          (volumeInCubicMeters (setup.state .f).volume -
            volumeInCubicMeters (setup.state .i).volume)

/-!
Macroscopic ideal-gas thermodynamics in coherent SI readouts:

* `pV = nRT` at each endpoint;
* `U = n C_V T` at each endpoint;
* `Q = U_f - U_i + W_by` for the depicted closed-system process.

None of these laws fixes the current question's numerical heat conclusion.
-/
structure SatisfiesIdealGasEnergyAndFirstLaws
    (setup : HydrogenStraightPVProcess) : Prop where
  idealGasLaw : ∀ label : StateLabel,
    pressureInPascals (setup.state label).pressure *
        volumeInCubicMeters (setup.state label).volume =
      setup.gas.amountInMoles *
        molarEnergyPerKelvinInSI setup.molarGasConstant *
          temperatureInKelvins (setup.state label).temperature
  internalEnergyLaw : ∀ label : StateLabel,
    energyInJoules (setup.state label).internalEnergy =
      setup.gas.amountInMoles *
        molarEnergyPerKelvinInSI
          setup.molarHeatCapacityAtConstantVolume *
          temperatureInKelvins (setup.state label).temperature
  firstLaw :
    energyInJoules setup.heatTransferredToGas =
      energyInJoules (setup.state .f).internalEnergy -
        energyInJoules (setup.state .i).internalEnergy +
          energyInJoules setup.workDoneByGas

/-! ## Derived quantities, displayed answers, and target -/

/-- Final-minus-initial internal-energy change in joules. -/
def internalEnergyChangeInJoules
    (setup : HydrogenStraightPVProcess) : ℝ :=
  energyInJoules (setup.state .f).internalEnergy -
    energyInJoules (setup.state .i).internalEnergy

/-- The straight-line pressure-volume work is exactly `50.6625 J`. -/
lemma workDoneByGas_in_joules
    (setup : HydrogenStraightPVProcess)
    (_figure : MatchesPrimaryFigure setup)
    (_pathLaw : SatisfiesStraightPVPathAndWorkLaw setup) :
    energyInJoules setup.workDoneByGas = (4053 / 80 : ℝ) := by
  have hAtm :
      pressureInPascals DimPressure.standardAtmosphere = (101325 : ℝ) := by
    norm_num [pressureInPascals, DimPressure.standardAtmosphere,
      DimPressure.pascal, CarriesDimension.toDimensionful_apply_apply,
      UnitChoices.dimScale]
  have hViCC :
      volumeInCubicCentimeters (setup.state .i).volume = (100 : ℝ) := by
    calc
      volumeInCubicCentimeters (setup.state .i).volume =
          setup.figure.pointVolumeCubicCentimeters .i :=
        (_figure.coordinatesRepresentPhysicalStates .i).1.symm
      _ = 100 := _figure.initialCoordinate.1
  have hVfCC :
      volumeInCubicCentimeters (setup.state .f).volume = (300 : ℝ) := by
    calc
      volumeInCubicCentimeters (setup.state .f).volume =
          setup.figure.pointVolumeCubicCentimeters .f :=
        (_figure.coordinatesRepresentPhysicalStates .f).1.symm
      _ = 300 := _figure.finalCoordinate.1
  have hVi :
      volumeInCubicMeters (setup.state .i).volume = (1 / 10000 : ℝ) := by
    rw [volumeInCubicCentimeters] at hViCC
    norm_num at hViCC ⊢
    linarith
  have hVf :
      volumeInCubicMeters (setup.state .f).volume = (3 / 10000 : ℝ) := by
    rw [volumeInCubicCentimeters] at hVfCC
    norm_num at hVfCC ⊢
    linarith
  have hPiAtm :
      pressureInAtmospheres (setup.state .i).pressure = (4 : ℝ) := by
    calc
      pressureInAtmospheres (setup.state .i).pressure =
          setup.figure.pointPressureAtmospheres .i :=
        (_figure.coordinatesRepresentPhysicalStates .i).2.symm
      _ = 4 := _figure.initialCoordinate.2
  have hPfAtm :
      pressureInAtmospheres (setup.state .f).pressure = (1 : ℝ) := by
    calc
      pressureInAtmospheres (setup.state .f).pressure =
          setup.figure.pointPressureAtmospheres .f :=
        (_figure.coordinatesRepresentPhysicalStates .f).2.symm
      _ = 1 := _figure.finalCoordinate.2
  have hPi :
      pressureInPascals (setup.state .i).pressure = (405300 : ℝ) := by
    rw [pressureInAtmospheres, hAtm] at hPiAtm
    linarith
  have hPf :
      pressureInPascals (setup.state .f).pressure = (101325 : ℝ) := by
    rw [pressureInAtmospheres, hAtm] at hPfAtm
    linarith
  have hwork :=
    _pathLaw.straightPathBoundaryWork _figure.pathIsStraight
  rw [hPi, hPf, hVf, hVi] at hwork
  norm_num at hwork ⊢
  exact hwork

/-!
The ideal-gas and effective three-degree internal-energy laws give
`ΔU = (3/2)(p_f V_f - p_i V_i) = -15.19875 J`.
-/
lemma internalEnergyChange_in_joules
    (setup : HydrogenStraightPVProcess)
    (_figure : MatchesPrimaryFigure setup)
    (_calibration : UsesThreeDegreeIdealGasCalibration setup)
    (_laws : SatisfiesIdealGasEnergyAndFirstLaws setup) :
    internalEnergyChangeInJoules setup = (-12159 / 800 : ℝ) := by
  have hAtm :
      pressureInPascals DimPressure.standardAtmosphere = (101325 : ℝ) := by
    norm_num [pressureInPascals, DimPressure.standardAtmosphere,
      DimPressure.pascal, CarriesDimension.toDimensionful_apply_apply,
      UnitChoices.dimScale]
  have hViCC :
      volumeInCubicCentimeters (setup.state .i).volume = (100 : ℝ) := by
    calc
      volumeInCubicCentimeters (setup.state .i).volume =
          setup.figure.pointVolumeCubicCentimeters .i :=
        (_figure.coordinatesRepresentPhysicalStates .i).1.symm
      _ = 100 := _figure.initialCoordinate.1
  have hVfCC :
      volumeInCubicCentimeters (setup.state .f).volume = (300 : ℝ) := by
    calc
      volumeInCubicCentimeters (setup.state .f).volume =
          setup.figure.pointVolumeCubicCentimeters .f :=
        (_figure.coordinatesRepresentPhysicalStates .f).1.symm
      _ = 300 := _figure.finalCoordinate.1
  have hVi :
      volumeInCubicMeters (setup.state .i).volume = (1 / 10000 : ℝ) := by
    rw [volumeInCubicCentimeters] at hViCC
    norm_num at hViCC ⊢
    linarith
  have hVf :
      volumeInCubicMeters (setup.state .f).volume = (3 / 10000 : ℝ) := by
    rw [volumeInCubicCentimeters] at hVfCC
    norm_num at hVfCC ⊢
    linarith
  have hPiAtm :
      pressureInAtmospheres (setup.state .i).pressure = (4 : ℝ) := by
    calc
      pressureInAtmospheres (setup.state .i).pressure =
          setup.figure.pointPressureAtmospheres .i :=
        (_figure.coordinatesRepresentPhysicalStates .i).2.symm
      _ = 4 := _figure.initialCoordinate.2
  have hPfAtm :
      pressureInAtmospheres (setup.state .f).pressure = (1 : ℝ) := by
    calc
      pressureInAtmospheres (setup.state .f).pressure =
          setup.figure.pointPressureAtmospheres .f :=
        (_figure.coordinatesRepresentPhysicalStates .f).2.symm
      _ = 1 := _figure.finalCoordinate.2
  have hPi :
      pressureInPascals (setup.state .i).pressure = (405300 : ℝ) := by
    rw [pressureInAtmospheres, hAtm] at hPiAtm
    linarith
  have hPf :
      pressureInPascals (setup.state .f).pressure = (101325 : ℝ) := by
    rw [pressureInAtmospheres, hAtm] at hPfAtm
    linarith
  have hU (label : StateLabel) :
      energyInJoules (setup.state label).internalEnergy =
        (3 / 2 : ℝ) *
          (pressureInPascals (setup.state label).pressure *
            volumeInCubicMeters (setup.state label).volume) := by
    calc
      energyInJoules (setup.state label).internalEnergy =
          setup.gas.amountInMoles *
            molarEnergyPerKelvinInSI
              setup.molarHeatCapacityAtConstantVolume *
              temperatureInKelvins (setup.state label).temperature :=
        _laws.internalEnergyLaw label
      _ = setup.gas.amountInMoles *
            ((3 / 2 : ℝ) *
              molarEnergyPerKelvinInSI setup.molarGasConstant) *
              temperatureInKelvins (setup.state label).temperature := by
        rw [_calibration.threeDegreeHeatCapacity]
      _ = (3 / 2 : ℝ) *
            (setup.gas.amountInMoles *
              molarEnergyPerKelvinInSI setup.molarGasConstant *
                temperatureInKelvins (setup.state label).temperature) := by
        ring
      _ = (3 / 2 : ℝ) *
            (pressureInPascals (setup.state label).pressure *
              volumeInCubicMeters (setup.state label).volume) := by
        rw [_laws.idealGasLaw label]
  have hUi := hU .i
  have hUf := hU .f
  rw [hPi, hVi] at hUi
  rw [hPf, hVf] at hUf
  rw [internalEnergyChangeInJoules, hUf, hUi]
  norm_num

/-- The four heat values displayed in the problem statement. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Heat transferred to the gas, in joules, printed beside each answer label. -/
def displayedHeatInJoules : AnswerChoice → ℝ
  | .A => -36
  | .B => 0
  | .C => 36
  | .D => 72

/-- Dataset metadata, deliberately separate from every theorem premise. -/
def recordedDatasetAnswer : AnswerChoice := .C

/-- The selected displayed heat is strictly closer than every other choice. -/
def IsUniqueClosestDisplayedHeat
    (actualHeatInJoules : ℝ) (choice : AnswerChoice) : Prop :=
  ∀ other : AnswerChoice, other ≠ choice →
    |actualHeatInJoules - displayedHeatInJoules choice| <
      |actualHeatInJoules - displayedHeatInJoules other|

/-!
The first law combines the exact work and internal-energy change to give
`Q = 28371/800 J = 35.46375 J`, so the positive `36 J` answer C is the unique
closest displayed value.

This is the declaration corresponding to blueprint label
`thm:physics:phyx_mini_0413:target`.
-/
theorem problem_phyx_mini_0413
    (setup : HydrogenStraightPVProcess)
    (_problem : MatchesProblemDescription setup)
    (_figure : MatchesPrimaryFigure setup)
    (_physical : HasPhysicalProcessParameters setup)
    (_calibration : UsesThreeDegreeIdealGasCalibration setup)
    (_pathLaw : SatisfiesStraightPVPathAndWorkLaw setup)
    (_laws : SatisfiesIdealGasEnergyAndFirstLaws setup) :
    energyInJoules setup.heatTransferredToGas = (28371 / 800 : ℝ) ∧
      IsUniqueClosestDisplayedHeat
        (energyInJoules setup.heatTransferredToGas) .C := by
  have hwork :=
    workDoneByGas_in_joules setup _figure _pathLaw
  have henergy :=
    internalEnergyChange_in_joules setup _figure _calibration _laws
  have hheat :
      energyInJoules setup.heatTransferredToGas = (28371 / 800 : ℝ) := by
    calc
      energyInJoules setup.heatTransferredToGas =
          internalEnergyChangeInJoules setup +
            energyInJoules setup.workDoneByGas := by
        rw [internalEnergyChangeInJoules]
        exact _laws.firstLaw
      _ = (28371 / 800 : ℝ) := by
        rw [henergy, hwork]
        norm_num
  refine ⟨hheat, ?_⟩
  rw [hheat]
  intro other hne
  cases other with
  | A => norm_num [displayedHeatInJoules]
  | B => norm_num [displayedHeatInJoules]
  | C => exact (hne rfl).elim
  | D => norm_num [displayedHeatInJoules]

end PhyXMiniProblems.ProblemPhyXMini0413
