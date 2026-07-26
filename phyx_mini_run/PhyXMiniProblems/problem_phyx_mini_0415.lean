import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Physlib.Units.WithDim.Energy
import Physlib.Units.WithDim.Pressure

/-!
# Heat transfer on the isochoric leg of a helium cycle

The primary `p`--`V` bitmap shows `120 mg` of helium traversing the directed
cycle `1 → 2 → 3 → 1`.  The upper curved leg `1 → 2` is labelled
“Isotherm”, the vertical leg `2 → 3` is isochoric, and the lower curved leg
`3 → 1` is labelled “Adiabat”.  The plotted readouts are

* state `1`: `p = 3 atm`, `V = 1000 cm³`;
* states `2` and `3`: `V = 3000 cm³`.

The pressures at states `2` and `3` are deliberately not entered as figure
data: they follow from the isothermal and adiabatic laws.  Likewise, the heat
on `2 → 3` is an independent signed energy observable, constrained only by
the first law and the general process laws below.

Pressure, volume, temperature, mass, internal energy, heat, work, and the
molar gas constant retain their physical dimensions through Physlib.  Real
numbers occur only as explicitly unit-labelled readouts, dimensionless
ratios and exponents, or displayed multiple-choice values.  Heat is positive
when transferred into the gas and work is positive when done by the gas, so
the first law is written `Q = ΔU + W`.
-/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0415

open Dimension

/-! ## Dimensionful quantities and named-unit readouts -/

/-- A nonnegative physical volume, carrying dimension `L³`. -/
abbrev VolumeQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * L𝓭 * L𝓭) NNReal)

/-- A physical pressure, using Physlib's pressure dimension. -/
abbrev PressureQuantity : Type := DimPressure

/-- A nonnegative absolute temperature, carrying the temperature dimension. -/
abbrev TemperatureQuantity : Type :=
  Dimensionful (WithDim Θ𝓭 NNReal)

/-- A nonnegative physical mass. -/
abbrev MassQuantity : Type :=
  Dimensionful (WithDim M𝓭 NNReal)

/-- A signed physical energy, used for internal energy, heat, and work. -/
abbrev EnergyQuantity : Type := DimEnergy

/-!
The molar gas constant carries energy-per-temperature dimensions.

Physlib's present `Dimension` has no amount-of-substance coordinate, so the
inverse-mole role is recorded explicitly by the unit-labelled readout and by
the gas sample's `amountInMoles` field.
-/
abbrev MolarGasConstantQuantity : Type :=
  Dimensionful
    (WithDim (M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹ * Θ𝓭⁻¹) NNReal)

/-- SI cubic-metre readout of a physical volume. -/
def volumeInCubicMeters (volume : VolumeQuantity) : ℝ :=
  ((volume UnitChoices.SI).val : ℝ)

/-- Cubic-centimetre readout used on the horizontal axis. -/
def volumeInCubicCentimeters (volume : VolumeQuantity) : ℝ :=
  1000000 * volumeInCubicMeters volume

/-- SI pascal readout of a physical pressure. -/
def pressureInPascals (pressure : PressureQuantity) : ℝ :=
  (pressure UnitChoices.SI).val /
    (DimPressure.pascal UnitChoices.SI).val

/-- Standard-atmosphere readout used on the vertical axis. -/
def pressureInAtmospheres (pressure : PressureQuantity) : ℝ :=
  pressureInPascals pressure / 101325

/-- Kelvin readout of an absolute temperature. -/
def temperatureInKelvins (temperature : TemperatureQuantity) : ℝ :=
  ((temperature UnitChoices.SI).val : ℝ)

/-- SI kilogram readout of the helium sample's mass. -/
def massInKilograms (mass : MassQuantity) : ℝ :=
  ((mass UnitChoices.SI).val : ℝ)

/-- Milligram readout used in the problem statement. -/
def massInMilligrams (mass : MassQuantity) : ℝ :=
  1000000 * massInKilograms mass

/-- SI joule readout of a signed energy. -/
def energyInJoules (energy : EnergyQuantity) : ℝ :=
  (energy UnitChoices.SI).val /
    (DimEnergy.joule UnitChoices.SI).val

/-- Joule-per-mole-kelvin readout of the molar gas constant. -/
def molarGasConstantInJoulesPerMoleKelvin
    (gasConstant : MolarGasConstantQuantity) : ℝ :=
  ((gasConstant UnitChoices.SI).val : ℝ)

/-! ## Gas, state, process, and primary-figure vocabulary -/

/-- Gas species named in the prose. -/
inductive GasSpecies where
  | helium
  | other
  deriving DecidableEq, Repr

/-- Equation-of-state and caloric model used for the sample. -/
inductive GasModel where
  | monatomicIdealGas
  | other
  deriving DecidableEq, Repr

/-!
The gas sample is a physical object, not a scalar alias.  Its mass is
dimensionful; amount and molar mass are explicitly named mole-based readouts
because amount of substance is not yet a Physlib base dimension.
-/
structure GasSample where
  species : GasSpecies
  model : GasModel
  mass : MassQuantity
  amountInMoles : ℝ
  molarMassInGramsPerMole : ℝ

/-- The three state labels printed next to the plotted points. -/
inductive StateLabel where
  | state1
  | state2
  | state3
  deriving DecidableEq, Fintype, Repr

/-- The three directed legs shown by arrows in the primary bitmap. -/
inductive ProcessPath where
  | oneToTwo
  | twoToThree
  | threeToOne
  deriving DecidableEq, Fintype, Repr

/-- Initial state of each directed path. -/
def pathStart : ProcessPath → StateLabel
  | .oneToTwo => .state1
  | .twoToThree => .state2
  | .threeToOne => .state3

/-- Final state of each directed path. -/
def pathFinish : ProcessPath → StateLabel
  | .oneToTwo => .state2
  | .twoToThree => .state3
  | .threeToOne => .state1

/-- Thermodynamic classification of a path. -/
inductive ProcessKind where
  | isothermal
  | isochoric
  | adiabatic
  deriving DecidableEq, Repr

/-- The two axes of the pressure-volume diagram. -/
inductive FigureAxis where
  | horizontal
  | vertical
  deriving DecidableEq, Repr

/-- Physical role assigned to a diagram axis. -/
inductive AxisQuantity where
  | volume
  | pressure
  deriving DecidableEq, Repr

/-- Unit text printed next to a diagram axis. -/
inductive AxisDisplayUnit where
  | cubicCentimeters
  | atmospheres
  deriving DecidableEq, Repr

/-- Mathematical symbol printed next to a diagram axis. -/
inductive AxisSymbol where
  | V
  | p
  deriving DecidableEq, Repr

/-- Geometric appearance of each path in the `p`--`V` plane. -/
inductive FigurePathGeometry where
  | upperCurve
  | verticalSegment
  | lowerCurve
  deriving DecidableEq, Repr

/-- Literal thermodynamic text attached to a path in the bitmap. -/
inductive FigurePathText where
  | none
  | isotherm
  | adiabat
  deriving DecidableEq, Repr

/-- Pressure, volume, temperature, and internal energy at one equilibrium state. -/
structure ThermodynamicState where
  pressure : PressureQuantity
  volume : VolumeQuantity
  temperature : TemperatureQuantity
  internalEnergy : EnergyQuantity

/-!
Structured transcription of image `415.png`.  Schematic point coordinates
are separated from the physical pressure and volume plotted at each state.
-/
structure PressureVolumeFigure where
  axisQuantity : FigureAxis → AxisQuantity
  axisDisplayUnit : FigureAxis → AxisDisplayUnit
  axisSymbol : FigureAxis → AxisSymbol
  axisMaximumTick : FigureAxis → ℝ
  stateLabelShown : StateLabel → Bool
  plottedPressure : StateLabel → PressureQuantity
  plottedVolume : StateLabel → VolumeQuantity
  pathShown : ProcessPath → Bool
  arrowShown : ProcessPath → Bool
  arrowStart : ProcessPath → StateLabel
  arrowFinish : ProcessPath → StateLabel
  pathGeometry : ProcessPath → FigurePathGeometry
  pathText : ProcessPath → FigurePathText
  schematicX : StateLabel → ℝ
  schematicY : StateLabel → ℝ

/-!
The helium sample, its equilibrium states, and independent signed process
energies.  In particular, `heatIntoGas .twoToThree` is not defined from an
answer choice or from the first law; the latter appears only as a hypothesis
interface below.
-/
structure HeliumPVProcessSetup where
  gas : GasSample
  state : StateLabel → ThermodynamicState
  processKind : ProcessPath → ProcessKind
  heatIntoGas : ProcessPath → EnergyQuantity
  workDoneByGas : ProcessPath → EnergyQuantity
  molarGasConstant : MolarGasConstantQuantity
  adiabaticExponent : ℝ
  figure : PressureVolumeFigure

/-! ## Problem statement and primary-image readouts -/

/-!
Direct transcription of the prose and bitmap.  Only state `1` has a labelled
pressure coordinate; state `2` and state `3` pressures remain unknown here.
The equal plotted volumes at states `2` and `3` encode the visible vertical
leg, not its heat transfer.
-/
structure MatchesProblemAndPrimaryFigure
    (setup : HeliumPVProcessSetup) : Prop where
  gasIsHelium : setup.gas.species = .helium
  sampleMassMilligrams : massInMilligrams setup.gas.mass = 120
  horizontalAxisIsVolume : setup.figure.axisQuantity .horizontal = .volume
  verticalAxisIsPressure : setup.figure.axisQuantity .vertical = .pressure
  horizontalUnitIsCubicCentimeters :
    setup.figure.axisDisplayUnit .horizontal = .cubicCentimeters
  verticalUnitIsAtmospheres :
    setup.figure.axisDisplayUnit .vertical = .atmospheres
  horizontalSymbolIsV : setup.figure.axisSymbol .horizontal = .V
  verticalSymbolIsP : setup.figure.axisSymbol .vertical = .p
  horizontalMaximumTickIs3000 : setup.figure.axisMaximumTick .horizontal = 3000
  verticalMaximumTickIs3 : setup.figure.axisMaximumTick .vertical = 3
  everyStateLabelShown : ∀ state, setup.figure.stateLabelShown state = true
  plottedCoordinatesAreStateCoordinates : ∀ state,
    setup.figure.plottedPressure state = (setup.state state).pressure ∧
      setup.figure.plottedVolume state = (setup.state state).volume
  state1PressureAtmospheres :
    pressureInAtmospheres (setup.figure.plottedPressure .state1) = 3
  state1VolumeCubicCentimeters :
    volumeInCubicCentimeters (setup.figure.plottedVolume .state1) = 1000
  state2VolumeCubicCentimeters :
    volumeInCubicCentimeters (setup.figure.plottedVolume .state2) = 3000
  state3VolumeCubicCentimeters :
    volumeInCubicCentimeters (setup.figure.plottedVolume .state3) = 3000
  everyPathAndArrowShown : ∀ path,
    setup.figure.pathShown path = true ∧ setup.figure.arrowShown path = true
  arrowsFollowDirectedCycle : ∀ path,
    setup.figure.arrowStart path = pathStart path ∧
      setup.figure.arrowFinish path = pathFinish path
  oneToTwoGeometry : setup.figure.pathGeometry .oneToTwo = .upperCurve
  twoToThreeGeometry : setup.figure.pathGeometry .twoToThree = .verticalSegment
  threeToOneGeometry : setup.figure.pathGeometry .threeToOne = .lowerCurve
  oneToTwoLabel : setup.figure.pathText .oneToTwo = .isotherm
  twoToThreeHasNoTextLabel : setup.figure.pathText .twoToThree = .none
  threeToOneLabel : setup.figure.pathText .threeToOne = .adiabat
  oneToTwoProcess : setup.processKind .oneToTwo = .isothermal
  twoToThreeProcess : setup.processKind .twoToThree = .isochoric
  threeToOneProcess : setup.processKind .threeToOne = .adiabatic
  state1IsLeftOfState2 :
    setup.figure.schematicX .state1 < setup.figure.schematicX .state2
  state2AndState3AreVerticallyAligned :
    setup.figure.schematicX .state2 = setup.figure.schematicX .state3
  state3IsBelowState2 :
    setup.figure.schematicY .state3 < setup.figure.schematicY .state2

/-!
Standard textbook calibrations for dilute monatomic helium.  The mass-to-mole
relation and constants are independent of the requested heat value.
-/
structure UsesTextbookHeliumCalibrations
    (setup : HeliumPVProcessSetup) : Prop where
  gasUsesMonatomicIdealModel : setup.gas.model = .monatomicIdealGas
  heliumMolarMassGramsPerMole : setup.gas.molarMassInGramsPerMole = 4
  massAmountRelation :
    massInMilligrams setup.gas.mass =
      1000 * setup.gas.amountInMoles * setup.gas.molarMassInGramsPerMole
  molarGasConstantValue :
    molarGasConstantInJoulesPerMoleKelvin setup.molarGasConstant = 831 / 100
  monatomicAdiabaticExponent : setup.adiabaticExponent = 5 / 3

/-- Positivity assumptions selecting physically meaningful branches. -/
structure HasPhysicalThermodynamicParameters
    (setup : HeliumPVProcessSetup) : Prop where
  amountPositive : 0 < setup.gas.amountInMoles
  molarMassPositive : 0 < setup.gas.molarMassInGramsPerMole
  gasConstantPositive :
    0 < molarGasConstantInJoulesPerMoleKelvin setup.molarGasConstant
  pressurePositive : ∀ state,
    0 < pressureInPascals (setup.state state).pressure
  volumePositive : ∀ state,
    0 < volumeInCubicMeters (setup.state state).volume
  temperaturePositive : ∀ state,
    0 < temperatureInKelvins (setup.state state).temperature
  adiabaticExponentGreaterThanOne : 1 < setup.adiabaticExponent

/-! ## Governing thermodynamic laws -/

/-!
Macroscopic laws for a closed monatomic ideal-gas sample:

* `pV = nRT` at every labelled state;
* `U = (3/2)pV` at every labelled state;
* equal endpoint temperatures on any isothermal path;
* the ideal-gas adiabatic pressure-volume ratio on any adiabatic path;
* equal endpoint volumes and zero boundary work on any isochoric path;
* zero heat exchange on any adiabatic path; and
* `Q = ΔU + W` on every directed path.

All clauses are quantified governing laws.  None assigns a numerical heat to
the requested `2 → 3` leg.
-/
structure SatisfiesMonatomicIdealGasProcessLaws
    (setup : HeliumPVProcessSetup) : Prop where
  idealGasLawAt : ∀ state,
    pressureInPascals (setup.state state).pressure *
        volumeInCubicMeters (setup.state state).volume =
      setup.gas.amountInMoles *
        molarGasConstantInJoulesPerMoleKelvin setup.molarGasConstant *
          temperatureInKelvins (setup.state state).temperature
  monatomicInternalEnergyAt : ∀ state,
    energyInJoules (setup.state state).internalEnergy =
      (3 / 2 : ℝ) * pressureInPascals (setup.state state).pressure *
        volumeInCubicMeters (setup.state state).volume
  isothermalEndpointTemperatures : ∀ path,
    setup.processKind path = .isothermal →
      (setup.state (pathStart path)).temperature =
        (setup.state (pathFinish path)).temperature
  adiabaticPressureVolumeRatio : ∀ path,
    setup.processKind path = .adiabatic →
      pressureInPascals (setup.state (pathFinish path)).pressure /
          pressureInPascals (setup.state (pathStart path)).pressure =
        Real.rpow
          (volumeInCubicMeters (setup.state (pathStart path)).volume /
            volumeInCubicMeters (setup.state (pathFinish path)).volume)
          setup.adiabaticExponent
  isochoricEndpointVolumes : ∀ path,
    setup.processKind path = .isochoric →
      (setup.state (pathStart path)).volume =
        (setup.state (pathFinish path)).volume
  isochoricBoundaryWork : ∀ path,
    setup.processKind path = .isochoric →
      energyInJoules (setup.workDoneByGas path) = 0
  adiabaticHeatExchange : ∀ path,
    setup.processKind path = .adiabatic →
      energyInJoules (setup.heatIntoGas path) = 0
  firstLaw : ∀ path,
    energyInJoules (setup.heatIntoGas path) =
      energyInJoules
          (setup.state (pathFinish path)).internalEnergy -
        energyInJoules
          (setup.state (pathStart path)).internalEnergy +
        energyInJoules (setup.workDoneByGas path)

/-! ## Derived state values and requested heat -/

/-!
The isothermal `1 → 2` leg and its endpoint volumes imply `p₂ = 1 atm`.
No pressure at state `2` was assumed in the figure readouts.
-/
lemma state2PressureInAtmospheres_eq_one
    (setup : HeliumPVProcessSetup)
    (_figure : MatchesProblemAndPrimaryFigure setup)
    (_physical : HasPhysicalThermodynamicParameters setup)
    (_laws : SatisfiesMonatomicIdealGasProcessLaws setup) :
    pressureInAtmospheres (setup.state .state2).pressure = 1 := by
  have hp₁atm := _figure.state1PressureAtmospheres
  rw [(_figure.plottedCoordinatesAreStateCoordinates .state1).1] at hp₁atm
  have hv₁cm := _figure.state1VolumeCubicCentimeters
  rw [(_figure.plottedCoordinatesAreStateCoordinates .state1).2] at hv₁cm
  have hv₂cm := _figure.state2VolumeCubicCentimeters
  rw [(_figure.plottedCoordinatesAreStateCoordinates .state2).2] at hv₂cm
  have hp₁ :
      pressureInPascals (setup.state .state1).pressure = 303975 := by
    dsimp [pressureInAtmospheres] at hp₁atm
    linarith
  have hv₁ :
      volumeInCubicMeters (setup.state .state1).volume = 1 / 1000 := by
    dsimp [volumeInCubicCentimeters] at hv₁cm
    norm_num at hv₁cm ⊢
    linarith
  have hv₂ :
      volumeInCubicMeters (setup.state .state2).volume = 3 / 1000 := by
    dsimp [volumeInCubicCentimeters] at hv₂cm
    norm_num at hv₂cm ⊢
    linarith
  have htemperature :
      temperatureInKelvins (setup.state .state1).temperature =
        temperatureInKelvins (setup.state .state2).temperature := by
    have h := _laws.isothermalEndpointTemperatures .oneToTwo
      _figure.oneToTwoProcess
    simpa [pathStart, pathFinish] using congrArg temperatureInKelvins h
  have hpv :
      pressureInPascals (setup.state .state1).pressure *
          volumeInCubicMeters (setup.state .state1).volume =
        pressureInPascals (setup.state .state2).pressure *
          volumeInCubicMeters (setup.state .state2).volume := by
    calc
      _ = setup.gas.amountInMoles *
            molarGasConstantInJoulesPerMoleKelvin setup.molarGasConstant *
              temperatureInKelvins (setup.state .state1).temperature :=
        _laws.idealGasLawAt .state1
      _ = setup.gas.amountInMoles *
            molarGasConstantInJoulesPerMoleKelvin setup.molarGasConstant *
              temperatureInKelvins (setup.state .state2).temperature := by
        rw [htemperature]
      _ = _ := (_laws.idealGasLawAt .state2).symm
  have hp₂ :
      pressureInPascals (setup.state .state2).pressure = 101325 := by
    rw [hp₁, hv₁, hv₂] at hpv
    norm_num at hpv ⊢
    linarith
  dsimp [pressureInAtmospheres]
  rw [hp₂]
  norm_num

/-!
The `3 → 1` adiabatic reference and the volume ratio `3 : 1` give
`p₃ = (1/3)^(2/3) atm`.  This is a derived state value, not a bitmap readout.
-/
lemma state3PressureInAtmospheres_eq_rpow
    (setup : HeliumPVProcessSetup)
    (_figure : MatchesProblemAndPrimaryFigure setup)
    (_calibrations : UsesTextbookHeliumCalibrations setup)
    (_physical : HasPhysicalThermodynamicParameters setup)
    (_laws : SatisfiesMonatomicIdealGasProcessLaws setup) :
    pressureInAtmospheres (setup.state .state3).pressure =
      Real.rpow (1 / 3 : ℝ) (2 / 3 : ℝ) := by
  have hp₁atm := _figure.state1PressureAtmospheres
  rw [(_figure.plottedCoordinatesAreStateCoordinates .state1).1] at hp₁atm
  have hv₁cm := _figure.state1VolumeCubicCentimeters
  rw [(_figure.plottedCoordinatesAreStateCoordinates .state1).2] at hv₁cm
  have hv₃cm := _figure.state3VolumeCubicCentimeters
  rw [(_figure.plottedCoordinatesAreStateCoordinates .state3).2] at hv₃cm
  have hp₁ :
      pressureInPascals (setup.state .state1).pressure = 303975 := by
    dsimp [pressureInAtmospheres] at hp₁atm
    linarith
  have hv₁ :
      volumeInCubicMeters (setup.state .state1).volume = 1 / 1000 := by
    dsimp [volumeInCubicCentimeters] at hv₁cm
    norm_num at hv₁cm ⊢
    linarith
  have hv₃ :
      volumeInCubicMeters (setup.state .state3).volume = 3 / 1000 := by
    dsimp [volumeInCubicCentimeters] at hv₃cm
    norm_num at hv₃cm ⊢
    linarith
  have hadiabat := _laws.adiabaticPressureVolumeRatio .threeToOne
    _figure.threeToOneProcess
  simp only [pathStart, pathFinish] at hadiabat
  rw [hp₁, hv₃, hv₁, _calibrations.monatomicAdiabaticExponent] at hadiabat
  norm_num at hadiabat
  have hp₃pos :
      0 < pressureInPascals (setup.state .state3).pressure :=
    _physical.pressurePositive .state3
  have hadiabat' :
      (303975 : ℝ) =
        Real.rpow 3 (5 / 3 : ℝ) *
          pressureInPascals (setup.state .state3).pressure :=
    (div_eq_iff hp₃pos.ne').mp hadiabat
  have hpow :
      Real.rpow 3 (5 / 3 : ℝ) *
          Real.rpow (1 / 3 : ℝ) (2 / 3 : ℝ) = 3 := by
    simp only [Real.rpow_eq_pow]
    rw [show (1 / 3 : ℝ) = (3 : ℝ)⁻¹ by norm_num,
      Real.inv_rpow (by norm_num : (0 : ℝ) ≤ 3)]
    rw [← div_eq_mul_inv, ← Real.rpow_sub (by norm_num : (0 : ℝ) < 3)]
    norm_num
  have hpowpos : 0 < Real.rpow 3 (5 / 3 : ℝ) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hp₃ :
      pressureInPascals (setup.state .state3).pressure =
        101325 * Real.rpow (1 / 3 : ℝ) (2 / 3 : ℝ) := by
    apply mul_left_cancel₀ hpowpos.ne'
    calc
      Real.rpow 3 (5 / 3 : ℝ) *
          pressureInPascals (setup.state .state3).pressure =
          303975 := hadiabat'.symm
      _ = Real.rpow 3 (5 / 3 : ℝ) *
          (101325 * Real.rpow (1 / 3 : ℝ) (2 / 3 : ℝ)) := by
        nlinarith [hpow]
  dsimp [pressureInAtmospheres]
  rw [hp₃]
  field_simp
  exact Real.rpow_eq_pow _ _

/-!
Since `2 → 3` is isochoric, its work vanishes.  Combining the first law with
`U = (3/2)pV` gives the exact model heat

`(3/2)(303975/1000)((1/3)^(2/3) - 1) J`.

This is approximately `-236.8 J`; among the supplied choices it is uniquely
closest to `-239 J`.
-/
lemma heatTwoToThreeInJoules_exact
    (setup : HeliumPVProcessSetup)
    (_figure : MatchesProblemAndPrimaryFigure setup)
    (_calibrations : UsesTextbookHeliumCalibrations setup)
    (_physical : HasPhysicalThermodynamicParameters setup)
    (_laws : SatisfiesMonatomicIdealGasProcessLaws setup) :
    energyInJoules (setup.heatIntoGas .twoToThree) =
      (3 / 2 : ℝ) * (303975 / 1000 : ℝ) *
        (Real.rpow (1 / 3 : ℝ) (2 / 3 : ℝ) - 1) := by
  have hp₂atm := state2PressureInAtmospheres_eq_one
    setup _figure _physical _laws
  have hp₃atm := state3PressureInAtmospheres_eq_rpow
    setup _figure _calibrations _physical _laws
  have hp₂ :
      pressureInPascals (setup.state .state2).pressure = 101325 := by
    dsimp [pressureInAtmospheres] at hp₂atm
    linarith
  have hp₃ :
      pressureInPascals (setup.state .state3).pressure =
        101325 * Real.rpow (1 / 3 : ℝ) (2 / 3 : ℝ) := by
    dsimp [pressureInAtmospheres] at hp₃atm
    norm_num at hp₃atm ⊢
    linarith
  have hv₂cm := _figure.state2VolumeCubicCentimeters
  rw [(_figure.plottedCoordinatesAreStateCoordinates .state2).2] at hv₂cm
  have hv₃cm := _figure.state3VolumeCubicCentimeters
  rw [(_figure.plottedCoordinatesAreStateCoordinates .state3).2] at hv₃cm
  have hv₂ :
      volumeInCubicMeters (setup.state .state2).volume = 3 / 1000 := by
    dsimp [volumeInCubicCentimeters] at hv₂cm
    norm_num at hv₂cm ⊢
    linarith
  have hv₃ :
      volumeInCubicMeters (setup.state .state3).volume = 3 / 1000 := by
    dsimp [volumeInCubicCentimeters] at hv₃cm
    norm_num at hv₃cm ⊢
    linarith
  have hu₂ := _laws.monatomicInternalEnergyAt .state2
  have hu₃ := _laws.monatomicInternalEnergyAt .state3
  rw [hp₂, hv₂] at hu₂
  rw [hp₃, hv₃] at hu₃
  have hwork := _laws.isochoricBoundaryWork .twoToThree
    _figure.twoToThreeProcess
  have hfirst := _laws.firstLaw .twoToThree
  simp only [pathStart, pathFinish] at hfirst
  rw [hu₂, hu₃, hwork] at hfirst
  norm_num at hfirst ⊢
  nlinarith

/-- Labels of the four answer choices in the source problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Signed heat in joules printed beside each answer label. -/
def AnswerChoice.heatInJoules : AnswerChoice → ℝ
  | .A => 0
  | .B => -334
  | .C => -239
  | .D => 239

/-- Answer label recorded by the supplied dataset metadata. -/
def recordedAnswerChoice : AnswerChoice := .C

/-!
A choice is the unique closest displayed whole-joule value to a model heat.
This expresses multiple-choice selection without asserting that a rounded
figure-derived model value is exactly equal to the printed integer.
-/
def IsUniqueClosestHeatChoice
    (heatJoules : ℝ) (choice : AnswerChoice) : Prop :=
  ∀ other, other ≠ choice →
    |heatJoules - choice.heatInJoules| <
      |heatJoules - other.heatInJoules|

/-!
The requested signed heat has the exact ideal-helium model value above, and
the uniquely closest listed value is answer C, `-239 J`.  The negative sign
means heat is transferred from the gas during `2 → 3`.

This declaration formalizes blueprint label
`thm:physics:phyx_mini_0415:target`.
-/
theorem problem_phyx_mini_0415
    (setup : HeliumPVProcessSetup)
    (_figure : MatchesProblemAndPrimaryFigure setup)
    (_calibrations : UsesTextbookHeliumCalibrations setup)
    (_physical : HasPhysicalThermodynamicParameters setup)
    (_laws : SatisfiesMonatomicIdealGasProcessLaws setup) :
    energyInJoules (setup.heatIntoGas .twoToThree) =
        (3 / 2 : ℝ) * (303975 / 1000 : ℝ) *
          (Real.rpow (1 / 3 : ℝ) (2 / 3 : ℝ) - 1) ∧
      IsUniqueClosestHeatChoice
        (energyInJoules (setup.heatIntoGas .twoToThree))
        recordedAnswerChoice ∧
      recordedAnswerChoice.heatInJoules = -239 := by
  have hheat := heatTwoToThreeInJoules_exact
    setup _figure _calibrations _physical _laws
  refine ⟨hheat, ?_, by rfl⟩
  rw [hheat]
  let r : ℝ := Real.rpow (1 / 3 : ℝ) (2 / 3 : ℝ)
  have hrcube : r ^ 3 = 1 / 9 := by
    dsimp [r]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 1 / 3)]
    norm_num
  have hr_lower : (2 / 5 : ℝ) < r := by
    rw [← (show Odd 3 by decide).pow_lt_pow]
    rw [hrcube]
    norm_num
  have hr_upper : r < (2 / 3 : ℝ) := by
    rw [← (show Odd 3 by decide).pow_lt_pow]
    rw [hrcube]
    norm_num
  dsimp [IsUniqueClosestHeatChoice, recordedAnswerChoice]
  intro other hother
  cases other with
  | A =>
      dsimp [AnswerChoice.heatInJoules]
      rw [← sq_lt_sq]
      dsimp [r] at hr_lower hr_upper ⊢
      nlinarith
  | B =>
      dsimp [AnswerChoice.heatInJoules]
      rw [← sq_lt_sq]
      dsimp [r] at hr_lower hr_upper ⊢
      nlinarith
  | C =>
      exact (hother rfl).elim
  | D =>
      dsimp [AnswerChoice.heatInJoules]
      rw [← sq_lt_sq]
      dsimp [r] at hr_lower hr_upper ⊢
      nlinarith

end PhyXMiniProblems.ProblemPhyXMini0415
