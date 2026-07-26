import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Physlib.Thermodynamics.Temperature.Basic
import Physlib.Units.WithDim.Energy
import Physlib.Units.WithDim.Pressure

/- USER: The assigned source file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0414

open Dimension

/-!
# Heat transferred on the three legs of a helium cycle

A `120 mg` sample of helium follows the directed cycle `1 → 2 → 3 → 1` in
the supplied pressure-volume diagram.  State 1 is at `1000 cm³`, pressure
`p₁`, and `133 °C`; state 2 has the same volume and pressure `5p₁`; the curved
leg from 2 to 3 is an isotherm; and state 3 returns to pressure `p₁` before the
horizontal compression to state 1.

Heat is positive when transferred into the gas, and work is positive when
done by the gas.  Mass, pressure, volume, heat, work, and internal-energy
change retain their physical dimensions through Physlib.  Real numbers are
used only for explicitly named unit readouts, amount-of-substance and molar
readouts (Physlib's current `Dimension` has no mole component), dimensionless
ratios, and the displayed answer values.
-/

/-! ## Dimensionful quantities and calibrated readouts -/

/-- A physical mass, carrying the mass dimension. -/
abbrev MassQuantity : Type :=
  Dimensionful (WithDim M𝓭 ℝ)

/-- A signed physical volume, carrying the length-cubed dimension. -/
abbrev VolumeQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * L𝓭 * L𝓭) ℝ)

/-- Read a physical mass in SI kilograms. -/
def massInKilograms (mass : MassQuantity) : ℝ :=
  (mass UnitChoices.SI).val

/-- Read a physical mass in grams. -/
def massInGrams (mass : MassQuantity) : ℝ :=
  1000 * massInKilograms mass

/-- Read a physical mass in milligrams. -/
def massInMilligrams (mass : MassQuantity) : ℝ :=
  1000000 * massInKilograms mass

/-- Read a physical volume in SI cubic metres. -/
def volumeInCubicMeters (volume : VolumeQuantity) : ℝ :=
  (volume UnitChoices.SI).val

/-- Read a physical pressure in SI pascals. -/
def pressureInPascals (pressure : DimPressure) : ℝ :=
  (pressure UnitChoices.SI).val

/-- Read a signed physical energy in joules. -/
def energyInJoules (energy : DimEnergy) : ℝ :=
  (energy UnitChoices.SI).val / (DimEnergy.joule UnitChoices.SI).val

/-- Read a signed physical energy in kilojoules. -/
def energyInKilojoules (energy : DimEnergy) : ℝ :=
  energyInJoules energy / 1000

/-- Read Physlib's absolute-temperature value in kelvins. -/
def temperatureInKelvin (temperature : Temperature) : ℝ :=
  temperature.toReal

/-- Read an absolute temperature in degrees Celsius. -/
def temperatureInDegreesCelsius (temperature : Temperature) : ℝ :=
  temperatureInKelvin temperature - (5463 / 20 : ℝ)

/-! ## Gas, state, process, and primary-figure vocabulary -/

/-- Chemical species named in the problem statement. -/
inductive GasSpecies where
  | helium
  deriving DecidableEq, Repr

/-- Textbook material model used for the helium sample. -/
inductive GasModel where
  | idealMonatomic
  deriving DecidableEq, Repr

/-- Labels printed at the three vertices of the pressure-volume diagram. -/
inductive StateLabel where
  | state1
  | state2
  | state3
  deriving DecidableEq, Repr

/-- Directed segments indicated by arrows in the primary figure. -/
inductive CycleSegment where
  | oneToTwo
  | twoToThree
  | threeToOne
  deriving DecidableEq, Repr

/-- Thermodynamic constraint on a process segment. -/
inductive ProcessKind where
  | isochoric
  | isothermal
  | isobaric
  deriving DecidableEq, Repr

/-- Geometric appearance of a segment in the pressure-volume diagram. -/
inductive PathGeometry where
  | verticalSegment
  | curvedSegment
  | horizontalSegment
  deriving DecidableEq, Repr

/-- Physical quantity shown on a diagram axis. -/
inductive AxisQuantity where
  | volume
  | pressure
  deriving DecidableEq, Repr

/-- A dimensionful equilibrium state of the helium sample. -/
structure ThermodynamicState where
  pressure : DimPressure
  volume : VolumeQuantity
  temperature : Temperature

/-!
The helium sample, three equilibrium states, directed paths, and signed energy
transfers.  `internalEnergyChange segment` means final minus initial internal
energy on that segment.

The fields `figurePressureP1` and `figureVolumeV3` represent the symbolic
labels `p₁` and `V₃` printed in the primary image; they do not prescribe the
requested heat transfer.
-/
structure HeliumThermodynamicCycle where
  species : GasSpecies
  gasModel : GasModel
  heliumMass : MassQuantity
  amountOfGasMoles : ℝ
  molarMassGramsPerMole : ℝ
  molarGasConstantJoulesPerMoleKelvin : ℝ
  stateAt : StateLabel → ThermodynamicState
  heatIntoGas : CycleSegment → DimEnergy
  workByGas : CycleSegment → DimEnergy
  internalEnergyChange : CycleSegment → DimEnergy
  pathStart : CycleSegment → StateLabel
  pathFinish : CycleSegment → StateLabel
  processKind : CycleSegment → ProcessKind
  pathGeometry : CycleSegment → PathGeometry
  horizontalAxisQuantity : AxisQuantity
  verticalAxisQuantity : AxisQuantity
  stateLabelVisible : StateLabel → Bool
  figurePressureP1 : DimPressure
  figureVolumeV3 : VolumeQuantity

/-! ## Stated data, figure readouts, reference data, and governing laws -/

/-- Data supplied by the prose.  No heat-transfer value occurs here. -/
structure MatchesProblemStatement
    (setup : HeliumThermodynamicCycle) : Prop where
  gas_is_helium : setup.species = .helium
  helium_mass_is_120_milligrams :
    massInMilligrams setup.heliumMass = 120

/-!
Literal transcription of the primary raster.  In particular, the unknown
horizontal coordinate at state 3 remains the independent figure label `V₃`;
its value is to follow from the isotherm and ideal-gas law.
-/
structure MatchesPrimaryPressureVolumeDiagram
    (setup : HeliumThermodynamicCycle) : Prop where
  horizontal_axis_is_volume :
    setup.horizontalAxisQuantity = .volume
  vertical_axis_is_pressure :
    setup.verticalAxisQuantity = .pressure
  state_one_label_visible : setup.stateLabelVisible .state1 = true
  state_two_label_visible : setup.stateLabelVisible .state2 = true
  state_three_label_visible : setup.stateLabelVisible .state3 = true
  state_one_volume_is_1000_cubic_centimeters :
    volumeInCubicMeters (setup.stateAt .state1).volume = (1 / 1000 : ℝ)
  state_two_has_state_one_volume :
    (setup.stateAt .state2).volume = (setup.stateAt .state1).volume
  state_three_volume_has_figure_label_V3 :
    (setup.stateAt .state3).volume = setup.figureVolumeV3
  state_one_pressure_is_p1 :
    (setup.stateAt .state1).pressure = setup.figurePressureP1
  state_two_pressure_is_five_p1 :
    pressureInPascals (setup.stateAt .state2).pressure =
      5 * pressureInPascals setup.figurePressureP1
  state_three_pressure_is_p1 :
    (setup.stateAt .state3).pressure = setup.figurePressureP1
  state_one_temperature_is_133_degrees_Celsius :
    temperatureInDegreesCelsius (setup.stateAt .state1).temperature = 133
  one_to_two_starts_at_one : setup.pathStart .oneToTwo = .state1
  one_to_two_finishes_at_two : setup.pathFinish .oneToTwo = .state2
  two_to_three_starts_at_two : setup.pathStart .twoToThree = .state2
  two_to_three_finishes_at_three : setup.pathFinish .twoToThree = .state3
  three_to_one_starts_at_three : setup.pathStart .threeToOne = .state3
  three_to_one_finishes_at_one : setup.pathFinish .threeToOne = .state1
  one_to_two_is_vertical :
    setup.pathGeometry .oneToTwo = .verticalSegment
  two_to_three_is_curved :
    setup.pathGeometry .twoToThree = .curvedSegment
  three_to_one_is_horizontal :
    setup.pathGeometry .threeToOne = .horizontalSegment
  one_to_two_is_isochoric : setup.processKind .oneToTwo = .isochoric
  two_to_three_is_isothermal : setup.processKind .twoToThree = .isothermal
  three_to_one_is_isobaric : setup.processKind .threeToOne = .isobaric

/-!
Textbook calibration data used to obtain a numerical result: helium is
treated as a monatomic ideal gas of molar mass `4.00 g/mol`, the molar gas
constant is `8.314 J/(mol K)`, and the amount in moles is mass divided by
molar mass.  These are reference/model data, not heat-transfer answers.
-/
structure UsesTextbookHeliumReferenceData
    (setup : HeliumThermodynamicCycle) : Prop where
  helium_is_ideal_monatomic : setup.gasModel = .idealMonatomic
  helium_molar_mass_grams_per_mole : setup.molarMassGramsPerMole = 4
  molar_gas_constant_in_SI :
    setup.molarGasConstantJoulesPerMoleKelvin = (4157 / 500 : ℝ)
  gas_amount_from_mass_and_molar_mass :
    setup.amountOfGasMoles =
      massInGrams setup.heliumMass / setup.molarMassGramsPerMole

/-- Positivity conditions selecting the physically meaningful branch. -/
structure HasPhysicalThermodynamicParameters
    (setup : HeliumThermodynamicCycle) : Prop where
  helium_mass_positive : 0 < massInKilograms setup.heliumMass
  amount_positive : 0 < setup.amountOfGasMoles
  molar_mass_positive : 0 < setup.molarMassGramsPerMole
  gas_constant_positive :
    0 < setup.molarGasConstantJoulesPerMoleKelvin
  pressure_positive : ∀ state,
    0 < pressureInPascals (setup.stateAt state).pressure
  volume_positive : ∀ state,
    0 < volumeInCubicMeters (setup.stateAt state).volume
  temperature_positive : ∀ state,
    0 < temperatureInKelvin (setup.stateAt state).temperature
  figure_p1_positive : 0 < pressureInPascals setup.figurePressureP1
  figure_V3_positive : 0 < volumeInCubicMeters setup.figureVolumeV3

/-!
Macroscopic laws for an ideal monatomic gas:

* `pV = nRT` at every labeled equilibrium state;
* `ΔU = (3/2)nRΔT` on each segment;
* `Q = ΔU + W_by` with heat into and work by the gas positive;
* zero boundary work for an isochoric process;
* constant temperature and logarithmic boundary work for an isotherm;
* constant pressure and `p ΔV` boundary work for an isobaric process.

All formulas are stated in compatible SI readouts.  No field fixes any of the
three requested heat transfers or an answer choice.
-/
structure ObeysIdealMonatomicGasLaws
    (setup : HeliumThermodynamicCycle) : Prop where
  ideal_gas_law : ∀ state,
    pressureInPascals (setup.stateAt state).pressure *
        volumeInCubicMeters (setup.stateAt state).volume =
      setup.amountOfGasMoles *
        setup.molarGasConstantJoulesPerMoleKelvin *
        temperatureInKelvin (setup.stateAt state).temperature
  monatomic_internal_energy_law : ∀ segment,
    energyInJoules (setup.internalEnergyChange segment) =
      (3 / 2 : ℝ) * setup.amountOfGasMoles *
        setup.molarGasConstantJoulesPerMoleKelvin *
        (temperatureInKelvin
              (setup.stateAt (setup.pathFinish segment)).temperature -
          temperatureInKelvin
              (setup.stateAt (setup.pathStart segment)).temperature)
  first_law : ∀ segment,
    energyInJoules (setup.heatIntoGas segment) =
      energyInJoules (setup.internalEnergyChange segment) +
        energyInJoules (setup.workByGas segment)
  isochoric_boundary_work_law : ∀ segment,
    setup.processKind segment = .isochoric →
      volumeInCubicMeters
          (setup.stateAt (setup.pathFinish segment)).volume =
        volumeInCubicMeters
          (setup.stateAt (setup.pathStart segment)).volume ∧
      energyInJoules (setup.workByGas segment) = 0
  isothermal_temperature_and_work_law : ∀ segment,
    setup.processKind segment = .isothermal →
      temperatureInKelvin
          (setup.stateAt (setup.pathFinish segment)).temperature =
        temperatureInKelvin
          (setup.stateAt (setup.pathStart segment)).temperature ∧
      energyInJoules (setup.workByGas segment) =
        setup.amountOfGasMoles *
          setup.molarGasConstantJoulesPerMoleKelvin *
          temperatureInKelvin
            (setup.stateAt (setup.pathStart segment)).temperature *
          Real.log
            (volumeInCubicMeters
                (setup.stateAt (setup.pathFinish segment)).volume /
              volumeInCubicMeters
                (setup.stateAt (setup.pathStart segment)).volume)
  isobaric_pressure_and_work_law : ∀ segment,
    setup.processKind segment = .isobaric →
      pressureInPascals
          (setup.stateAt (setup.pathFinish segment)).pressure =
        pressureInPascals
          (setup.stateAt (setup.pathStart segment)).pressure ∧
      energyInJoules (setup.workByGas segment) =
        pressureInPascals
            (setup.stateAt (setup.pathStart segment)).pressure *
          (volumeInCubicMeters
                (setup.stateAt (setup.pathFinish segment)).volume -
            volumeInCubicMeters
                (setup.stateAt (setup.pathStart segment)).volume)

/-! ## Displayed choices and requested heat transfers -/

/-- Labels printed beside the four answer choices. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Heat readout in kilojoules printed beside each answer label. -/
def displayedHeatInKilojoules : AnswerChoice → ℝ
  | .A => 101 / 100
  | .B => 0
  | .C => -(101 / 100)
  | .D => -(61 / 100)

/-- Answer label recorded in the supplied dataset metadata. -/
def recordedAnswerChoice : AnswerChoice := .C

/-- A kilojoule readout rounds to `displayed` to the nearest hundredth. -/
def RoundsToNearestHundredthKilojoule
    (actual displayed : ℝ) : Prop :=
  |actual - displayed| < (1 / 200 : ℝ)

/-- A displayed choice is at least as close to the actual heat as every alternative. -/
def IsNearestDisplayedChoice
    (actual : ℝ) (choice : AnswerChoice) : Prop :=
  ∀ alternative : AnswerChoice,
    |actual - displayedHeatInKilojoules choice| ≤
      |actual - displayedHeatInKilojoules alternative|

/-!
The exact heat entering the gas on each directed segment, in joules.  Thus
the first isochoric leg receives about `0.608 kJ`, the isothermal expansion
receives about `0.815 kJ`, and the final isobaric compression rejects about
`1.013 kJ`.
-/
lemma heatTransferReadoutsOnAllThreeSegments
    (setup : HeliumThermodynamicCycle)
    (_problem : MatchesProblemStatement setup)
    (_figure : MatchesPrimaryPressureVolumeDiagram setup)
    (_referenceData : UsesTextbookHeliumReferenceData setup)
    (_physical : HasPhysicalThermodynamicParameters setup)
    (_laws : ObeysIdealMonatomicGasLaws setup) :
    energyInJoules (setup.heatIntoGas .oneToTwo) =
        (303905799 / 500000 : ℝ) ∧
      energyInJoules (setup.heatIntoGas .twoToThree) =
        (101301933 / 200000 : ℝ) * Real.log 5 ∧
      energyInJoules (setup.heatIntoGas .threeToOne) =
        -(101301933 / 100000 : ℝ) := by
  have hMassKilograms :
      massInKilograms setup.heliumMass = (3 / 25000 : ℝ) := by
    have hMass := _problem.helium_mass_is_120_milligrams
    unfold massInMilligrams at hMass
    nlinarith
  have hMassGrams :
      massInGrams setup.heliumMass = (3 / 25 : ℝ) := by
    unfold massInGrams
    rw [hMassKilograms]
    norm_num
  have hAmount :
      setup.amountOfGasMoles = (3 / 100 : ℝ) := by
    have hAmountLaw := _referenceData.gas_amount_from_mass_and_molar_mass
    rw [hMassGrams, _referenceData.helium_molar_mass_grams_per_mole] at hAmountLaw
    norm_num at hAmountLaw ⊢
    exact hAmountLaw
  have hTemperatureOne :
      temperatureInKelvin (setup.stateAt .state1).temperature =
        (8123 / 20 : ℝ) := by
    have hTemperature :=
      _figure.state_one_temperature_is_133_degrees_Celsius
    unfold temperatureInDegreesCelsius at hTemperature
    nlinarith
  have hVolumeOne :
      volumeInCubicMeters (setup.stateAt .state1).volume =
        (1 / 1000 : ℝ) :=
    _figure.state_one_volume_is_1000_cubic_centimeters
  have hVolumeTwo :
      volumeInCubicMeters (setup.stateAt .state2).volume =
        (1 / 1000 : ℝ) := by
    calc
      volumeInCubicMeters (setup.stateAt .state2).volume =
          volumeInCubicMeters (setup.stateAt .state1).volume :=
        congrArg volumeInCubicMeters _figure.state_two_has_state_one_volume
      _ = (1 / 1000 : ℝ) := hVolumeOne
  have hPressureOne :
      pressureInPascals (setup.stateAt .state1).pressure =
        (101301933 / 1000 : ℝ) := by
    have hIdeal := _laws.ideal_gas_law .state1
    rw [hVolumeOne, hAmount,
      _referenceData.molar_gas_constant_in_SI, hTemperatureOne] at hIdeal
    nlinarith
  have hFigurePressure :
      pressureInPascals setup.figurePressureP1 =
        (101301933 / 1000 : ℝ) := by
    rw [← _figure.state_one_pressure_is_p1]
    exact hPressureOne
  have hPressureTwo :
      pressureInPascals (setup.stateAt .state2).pressure =
        (101301933 / 200 : ℝ) := by
    have hPressure := _figure.state_two_pressure_is_five_p1
    rw [hFigurePressure] at hPressure
    nlinarith
  have hPressureThree :
      pressureInPascals (setup.stateAt .state3).pressure =
        (101301933 / 1000 : ℝ) := by
    rw [_figure.state_three_pressure_is_p1]
    exact hFigurePressure
  have hTemperatureTwo :
      temperatureInKelvin (setup.stateAt .state2).temperature =
        (8123 / 4 : ℝ) := by
    have hIdeal := _laws.ideal_gas_law .state2
    rw [hPressureTwo, hVolumeTwo, hAmount,
      _referenceData.molar_gas_constant_in_SI] at hIdeal
    nlinarith
  have hTemperatureThree :
      temperatureInKelvin (setup.stateAt .state3).temperature =
        (8123 / 4 : ℝ) := by
    have hIsothermal :=
      (_laws.isothermal_temperature_and_work_law .twoToThree
        _figure.two_to_three_is_isothermal).1
    rw [_figure.two_to_three_finishes_at_three,
      _figure.two_to_three_starts_at_two, hTemperatureTwo] at hIsothermal
    exact hIsothermal
  have hVolumeThree :
      volumeInCubicMeters (setup.stateAt .state3).volume =
        (1 / 200 : ℝ) := by
    have hIdeal := _laws.ideal_gas_law .state3
    rw [hPressureThree, hAmount,
      _referenceData.molar_gas_constant_in_SI, hTemperatureThree] at hIdeal
    nlinarith
  have hInternalEnergyOneToTwo :
      energyInJoules (setup.internalEnergyChange .oneToTwo) =
        (303905799 / 500000 : ℝ) := by
    have hEnergy := _laws.monatomic_internal_energy_law .oneToTwo
    rw [_figure.one_to_two_finishes_at_two,
      _figure.one_to_two_starts_at_one, hAmount,
      _referenceData.molar_gas_constant_in_SI, hTemperatureTwo,
      hTemperatureOne] at hEnergy
    norm_num at hEnergy ⊢
    exact hEnergy
  have hInternalEnergyTwoToThree :
      energyInJoules (setup.internalEnergyChange .twoToThree) = 0 := by
    have hEnergy := _laws.monatomic_internal_energy_law .twoToThree
    rw [_figure.two_to_three_finishes_at_three,
      _figure.two_to_three_starts_at_two, hAmount,
      _referenceData.molar_gas_constant_in_SI, hTemperatureThree,
      hTemperatureTwo] at hEnergy
    norm_num at hEnergy ⊢
    exact hEnergy
  have hInternalEnergyThreeToOne :
      energyInJoules (setup.internalEnergyChange .threeToOne) =
        -(303905799 / 500000 : ℝ) := by
    have hEnergy := _laws.monatomic_internal_energy_law .threeToOne
    rw [_figure.three_to_one_finishes_at_one,
      _figure.three_to_one_starts_at_three, hAmount,
      _referenceData.molar_gas_constant_in_SI, hTemperatureOne,
      hTemperatureThree] at hEnergy
    norm_num at hEnergy ⊢
    exact hEnergy
  have hWorkOneToTwo :
      energyInJoules (setup.workByGas .oneToTwo) = 0 :=
    (_laws.isochoric_boundary_work_law .oneToTwo
      _figure.one_to_two_is_isochoric).2
  have hWorkTwoToThree :
      energyInJoules (setup.workByGas .twoToThree) =
        (101301933 / 200000 : ℝ) * Real.log 5 := by
    have hWork :=
      (_laws.isothermal_temperature_and_work_law .twoToThree
        _figure.two_to_three_is_isothermal).2
    rw [_figure.two_to_three_starts_at_two,
      _figure.two_to_three_finishes_at_three, hAmount,
      _referenceData.molar_gas_constant_in_SI, hTemperatureTwo,
      hVolumeThree, hVolumeTwo] at hWork
    norm_num at hWork ⊢
    exact hWork
  have hWorkThreeToOne :
      energyInJoules (setup.workByGas .threeToOne) =
        -(101301933 / 250000 : ℝ) := by
    have hWork :=
      (_laws.isobaric_pressure_and_work_law .threeToOne
        _figure.three_to_one_is_isobaric).2
    rw [_figure.three_to_one_starts_at_three,
      _figure.three_to_one_finishes_at_one, hPressureThree,
      hVolumeOne, hVolumeThree] at hWork
    norm_num at hWork ⊢
    exact hWork
  have hHeatOneToTwo :
      energyInJoules (setup.heatIntoGas .oneToTwo) =
        (303905799 / 500000 : ℝ) := by
    have hFirstLaw := _laws.first_law .oneToTwo
    rw [hInternalEnergyOneToTwo, hWorkOneToTwo] at hFirstLaw
    simpa using hFirstLaw
  have hHeatTwoToThree :
      energyInJoules (setup.heatIntoGas .twoToThree) =
        (101301933 / 200000 : ℝ) * Real.log 5 := by
    have hFirstLaw := _laws.first_law .twoToThree
    rw [hInternalEnergyTwoToThree, hWorkTwoToThree] at hFirstLaw
    simpa using hFirstLaw
  have hHeatThreeToOne :
      energyInJoules (setup.heatIntoGas .threeToOne) =
        -(101301933 / 100000 : ℝ) := by
    have hFirstLaw := _laws.first_law .threeToOne
    rw [hInternalEnergyThreeToOne, hWorkThreeToOne] at hFirstLaw
    norm_num at hFirstLaw ⊢
    exact hFirstLaw
  exact ⟨hHeatOneToTwo, hHeatTwoToThree, hHeatThreeToOne⟩

/-!
Blueprint label: `thm:physics:phyx_mini_0414:target`.

All three segment heats are determined by the figure and thermodynamic laws.
On the `3 → 1` segment the gas rejects `1.01301933 kJ`, which rounds to
`-1.01 kJ` and is nearest the recorded answer choice C.
-/
theorem heatTransfersOnCycleSegments_and_recordedChoiceC
    (setup : HeliumThermodynamicCycle)
    (_problem : MatchesProblemStatement setup)
    (_figure : MatchesPrimaryPressureVolumeDiagram setup)
    (_referenceData : UsesTextbookHeliumReferenceData setup)
    (_physical : HasPhysicalThermodynamicParameters setup)
    (_laws : ObeysIdealMonatomicGasLaws setup) :
    energyInJoules (setup.heatIntoGas .oneToTwo) =
        (303905799 / 500000 : ℝ) ∧
      energyInJoules (setup.heatIntoGas .twoToThree) =
        (101301933 / 200000 : ℝ) * Real.log 5 ∧
      energyInJoules (setup.heatIntoGas .threeToOne) =
        -(101301933 / 100000 : ℝ) ∧
      RoundsToNearestHundredthKilojoule
        (energyInKilojoules (setup.heatIntoGas .threeToOne))
        (displayedHeatInKilojoules recordedAnswerChoice) ∧
      IsNearestDisplayedChoice
        (energyInKilojoules (setup.heatIntoGas .threeToOne))
        recordedAnswerChoice := by
  rcases heatTransferReadoutsOnAllThreeSegments setup _problem _figure
      _referenceData _physical _laws with
    ⟨hHeatOneToTwo, hHeatTwoToThree, hHeatThreeToOne⟩
  have hRounds :
      RoundsToNearestHundredthKilojoule
        (energyInKilojoules (setup.heatIntoGas .threeToOne))
        (displayedHeatInKilojoules recordedAnswerChoice) := by
    unfold RoundsToNearestHundredthKilojoule energyInKilojoules
    rw [hHeatThreeToOne]
    norm_num [recordedAnswerChoice, displayedHeatInKilojoules]
  have hNearest :
      IsNearestDisplayedChoice
        (energyInKilojoules (setup.heatIntoGas .threeToOne))
        recordedAnswerChoice := by
    unfold IsNearestDisplayedChoice
    intro alternative
    simp only [energyInKilojoules, hHeatThreeToOne]
    cases alternative <;>
      norm_num [recordedAnswerChoice, displayedHeatInKilojoules]
  exact
    ⟨hHeatOneToTwo, hHeatTwoToThree, hHeatThreeToOne, hRounds, hNearest⟩

end PhyXMiniProblems.ProblemPhyXMini0414
