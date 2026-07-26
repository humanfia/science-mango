import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Physlib.Thermodynamics.Temperature.Basic
import Physlib.Units.WithDim.Energy
import Physlib.Units.WithDim.Pressure

/- USER: The assigned source file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0350

open Dimension

/-!
# Efficiency of an ideal-diatomic-gas heat-engine cycle

One mole of ideal diatomic gas follows the clockwise cycle `a → b → c → a`
shown in the supplied pressure-volume diagram.  The primary image places

* `a` at `(0.010 m³, 2.0 × 10⁵ Pa)`,
* `b` at `(0.005 m³, 4.0 × 10⁵ Pa)`, and
* `c` at `(0.010 m³, 4.0 × 10⁵ Pa)`.

The curved leg `a → b` is the isothermal compression, `b → c` is an isobaric
expansion, and `c → a` is an isochoric cooling.  The auxiliary caption calls
the final leg constant-pressure, but the image clearly shows a vertical
constant-volume segment and is designated as the primary evidence.

Pressure, volume, heat, work, and internal-energy change retain their physical
dimensions through Physlib.  Real numbers below are explicitly named SI or
molar readouts, figure coordinates, dimensionless efficiencies, or displayed
answer values.
-/

/-! ## Dimensionful quantities and calibrated readouts -/

/-- A signed physical volume, with length-cubed dimension. -/
abbrev VolumeQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * L𝓭 * L𝓭) ℝ)

/-- Read a physical volume in SI cubic metres. -/
def volumeInCubicMeters (volume : VolumeQuantity) : ℝ :=
  (volume UnitChoices.SI).val

/-- Read a physical pressure in SI pascals. -/
def pressureInPascals (pressure : DimPressure) : ℝ :=
  (pressure UnitChoices.SI).val

/-- Read a signed physical energy in joules. -/
def energyInJoules (energy : DimEnergy) : ℝ :=
  (energy UnitChoices.SI).val / (DimEnergy.joule UnitChoices.SI).val

/-- Read Physlib's nonnegative absolute-temperature value in kelvins.

The `Temperature` values used by this setup are calibrated in the kelvin unit.
-/
def temperatureInKelvin (temperature : Temperature) : ℝ :=
  temperature.toReal

/-! ## Gas, cycle, and figure vocabulary -/

/-- The thermodynamic working-substance model named in the problem. -/
inductive GasModel where
  | idealDiatomic
  deriving DecidableEq, Repr

/-- The role played by the cyclic thermodynamic device. -/
inductive ThermodynamicDeviceRole where
  | heatEngine
  deriving DecidableEq, Repr

/-- Labels of the three states in the supplied `pV` diagram. -/
inductive StateLabel where
  | a
  | b
  | c
  deriving DecidableEq, Repr

/-- Directed legs of the clockwise cycle shown by the arrows. -/
inductive CycleLeg where
  | aToB
  | bToC
  | cToA
  deriving DecidableEq, Repr

/-- Thermodynamic constraint holding along a process leg. -/
inductive ProcessKind where
  | isothermal
  | isobaric
  | isochoric
  deriving DecidableEq, Repr

/-- Geometric appearance of a process leg in the primary `pV` diagram. -/
inductive PathGeometry where
  | curvedSegment
  | horizontalSegment
  | verticalSegment
  deriving DecidableEq, Repr

/-- Physical quantity and SI unit printed on an axis of the diagram. -/
inductive AxisQuantity where
  | volumeCubicMeters
  | pressurePascals
  deriving DecidableEq, Repr

/-- A dimensionful thermodynamic state of the working gas. -/
structure ThermodynamicState where
  pressure : DimPressure
  volume : VolumeQuantity
  temperature : Temperature

/-!
The working gas, its three thermodynamic states, energy transfers, and the
figure's directed path.  Work is positive when done by the gas and heat is
positive when transferred into the gas.  Internal-energy change is
`U_finish - U_start` on each leg.
-/
structure IdealDiatomicHeatEngineCycle where
  gasModel : GasModel
  deviceRole : ThermodynamicDeviceRole
  amountOfGasMoles : ℝ
  molarGasConstantJoulesPerMoleKelvin : ℝ
  stateAt : StateLabel → ThermodynamicState
  workByGas : CycleLeg → DimEnergy
  heatIntoGas : CycleLeg → DimEnergy
  internalEnergyChange : CycleLeg → DimEnergy
  pathStart : CycleLeg → StateLabel
  pathFinish : CycleLeg → StateLabel
  processKind : CycleLeg → ProcessKind
  pathGeometry : CycleLeg → PathGeometry
  horizontalAxisQuantity : AxisQuantity
  verticalAxisQuantity : AxisQuantity
  stateLabelVisible : StateLabel → Bool

/-! ## Problem data, primary-figure readouts, and governing laws -/

/-- Data stated explicitly in the prose: a one-mole ideal diatomic gas in a
heat engine.  No requested efficiency is fixed here. -/
structure MatchesProblemStatement
    (setup : IdealDiatomicHeatEngineCycle) : Prop where
  is_ideal_diatomic_gas : setup.gasModel = .idealDiatomic
  is_heat_engine : setup.deviceRole = .heatEngine
  amount_is_one_mole : setup.amountOfGasMoles = 1

/-!
Transcription of the primary raster, including the arrow directions and the
constant-variable interpretation of each leg.  The `c → a` segment is treated
as isochoric because it is vertical on the volume axis.
-/
structure MatchesPrimaryPVDiagram
    (setup : IdealDiatomicHeatEngineCycle) : Prop where
  horizontal_axis_is_volume :
    setup.horizontalAxisQuantity = .volumeCubicMeters
  vertical_axis_is_pressure :
    setup.verticalAxisQuantity = .pressurePascals
  volume_a_cubic_meters :
    volumeInCubicMeters (setup.stateAt .a).volume = 1 / 100
  pressure_a_pascals :
    pressureInPascals (setup.stateAt .a).pressure = 200000
  volume_b_cubic_meters :
    volumeInCubicMeters (setup.stateAt .b).volume = 1 / 200
  pressure_b_pascals :
    pressureInPascals (setup.stateAt .b).pressure = 400000
  volume_c_cubic_meters :
    volumeInCubicMeters (setup.stateAt .c).volume = 1 / 100
  pressure_c_pascals :
    pressureInPascals (setup.stateAt .c).pressure = 400000
  a_label_visible : setup.stateLabelVisible .a = true
  b_label_visible : setup.stateLabelVisible .b = true
  c_label_visible : setup.stateLabelVisible .c = true
  ab_starts_at_a : setup.pathStart .aToB = .a
  ab_finishes_at_b : setup.pathFinish .aToB = .b
  bc_starts_at_b : setup.pathStart .bToC = .b
  bc_finishes_at_c : setup.pathFinish .bToC = .c
  ca_starts_at_c : setup.pathStart .cToA = .c
  ca_finishes_at_a : setup.pathFinish .cToA = .a
  ab_is_curved : setup.pathGeometry .aToB = .curvedSegment
  bc_is_horizontal : setup.pathGeometry .bToC = .horizontalSegment
  ca_is_vertical : setup.pathGeometry .cToA = .verticalSegment
  ab_is_isothermal : setup.processKind .aToB = .isothermal
  bc_is_isobaric : setup.processKind .bToC = .isobaric
  ca_is_isochoric : setup.processKind .cToA = .isochoric

/-- Positivity conditions for the amount, gas constant, and physical state
readouts. -/
structure HasPhysicalThermodynamicParameters
    (setup : IdealDiatomicHeatEngineCycle) : Prop where
  amount_positive : 0 < setup.amountOfGasMoles
  gas_constant_positive :
    0 < setup.molarGasConstantJoulesPerMoleKelvin
  pressure_positive :
    ∀ state, 0 < pressureInPascals (setup.stateAt state).pressure
  volume_positive :
    ∀ state, 0 < volumeInCubicMeters (setup.stateAt state).volume
  temperature_positive :
    ∀ state, 0 < temperatureInKelvin (setup.stateAt state).temperature

/-!
Macroscopic governing laws for this ideal diatomic gas.

* `pV = nRT` is imposed at every labeled equilibrium state.
* `ΔU = (5/2)nRΔT` is the ideal-diatomic internal-energy law.
* `Q = ΔU + W_by` is the first law with the stated sign convention.
* Boundary work is specialized to the three process kinds.  The isothermal
  formula is `nRT log(V_f/V_i)`; the isobaric formula is
  `p(V_f-V_i)`; an isochoric leg has zero work.

These are general physical laws.  In particular, no field states the net
cycle work, total heat input, thermal efficiency, or an answer choice.
-/
structure ObeysIdealDiatomicGasLaws
    (setup : IdealDiatomicHeatEngineCycle) : Prop where
  ideal_gas_law : ∀ state,
    pressureInPascals (setup.stateAt state).pressure *
        volumeInCubicMeters (setup.stateAt state).volume =
      setup.amountOfGasMoles *
        setup.molarGasConstantJoulesPerMoleKelvin *
        temperatureInKelvin (setup.stateAt state).temperature
  diatomic_internal_energy_law : ∀ leg,
    energyInJoules (setup.internalEnergyChange leg) =
      (5 / 2 : ℝ) * setup.amountOfGasMoles *
        setup.molarGasConstantJoulesPerMoleKelvin *
        (temperatureInKelvin
              (setup.stateAt (setup.pathFinish leg)).temperature -
          temperatureInKelvin
              (setup.stateAt (setup.pathStart leg)).temperature)
  first_law : ∀ leg,
    energyInJoules (setup.heatIntoGas leg) =
      energyInJoules (setup.internalEnergyChange leg) +
        energyInJoules (setup.workByGas leg)
  isothermal_temperature_law : ∀ leg,
    setup.processKind leg = .isothermal →
      temperatureInKelvin
          (setup.stateAt (setup.pathFinish leg)).temperature =
        temperatureInKelvin
          (setup.stateAt (setup.pathStart leg)).temperature
  isothermal_boundary_work_law : ∀ leg,
    setup.processKind leg = .isothermal →
      energyInJoules (setup.workByGas leg) =
        setup.amountOfGasMoles *
          setup.molarGasConstantJoulesPerMoleKelvin *
          temperatureInKelvin
            (setup.stateAt (setup.pathStart leg)).temperature *
          Real.log
            (volumeInCubicMeters
                (setup.stateAt (setup.pathFinish leg)).volume /
              volumeInCubicMeters
                (setup.stateAt (setup.pathStart leg)).volume)
  isobaric_boundary_work_law : ∀ leg,
    setup.processKind leg = .isobaric →
      pressureInPascals
          (setup.stateAt (setup.pathFinish leg)).pressure =
        pressureInPascals
          (setup.stateAt (setup.pathStart leg)).pressure ∧
      energyInJoules (setup.workByGas leg) =
        pressureInPascals
            (setup.stateAt (setup.pathStart leg)).pressure *
          (volumeInCubicMeters
                (setup.stateAt (setup.pathFinish leg)).volume -
            volumeInCubicMeters
                (setup.stateAt (setup.pathStart leg)).volume)
  isochoric_boundary_work_law : ∀ leg,
    setup.processKind leg = .isochoric →
      volumeInCubicMeters
          (setup.stateAt (setup.pathFinish leg)).volume =
        volumeInCubicMeters
          (setup.stateAt (setup.pathStart leg)).volume ∧
      energyInJoules (setup.workByGas leg) = 0

/-! ## Thermal efficiency and displayed answer choices -/

/-- Net work done by the gas over one traversal of the three-leg cycle. -/
def netWorkByGasInJoules (setup : IdealDiatomicHeatEngineCycle) : ℝ :=
  energyInJoules (setup.workByGas .aToB) +
    energyInJoules (setup.workByGas .bToC) +
    energyInJoules (setup.workByGas .cToA)

/-- Total heat entering the gas, obtained by summing only positive heat
transfers over the three legs. -/
def totalHeatInputInJoules (setup : IdealDiatomicHeatEngineCycle) : ℝ :=
  max (energyInJoules (setup.heatIntoGas .aToB)) 0 +
    max (energyInJoules (setup.heatIntoGas .bToC)) 0 +
    max (energyInJoules (setup.heatIntoGas .cToA)) 0

/-- Dimensionless thermal efficiency `W_net / Q_in`. -/
def thermalEfficiency (setup : IdealDiatomicHeatEngineCycle) : ℝ :=
  netWorkByGasInJoules setup / totalHeatInputInJoules setup

/-- Labels of the four answer choices in the supplied problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Percentage printed beside each answer label. -/
def displayedEfficiencyPercent : AnswerChoice → ℝ
  | .A => 10
  | .B => 87 / 10
  | .C => 159 / 10
  | .D => 123 / 10

/-- The answer label recorded in the supplied dataset metadata. -/
def recordedAnswerChoice : AnswerChoice := .B

/-- A fractional efficiency truncates to a displayed percentage at one digit
after the decimal point. -/
def TruncatesToOneDecimalPercent
    (efficiency displayedPercent : ℝ) : Prop :=
  displayedPercent / 100 ≤ efficiency ∧
    efficiency < (displayedPercent + 1 / 10) / 100

/-!
The leg-by-leg energy readouts implied by the figure and governing laws.
This intermediate result leaves the requested efficiency to the theorem below.
-/
lemma cycleLegEnergyReadouts
    (setup : IdealDiatomicHeatEngineCycle)
    (h_problem : MatchesProblemStatement setup)
    (h_figure : MatchesPrimaryPVDiagram setup)
    (h_physical : HasPhysicalThermodynamicParameters setup)
    (h_laws : ObeysIdealDiatomicGasLaws setup) :
    energyInJoules (setup.workByGas .aToB) =
        -(2000 * Real.log 2) ∧
      energyInJoules (setup.workByGas .bToC) = 2000 ∧
      energyInJoules (setup.workByGas .cToA) = 0 ∧
      energyInJoules (setup.heatIntoGas .aToB) =
        -(2000 * Real.log 2) ∧
      energyInJoules (setup.heatIntoGas .bToC) = 7000 ∧
      energyInJoules (setup.heatIntoGas .cToA) = -5000 := by
  have h_a := h_laws.ideal_gas_law .a
  have h_b := h_laws.ideal_gas_law .b
  have h_c := h_laws.ideal_gas_law .c
  rw [h_figure.pressure_a_pascals, h_figure.volume_a_cubic_meters,
    h_problem.amount_is_one_mole] at h_a
  rw [h_figure.pressure_b_pascals, h_figure.volume_b_cubic_meters,
    h_problem.amount_is_one_mole] at h_b
  rw [h_figure.pressure_c_pascals, h_figure.volume_c_cubic_meters,
    h_problem.amount_is_one_mole] at h_c
  norm_num at h_a h_b h_c

  have h_ab_work :=
    h_laws.isothermal_boundary_work_law .aToB h_figure.ab_is_isothermal
  rw [h_figure.ab_starts_at_a, h_figure.ab_finishes_at_b,
    h_problem.amount_is_one_mole, h_figure.volume_a_cubic_meters,
    h_figure.volume_b_cubic_meters] at h_ab_work
  norm_num at h_ab_work
  rw [show (1 / 2 : ℝ) = 2⁻¹ by norm_num, Real.log_inv] at h_ab_work
  have h_ab_work' :
      energyInJoules (setup.workByGas .aToB) =
        -(2000 * Real.log 2) := by
    calc
      energyInJoules (setup.workByGas .aToB) =
          (setup.molarGasConstantJoulesPerMoleKelvin *
              temperatureInKelvin (setup.stateAt .a).temperature) *
            (-Real.log 2) := h_ab_work
      _ = 2000 * (-Real.log 2) := by rw [← h_a]
      _ = -(2000 * Real.log 2) := by ring

  have h_bc_work :=
    (h_laws.isobaric_boundary_work_law .bToC h_figure.bc_is_isobaric).2
  rw [h_figure.bc_starts_at_b, h_figure.bc_finishes_at_c,
    h_figure.pressure_b_pascals, h_figure.volume_b_cubic_meters,
    h_figure.volume_c_cubic_meters] at h_bc_work
  norm_num at h_bc_work

  have h_ca_work :=
    (h_laws.isochoric_boundary_work_law .cToA h_figure.ca_is_isochoric).2

  have h_ab_internal := h_laws.diatomic_internal_energy_law .aToB
  rw [h_figure.ab_starts_at_a, h_figure.ab_finishes_at_b,
    h_problem.amount_is_one_mole] at h_ab_internal
  have h_ab_temperature :=
    h_laws.isothermal_temperature_law .aToB h_figure.ab_is_isothermal
  rw [h_figure.ab_starts_at_a, h_figure.ab_finishes_at_b] at h_ab_temperature
  rw [h_ab_temperature] at h_ab_internal
  norm_num at h_ab_internal

  have h_bc_internal := h_laws.diatomic_internal_energy_law .bToC
  rw [h_figure.bc_starts_at_b, h_figure.bc_finishes_at_c,
    h_problem.amount_is_one_mole] at h_bc_internal
  norm_num at h_bc_internal

  have h_ca_internal := h_laws.diatomic_internal_energy_law .cToA
  rw [h_figure.ca_starts_at_c, h_figure.ca_finishes_at_a,
    h_problem.amount_is_one_mole] at h_ca_internal
  norm_num at h_ca_internal

  have h_ab_heat := h_laws.first_law .aToB
  have h_bc_heat := h_laws.first_law .bToC
  have h_ca_heat := h_laws.first_law .cToA
  constructor
  · exact h_ab_work'
  constructor
  · exact h_bc_work
  constructor
  · exact h_ca_work
  constructor
  · linarith [h_ab_work']
  constructor
  · nlinarith [h_b, h_c]
  · nlinarith [h_a, h_c]

/-!
The exact efficiency is

`(2000 - 2000 log 2) / 7000 = (2/7)(1 - log 2)`.

It lies in `[0.087, 0.088)`, so its percentage truncates to `8.7%`, the
displayed value of recorded answer choice B.
-/
theorem thermalEfficiency_eq_answerChoiceB
    (setup : IdealDiatomicHeatEngineCycle)
    (h_problem : MatchesProblemStatement setup)
    (h_figure : MatchesPrimaryPVDiagram setup)
    (h_physical : HasPhysicalThermodynamicParameters setup)
    (h_laws : ObeysIdealDiatomicGasLaws setup) :
    thermalEfficiency setup = (2 / 7 : ℝ) * (1 - Real.log 2) ∧
      TruncatesToOneDecimalPercent
        (thermalEfficiency setup)
        (displayedEfficiencyPercent recordedAnswerChoice) := by
  rcases cycleLegEnergyReadouts setup h_problem h_figure h_physical h_laws with
    ⟨h_ab_work, h_bc_work, h_ca_work, h_ab_heat, h_bc_heat, h_ca_heat⟩
  have h_log_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h_ab_value_nonpos : -(2000 * Real.log 2) ≤ 0 := by
    nlinarith
  have h_heat_input : totalHeatInputInJoules setup = 7000 := by
    simp only [totalHeatInputInJoules]
    rw [h_ab_heat, h_bc_heat, h_ca_heat,
      max_eq_right h_ab_value_nonpos]
    norm_num
  have h_net_work :
      netWorkByGasInJoules setup = 2000 - 2000 * Real.log 2 := by
    simp only [netWorkByGasInJoules]
    rw [h_ab_work, h_bc_work, h_ca_work]
    ring
  have h_efficiency :
      thermalEfficiency setup = (2 / 7 : ℝ) * (1 - Real.log 2) := by
    rw [thermalEfficiency, h_net_work, h_heat_input]
    ring
  have h_log_upper : Real.log 2 ≤ (1391 / 2000 : ℝ) := by
    let q : ℝ := 739 / 737
    have hq : 0 < q := by norm_num [q]
    have hp : (2 : ℝ) ≤ q ^ 256 := by norm_num [q]
    have hl := Real.log_le_log (by norm_num : (0 : ℝ) < 2) hp
    rw [Real.log_pow] at hl
    have hqlog := Real.log_le_sub_one_of_pos hq
    dsimp [q] at hl hqlog
    norm_num at hl hqlog ⊢
    linarith
  have h_log_lower : (173 / 250 : ℝ) < Real.log 2 := by
    let q : ℝ := 2589 / 2582
    have hq : 0 < q := by norm_num [q]
    have hp : q ^ 256 ≤ (2 : ℝ) := by norm_num [q]
    have hl := Real.log_le_log (pow_pos hq 256) hp
    rw [Real.log_pow] at hl
    have hqlog := Real.one_sub_inv_le_log_of_pos hq
    dsimp [q] at hl hqlog
    norm_num at hl hqlog ⊢
    linarith
  refine ⟨h_efficiency, ?_⟩
  rw [TruncatesToOneDecimalPercent, h_efficiency]
  norm_num [displayedEfficiencyPercent, recordedAnswerChoice]
  constructor <;> nlinarith

end PhyXMiniProblems.ProblemPhyXMini0350
