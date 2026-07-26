import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Physlib.Thermodynamics.Temperature.Basic
import Physlib.Units.WithDim.Energy
import Physlib.Units.WithDim.Pressure

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0410

open Dimension

/-!
# Heat transferred during an isothermal compression of nitrogen

The primary pressure--volume diagram shows `0.10 mol` of nitrogen following
two compression paths.  The upper path is an isotherm from
`i = (3000 cm³, 1 atm)` to `f = (1000 cm³, 3 atm)`.  The lower path is an
adiabat with its own point labelled `i`, at the same initial volume and below
`1 atm`, and the same final point `f`.  Both arrows point from `i` toward `f`.

Heat is positive into the gas and boundary work is positive when done by the
gas.  Thus compression gives negative isothermal work and, because the ideal
gas internal-energy change vanishes on an isotherm, negative heat transfer.

Pressure, volume, temperature, heat, work, and internal-energy change retain
their physical roles.  Real numbers below are explicitly named readouts in
atmospheres, cubic centimetres, joules, or moles, or are schematic figure
data and displayed answer values.
-/

/-! ## Dimensionful physical quantities and calibrated readouts -/

/-- A signed physical gas volume, carrying the dimension `L³`. -/
abbrev VolumeQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * L𝓭 * L𝓭) ℝ)

/-- A physical pressure, grounded by Physlib's pressure dimension. -/
abbrev PressureQuantity : Type := DimPressure

/-- A signed physical energy, used for heat, work, and internal energy. -/
abbrev EnergyQuantity : Type := DimEnergy

/-- Read a physical volume in coherent SI cubic metres. -/
def volumeInCubicMetres (volume : VolumeQuantity) : ℝ :=
  (volume UnitChoices.SI).val

/-- Read a physical volume in cubic centimetres. -/
def volumeInCubicCentimetres (volume : VolumeQuantity) : ℝ :=
  10 ^ 6 * volumeInCubicMetres volume

/-- Read a physical pressure in coherent SI pascals. -/
def pressureInPascals (pressure : PressureQuantity) : ℝ :=
  (pressure UnitChoices.SI).val

/-- Read a physical pressure in standard atmospheres. -/
def pressureInAtmospheres (pressure : PressureQuantity) : ℝ :=
  pressureInPascals pressure /
    (DimPressure.standardAtmosphere UnitChoices.SI).val

/-- Read heat, work, or internal-energy change in joules. -/
def energyInJoules (energy : EnergyQuantity) : ℝ :=
  (energy UnitChoices.SI).val /
    (DimEnergy.joule UnitChoices.SI).val

/-- The exact number of joules represented by one `atm cm³`. -/
def joulesPerCubicCentimetreAtmosphere : ℝ :=
  101325 / 10 ^ 6

/-! ## Gas, process, state, and figure vocabulary -/

/-- Chemical species named in the problem statement. -/
inductive GasSpecies where
  | nitrogen
  deriving DecidableEq, Repr

/-- A fixed gas sample; its amount is an explicitly named mole readout. -/
structure GasSample where
  species : GasSpecies
  amountOfSubstanceMoles : ℝ

/-- The two thermodynamic paths named in the primary figure. -/
inductive ProcessPath where
  | isotherm
  | adiabat
  deriving DecidableEq, Repr

/-!
The raster contains two distinct points printed `i`, one on each curve, and
one common point printed `f`.
-/
inductive StateLabel where
  | isothermInitial
  | adiabatInitial
  | final
  deriving DecidableEq, Repr

/-- Initial state selected by a displayed path. -/
def ProcessPath.initialState : ProcessPath → StateLabel
  | .isotherm => .isothermInitial
  | .adiabat => .adiabatInitial

/-- Both displayed paths finish at the common point `f`. -/
def ProcessPath.finalState (_path : ProcessPath) : StateLabel := .final

/-- The two physical quantities assigned to the diagram axes. -/
inductive AxisQuantity where
  | pressure
  | volume
  deriving DecidableEq, Repr

/-- Unit label printed on the pressure axis. -/
inductive PressureAxisUnit where
  | atmosphere
  deriving DecidableEq, Repr

/-- Unit label printed on the volume axis. -/
inductive VolumeAxisUnit where
  | cubicCentimetre
  deriving DecidableEq, Repr

/-- Thermodynamic regime implicit in the smooth equilibrium paths. -/
inductive ProcessRegime where
  | quasistatic
  deriving DecidableEq, Repr

/-!
Qualitative content of the supplied bitmap.  Coordinates and physical
quantities live in `GasProcessSetup`; this structure retains axes, unit
labels, curve labels, points, arrows, and the ordering of the two curves.
-/
structure PressureVolumeFigure where
  horizontalAxisQuantity : AxisQuantity
  verticalAxisQuantity : AxisQuantity
  pressureAxisUnit : PressureAxisUnit
  volumeAxisUnit : VolumeAxisUnit
  originZeroShown : Bool
  pressureTickShown : ℕ → Bool
  volumeTickShown : ℕ → Bool
  curveShown : ProcessPath → Bool
  curveLabelShown : ProcessPath → Bool
  initialPointShown : ProcessPath → Bool
  initialLabelIShown : ProcessPath → Bool
  finalPointShown : Bool
  finalLabelFShown : Bool
  arrowStart : ProcessPath → StateLabel
  arrowFinish : ProcessPath → StateLabel
  isothermAboveAdiabatBetweenEndpoints : Bool

/-!
Independent thermodynamic quantities for the two processes.  In particular,
the requested heat is a field, not a definition of the displayed answer.
-/
structure GasProcessSetup where
  sample : GasSample
  figure : PressureVolumeFigure
  pressureAt : StateLabel → PressureQuantity
  volumeAt : StateLabel → VolumeQuantity
  temperatureAt : StateLabel → Temperature
  processRegime : ProcessPath → ProcessRegime
  workDoneByGasAlong : ProcessPath → EnergyQuantity
  heatTransferredIntoGasAlong : ProcessPath → EnergyQuantity
  internalEnergyChangeAlong : ProcessPath → EnergyQuantity

/-! ## Problem data and primary-figure transcription -/

/-- Problem-text data: a `0.10 mol` sample of nitrogen. -/
structure MatchesProblemStatement (setup : GasProcessSetup) : Prop where
  species_is_nitrogen : setup.sample.species = .nitrogen
  amount_is_point_ten_moles : setup.sample.amountOfSubstanceMoles = 1 / 10
  isotherm_is_quasistatic : setup.processRegime .isotherm = .quasistatic
  adiabat_is_quasistatic : setup.processRegime .adiabat = .quasistatic

/-!
Exact and qualitative readouts from the primary raster.  The isothermal point
`i` is `(3000 cm³, 1 atm)` and the common point `f` is
`(1000 cm³, 3 atm)`.  The lower adiabatic `i` is visibly at the same volume
and between `0` and `1 atm`; no unsupported exact pressure is assigned to it.
No heat, work, or internal-energy value appears in this figure predicate.
-/
structure MatchesPrimaryPressureVolumeFigure
    (setup : GasProcessSetup) : Prop where
  horizontal_axis_is_volume :
    setup.figure.horizontalAxisQuantity = .volume
  vertical_axis_is_pressure :
    setup.figure.verticalAxisQuantity = .pressure
  pressure_axis_is_in_atmospheres :
    setup.figure.pressureAxisUnit = .atmosphere
  volume_axis_is_in_cubic_centimetres :
    setup.figure.volumeAxisUnit = .cubicCentimetre
  origin_zero_is_shown : setup.figure.originZeroShown = true
  pressure_ticks_are_shown :
    ∀ tick ∈ ([0, 1, 2, 3] : List ℕ),
      setup.figure.pressureTickShown tick = true
  volume_ticks_are_shown :
    ∀ tick ∈ ([0, 1000, 2000, 3000] : List ℕ),
      setup.figure.volumeTickShown tick = true
  both_curves_are_shown :
    ∀ path, setup.figure.curveShown path = true
  both_curve_labels_are_shown :
    ∀ path, setup.figure.curveLabelShown path = true
  both_initial_points_are_shown :
    ∀ path, setup.figure.initialPointShown path = true
  both_initial_points_are_labelled_i :
    ∀ path, setup.figure.initialLabelIShown path = true
  final_point_is_shown : setup.figure.finalPointShown = true
  final_point_is_labelled_f : setup.figure.finalLabelFShown = true
  every_arrow_starts_at_its_i : ∀ path,
    setup.figure.arrowStart path = path.initialState
  every_arrow_finishes_at_f : ∀ path,
    setup.figure.arrowFinish path = path.finalState
  isotherm_is_above_adiabat :
    setup.figure.isothermAboveAdiabatBetweenEndpoints = true
  isotherm_initial_volume_cm3 :
    volumeInCubicCentimetres
        (setup.volumeAt .isothermInitial) = 3000
  isotherm_initial_pressure_atm :
    pressureInAtmospheres
        (setup.pressureAt .isothermInitial) = 1
  adiabat_initial_volume_cm3 :
    volumeInCubicCentimetres
        (setup.volumeAt .adiabatInitial) = 3000
  adiabat_initial_pressure_below_one_atm :
    pressureInAtmospheres
        (setup.pressureAt .adiabatInitial) < 1
  final_volume_cm3 :
    volumeInCubicCentimetres (setup.volumeAt .final) = 1000
  final_pressure_atm :
    pressureInAtmospheres (setup.pressureAt .final) = 3

/-- Positivity conditions selecting physically meaningful gas states. -/
structure HasPhysicalThermodynamicParameters
    (setup : GasProcessSetup) : Prop where
  amount_positive : 0 < setup.sample.amountOfSubstanceMoles
  pressure_positive : ∀ state,
    0 < pressureInAtmospheres (setup.pressureAt state)
  volume_positive : ∀ state,
    0 < volumeInCubicCentimetres (setup.volumeAt state)
  absolute_temperature_positive : ∀ state,
    0 < (setup.temperatureAt state).val

/-! ## Governing thermodynamic laws -/

/-!
Ideal-gas laws specialized to the displayed quasistatic isotherm.  For a
fixed amount of ideal gas, constant temperature gives constant `pV`, zero
internal-energy change, and boundary work

`W_by = p_i V_i log (V_f / V_i)`.

The conversion factor turns the diagram's `atm cm³` into joules.  This law
contains no heat value or answer-choice value.
-/
structure SatisfiesIdealGasIsothermalLaws
    (setup : GasProcessSetup) : Prop where
  endpoint_temperatures_equal :
    setup.temperatureAt .isothermInitial = setup.temperatureAt .final
  pressure_volume_product_constant :
    pressureInAtmospheres (setup.pressureAt .isothermInitial) *
        volumeInCubicCentimetres (setup.volumeAt .isothermInitial) =
      pressureInAtmospheres (setup.pressureAt .final) *
        volumeInCubicCentimetres (setup.volumeAt .final)
  internal_energy_change_zero :
    energyInJoules (setup.internalEnergyChangeAlong .isotherm) = 0
  quasistatic_boundary_work :
    energyInJoules (setup.workDoneByGasAlong .isotherm) =
      pressureInAtmospheres (setup.pressureAt .isothermInitial) *
        volumeInCubicCentimetres (setup.volumeAt .isothermInitial) *
          joulesPerCubicCentimetreAtmosphere *
            Real.log
              (volumeInCubicCentimetres (setup.volumeAt .final) /
                volumeInCubicCentimetres
                  (setup.volumeAt .isothermInitial))

/-!
Definition of the displayed adiabatic comparison process: no heat crosses the
system boundary.  This setup law is retained even though the current question
asks for heat on the other path.
-/
structure SatisfiesAdiabaticHeatLaw
    (setup : GasProcessSetup) : Prop where
  adiabatic_heat_transfer_zero :
    energyInJoules (setup.heatTransferredIntoGasAlong .adiabat) = 0

/-!
Closed-system first law for either path, with heat into the gas and work done
by the gas positive: `ΔU = Q_in - W_by`.  It relates independent energy fields
and does not prescribe the requested heat.
-/
structure SatisfiesClosedSystemFirstLaw
    (setup : GasProcessSetup) : Prop where
  first_law : ∀ path,
    energyInJoules (setup.internalEnergyChangeAlong path) =
      energyInJoules (setup.heatTransferredIntoGasAlong path) -
        energyInJoules (setup.workDoneByGasAlong path)

/-! ## Exact heat expression and displayed multiple-choice answer -/

/-- The four answer labels printed with the exercise. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Joule readout printed beside each answer label. -/
def displayedHeatJoules : AnswerChoice → ℝ
  | .A => 330
  | .B => 0
  | .C => -330
  | .D => -660

/-!
The choices are stated to the nearest ten joules.  A strict half-unit window
also makes the selected displayed value unambiguous.
-/
def RoundsToNearestTenJoules (actual displayed : ℝ) : Prop :=
  |actual - displayed| < 5

/-- The exact logarithmic heat expression determined by the isothermal path. -/
def isothermalHeatExpressionInJoules (setup : GasProcessSetup) : ℝ :=
  pressureInAtmospheres (setup.pressureAt .isothermInitial) *
    volumeInCubicCentimetres (setup.volumeAt .isothermInitial) *
      joulesPerCubicCentimetreAtmosphere *
        Real.log
          (volumeInCubicCentimetres (setup.volumeAt .final) /
            volumeInCubicCentimetres (setup.volumeAt .isothermInitial))

/-!
The first law and zero isothermal internal-energy change make heat into the
gas equal the (negative) work done by the gas during this compression.
-/
lemma isothermalHeatEqualsBoundaryWork
    (setup : GasProcessSetup)
    (h_isothermal : SatisfiesIdealGasIsothermalLaws setup)
    (h_firstLaw : SatisfiesClosedSystemFirstLaw setup) :
    energyInJoules (setup.heatTransferredIntoGasAlong .isotherm) =
      isothermalHeatExpressionInJoules setup := by
  unfold isothermalHeatExpressionInJoules
  rw [← h_isothermal.quasistatic_boundary_work]
  linarith [h_isothermal.internal_energy_change_zero,
    h_firstLaw.first_law .isotherm]

/-!
The figure values give
`Q = 3000 (101325 / 10^6) log (1/3) J ≈ -333.95 J`.
Consequently the result rounds to the displayed `-330 J`, and no other listed
choice lies in the same nearest-ten-joule window.

Blueprint: `thm:physics:phyx_mini_0410:target`.
-/
theorem problem_phyx_mini_0410
    (setup : GasProcessSetup)
    (h_statement : MatchesProblemStatement setup)
    (h_figure : MatchesPrimaryPressureVolumeFigure setup)
    (h_physical : HasPhysicalThermodynamicParameters setup)
    (h_isothermal : SatisfiesIdealGasIsothermalLaws setup)
    (h_adiabatic : SatisfiesAdiabaticHeatLaw setup)
    (h_firstLaw : SatisfiesClosedSystemFirstLaw setup) :
    energyInJoules (setup.heatTransferredIntoGasAlong .isotherm) =
        isothermalHeatExpressionInJoules setup ∧
      RoundsToNearestTenJoules
        (energyInJoules (setup.heatTransferredIntoGasAlong .isotherm))
        (displayedHeatJoules .C) ∧
      ∀ choice : AnswerChoice,
        RoundsToNearestTenJoules
            (energyInJoules (setup.heatTransferredIntoGasAlong .isotherm))
            (displayedHeatJoules choice) →
          choice = .C := by
  have h_heat :=
    isothermalHeatEqualsBoundaryWork setup h_isothermal h_firstLaw
  have h_log_lower : (64 / 59 : ℝ) ≤ Real.log 3 := by
    let q : ℝ := 59 / 58
    have hq : 0 < q := by norm_num [q]
    have hp : q ^ 64 ≤ (3 : ℝ) := by norm_num [q]
    have hl := Real.log_le_log (pow_pos hq 64) hp
    rw [Real.log_pow] at hl
    have hqlog := Real.one_sub_inv_le_log_of_pos hq
    dsimp [q] at hl hqlog
    norm_num at hl hqlog ⊢
    linarith
  have h_log_upper : Real.log 3 ≤ (768 / 697 : ℝ) := by
    let q : ℝ := 700 / 697
    have hq : 0 < q := by norm_num [q]
    have hp : (3 : ℝ) ≤ q ^ 256 := by norm_num [q]
    have hl := Real.log_le_log (by norm_num : (0 : ℝ) < 3) hp
    rw [Real.log_pow] at hl
    have hqlog := Real.log_le_sub_one_of_pos hq
    dsimp [q] at hl hqlog
    norm_num at hl hqlog ⊢
    linarith
  have h_heat_value :
      energyInJoules (setup.heatTransferredIntoGasAlong .isotherm) =
        -(12159 / 40 * Real.log 3) := by
    rw [h_heat]
    unfold isothermalHeatExpressionInJoules
    rw [h_figure.isotherm_initial_pressure_atm,
      h_figure.isotherm_initial_volume_cm3, h_figure.final_volume_cm3]
    unfold joulesPerCubicCentimetreAtmosphere
    norm_num
    rw [show (1 / 3 : ℝ) = 3⁻¹ by norm_num, Real.log_inv]
    ring
  have h_heat_lower :
      (-335 : ℝ) <
        energyInJoules (setup.heatTransferredIntoGasAlong .isotherm) := by
    rw [h_heat_value]
    nlinarith [h_log_upper]
  have h_heat_upper :
      energyInJoules (setup.heatTransferredIntoGasAlong .isotherm) <
        (-325 : ℝ) := by
    rw [h_heat_value]
    nlinarith [h_log_lower]
  refine ⟨h_heat, ?_, ?_⟩
  · unfold RoundsToNearestTenJoules
    simp only [displayedHeatJoules]
    rw [abs_lt]
    constructor <;> linarith
  · intro choice h_choice
    cases choice with
    | A =>
        unfold RoundsToNearestTenJoules at h_choice
        simp only [displayedHeatJoules] at h_choice
        rw [abs_lt] at h_choice
        exfalso
        linarith
    | B =>
        unfold RoundsToNearestTenJoules at h_choice
        simp only [displayedHeatJoules] at h_choice
        rw [abs_lt] at h_choice
        exfalso
        linarith
    | C => rfl
    | D =>
        unfold RoundsToNearestTenJoules at h_choice
        simp only [displayedHeatJoules] at h_choice
        rw [abs_lt] at h_choice
        exfalso
        linarith

end PhyXMiniProblems.ProblemPhyXMini0410
