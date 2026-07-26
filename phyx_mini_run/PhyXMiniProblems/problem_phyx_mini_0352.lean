import Mathlib
import Physlib.Units.WithDim.Energy
import Physlib.Units.WithDim.Pressure

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0352

open Dimension

/-!
# Efficiency of a triangular monatomic-ideal-gas cycle

A monatomic ideal gas follows the clockwise cycle `a → b → c → a` in the
supplied pressure-volume diagram.  The primary image places the states at

* `a = (0.500 m³, 3.00 × 10⁵ Pa)`,
* `b = (0.800 m³, 3.00 × 10⁵ Pa)`, and
* `c = (0.800 m³, 1.00 × 10⁵ Pa)`.

Thus `a → b` is an isobaric expansion, `b → c` is an isochoric pressure
decrease, and the explicitly stated `c → a` path is a diagonal straight-line
compression.  The auxiliary caption calls the last leg isochoric, but that is
incompatible with both the problem text and the primary image.

Pressure, volume, internal energy, heat, and work remain unit-independent
dimensionful quantities.  Real numbers below are SI readouts, a dimensionless
efficiency, schematic coordinates, or displayed percentage values.
-/

/-! ## Dimensionful quantities and SI readouts -/

/-- A signed physical volume, carrying the dimension of length cubed. -/
abbrev VolumeQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * L𝓭 * L𝓭) ℝ)

/-- A physical pressure, using Physlib's pressure dimension. -/
abbrev PressureQuantity : Type := DimPressure

/-- A signed physical energy, used for internal energy, heat, and work. -/
abbrev EnergyQuantity : Type := DimEnergy

/-- SI readout of a volume, in cubic metres. -/
def volumeInCubicMeters (volume : VolumeQuantity) : ℝ :=
  (volume UnitChoices.SI).val

/-- SI readout of a pressure, in pascals. -/
def pressureInPascals (pressure : PressureQuantity) : ℝ :=
  (pressure UnitChoices.SI).val /
    (DimPressure.pascal UnitChoices.SI).val

/-- SI readout of a signed energy, in joules. -/
def energyInJoules (energy : EnergyQuantity) : ℝ :=
  (energy UnitChoices.SI).val /
    (DimEnergy.joule UnitChoices.SI).val

/-! ## Gas, process, and primary-figure labels -/

/-- The material model named in the problem statement. -/
inductive GasModel where
  | monatomicIdealGas
  deriving DecidableEq, Repr

/-- The three labeled equilibrium states in the `pV` diagram. -/
inductive CycleState where
  | a
  | b
  | c
  deriving DecidableEq, Fintype, Repr

/-- The directed legs of the cycle, in traversal order. -/
inductive CycleLeg where
  | aToB
  | bToC
  | cToA
  deriving DecidableEq, Fintype, Repr

/-- Thermodynamic character singled out for each process leg. -/
inductive ProcessKind where
  | isobaric
  | isochoric
  | straightLineCompression
  deriving DecidableEq, Repr

/-- Geometric shape of a process in the pressure-volume plane. -/
inductive PathShape where
  | straightLine
  deriving DecidableEq, Repr

/-- Directions of the three blue arrows in the primary image. -/
inductive ArrowDirection where
  | right
  | down
  | upAndLeft
  deriving DecidableEq, Repr

/-- Literal mathematical labels shown on the axes and at the origin. -/
inductive AxisLabel where
  | pressureP
  | volumeV
  | originO
  deriving DecidableEq, Fintype, Repr

/-!
The independent physical observables of the gas cycle.

The efficiency is retained as an independent dimensionless observable and is
constrained only by the general efficiency law below.  In particular, it is
not defined to be the requested numerical answer.
-/
structure MonatomicIdealGasCycle where
  gasModel : GasModel
  volumeAt : CycleState → VolumeQuantity
  pressureAt : CycleState → PressureQuantity
  internalEnergyAt : CycleState → EnergyQuantity
  workByGas : CycleLeg → EnergyQuantity
  heatIntoGas : CycleLeg → EnergyQuantity
  thermalEfficiency : ℝ
  pathStart : CycleLeg → CycleState
  pathFinish : CycleLeg → CycleState
  processKind : CycleLeg → ProcessKind
  pathShape : CycleLeg → PathShape
  arrowDirection : CycleLeg → ArrowDirection
  axisLabelVisible : AxisLabel → Bool
  stateLabelVisible : CycleState → Bool
  schematicX : CycleState → ℝ
  schematicY : CycleState → ℝ

/-! ## General cycle accounting -/

/-- Total work done by the gas over one traversal of the three-leg cycle. -/
def cycleNetWorkInJoules (setup : MonatomicIdealGasCycle) : ℝ :=
  energyInJoules (setup.workByGas .aToB) +
    energyInJoules (setup.workByGas .bToC) +
    energyInJoules (setup.workByGas .cToA)

/-- The positive part of a signed heat transfer into the gas. -/
def positiveHeatInJoules (heat : EnergyQuantity) : ℝ :=
  max (energyInJoules heat) 0

/-- Total heat absorbed by the gas, excluding legs on which heat leaves it. -/
def cycleHeatInputInJoules (setup : MonatomicIdealGasCycle) : ℝ :=
  positiveHeatInJoules (setup.heatIntoGas .aToB) +
    positiveHeatInJoules (setup.heatIntoGas .bToC) +
    positiveHeatInJoules (setup.heatIntoGas .cToA)

/-! ## Figure/data readouts -/

/-!
Exact transcription of the problem statement and the primary raster image.
The state coordinates are physical SI readouts.  The path endpoints and arrow
directions record the displayed clockwise traversal, while the process tags
record the horizontal, vertical, and diagonal legs.  No requested efficiency
or answer-choice value occurs in this structure.
-/
structure MatchesProblemAndPrimaryFigure
    (setup : MonatomicIdealGasCycle) : Prop where
  gas_is_monatomic_ideal : setup.gasModel = .monatomicIdealGas
  volume_a_cubic_meters : volumeInCubicMeters (setup.volumeAt .a) = 1 / 2
  pressure_a_pascals : pressureInPascals (setup.pressureAt .a) = 300000
  volume_b_cubic_meters : volumeInCubicMeters (setup.volumeAt .b) = 4 / 5
  pressure_b_pascals : pressureInPascals (setup.pressureAt .b) = 300000
  volume_c_cubic_meters : volumeInCubicMeters (setup.volumeAt .c) = 4 / 5
  pressure_c_pascals : pressureInPascals (setup.pressureAt .c) = 100000
  ab_starts_at_a : setup.pathStart .aToB = .a
  ab_finishes_at_b : setup.pathFinish .aToB = .b
  bc_starts_at_b : setup.pathStart .bToC = .b
  bc_finishes_at_c : setup.pathFinish .bToC = .c
  ca_starts_at_c : setup.pathStart .cToA = .c
  ca_finishes_at_a : setup.pathFinish .cToA = .a
  ab_is_isobaric : setup.processKind .aToB = .isobaric
  bc_is_isochoric : setup.processKind .bToC = .isochoric
  ca_is_straight_line_compression :
    setup.processKind .cToA = .straightLineCompression
  every_leg_is_straight : ∀ leg, setup.pathShape leg = .straightLine
  ab_arrow_points_right : setup.arrowDirection .aToB = .right
  bc_arrow_points_down : setup.arrowDirection .bToC = .down
  ca_arrow_points_up_and_left : setup.arrowDirection .cToA = .upAndLeft
  every_axis_label_is_visible : ∀ label, setup.axisLabelVisible label = true
  every_state_label_is_visible : ∀ state, setup.stateLabelVisible state = true
  ab_is_horizontal_in_figure : setup.schematicY .a = setup.schematicY .b
  bc_is_vertical_in_figure : setup.schematicX .b = setup.schematicX .c
  a_is_left_of_b : setup.schematicX .a < setup.schematicX .b
  c_is_below_b : setup.schematicY .c < setup.schematicY .b

/-- Positivity and nondegeneracy conditions for a physical heat-engine cycle. -/
structure HasPhysicalCycleParameters
    (setup : MonatomicIdealGasCycle) : Prop where
  volume_positive :
    ∀ state, 0 < volumeInCubicMeters (setup.volumeAt state)
  pressure_positive :
    ∀ state, 0 < pressureInPascals (setup.pressureAt state)
  heat_input_positive : 0 < cycleHeatInputInJoules setup

/-! ## Governing thermodynamic laws -/

/-!
For a monatomic ideal gas, `U = (3/2) nRT = (3/2) pV` at every equilibrium
state.  This is the only ideal-gas caloric relation needed for the cycle; it
contains no figure-specific coordinates or requested efficiency.
-/
structure SatisfiesMonatomicIdealGasInternalEnergyLaw
    (setup : MonatomicIdealGasCycle) : Prop where
  internal_energy_law : ∀ state,
    energyInJoules (setup.internalEnergyAt state) =
      (3 / 2 : ℝ) * pressureInPascals (setup.pressureAt state) *
        volumeInCubicMeters (setup.volumeAt state)

/-!
Boundary work for any straight segment in the `pV` plane.  Linear pressure
variation makes the work by the gas equal to average pressure times the
change in volume.  The formula covers the isobaric, isochoric, and diagonal
legs uniformly and is independent of this problem's numerical data.
-/
structure SatisfiesStraightPathBoundaryWorkLaw
    (setup : MonatomicIdealGasCycle) : Prop where
  work_for_straight_leg : ∀ leg,
    setup.pathShape leg = .straightLine →
      energyInJoules (setup.workByGas leg) =
        ((pressureInPascals
              (setup.pressureAt (setup.pathStart leg)) +
            pressureInPascals
              (setup.pressureAt (setup.pathFinish leg))) / 2) *
          (volumeInCubicMeters
              (setup.volumeAt (setup.pathFinish leg)) -
            volumeInCubicMeters
              (setup.volumeAt (setup.pathStart leg)))

/-!
First law on each directed leg, using heat into the gas and work by the gas
as positive: `Q = ΔU + W`.  Heat transfers are independent observables rather
than definitions chosen to produce the final efficiency.
-/
structure SatisfiesFirstLawOnEachLeg
    (setup : MonatomicIdealGasCycle) : Prop where
  first_law : ∀ leg,
    energyInJoules (setup.heatIntoGas leg) =
      energyInJoules
          (setup.internalEnergyAt (setup.pathFinish leg)) -
        energyInJoules
          (setup.internalEnergyAt (setup.pathStart leg)) +
        energyInJoules (setup.workByGas leg)

/-!
Definition of thermal efficiency for a cyclic heat engine: net work output
divided by total positive heat input.  This general relation does not specify
the efficiency of the present numerical cycle.
-/
structure SatisfiesHeatEngineEfficiencyLaw
    (setup : MonatomicIdealGasCycle) : Prop where
  efficiency_law :
    setup.thermalEfficiency =
      cycleNetWorkInJoules setup / cycleHeatInputInJoules setup

/-! ## Derived energy accounting and requested answer -/

/-!
The thermodynamic laws and figure readouts determine all three signed works,
state internal energies, and signed heats.  Positive work and heat are into
the output/work and gas/heat conventions described above.
-/
lemma cycle_energy_accounting
    (setup : MonatomicIdealGasCycle)
    (hFigure : MatchesProblemAndPrimaryFigure setup)
    (hInternalEnergy : SatisfiesMonatomicIdealGasInternalEnergyLaw setup)
    (hBoundaryWork : SatisfiesStraightPathBoundaryWorkLaw setup)
    (hFirstLaw : SatisfiesFirstLawOnEachLeg setup) :
    energyInJoules (setup.internalEnergyAt .a) = 225000 ∧
      energyInJoules (setup.internalEnergyAt .b) = 360000 ∧
      energyInJoules (setup.internalEnergyAt .c) = 120000 ∧
      energyInJoules (setup.workByGas .aToB) = 90000 ∧
      energyInJoules (setup.workByGas .bToC) = 0 ∧
      energyInJoules (setup.workByGas .cToA) = -60000 ∧
      energyInJoules (setup.heatIntoGas .aToB) = 225000 ∧
      energyInJoules (setup.heatIntoGas .bToC) = -240000 ∧
      energyInJoules (setup.heatIntoGas .cToA) = 45000 ∧
      cycleNetWorkInJoules setup = 30000 ∧
      cycleHeatInputInJoules setup = 270000 := by
  have hUa := hInternalEnergy.internal_energy_law .a
  rw [hFigure.pressure_a_pascals, hFigure.volume_a_cubic_meters] at hUa
  norm_num at hUa
  have hUb := hInternalEnergy.internal_energy_law .b
  rw [hFigure.pressure_b_pascals, hFigure.volume_b_cubic_meters] at hUb
  norm_num at hUb
  have hUc := hInternalEnergy.internal_energy_law .c
  rw [hFigure.pressure_c_pascals, hFigure.volume_c_cubic_meters] at hUc
  norm_num at hUc
  have hWab := hBoundaryWork.work_for_straight_leg .aToB
    (hFigure.every_leg_is_straight .aToB)
  rw [hFigure.ab_starts_at_a, hFigure.ab_finishes_at_b,
    hFigure.pressure_a_pascals, hFigure.pressure_b_pascals,
    hFigure.volume_a_cubic_meters, hFigure.volume_b_cubic_meters] at hWab
  norm_num at hWab
  have hWbc := hBoundaryWork.work_for_straight_leg .bToC
    (hFigure.every_leg_is_straight .bToC)
  rw [hFigure.bc_starts_at_b, hFigure.bc_finishes_at_c,
    hFigure.pressure_b_pascals, hFigure.pressure_c_pascals,
    hFigure.volume_b_cubic_meters, hFigure.volume_c_cubic_meters] at hWbc
  norm_num at hWbc
  have hWca := hBoundaryWork.work_for_straight_leg .cToA
    (hFigure.every_leg_is_straight .cToA)
  rw [hFigure.ca_starts_at_c, hFigure.ca_finishes_at_a,
    hFigure.pressure_c_pascals, hFigure.pressure_a_pascals,
    hFigure.volume_c_cubic_meters, hFigure.volume_a_cubic_meters] at hWca
  norm_num at hWca
  have hQab := hFirstLaw.first_law .aToB
  rw [hFigure.ab_starts_at_a, hFigure.ab_finishes_at_b,
    hUa, hUb, hWab] at hQab
  norm_num at hQab
  have hQbc := hFirstLaw.first_law .bToC
  rw [hFigure.bc_starts_at_b, hFigure.bc_finishes_at_c,
    hUb, hUc, hWbc] at hQbc
  norm_num at hQbc
  have hQca := hFirstLaw.first_law .cToA
  rw [hFigure.ca_starts_at_c, hFigure.ca_finishes_at_a,
    hUc, hUa, hWca] at hQca
  norm_num at hQca
  have hNet : cycleNetWorkInJoules setup = 30000 := by
    simp only [cycleNetWorkInJoules]
    rw [hWab, hWbc, hWca]
    norm_num
  have hHeat : cycleHeatInputInJoules setup = 270000 := by
    simp only [cycleHeatInputInJoules, positiveHeatInJoules]
    rw [hQab, hQbc, hQca]
    norm_num
  exact
    ⟨hUa, hUb, hUc, hWab, hWbc, hWca, hQab, hQbc, hQca, hNet, hHeat⟩

/-- Labels of the four multiple-choice answers. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Percentage printed beside each answer label. -/
def displayedEfficiencyPercent : AnswerChoice → ℝ
  | .A => 10
  | .B => 111 / 10
  | .C => 159 / 10
  | .D => 123 / 10

/-- The answer label recorded in the supplied dataset metadata. -/
def recordedAnswerChoice : AnswerChoice := .B

/-- Convert a dimensionless efficiency to a percentage readout. -/
def efficiencyPercent (efficiency : ℝ) : ℝ := 100 * efficiency

/-- Agreement with a percentage displayed to the nearest tenth of a percent. -/
def EfficiencyMatchesDisplayedChoice
    (efficiency : ℝ) (choice : AnswerChoice) : Prop :=
  |efficiencyPercent efficiency - displayedEfficiencyPercent choice| < 1 / 20

/-!
The cycle produces `30000 J` of net work while absorbing `270000 J` of heat.
Consequently its exact efficiency is `1/9`; as a percentage this is
`11.111… %`, which rounds to the displayed `11.1 %` and selects answer B.

Blueprint: `thm:physics:phyx_mini_0352:target`.
-/
theorem problem_phyx_mini_0352
    (setup : MonatomicIdealGasCycle)
    (hFigure : MatchesProblemAndPrimaryFigure setup)
    (hPhysical : HasPhysicalCycleParameters setup)
    (hInternalEnergy : SatisfiesMonatomicIdealGasInternalEnergyLaw setup)
    (hBoundaryWork : SatisfiesStraightPathBoundaryWorkLaw setup)
    (hFirstLaw : SatisfiesFirstLawOnEachLeg setup)
    (hEfficiency : SatisfiesHeatEngineEfficiencyLaw setup) :
    setup.thermalEfficiency = (1 / 9 : ℝ) ∧
      EfficiencyMatchesDisplayedChoice
        setup.thermalEfficiency recordedAnswerChoice := by
  obtain ⟨_, _, _, _, _, _, _, _, _, hNet, hHeat⟩ :=
    cycle_energy_accounting setup hFigure hInternalEnergy hBoundaryWork hFirstLaw
  have hHeatPositive : 0 < cycleHeatInputInJoules setup :=
    hPhysical.heat_input_positive
  have hExact : setup.thermalEfficiency = (1 / 9 : ℝ) := by
    rw [hEfficiency.efficiency_law, hNet]
    apply (div_eq_iff (ne_of_gt hHeatPositive)).2
    rw [hHeat]
    norm_num
  refine ⟨hExact, ?_⟩
  rw [hExact]
  norm_num [EfficiencyMatchesDisplayedChoice, efficiencyPercent,
    recordedAnswerChoice, displayedEfficiencyPercent]

end PhyXMiniProblems.ProblemPhyXMini0352
