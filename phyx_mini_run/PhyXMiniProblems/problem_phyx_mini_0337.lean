import Mathlib
import Physlib.Units.WithDim.Energy
import Physlib.Units.WithDim.Pressure

/- USER: The assigned source file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0337

open Dimension

/-!
# Work and internal-energy change along a piecewise-straight `pV` path

An ideal-gas sample follows the path `a → b → c` in the supplied pressure-volume
diagram.  The primary image places

* `a` at `(2.0 L, 0.20 atm)`,
* `b` at `(2.0 L, 0.50 atm)`, and
* `c` at `(6.0 L, 0.30 atm)`.

The auxiliary caption's `0.35 atm` readout for `c` conflicts with the image;
the image is explicitly designated as primary evidence.  Work is signed
positive when done by the gas, so work done on the gas is its negative.

Pressure, volume, heat, work, and internal-energy change retain their physical
dimensions.  Real numbers below are explicitly named readouts in atmospheres,
litres, joules, moles, or schematic figure coordinates.
-/

/-! ## Dimensionful quantities and scalar readouts -/

/-- A signed physical volume, with length-cubed dimension. -/
abbrev VolumeQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * L𝓭 * L𝓭) ℝ)

/-- A physical pressure using Physlib's pressure dimension. -/
abbrev PressureQuantity : Type := DimPressure

/-- A signed physical energy using Physlib's energy dimension. -/
abbrev EnergyQuantity : Type := DimEnergy

/-- Read a volume in SI cubic metres. -/
def volumeInCubicMeters (volume : VolumeQuantity) : ℝ :=
  (volume UnitChoices.SI).val

/-- Read a volume in litres, using `1 m³ = 1000 L`. -/
def volumeInLiters (volume : VolumeQuantity) : ℝ :=
  1000 * volumeInCubicMeters volume

/-- Read a pressure in pascals. -/
def pressureInPascals (pressure : PressureQuantity) : ℝ :=
  (pressure UnitChoices.SI).val

/-- Read a pressure in standard atmospheres. -/
def pressureInAtmospheres (pressure : PressureQuantity) : ℝ :=
  pressureInPascals pressure /
    (DimPressure.standardAtmosphere UnitChoices.SI).val

/-- Read a signed physical energy in joules. -/
def energyInJoules (energy : EnergyQuantity) : ℝ :=
  (energy UnitChoices.SI).val / (DimEnergy.joule UnitChoices.SI).val

/-- The exact joule value of one litre-atmosphere. -/
def joulesPerLiterAtmosphere : ℝ := 101325 / 1000

/-! ## Gas, process, and figure labels -/

/-- The thermodynamic model named in the problem statement. -/
inductive GasModel where
  | idealGas
  deriving DecidableEq, Repr

/-- The three labeled states shown on the `pV` diagram. -/
inductive ProcessState where
  | a
  | b
  | c
  deriving DecidableEq, Repr

/-- The two directed legs of the process `a → b → c`. -/
inductive ProcessLeg where
  | aToB
  | bToC
  deriving DecidableEq, Repr

/-- Geometric shape of a process leg in the `pV` plane. -/
inductive PathShape where
  | straightLine
  deriving DecidableEq, Repr

/-- Directions of the two arrows as drawn in the primary figure. -/
inductive PathDirection where
  | verticallyUp
  | diagonallyDownAndRight
  deriving DecidableEq, Repr

/-- Literal labels printed on the two axes and at the origin. -/
inductive AxisLabel where
  | originO
  | pressurePAtmospheres
  | volumeVLiters
  deriving DecidableEq, Repr

/-!
The physical gas process and its figure transcription.

`workByGas` is an independent dimensionful quantity for each leg.  Neither it
nor `internalEnergyChangeAlongABC` is defined to equal a requested answer.
-/
structure IdealGasPVProcess where
  gasModel : GasModel
  amountOfGasMoles : ℝ
  volumeAt : ProcessState → VolumeQuantity
  pressureAt : ProcessState → PressureQuantity
  workByGas : ProcessLeg → EnergyQuantity
  heatIntoGasAlongABC : EnergyQuantity
  internalEnergyChangeAlongABC : EnergyQuantity
  pathStart : ProcessLeg → ProcessState
  pathFinish : ProcessLeg → ProcessState
  pathShape : ProcessLeg → PathShape
  pathDirection : ProcessLeg → PathDirection
  axisLabelVisible : AxisLabel → Bool
  stateLabelVisible : ProcessState → Bool
  gridVisible : Bool
  schematicX : ProcessState → ℝ
  schematicY : ProcessState → ℝ

/-- Work done on the gas, expressed using the opposite sign convention. -/
def workOnGasInJoules
    (setup : IdealGasPVProcess) (leg : ProcessLeg) : ℝ :=
  -energyInJoules (setup.workByGas leg)

/-! ## Figure/data readouts and governing laws -/

/-!
Problem-text data: `0.0175 mol` of ideal gas and `215 J` of heat supplied over
the complete path.  The unknown internal-energy change is not fixed here.
-/
structure HasStatedProblemData (setup : IdealGasPVProcess) : Prop where
  ideal_gas : setup.gasModel = .idealGas
  amount_moles : setup.amountOfGasMoles = 7 / 400
  heat_input_joules : energyInJoules setup.heatIntoGasAlongABC = 215

/-!
Transcription of the primary raster.  In particular, the image puts `c` on
the `0.30 atm` grid line, despite the auxiliary caption's `0.35 atm` claim.
-/
structure MatchesPrimaryPVDiagram (setup : IdealGasPVProcess) : Prop where
  volume_a_liters : volumeInLiters (setup.volumeAt .a) = 2
  pressure_a_atmospheres : pressureInAtmospheres (setup.pressureAt .a) = 1 / 5
  volume_b_liters : volumeInLiters (setup.volumeAt .b) = 2
  pressure_b_atmospheres : pressureInAtmospheres (setup.pressureAt .b) = 1 / 2
  volume_c_liters : volumeInLiters (setup.volumeAt .c) = 6
  pressure_c_atmospheres : pressureInAtmospheres (setup.pressureAt .c) = 3 / 10
  ab_starts_at_a : setup.pathStart .aToB = .a
  ab_finishes_at_b : setup.pathFinish .aToB = .b
  bc_starts_at_b : setup.pathStart .bToC = .b
  bc_finishes_at_c : setup.pathFinish .bToC = .c
  ab_is_straight : setup.pathShape .aToB = .straightLine
  bc_is_straight : setup.pathShape .bToC = .straightLine
  ab_arrow : setup.pathDirection .aToB = .verticallyUp
  bc_arrow : setup.pathDirection .bToC = .diagonallyDownAndRight
  origin_label : setup.axisLabelVisible .originO = true
  pressure_axis_label : setup.axisLabelVisible .pressurePAtmospheres = true
  volume_axis_label : setup.axisLabelVisible .volumeVLiters = true
  label_a : setup.stateLabelVisible .a = true
  label_b : setup.stateLabelVisible .b = true
  label_c : setup.stateLabelVisible .c = true
  background_grid : setup.gridVisible = true
  a_b_same_schematic_x : setup.schematicX .a = setup.schematicX .b
  b_left_of_c : setup.schematicX .b < setup.schematicX .c
  a_below_b : setup.schematicY .a < setup.schematicY .b
  c_below_b : setup.schematicY .c < setup.schematicY .b

/-- Positivity conditions selecting physical pressures, volumes, and gas amount. -/
structure HasPhysicalPVParameters (setup : IdealGasPVProcess) : Prop where
  amount_positive : 0 < setup.amountOfGasMoles
  volume_positive : ∀ state, 0 < volumeInLiters (setup.volumeAt state)
  pressure_positive : ∀ state, 0 < pressureInAtmospheres (setup.pressureAt state)

/-!
Boundary-work law for a straight segment in a `pV` diagram.  Since pressure
varies linearly with volume on such a segment,

`W_by = ((p_start + p_finish) / 2) * (V_finish - V_start)`.

The last factor converts litre-atmospheres to joules.  This is a general law
for either leg and contains none of this problem's numerical answers.
-/
structure SatisfiesStraightPathBoundaryWorkLaw
    (setup : IdealGasPVProcess) : Prop where
  work_for_straight_leg : ∀ leg,
    setup.pathShape leg = .straightLine →
      energyInJoules (setup.workByGas leg) =
        ((pressureInAtmospheres
              (setup.pressureAt (setup.pathStart leg)) +
            pressureInAtmospheres
              (setup.pressureAt (setup.pathFinish leg))) / 2) *
          (volumeInLiters (setup.volumeAt (setup.pathFinish leg)) -
            volumeInLiters (setup.volumeAt (setup.pathStart leg))) *
          joulesPerLiterAtmosphere

/-!
First law of thermodynamics for the complete route, with heat into the gas
and work by the gas positive:

`ΔU = Q_in - (W_ab + W_bc)`.

The law relates three independent dimensionful-energy fields and does not
state the requested numerical internal-energy change.
-/
structure SatisfiesFirstLawAlongABC (setup : IdealGasPVProcess) : Prop where
  first_law :
    energyInJoules setup.internalEnergyChangeAlongABC =
      energyInJoules setup.heatIntoGasAlongABC -
        (energyInJoules (setup.workByGas .aToB) +
          energyInJoules (setup.workByGas .bToC))

/-! ## Requested work values and internal-energy answer -/

/-- Labels of the four displayed internal-energy answer choices. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Joule readout printed beside each answer label. -/
def displayedInternalEnergyJoules : AnswerChoice → ℝ
  | .A => 58
  | .B => 53
  | .C => 33
  | .D => 63

/-- The answer label recorded in the supplied dataset metadata. -/
def recordedAnswerChoice : AnswerChoice := .B

/-- A real energy readout rounds to the displayed whole number of joules. -/
def RoundsToNearestJoule (value displayedValue : ℝ) : Prop :=
  |value - displayedValue| < 1 / 2

/-!
The constant-volume leg does no work.  On `b → c`, the average pressure is
`0.40 atm` and the volume increase is `4.0 L`, so the gas does exactly
`162.12 J = 4053/25 J` of work (and the work on the gas is its negative).
-/
lemma workAlongProcessLegs
    (setup : IdealGasPVProcess)
    (h_figure : MatchesPrimaryPVDiagram setup)
    (h_work : SatisfiesStraightPathBoundaryWorkLaw setup) :
    energyInJoules (setup.workByGas .aToB) = 0 ∧
      workOnGasInJoules setup .aToB = 0 ∧
      energyInJoules (setup.workByGas .bToC) = 4053 / 25 ∧
      workOnGasInJoules setup .bToC = -(4053 / 25) := by
  have h_ab :=
    h_work.work_for_straight_leg .aToB h_figure.ab_is_straight
  rw [h_figure.ab_starts_at_a, h_figure.ab_finishes_at_b,
    h_figure.pressure_a_atmospheres, h_figure.pressure_b_atmospheres,
    h_figure.volume_a_liters, h_figure.volume_b_liters] at h_ab
  norm_num [joulesPerLiterAtmosphere] at h_ab
  have h_bc :=
    h_work.work_for_straight_leg .bToC h_figure.bc_is_straight
  rw [h_figure.bc_starts_at_b, h_figure.bc_finishes_at_c,
    h_figure.pressure_b_atmospheres, h_figure.pressure_c_atmospheres,
    h_figure.volume_b_liters, h_figure.volume_c_liters] at h_bc
  norm_num [joulesPerLiterAtmosphere] at h_bc
  exact ⟨h_ab, by simp [workOnGasInJoules, h_ab],
    h_bc, by simp [workOnGasInJoules, h_bc]⟩

/-!
With `215 J` of heat entering the gas, the first law gives the exact internal
energy increase `215 - 162.12 = 52.88 J = 1322/25 J`, which rounds to the
displayed `53 J` and hence selects recorded answer B.

Blueprint: `thm:physics:phyx_mini_0337:target`.
-/
theorem problem_phyx_mini_0337
    (setup : IdealGasPVProcess)
    (h_data : HasStatedProblemData setup)
    (h_figure : MatchesPrimaryPVDiagram setup)
    (h_physical : HasPhysicalPVParameters setup)
    (h_work : SatisfiesStraightPathBoundaryWorkLaw setup)
    (h_firstLaw : SatisfiesFirstLawAlongABC setup) :
    energyInJoules (setup.workByGas .aToB) = 0 ∧
      workOnGasInJoules setup .aToB = 0 ∧
      energyInJoules (setup.workByGas .bToC) = 4053 / 25 ∧
      workOnGasInJoules setup .bToC = -(4053 / 25) ∧
      energyInJoules setup.internalEnergyChangeAlongABC = 1322 / 25 ∧
      RoundsToNearestJoule
        (energyInJoules setup.internalEnergyChangeAlongABC)
        (displayedInternalEnergyJoules recordedAnswerChoice) := by
  obtain ⟨h_ab, h_on_ab, h_bc, h_on_bc⟩ :=
    workAlongProcessLegs setup h_figure h_work
  have h_internal := h_firstLaw.first_law
  rw [h_data.heat_input_joules, h_ab, h_bc] at h_internal
  norm_num at h_internal
  refine ⟨h_ab, h_on_ab, h_bc, h_on_bc, h_internal, ?_⟩
  rw [h_internal]
  norm_num [RoundsToNearestJoule, displayedInternalEnergyJoules,
    recordedAnswerChoice, abs_of_nonpos]

end PhyXMiniProblems.ProblemPhyXMini0337
