import Mathlib
import Physlib.Units.WithDim.Energy
import Physlib.Units.WithDim.Pressure

/- USER: The assigned source file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0494

open Dimension

/-!
# Heat transfer on the final leg of a pressure--volume cycle

The supplied pressure--volume diagram contains the labeled states `a`, `b`,
`c`, and `d`.  Its arrows show the rectangular cycle
`a → b → c → d → a` and a separate curved path `a → c`.  The image is used as
the primary source for the geometry: horizontal segments are isobaric and
vertical segments are isochoric.  This corrects the reversed constant-variable
descriptions in the auxiliary caption.

Heat is signed positive when added to the gas, and work is signed positive
when done by the gas.  Thus the first law is written `Q = ΔU + W_by`.
Energies, work, heat, pressure, and volume retain physical dimensions through
Physlib.  Real numbers below are only named-unit readouts or displayed answer
values.
-/

/-! ## Dimensionful quantities and named-unit readouts -/

/-- A signed physical volume carrying dimension `L³`. -/
abbrev VolumeQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * L𝓭 * L𝓭) ℝ)

/-- Read a signed physical energy, heat transfer, or work in joules. -/
def energyInJoules (energy : DimEnergy) : ℝ :=
  (energy UnitChoices.SI).val /
    (DimEnergy.joule UnitChoices.SI).val

/-- Read a physical pressure in pascals. -/
def pressureInPascals (pressure : DimPressure) : ℝ :=
  (pressure UnitChoices.SI).val /
    (DimPressure.pascal UnitChoices.SI).val

/-- Read a physical volume in coherent SI cubic metres. -/
def volumeInCubicMeters (volume : VolumeQuantity) : ℝ :=
  (volume UnitChoices.SI).val

/-! ## State, path, and diagram vocabulary -/

/-- The four thermodynamic state labels printed in the diagram. -/
inductive StateLabel where
  | a
  | b
  | c
  | d
  deriving DecidableEq, Fintype, Repr

/--
Directed processes mentioned in the prose or visible in the image.
`aToBToC` names the concatenated path `abc`; it is not an additional edge.
-/
inductive ProcessPath where
  | curvedAToC
  | aToB
  | bToC
  | cToD
  | dToA
  | aToBToC
  deriving DecidableEq, Fintype, Repr

/-- Initial state of each directed process. -/
def pathStart : ProcessPath → StateLabel
  | .curvedAToC => .a
  | .aToB => .a
  | .bToC => .b
  | .cToD => .c
  | .dToA => .d
  | .aToBToC => .a

/-- Final state of each directed process. -/
def pathFinish : ProcessPath → StateLabel
  | .curvedAToC => .c
  | .aToB => .b
  | .bToC => .c
  | .cToD => .d
  | .dToA => .a
  | .aToBToC => .c

/-- Geometric appearance of a process in the primary pressure--volume plot. -/
inductive PathGeometry where
  | curvedSegment
  | horizontalSegment
  | verticalSegment
  | twoSegmentComposite
  deriving DecidableEq, Repr

/-- Thermodynamic constraint represented by a path. -/
inductive ProcessKind where
  | generalCurved
  | isobaric
  | isochoric
  | composite
  deriving DecidableEq, Repr

/-- Geometry read from the primary image. -/
def displayedPathGeometry : ProcessPath → PathGeometry
  | .curvedAToC => .curvedSegment
  | .aToB => .horizontalSegment
  | .bToC => .verticalSegment
  | .cToD => .horizontalSegment
  | .dToA => .verticalSegment
  | .aToBToC => .twoSegmentComposite

/-- Process kinds determined by the axes and segment orientations. -/
def displayedProcessKind : ProcessPath → ProcessKind
  | .curvedAToC => .generalCurved
  | .aToB => .isobaric
  | .bToC => .isochoric
  | .cToD => .isobaric
  | .dToA => .isochoric
  | .aToBToC => .composite

/-- Physical quantity assigned to one of the two plotted axes. -/
inductive AxisQuantity where
  | volume
  | pressure
  deriving DecidableEq, Repr

/-- A dimensionful equilibrium state of the gas. -/
structure ThermodynamicState where
  pressure : DimPressure
  volume : VolumeQuantity

/-- Qualitative and dimensionful content of the supplied `P`--`V` diagram. -/
structure PVDiagram where
  stateAt : StateLabel → ThermodynamicState
  horizontalAxisQuantity : AxisQuantity
  verticalAxisQuantity : AxisQuantity
  originLabelVisible : Bool
  stateLabelVisible : StateLabel → Bool
  pathArrowVisible : ProcessPath → Bool
  pathGeometry : ProcessPath → PathGeometry

/-!
The gas system and its thermodynamic observables.  Heat and work are kept as
independent dimensionful physical quantities.  Internal energy is a state
function, rather than a separately assignable change on each path.
-/
structure GasPVExperiment where
  diagram : PVDiagram
  internalEnergyAt : StateLabel → DimEnergy
  workDoneByGasOn : ProcessPath → DimEnergy
  heatAddedToGasOn : ProcessPath → DimEnergy
  processKind : ProcessPath → ProcessKind

/-- Joule readout of the internal energy at a labeled state. -/
def internalEnergyInJoules
    (setup : GasPVExperiment) (state : StateLabel) : ℝ :=
  energyInJoules (setup.internalEnergyAt state)

/-- Endpoint-defined internal-energy change `U_finish - U_start`, in joules. -/
def internalEnergyChangeInJoules
    (setup : GasPVExperiment) (path : ProcessPath) : ℝ :=
  internalEnergyInJoules setup (pathFinish path) -
    internalEnergyInJoules setup (pathStart path)

/-- Signed joule readout of work done by the gas on a directed path. -/
def workDoneByGasInJoules
    (setup : GasPVExperiment) (path : ProcessPath) : ℝ :=
  energyInJoules (setup.workDoneByGasOn path)

/-- Signed joule readout of heat added to the gas on a directed path. -/
def heatAddedToGasInJoules
    (setup : GasPVExperiment) (path : ProcessPath) : ℝ :=
  energyInJoules (setup.heatAddedToGasOn path)

/-! ## Assumptions: stated data, primary-image readouts, and physical laws -/

/-!
The numeric data stated in the problem.  In particular, this structure does
not assign any heat to `d → a`.
-/
structure MatchesProblemStatement (setup : GasPVExperiment) : Prop where
  curved_a_to_c_work_joules :
    workDoneByGasInJoules setup .curvedAToC = -35
  curved_a_to_c_heat_joules :
    heatAddedToGasInJoules setup .curvedAToC = -175
  path_abc_work_joules :
    workDoneByGasInJoules setup .aToBToC = -56
  internal_energy_d_minus_c_joules :
    internalEnergyInJoules setup .d -
      internalEnergyInJoules setup .c = 42

/-!
Transcription of the primary bitmap.  The four rectangle edges and the curved
`a → c` path carry visible arrows.  Equal-coordinate and strict-order fields
record the relative point locations even though the image supplies no numeric
pressure or volume scale.
-/
structure MatchesPrimaryPVDiagram (setup : GasPVExperiment) : Prop where
  horizontal_axis_is_volume :
    setup.diagram.horizontalAxisQuantity = .volume
  vertical_axis_is_pressure :
    setup.diagram.verticalAxisQuantity = .pressure
  origin_is_labeled : setup.diagram.originLabelVisible = true
  every_state_label_is_visible :
    ∀ state, setup.diagram.stateLabelVisible state = true
  curved_a_to_c_arrow_is_visible :
    setup.diagram.pathArrowVisible .curvedAToC = true
  a_to_b_arrow_is_visible :
    setup.diagram.pathArrowVisible .aToB = true
  b_to_c_arrow_is_visible :
    setup.diagram.pathArrowVisible .bToC = true
  c_to_d_arrow_is_visible :
    setup.diagram.pathArrowVisible .cToD = true
  d_to_a_arrow_is_visible :
    setup.diagram.pathArrowVisible .dToA = true
  displayed_geometries_agree :
    ∀ path, setup.diagram.pathGeometry path = displayedPathGeometry path
  displayed_process_kinds_agree :
    ∀ path, setup.processKind path = displayedProcessKind path
  top_states_have_equal_pressure :
    pressureInPascals (setup.diagram.stateAt .a).pressure =
      pressureInPascals (setup.diagram.stateAt .b).pressure
  bottom_states_have_equal_pressure :
    pressureInPascals (setup.diagram.stateAt .c).pressure =
      pressureInPascals (setup.diagram.stateAt .d).pressure
  bottom_pressure_is_less_than_top_pressure :
    pressureInPascals (setup.diagram.stateAt .c).pressure <
      pressureInPascals (setup.diagram.stateAt .a).pressure
  right_states_have_equal_volume :
    volumeInCubicMeters (setup.diagram.stateAt .a).volume =
      volumeInCubicMeters (setup.diagram.stateAt .d).volume
  left_states_have_equal_volume :
    volumeInCubicMeters (setup.diagram.stateAt .b).volume =
      volumeInCubicMeters (setup.diagram.stateAt .c).volume
  left_volume_is_less_than_right_volume :
    volumeInCubicMeters (setup.diagram.stateAt .b).volume <
      volumeInCubicMeters (setup.diagram.stateAt .a).volume
  every_pressure_is_positive :
    ∀ state, 0 < pressureInPascals (setup.diagram.stateAt state).pressure
  every_volume_is_positive :
    ∀ state, 0 < volumeInCubicMeters (setup.diagram.stateAt state).volume

/-!
Macroscopic laws used by the intended calculation.

* The first law uses heat into the gas and work done by the gas:
  `Q = (U_finish - U_start) + W_by`.
* Boundary work vanishes for any isochoric process.
* Work and heat are additive on the specifically named concatenated path
  `a → b → c`.

These are general governing relations.  No field fixes the requested heat on
`d → a` or mentions an answer choice.
-/
structure ObeysThermodynamicLaws (setup : GasPVExperiment) : Prop where
  first_law : ∀ path,
    heatAddedToGasInJoules setup path =
      internalEnergyChangeInJoules setup path +
        workDoneByGasInJoules setup path
  isochoric_work_is_zero : ∀ path,
    setup.processKind path = .isochoric →
      workDoneByGasInJoules setup path = 0
  work_is_additive_on_abc :
    workDoneByGasInJoules setup .aToBToC =
      workDoneByGasInJoules setup .aToB +
        workDoneByGasInJoules setup .bToC
  heat_is_additive_on_abc :
    heatAddedToGasInJoules setup .aToBToC =
      heatAddedToGasInJoules setup .aToB +
        heatAddedToGasInJoules setup .bToC

/-! ## Recorded multiple-choice metadata and physically supported target -/

/-- Displayed answer-choice labels. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Joule values printed beside the four answer choices. -/
def displayedAnswerInJoules : AnswerChoice → ℝ
  | .A => 21
  | .B => 19
  | .C => 13
  | .D => 16

/-- The dataset records choice `D`; this is metadata, not a physics premise. -/
def recordedAnswerChoice : AnswerChoice := .D

/--
Blueprint target `thm:physics:phyx_mini_0494:target`: the heat added to the gas
on `d → a` is `98 J` under the stated sign convention and the geometry in the
primary image.

Indeed, the curved `a → c` data and the first law give `U_c - U_a = -140 J`.
Together with `U_d - U_c = 42 J`, this gives `U_a - U_d = 98 J`.  The primary
image makes `d → a` isochoric, so its work is zero and the first law gives the
claimed heat.  The dataset's recorded choice `D = 16 J` is retained above only
as metadata because it contradicts these source data and governing laws.

The target is intentionally kept out of all premise structures.
-/
theorem heat_added_on_d_to_a_is_ninety_eight_joules
    (setup : GasPVExperiment)
    (hProblem : MatchesProblemStatement setup)
    (hFigure : MatchesPrimaryPVDiagram setup)
    (hLaws : ObeysThermodynamicLaws setup) :
    heatAddedToGasInJoules setup .dToA = 98 := by
  have hCurvedFirstLaw := hLaws.first_law .curvedAToC
  have hDtoAFirstLaw := hLaws.first_law .dToA
  have hDtoAIsIsochoric : setup.processKind .dToA = .isochoric := by
    rw [hFigure.displayed_process_kinds_agree]
    rfl
  have hDtoAWorkIsZero :=
    hLaws.isochoric_work_is_zero .dToA hDtoAIsIsochoric
  simp only [internalEnergyChangeInJoules, pathFinish, pathStart] at hCurvedFirstLaw hDtoAFirstLaw
  rw [hProblem.curved_a_to_c_heat_joules,
      hProblem.curved_a_to_c_work_joules] at hCurvedFirstLaw
  rw [hDtoAWorkIsZero] at hDtoAFirstLaw
  linarith [hProblem.internal_energy_d_minus_c_joules]

end PhyXMiniProblems.ProblemPhyXMini0494
