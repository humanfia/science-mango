import Mathlib.Data.Real.Basic
import Physlib.Thermodynamics.Temperature.Basic
import Physlib.Units.WithDim.Pressure

/-!
# Volume at the end of an isothermal ideal-gas segment

This file formalizes problem `phyx_mini_0343`.  The primary figure is a
pressure--volume diagram for `0.0040 mol` of ideal molecular hydrogen.  Its
directed cycle runs from `a` to `b`, then along the isothermal curve from `b`
to `c`, and finally from `c` back to `a`.

Pressure, volume, and temperature are physical quantities.  Real numbers are
used only for readouts in the units printed on the figure (atmospheres and
litres), the amount readout in moles, and answer-choice values.
-/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0343

open Dimension

/-! ## Dimensionful quantities and named-unit readouts -/

/-- Physical pressure, represented by Physlib's dimensionful pressure type. -/
abbrev PressureQuantity : Type := DimPressure

/-- A nonnegative physical volume with dimension `length ^ 3`. -/
abbrev VolumeQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * L𝓭 * L𝓭) NNReal)

/-- Absolute thermodynamic temperature. -/
abbrev TemperatureQuantity : Type := Temperature

/-- Coherent-SI pressure readout in pascals. -/
def pressureInPascals (pressure : PressureQuantity) : ℝ :=
  (pressure UnitChoices.SI).val

/-!
Pressure readout in standard atmospheres.  The denominator is Physlib's
dimensionful standard-atmosphere constant, rather than an untyped conversion
factor hidden in the model.
-/
def pressureInAtmospheres (pressure : PressureQuantity) : ℝ :=
  pressureInPascals pressure /
    pressureInPascals DimPressure.standardAtmosphere

/-- Volume readout in litres; one cubic metre is one thousand litres. -/
def volumeInLiters (volume : VolumeQuantity) : ℝ :=
  1000 * ((volume UnitChoices.SI).val : ℝ)

/-!
Numerical readout of absolute temperature in the common temperature unit used
by the molar gas constant below.  Only equality of the `b` and `c` readings is
needed by this problem.
-/
def temperatureReadout (temperature : TemperatureQuantity) : ℝ :=
  Temperature.toReal temperature

/-! ## Gas identity, diagram labels, and directed geometry -/

/-- Chemical species named in the problem statement. -/
inductive ChemicalSpecies where
  | molecularHydrogen
  deriving DecidableEq, Repr

/-- Equation-of-state model specified by the word “ideal”. -/
inductive EquationOfStateModel where
  | idealGas
  deriving DecidableEq, Repr

/-!
The physical gas sample.  `amountInMoles` is an explicitly unit-labelled
scalar readout, not a replacement type for the sample itself.
-/
structure GasSample where
  species : ChemicalSpecies
  equationOfState : EquationOfStateModel
  amountInMoles : ℝ

/-- The three labelled thermodynamic states in the primary figure. -/
inductive DiagramPoint where
  | a
  | b
  | c
  deriving DecidableEq, Repr

/-- The three directed process segments in cycle order. -/
inductive DiagramSegment where
  | ab
  | bc
  | ca
  deriving DecidableEq, Repr

/-- Initial endpoint of each arrow in the depicted cycle. -/
def DiagramSegment.startPoint : DiagramSegment → DiagramPoint
  | .ab => .a
  | .bc => .b
  | .ca => .c

/-- Final endpoint of each arrow in the depicted cycle. -/
def DiagramSegment.endPoint : DiagramSegment → DiagramPoint
  | .ab => .b
  | .bc => .c
  | .ca => .a

/-- Qualitative shapes of process segments shown in the bitmap. -/
inductive SegmentShape where
  | vertical
  | curved
  | horizontal
  deriving DecidableEq, Repr

/-- Pressure, volume, and temperature at one labelled state. -/
structure ThermodynamicState where
  pressure : PressureQuantity
  volume : VolumeQuantity
  temperature : TemperatureQuantity

/-!
The gas, its three states, and the qualitative geometry of the displayed
cycle.  The gas constant is a readout in litre-atmospheres per mole per the
temperature unit used by `temperatureReadout`.
-/
structure IdealHydrogenPVCycle where
  gas : GasSample
  state : DiagramPoint → ThermodynamicState
  segmentShape : DiagramSegment → SegmentShape
  gasConstantLiterAtmospherePerMoleTemperatureUnit : ℝ

/-! ## Problem statement and primary-figure readouts -/

/-!
Data stated in the prose or read directly from the primary bitmap.  Point
`c`'s pressure and its qualitative position are included, but its requested
volume is deliberately not assigned a numerical value here.
-/
structure MatchesProblemAndFigure (setup : IdealHydrogenPVCycle) : Prop where
  gasIsMolecularHydrogen : setup.gas.species = .molecularHydrogen
  gasUsesIdealEquationOfState : setup.gas.equationOfState = .idealGas
  gasAmountMoles : setup.gas.amountInMoles = (4 : ℝ) / 1000
  pressureAtAAtmospheres :
    pressureInAtmospheres (setup.state .a).pressure = (1 : ℝ) / 2
  volumeAtALiters :
    volumeInLiters (setup.state .a).volume = (1 : ℝ) / 5
  pressureAtBAtmospheres :
    pressureInAtmospheres (setup.state .b).pressure = 2
  volumeAtBLiters :
    volumeInLiters (setup.state .b).volume = (1 : ℝ) / 5
  pressureAtCAtmospheres :
    pressureInAtmospheres (setup.state .c).pressure = (1 : ℝ) / 2
  pointCIsRightOfPointA :
    volumeInLiters (setup.state .a).volume <
      volumeInLiters (setup.state .c).volume
  segmentABIsVertical : setup.segmentShape .ab = .vertical
  segmentBCIsCurved : setup.segmentShape .bc = .curved
  segmentCAIsHorizontal : setup.segmentShape .ca = .horizontal
  temperatureConstantAlongBC :
    (setup.state .b).temperature = (setup.state .c).temperature

/-! ## Physical-domain conditions and governing law -/

/-- Positivity conditions selecting physically meaningful gas states. -/
structure HasPhysicalIdealGasParameters
    (setup : IdealHydrogenPVCycle) : Prop where
  amountPositive : 0 < setup.gas.amountInMoles
  gasConstantPositive :
    0 < setup.gasConstantLiterAtmospherePerMoleTemperatureUnit
  pressurePositive : ∀ point : DiagramPoint,
    0 < pressureInAtmospheres (setup.state point).pressure
  volumePositive : ∀ point : DiagramPoint,
    0 < volumeInLiters (setup.state point).volume
  temperaturePositive : ∀ point : DiagramPoint,
    0 < temperatureReadout (setup.state point).temperature

/-!
The molar ideal-gas equation `p V = n R T`, stated at every labelled state in
the units used by the figure.  This is a general governing law and contains no
numerical value for the requested volume at `c`.
-/
structure SatisfiesMolarIdealGasLaw
    (setup : IdealHydrogenPVCycle) : Prop where
  idealGasLawAt : ∀ point : DiagramPoint,
    pressureInAtmospheres (setup.state point).pressure *
        volumeInLiters (setup.state point).volume =
      setup.gas.amountInMoles *
        setup.gasConstantLiterAtmospherePerMoleTemperatureUnit *
          temperatureReadout (setup.state point).temperature

/-! ## Isothermal consequence and displayed answer -/

/-!
Along the isothermal segment `b c`, the common sample obeying the ideal-gas
law has equal pressure--volume products at the endpoints.
-/
lemma pressureVolumeProduct_eq_alongBC
    (setup : IdealHydrogenPVCycle)
    (_problem : MatchesProblemAndFigure setup)
    (_physical : HasPhysicalIdealGasParameters setup)
    (_idealGas : SatisfiesMolarIdealGasLaw setup) :
    pressureInAtmospheres (setup.state .b).pressure *
        volumeInLiters (setup.state .b).volume =
      pressureInAtmospheres (setup.state .c).pressure *
        volumeInLiters (setup.state .c).volume := by
  calc
    pressureInAtmospheres (setup.state .b).pressure *
          volumeInLiters (setup.state .b).volume =
        setup.gas.amountInMoles *
          setup.gasConstantLiterAtmospherePerMoleTemperatureUnit *
            temperatureReadout (setup.state .b).temperature :=
      _idealGas.idealGasLawAt .b
    _ = setup.gas.amountInMoles *
          setup.gasConstantLiterAtmospherePerMoleTemperatureUnit *
            temperatureReadout (setup.state .c).temperature := by
      rw [_problem.temperatureConstantAlongBC]
    _ = pressureInAtmospheres (setup.state .c).pressure *
          volumeInLiters (setup.state .c).volume :=
      (_idealGas.idealGasLawAt .c).symm

/-- Labels of the four displayed answer choices. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Volume in litres printed beside each answer label. -/
def AnswerChoice.liters : AnswerChoice → ℝ
  | .A => 83 / 100
  | .B => 4 / 5
  | .C => 9 / 10
  | .D => 9 / 5

/-- The answer label recorded in the supplied dataset metadata. -/
def recordedAnswerChoice : AnswerChoice := .B

/-!
The `b c` isotherm gives
`(2 atm) * (0.20 L) = (0.50 atm) * V_c`, hence `V_c = 0.8 L`,
which is displayed choice B.

This formalizes blueprint label `thm:physics:phyx_mini_0343:target`.
-/
theorem volumeAtPointC_matches_recordedAnswerB
    (setup : IdealHydrogenPVCycle)
    (_problem : MatchesProblemAndFigure setup)
    (_physical : HasPhysicalIdealGasParameters setup)
    (_idealGas : SatisfiesMolarIdealGasLaw setup) :
    volumeInLiters (setup.state .c).volume = (4 : ℝ) / 5 ∧
      volumeInLiters (setup.state .c).volume = recordedAnswerChoice.liters := by
  have hproduct :=
    pressureVolumeProduct_eq_alongBC setup _problem _physical _idealGas
  rw [_problem.pressureAtBAtmospheres, _problem.volumeAtBLiters,
    _problem.pressureAtCAtmospheres] at hproduct
  have hvolume :
      volumeInLiters (setup.state .c).volume = (4 : ℝ) / 5 := by
    linarith
  exact ⟨hvolume, by
    simpa [recordedAnswerChoice, AnswerChoice.liters] using hvolume⟩

end PhyXMiniProblems.ProblemPhyXMini0343
