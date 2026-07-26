import Mathlib
import Physlib.Units.WithDim.Basic

/- USER: The assigned Lean file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0984

open Dimension

/-!
# Currents in a switched parallel resistor--inductor circuit

The primary raster `984.png` shows an ideal battery and switch feeding two
parallel branches.  The middle branch consists of `R₁`; the right branch
consists of `R₂` in series with `L`.  The arrows label the source current `i₁`,
the `R₁`-branch current `i₂`, and the `R₂`--`L` branch current `i₃`.

The source text supplies `L = 0.300 H`, `R₁ = 12.0 Ω`, `R₂ = 16.0 Ω`, and
`ε = 96.0 V`, and says that the switch closes at `t = 0`.  Physical component
values and currents are represented by unit-independent Physlib
`Dimensionful` quantities.  The real argument of a trajectory is explicitly
time in seconds, and real values otherwise occur only at coherent-SI readout
boundaries or in literal source data.

Assumption/target split:

* governing laws: ideal-source voltage clamping, Ohm's laws for `R₁` and
  `R₂`, Kirchhoff's current and voltage laws, `v_L = L di₃/dt`, convergence to
  a steady current, and the zero-inductor-voltage steady-state relation;
* previous-part results: none;
* figure/data readouts: the labelled parallel topology and arrow directions,
  the two negligible parasitic resistances, the switch closing at `t = 0`,
  and the four stated component values;
* current target conclusion: at a nonnegative time when `i₃` is half its
  final value, `i₂ = 8 A`.

The supplied metadata records choice B, `11.0 A`, for a question that asks for
`i₂`.  In the ideal circuit shown, `i₂ = ε / R₁ = 8 A` at every post-switch
time, while `i₁ = i₂ + i₃ = 11 A` at the specified event.  The target follows
the quantity actually asked for and retains choice B only as dataset metadata;
this makes the apparent `i₁`/`i₂` source-label mismatch explicit without
building the recorded answer into a premise or conclusion.
-/

/-! ## Physical dimensions, quantities, and coherent-SI readouts -/

/-- Electric current has physical dimension charge per time. -/
def electricCurrentDimension : Dimension :=
  C𝓭 * T𝓭⁻¹

/-- Electric potential difference has physical dimension energy per charge. -/
def electricPotentialDimension : Dimension :=
  M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹ * C𝓭⁻¹

/-- Electrical resistance has physical dimension voltage per current. -/
def electricalResistanceDimension : Dimension :=
  electricPotentialDimension * electricCurrentDimension⁻¹

/-- Electrical inductance has physical dimension resistance times time. -/
def electricalInductanceDimension : Dimension :=
  electricalResistanceDimension * T𝓭

/-- A signed, unit-independent physical electric current. -/
abbrev ElectricCurrentQuantity : Type :=
  Dimensionful (WithDim electricCurrentDimension ℝ)

/-- A signed, unit-independent physical potential difference. -/
abbrev ElectricPotentialQuantity : Type :=
  Dimensionful (WithDim electricPotentialDimension ℝ)

/-- A nonnegative, unit-independent physical resistance magnitude. -/
abbrev ResistanceMagnitude : Type :=
  Dimensionful (WithDim electricalResistanceDimension NNReal)

/-- A nonnegative, unit-independent physical inductance magnitude. -/
abbrev InductanceMagnitude : Type :=
  Dimensionful (WithDim electricalInductanceDimension NNReal)

/-- Coherent-SI readout of a signed dimensionful quantity. -/
def signedSIReadout {dimension : Dimension}
    (quantity : Dimensionful (WithDim dimension ℝ)) : ℝ :=
  (quantity UnitChoices.SI).val

/-- Coherent-SI readout of a nonnegative dimensionful quantity. -/
def nonnegativeSIReadout {dimension : Dimension}
    (quantity : Dimensionful (WithDim dimension NNReal)) : ℝ :=
  ((quantity UnitChoices.SI).val : ℝ)

/-- Read a signed current in amperes, positive along its labelled arrow. -/
def currentInAmperes (current : ElectricCurrentQuantity) : ℝ :=
  signedSIReadout current

/-- Read an oriented potential difference in volts. -/
def potentialInVolts (potential : ElectricPotentialQuantity) : ℝ :=
  signedSIReadout potential

/-- Read a resistance magnitude in ohms. -/
def resistanceInOhms (resistance : ResistanceMagnitude) : ℝ :=
  nonnegativeSIReadout resistance

/-- Read an inductance magnitude in henries. -/
def inductanceInHenries (inductance : InductanceMagnitude) : ℝ :=
  nonnegativeSIReadout inductance

/-! ## Circuit roles and primary-raster geometry -/

/-- Electrically distinct nodes needed to express the raster's topology. -/
inductive CircuitNode where
  | sourcePositive
  | topJunction
  | rightMidpoint
  | bottomReturn
  deriving DecidableEq, Fintype, Repr

/-- The five labelled components visible in the supplied schematic. -/
inductive CircuitElement where
  | battery
  | switchS
  | resistorR1
  | resistorR2
  | inductorL
  deriving DecidableEq, Fintype, Repr

/-- The three current labels printed beside purple arrows in the raster. -/
inductive CurrentSymbol where
  | i1
  | i2
  | i3
  deriving DecidableEq, Fintype, Repr

/-- Screen directions of the three current arrows. -/
inductive ArrowDirection where
  | upward
  | downward
  | rightward
  deriving DecidableEq, Repr

/-- State of the switch as a function of the time coordinate in seconds. -/
inductive SwitchState where
  | open
  | closed
  deriving DecidableEq, Repr

/-- Idealized physical roles assigned to the five component symbols. -/
inductive ComponentModel where
  | idealVoltageSource
  | idealSwitch
  | idealOhmicResistor
  | idealInductor
  deriving DecidableEq, Repr

/-!
Literal qualitative information transcribed from image `984.png`.  Ordered
terminal pairs follow the positive directions of the labelled currents and
voltage drops used below.
-/
structure ParallelRLFigure where
  componentSymbolShown : CircuitElement → Bool
  currentLabelShown : CurrentSymbol → Bool
  elementTerminals : CircuitElement → CircuitNode × CircuitNode
  currentArrowElement : CurrentSymbol → CircuitElement
  currentArrowDirection : CurrentSymbol → ArrowDirection
  batteryPositiveTerminalAtTop : Bool
  resistorR1IsMiddleVerticalBranch : Bool
  resistorR2AboveInductorOnRightBranch : Bool
  resistorR1ParallelToSeriesR2InductorBranch : Bool

/-!
Independent physical objects and time-dependent observables of the circuit.
Every real trajectory argument is elapsed time in seconds.  In particular,
the final `i₃` current is independent setup data constrained by convergence
and steady-state laws rather than defined from the requested numerical value.
-/
structure ParallelRLTransientSetup where
  figure : ParallelRLFigure
  componentModel : CircuitElement → ComponentModel
  resistorR1 : ResistanceMagnitude
  resistorR2 : ResistanceMagnitude
  inductanceL : InductanceMagnitude
  batteryInternalResistance : ResistanceMagnitude
  inductorWindingResistance : ResistanceMagnitude
  batteryEmf : ElectricPotentialQuantity
  switchStateAtSeconds : ℝ → SwitchState
  currentI1AtSeconds : ℝ → ElectricCurrentQuantity
  currentI2AtSeconds : ℝ → ElectricCurrentQuantity
  currentI3AtSeconds : ℝ → ElectricCurrentQuantity
  finalCurrentI3 : ElectricCurrentQuantity
  voltageAcrossR1AtSeconds : ℝ → ElectricPotentialQuantity
  voltageAcrossR2AtSeconds : ℝ → ElectricPotentialQuantity
  voltageAcrossInductorAtSeconds : ℝ → ElectricPotentialQuantity

/-! ## Figure evidence and stated problem data -/

/-- The topology, labels, and arrow directions visible in the primary bitmap. -/
structure MatchesPrimaryParallelRLFigure
    (setup : ParallelRLTransientSetup) : Prop where
  everyComponentSymbolShown : ∀ element,
    setup.figure.componentSymbolShown element = true
  everyCurrentLabelShown : ∀ symbol,
    setup.figure.currentLabelShown symbol = true
  batteryTerminals :
    setup.figure.elementTerminals .battery =
      (.bottomReturn, .sourcePositive)
  switchTerminals :
    setup.figure.elementTerminals .switchS =
      (.sourcePositive, .topJunction)
  resistorR1Terminals :
    setup.figure.elementTerminals .resistorR1 =
      (.topJunction, .bottomReturn)
  resistorR2Terminals :
    setup.figure.elementTerminals .resistorR2 =
      (.topJunction, .rightMidpoint)
  inductorTerminals :
    setup.figure.elementTerminals .inductorL =
      (.rightMidpoint, .bottomReturn)
  i1RunsThroughBattery :
    setup.figure.currentArrowElement .i1 = .battery
  i2RunsThroughR1 :
    setup.figure.currentArrowElement .i2 = .resistorR1
  i3RunsThroughR2LBranch :
    setup.figure.currentArrowElement .i3 = .resistorR2
  i1PointsUp : setup.figure.currentArrowDirection .i1 = .upward
  i2PointsDown : setup.figure.currentArrowDirection .i2 = .downward
  i3PointsRight : setup.figure.currentArrowDirection .i3 = .rightward
  batteryPolarity : setup.figure.batteryPositiveTerminalAtTop = true
  r1Placement : setup.figure.resistorR1IsMiddleVerticalBranch = true
  r2AndInductorPlacement :
    setup.figure.resistorR2AboveInductorOnRightBranch = true
  parallelBranchTopology :
    setup.figure.resistorR1ParallelToSeriesR2InductorBranch = true

/-- Scalar labels stated in the prose, with their units fixed by field names. -/
structure StatedProblemData where
  resistorR1LabelOhms : ℝ
  resistorR2LabelOhms : ℝ
  inductanceLabelHenries : ℝ
  batteryEmfLabelVolts : ℝ
  switchClosingTimeSeconds : ℝ

/-!
The prose data and their calibration to independent dimensionful physical
objects.  The zero parasitic resistances formalize the stated negligible
battery internal resistance and negligible inductor winding resistance.
-/
structure MatchesStatedProblemData
    (setup : ParallelRLTransientSetup) (data : StatedProblemData) : Prop where
  resistorR1Label : data.resistorR1LabelOhms = 12
  resistorR2Label : data.resistorR2LabelOhms = 16
  inductanceLabel : data.inductanceLabelHenries = 3 / 10
  batteryEmfLabel : data.batteryEmfLabelVolts = 96
  switchingTimeLabel : data.switchClosingTimeSeconds = 0
  resistorR1Calibration :
    resistanceInOhms setup.resistorR1 = data.resistorR1LabelOhms
  resistorR2Calibration :
    resistanceInOhms setup.resistorR2 = data.resistorR2LabelOhms
  inductanceCalibration :
    inductanceInHenries setup.inductanceL = data.inductanceLabelHenries
  batteryEmfCalibration :
    potentialInVolts setup.batteryEmf = data.batteryEmfLabelVolts
  batteryInternalResistanceNegligible :
    resistanceInOhms setup.batteryInternalResistance = 0
  inductorWindingResistanceNegligible :
    resistanceInOhms setup.inductorWindingResistance = 0
  switchOpenBeforeClosing : ∀ timeInSeconds,
    timeInSeconds < data.switchClosingTimeSeconds →
      setup.switchStateAtSeconds timeInSeconds = .open
  switchClosedFromClosingTime : ∀ timeInSeconds,
    data.switchClosingTimeSeconds ≤ timeInSeconds →
      setup.switchStateAtSeconds timeInSeconds = .closed

/-- Assignment of the standard ideal lumped-element models stated in prose. -/
structure MatchesIdealParallelRLScenario
    (setup : ParallelRLTransientSetup) : Prop where
  batteryModel : setup.componentModel .battery = .idealVoltageSource
  switchModel : setup.componentModel .switchS = .idealSwitch
  resistorR1Model : setup.componentModel .resistorR1 = .idealOhmicResistor
  resistorR2Model : setup.componentModel .resistorR2 = .idealOhmicResistor
  inductorModel : setup.componentModel .inductorL = .idealInductor

/-- Positivity and sign conditions for the nondegenerate passive circuit. -/
structure HasPhysicalParallelRLParameters
    (setup : ParallelRLTransientSetup) : Prop where
  resistorR1Positive : 0 < resistanceInOhms setup.resistorR1
  resistorR2Positive : 0 < resistanceInOhms setup.resistorR2
  inductancePositive : 0 < inductanceInHenries setup.inductanceL
  emfPositive : 0 < potentialInVolts setup.batteryEmf
  finalCurrentI3Nonnegative : 0 ≤ currentInAmperes setup.finalCurrentI3

/-! ## Governing circuit laws -/

/-!
Generic transient and steady-state laws for the ideal switched parallel RL
circuit.  No field states either requested numerical current.  The final
current is connected to the trajectory both by a genuine limit and by the
zero-inductor-voltage steady-state Kirchhoff relation.
-/
structure SatisfiesIdealParallelRLTransientLaws
    (setup : ParallelRLTransientSetup) : Prop where
  sourceClampsR1BranchVoltage : ∀ timeInSeconds,
    0 ≤ timeInSeconds →
      potentialInVolts (setup.voltageAcrossR1AtSeconds timeInSeconds) =
        potentialInVolts setup.batteryEmf
  resistorR1OhmLaw : ∀ timeInSeconds,
    0 ≤ timeInSeconds →
      potentialInVolts (setup.voltageAcrossR1AtSeconds timeInSeconds) =
        currentInAmperes (setup.currentI2AtSeconds timeInSeconds) *
          resistanceInOhms setup.resistorR1
  resistorR2OhmLaw : ∀ timeInSeconds,
    0 ≤ timeInSeconds →
      potentialInVolts (setup.voltageAcrossR2AtSeconds timeInSeconds) =
        currentInAmperes (setup.currentI3AtSeconds timeInSeconds) *
          resistanceInOhms setup.resistorR2
  inductorConstitutiveLaw : ∀ timeInSeconds,
    0 < timeInSeconds →
      ∃ derivativeAmperesPerSecond : ℝ,
        HasDerivAt
            (fun time : ℝ =>
              currentInAmperes (setup.currentI3AtSeconds time))
            derivativeAmperesPerSecond timeInSeconds ∧
          potentialInVolts
              (setup.voltageAcrossInductorAtSeconds timeInSeconds) =
            inductanceInHenries setup.inductanceL *
              derivativeAmperesPerSecond
  rightBranchKirchhoffVoltageLaw : ∀ timeInSeconds,
    0 ≤ timeInSeconds →
      potentialInVolts setup.batteryEmf =
        potentialInVolts (setup.voltageAcrossR2AtSeconds timeInSeconds) +
          potentialInVolts
            (setup.voltageAcrossInductorAtSeconds timeInSeconds)
  topJunctionKirchhoffCurrentLaw : ∀ timeInSeconds,
    0 ≤ timeInSeconds →
      currentInAmperes (setup.currentI1AtSeconds timeInSeconds) =
        currentInAmperes (setup.currentI2AtSeconds timeInSeconds) +
          currentInAmperes (setup.currentI3AtSeconds timeInSeconds)
  inductorCurrentInitiallyZero :
    currentInAmperes (setup.currentI3AtSeconds 0) = 0
  inductorCurrentTendsToFinalValue :
    Filter.Tendsto
      (fun time : ℝ =>
        currentInAmperes (setup.currentI3AtSeconds time))
      Filter.atTop
      (nhds (currentInAmperes setup.finalCurrentI3))
  finalSteadyStateRightBranchLaw :
    potentialInVolts setup.batteryEmf =
      currentInAmperes setup.finalCurrentI3 *
        resistanceInOhms setup.resistorR2

/-! ## Displayed answer choices and physically grounded conclusion -/

/-- Labels of the four current-valued answer choices printed with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- The current magnitude printed beside each answer choice, in amperes. -/
def AnswerChoice.displayedCurrentInAmperes : AnswerChoice → ℝ
  | .A => 5
  | .B => 11
  | .C => 3
  | .D => 6

/-- The answer label recorded in the supplied dataset metadata. -/
def recordedDatasetAnswer : AnswerChoice := .B

/-!
Blueprint label: `thm:physics:phyx_mini_0984:target`.

At any nonnegative time when `i₃` has half its final value, the ideal battery
still places `96 V` across `R₁`, so the current asked for in the prose is
`i₂ = 96/12 = 8 A`.  Separately, the same laws imply that the final
right-branch current is `96/16 = 6 A`, hence `i₃ = 3 A` at the event and
Kirchhoff's current law gives `i₁ = 8 + 3 = 11 A`; that explains why the
recorded choice B appears to answer a different current label.
-/
theorem problem_phyx_mini_0984
    (setup : ParallelRLTransientSetup)
    (data : StatedProblemData)
    (_scenario : MatchesIdealParallelRLScenario setup)
    (_figure : MatchesPrimaryParallelRLFigure setup)
    (_data : MatchesStatedProblemData setup data)
    (_physical : HasPhysicalParallelRLParameters setup)
    (_laws : SatisfiesIdealParallelRLTransientLaws setup)
    (observationTimeSeconds : ℝ)
    (_timeAfterSwitchCloses : 0 ≤ observationTimeSeconds)
    (_i3IsHalfItsFinalValue :
      currentInAmperes
          (setup.currentI3AtSeconds observationTimeSeconds) =
        currentInAmperes setup.finalCurrentI3 / 2) :
    currentInAmperes
        (setup.currentI2AtSeconds observationTimeSeconds) = 8 := by
  have hR1 :
      resistanceInOhms setup.resistorR1 = 12 :=
    _data.resistorR1Calibration.trans _data.resistorR1Label
  have hEmf :
      potentialInVolts setup.batteryEmf = 96 :=
    _data.batteryEmfCalibration.trans _data.batteryEmfLabel
  have hClamped :=
    _laws.sourceClampsR1BranchVoltage observationTimeSeconds
      _timeAfterSwitchCloses
  have hOhm :=
    _laws.resistorR1OhmLaw observationTimeSeconds
      _timeAfterSwitchCloses
  rw [hEmf] at hClamped
  rw [hR1] at hOhm
  nlinarith

end PhyXMiniProblems.ProblemPhyXMini0984
