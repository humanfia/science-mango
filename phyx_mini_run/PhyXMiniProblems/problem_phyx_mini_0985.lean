import Mathlib
import Physlib.Units.WithDim.Basic

/- USER: The assigned Lean file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0985

open Dimension

/-!
# Current in a switched parallel resistor--inductor circuit

The primary raster `985.png` shows a `48.0 V` ideal battery and switch feeding
`R₁ = 8.00 Ω` in series.  After `R₁`, the circuit splits into two parallel
branches: `R₂ = 6.00 Ω`, carrying the downward current `i₂`, and an ideal
`L = 0.200 H` inductor, carrying the downward current `i₃`.  The source/feed
current `i₁` is drawn upward on the battery side.  Thus the image, rather than
the auxiliary caption, determines that `R₁` is the common series resistor and
that `i₂` is the `R₂`-branch current.

All component values and currents are represented by Physlib's unit-independent
`Dimensionful (WithDim ...)` quantities.  Real numbers are used only for
coherent-SI readouts and for the time coordinate measured in seconds.

Assumption/target split:

* governing laws: Kirchhoff's current law at the split, Ohm's law for `R₂`,
  the source-loop voltage balance, `V_L = L · d i₃/dt`, convergence to the
  named final values, and zero final voltage across an ideal DC inductor;
* previous-part results: none;
* figure/data readouts: the topology and current-arrow directions in
  `985.png`, `48.0 V`, `8.00 Ω`, `6.00 Ω`, `0.200 H`, negligible source and
  inductor resistance, and switch closure at `t = 0`;
* current target: when `i₃` is half its final value, `i₁ = 33/7 A`, whose
  nearest-hundredth display is `4.71 A` (choice B).

Neither `33/7` nor `4.71` occurs in a physical-law, scenario, or data premise.
-/

/-! ## Dimensionful electrical quantities and coherent-SI readouts -/

/-- Electric current has physical dimension charge per time. -/
def electricCurrentDimension : Dimension := C𝓭 * T𝓭⁻¹

/-- Electric potential difference has physical dimension energy per charge. -/
def electricPotentialDimension : Dimension :=
  M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹ * C𝓭⁻¹

/-- Electrical resistance has dimension potential difference per current. -/
def electricalResistanceDimension : Dimension :=
  electricPotentialDimension * electricCurrentDimension⁻¹

/-- Inductance has dimension resistance times time. -/
def electricalInductanceDimension : Dimension :=
  electricalResistanceDimension * T𝓭

/-- A signed, unit-independent branch current. -/
abbrev ElectricCurrent : Type :=
  Dimensionful (WithDim electricCurrentDimension ℝ)

/-- A signed, oriented, unit-independent potential difference. -/
abbrev ElectricPotentialDifference : Type :=
  Dimensionful (WithDim electricPotentialDimension ℝ)

/-- A nonnegative, unit-independent resistance magnitude. -/
abbrev ElectricalResistanceMagnitude : Type :=
  Dimensionful (WithDim electricalResistanceDimension NNReal)

/-- A nonnegative, unit-independent inductance magnitude. -/
abbrev ElectricalInductanceMagnitude : Type :=
  Dimensionful (WithDim electricalInductanceDimension NNReal)

/-- Read a signed electric current in coherent SI amperes. -/
def electricCurrentInAmperes (current : ElectricCurrent) : ℝ :=
  (current UnitChoices.SI).val

/-- Read an oriented potential difference or emf in coherent SI volts. -/
def potentialDifferenceInVolts
    (voltage : ElectricPotentialDifference) : ℝ :=
  (voltage UnitChoices.SI).val

/-- Read a resistance magnitude in coherent SI ohms. -/
def resistanceInOhms (resistance : ElectricalResistanceMagnitude) : ℝ :=
  ((resistance UnitChoices.SI).val : ℝ)

/-- Read an inductance magnitude in coherent SI henries. -/
def inductanceInHenries (inductance : ElectricalInductanceMagnitude) : ℝ :=
  ((inductance UnitChoices.SI).val : ℝ)

/-! ## Circuit roles and primary-figure geometry -/

/-- Electrically distinct nodes needed to describe the raster's topology. -/
inductive CircuitNode where
  | lowerReturn
  | batteryPositive
  | afterSwitch
  | branchJunction
  deriving DecidableEq, Fintype, Repr

/-- The five lumped elements shown in the circuit. -/
inductive CircuitElement where
  | battery
  | switch
  | resistorOne
  | resistorTwo
  | inductor
  deriving DecidableEq, Fintype, Repr

/-- Current labels printed beside the three arrows in the raster. -/
inductive CurrentLabel where
  | i1
  | i2
  | i3
  deriving DecidableEq, Fintype, Repr

/-- Idealized state of the switching element. -/
inductive SwitchState where
  | open
  | closed
  deriving DecidableEq, Fintype, Repr

/-- Constitutive role assigned to each displayed circuit symbol. -/
inductive ComponentModel where
  | idealVoltageSource
  | idealSwitch
  | idealOhmicResistor
  | idealInductor
  | other
  deriving DecidableEq, Fintype, Repr

/-- Figure-derived labels, incidences, and directed branch paths. -/
structure ParallelRLFigure where
  componentSymbolShown : CircuitElement → Bool
  currentArrowShown : CurrentLabel → Bool
  elementTerminals : CircuitElement → CircuitNode × CircuitNode
  currentArrowEndpoints : CurrentLabel → CircuitNode × CircuitNode
  seriesFeedOrder : List CircuitElement
  branchElements : CurrentLabel → List CircuitElement
  batteryPositiveTerminal : CircuitNode
  switchSymbolState : SwitchState

/-!
Independent physical quantities and transient observables for the switched
circuit.  In particular, every current and final current is an independent
field constrained below by physical laws; no target current is defined from
the desired answer.
-/
structure ParallelRLTransientSetup where
  componentModel : CircuitElement → ComponentModel
  batteryEMF : ElectricPotentialDifference
  batteryInternalResistance : ElectricalResistanceMagnitude
  resistorOneResistance : ElectricalResistanceMagnitude
  resistorTwoResistance : ElectricalResistanceMagnitude
  inductance : ElectricalInductanceMagnitude
  inductorWindingResistance : ElectricalResistanceMagnitude
  switchStateAtSeconds : ℝ → SwitchState
  currentAtSeconds : ℝ → CurrentLabel → ElectricCurrent
  parallelVoltageAtSeconds : ℝ → ElectricPotentialDifference
  finalCurrent : CurrentLabel → ElectricCurrent
  finalParallelVoltage : ElectricPotentialDifference
  figure : ParallelRLFigure

/-! ## Scenario assumptions and supplied data -/

/-- The standard ideal lumped-component interpretation of the five symbols. -/
structure MatchesIdealParallelRLScenario
    (setup : ParallelRLTransientSetup) : Prop where
  batteryModel : setup.componentModel .battery = .idealVoltageSource
  switchModel : setup.componentModel .switch = .idealSwitch
  resistorOneModel :
    setup.componentModel .resistorOne = .idealOhmicResistor
  resistorTwoModel :
    setup.componentModel .resistorTwo = .idealOhmicResistor
  inductorModel : setup.componentModel .inductor = .idealInductor

/-!
Topology and arrow directions read from the primary image.  The source image
shows the switch symbol open even though the problem asks for its subsequent
closed-circuit transient.
-/
structure MatchesSuppliedParallelRLFigure
    (setup : ParallelRLTransientSetup) : Prop where
  everyComponentShown : ∀ element,
    setup.figure.componentSymbolShown element = true
  everyCurrentArrowShown : ∀ label,
    setup.figure.currentArrowShown label = true
  batteryTerminals :
    setup.figure.elementTerminals .battery =
      (.lowerReturn, .batteryPositive)
  switchTerminals :
    setup.figure.elementTerminals .switch =
      (.batteryPositive, .afterSwitch)
  resistorOneTerminals :
    setup.figure.elementTerminals .resistorOne =
      (.afterSwitch, .branchJunction)
  resistorTwoTerminals :
    setup.figure.elementTerminals .resistorTwo =
      (.branchJunction, .lowerReturn)
  inductorTerminals :
    setup.figure.elementTerminals .inductor =
      (.branchJunction, .lowerReturn)
  i1ArrowDirection :
    setup.figure.currentArrowEndpoints .i1 =
      (.lowerReturn, .batteryPositive)
  i2ArrowDirection :
    setup.figure.currentArrowEndpoints .i2 =
      (.branchJunction, .lowerReturn)
  i3ArrowDirection :
    setup.figure.currentArrowEndpoints .i3 =
      (.branchJunction, .lowerReturn)
  feedOrder :
    setup.figure.seriesFeedOrder =
      [.battery, .switch, .resistorOne]
  i1FeedPath :
    setup.figure.branchElements .i1 =
      [.battery, .switch, .resistorOne]
  i2ResistorBranch :
    setup.figure.branchElements .i2 = [.resistorTwo]
  i3InductorBranch :
    setup.figure.branchElements .i3 = [.inductor]
  positiveBatteryTerminal :
    setup.figure.batteryPositiveTerminal = .batteryPositive
  switchDrawnOpen : setup.figure.switchSymbolState = .open

/-- Numerical component data and switching protocol stated in the problem. -/
structure MatchesGivenParallelRLData
    (setup : ParallelRLTransientSetup) : Prop where
  batteryEMFCalibration :
    potentialDifferenceInVolts setup.batteryEMF = 48
  resistorOneCalibration :
    resistanceInOhms setup.resistorOneResistance = 8
  resistorTwoCalibration :
    resistanceInOhms setup.resistorTwoResistance = 6
  inductanceCalibration :
    inductanceInHenries setup.inductance = 1 / 5
  negligibleBatteryInternalResistance :
    resistanceInOhms setup.batteryInternalResistance = 0
  negligibleInductorWindingResistance :
    resistanceInOhms setup.inductorWindingResistance = 0
  switchOpenBeforeClosure : ∀ {timeInSeconds : ℝ},
    timeInSeconds < 0 → setup.switchStateAtSeconds timeInSeconds = .open
  switchClosedFromZero : ∀ {timeInSeconds : ℝ},
    0 ≤ timeInSeconds → setup.switchStateAtSeconds timeInSeconds = .closed
  initiallyUnenergizedInductor :
    electricCurrentInAmperes (setup.currentAtSeconds 0 .i3) = 0

/-! ## Governing circuit laws -/

/-!
Ideal transient and DC-final-value laws.  These are general relations among
independent observables.  They do not assign the requested value to `i₁`.
-/
structure SatisfiesIdealParallelRLTransientLaws
    (setup : ParallelRLTransientSetup) : Prop where
  junctionCurrentLaw : ∀ {timeInSeconds : ℝ}, 0 ≤ timeInSeconds →
    electricCurrentInAmperes (setup.currentAtSeconds timeInSeconds .i1) =
      electricCurrentInAmperes (setup.currentAtSeconds timeInSeconds .i2) +
        electricCurrentInAmperes (setup.currentAtSeconds timeInSeconds .i3)
  resistorTwoOhmLaw : ∀ {timeInSeconds : ℝ}, 0 ≤ timeInSeconds →
    potentialDifferenceInVolts
        (setup.parallelVoltageAtSeconds timeInSeconds) =
      resistanceInOhms setup.resistorTwoResistance *
        electricCurrentInAmperes
          (setup.currentAtSeconds timeInSeconds .i2)
  sourceLoopVoltageLaw : ∀ {timeInSeconds : ℝ}, 0 ≤ timeInSeconds →
    potentialDifferenceInVolts setup.batteryEMF =
      resistanceInOhms setup.resistorOneResistance *
          electricCurrentInAmperes
            (setup.currentAtSeconds timeInSeconds .i1) +
        potentialDifferenceInVolts
          (setup.parallelVoltageAtSeconds timeInSeconds)
  inductorConstitutiveLaw : ∀ {timeInSeconds : ℝ}, 0 < timeInSeconds →
    HasDerivAt
      (fun time : ℝ =>
        electricCurrentInAmperes (setup.currentAtSeconds time .i3))
      (potentialDifferenceInVolts
          (setup.parallelVoltageAtSeconds timeInSeconds) /
        inductanceInHenries setup.inductance)
      timeInSeconds
  currentHasFinalValue : ∀ label,
    Filter.Tendsto
      (fun time : ℝ =>
        electricCurrentInAmperes (setup.currentAtSeconds time label))
      Filter.atTop
      (nhds (electricCurrentInAmperes (setup.finalCurrent label)))
  parallelVoltageHasFinalValue :
    Filter.Tendsto
      (fun time : ℝ =>
        potentialDifferenceInVolts (setup.parallelVoltageAtSeconds time))
      Filter.atTop
      (nhds (potentialDifferenceInVolts setup.finalParallelVoltage))
  finalJunctionCurrentLaw :
    electricCurrentInAmperes (setup.finalCurrent .i1) =
      electricCurrentInAmperes (setup.finalCurrent .i2) +
        electricCurrentInAmperes (setup.finalCurrent .i3)
  finalResistorTwoOhmLaw :
    potentialDifferenceInVolts setup.finalParallelVoltage =
      resistanceInOhms setup.resistorTwoResistance *
        electricCurrentInAmperes (setup.finalCurrent .i2)
  finalSourceLoopVoltageLaw :
    potentialDifferenceInVolts setup.batteryEMF =
      resistanceInOhms setup.resistorOneResistance *
          electricCurrentInAmperes (setup.finalCurrent .i1) +
        potentialDifferenceInVolts setup.finalParallelVoltage
  idealInductorFinalVoltageLaw :
    potentialDifferenceInVolts setup.finalParallelVoltage = 0

/-! ## Displayed answer choices and requested conclusion -/

/-- Labels of the four current-valued choices printed with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Current printed beside each answer choice, in amperes. -/
def AnswerChoice.displayedCurrentInAmperes : AnswerChoice → ℝ
  | .A => 3
  | .B => 471 / 100
  | .C => 6
  | .D => 4

/-- Agreement with a displayed current rounded to the nearest hundredth. -/
def AnswerChoice.matchesRoundedCurrent
    (choice : AnswerChoice) (currentInAmperes : ℝ) : Prop :=
  |currentInAmperes - choice.displayedCurrentInAmperes| ≤ 1 / 200

/-- The answer label recorded in the supplied dataset metadata. -/
def recordedDatasetAnswer : AnswerChoice := .B

/-!
Blueprint label: `thm:physics:phyx_mini_0985:target`.

At DC steady state the ideal inductor has zero branch voltage, so `R₂` carries
zero final current and `i₃,final = 48/8 = 6 A`.  At the queried instant
`i₃ = 3 A`; Kirchhoff's current law, Ohm's law for `R₂`, and the source loop
then give `i₁ = 33/7 A ≈ 4.71 A`, displayed choice B.
-/
theorem problem_phyx_mini_0985
    (setup : ParallelRLTransientSetup)
    (_scenario : MatchesIdealParallelRLScenario setup)
    (_figure : MatchesSuppliedParallelRLFigure setup)
    (_data : MatchesGivenParallelRLData setup)
    (_laws : SatisfiesIdealParallelRLTransientLaws setup)
    (queryTimeInSeconds : ℝ)
    (_queryAfterSwitchClosure : 0 ≤ queryTimeInSeconds)
    (_inductorCurrentIsHalfFinal :
      electricCurrentInAmperes
          (setup.currentAtSeconds queryTimeInSeconds .i3) =
        (1 / 2 : ℝ) *
          electricCurrentInAmperes (setup.finalCurrent .i3)) :
    electricCurrentInAmperes
          (setup.currentAtSeconds queryTimeInSeconds .i1) =
        33 / 7 ∧
      recordedDatasetAnswer.matchesRoundedCurrent
        (electricCurrentInAmperes
          (setup.currentAtSeconds queryTimeInSeconds .i1)) := by
  have finalI2 :
      electricCurrentInAmperes (setup.finalCurrent .i2) = 0 := by
    have h := _laws.finalResistorTwoOhmLaw
    rw [_laws.idealInductorFinalVoltageLaw,
      _data.resistorTwoCalibration] at h
    linarith
  have finalI1 :
      electricCurrentInAmperes (setup.finalCurrent .i1) = 6 := by
    have h := _laws.finalSourceLoopVoltageLaw
    rw [_data.batteryEMFCalibration, _data.resistorOneCalibration,
      _laws.idealInductorFinalVoltageLaw] at h
    linarith
  have finalI3 :
      electricCurrentInAmperes (setup.finalCurrent .i3) = 6 := by
    have h := _laws.finalJunctionCurrentLaw
    rw [finalI1, finalI2] at h
    linarith
  have queryI3 :
      electricCurrentInAmperes
          (setup.currentAtSeconds queryTimeInSeconds .i3) = 3 := by
    calc
      electricCurrentInAmperes
          (setup.currentAtSeconds queryTimeInSeconds .i3) =
          (1 / 2 : ℝ) *
            electricCurrentInAmperes (setup.finalCurrent .i3) :=
        _inductorCurrentIsHalfFinal
      _ = 3 := by rw [finalI3]; norm_num
  have queryI1 :
      electricCurrentInAmperes
          (setup.currentAtSeconds queryTimeInSeconds .i1) = 33 / 7 := by
    have hKCL := _laws.junctionCurrentLaw _queryAfterSwitchClosure
    have hOhm := _laws.resistorTwoOhmLaw _queryAfterSwitchClosure
    have hLoop := _laws.sourceLoopVoltageLaw _queryAfterSwitchClosure
    rw [queryI3] at hKCL
    rw [_data.resistorTwoCalibration] at hOhm
    rw [_data.batteryEMFCalibration,
      _data.resistorOneCalibration] at hLoop
    linarith
  constructor
  · exact queryI1
  · rw [queryI1]
    norm_num [recordedDatasetAnswer, AnswerChoice.matchesRoundedCurrent,
      AnswerChoice.displayedCurrentInAmperes, abs_of_nonneg, abs_of_nonpos]

end PhyXMiniProblems.ProblemPhyXMini0985
