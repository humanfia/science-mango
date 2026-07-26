import Mathlib
import Physlib.SpaceAndTime.Time.TimeUnit
import Physlib.Units.WithDim.Basic

/- USER: The assigned Lean file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0941

open Dimension

/-!
# Protective inductor in a switched series R-L circuit

A sensitive device of resistance `175 Ω` is operated from an ideal voltage
source.  Its intended steady current is `36 mA`, but during the first `58 μs`
after `S₁` is closed its current may rise only to `4.9 mA`.  The primary
raster shows the device resistor between nodes `a` and `b`, the inductor
between `b` and `c`, and a rightward current arrow through both components.

Physical voltage, resistance, inductance, current, and time are represented
by unit-independent Physlib `Dimensionful` quantities.  Real numbers occur
only at explicit coherent-unit readout boundaries and in literal figure or
answer-choice data.

Assumption/target split:

* governing laws: the source obeys the steady-state Ohm relation, the series
  `R-L` time constant obeys `L = R τ`, and the current after closing `S₁`
  follows the ideal exponential step response;
* previous-part results: none;
* figure/data readouts: `R = 175 Ω`, intended current `36 mA`, limiting current
  `4.9 mA` throughout the first `58 μs`, negligible source resistance, the
  nodes `a,b,c`, components `R,L`, switches `S₁,S₂`, current arrow `i`, source
  polarity, colours, and the two switching captions;
* current target conclusion: the lower bound on `τ` forced by the safety
  inequality.

The source data print `μH` beside all four answer numbers even though `τ` is a
time.  That dimensional mismatch is preserved below as answer metadata.  In
particular, no answer choice is compared with or asserted to equal the time
constant, and no saturation of the safety inequality is assumed.
-/

/-! ## Dimensionful physical quantities and named-unit readouts -/

/-- Energy has physical dimension `M L² T⁻²`. -/
def energyDimension : Dimension :=
  M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹

/-- Electric current has physical dimension charge per time. -/
def electricCurrentDimension : Dimension :=
  C𝓭 * T𝓭⁻¹

/-- Electric potential difference has physical dimension energy per charge. -/
def electricPotentialDimension : Dimension :=
  energyDimension * C𝓭⁻¹

/-- Electrical resistance has physical dimension voltage per current. -/
def electricalResistanceDimension : Dimension :=
  electricPotentialDimension * electricCurrentDimension⁻¹

/-- Inductance has physical dimension resistance times time. -/
def inductanceDimension : Dimension :=
  electricalResistanceDimension * T𝓭

/-- A nonnegative, unit-independent electromotive-force magnitude. -/
abbrev VoltageMagnitude : Type :=
  Dimensionful (WithDim electricPotentialDimension NNReal)

/-- A nonnegative, unit-independent electrical resistance. -/
abbrev ResistanceMagnitude : Type :=
  Dimensionful (WithDim electricalResistanceDimension NNReal)

/-- A nonnegative, unit-independent inductance. -/
abbrev InductanceMagnitude : Type :=
  Dimensionful (WithDim inductanceDimension NNReal)

/-- A nonnegative, unit-independent electric-current magnitude. -/
abbrev CurrentMagnitude : Type :=
  Dimensionful (WithDim electricCurrentDimension NNReal)

/-- A nonnegative, unit-independent elapsed time. -/
abbrev TimeMagnitude : Type :=
  Dimensionful (WithDim T𝓭 NNReal)

/-- Coherent-SI readout of a nonnegative dimensionful quantity. -/
def coherentSIReadout {d : Dimension}
    (quantity : Dimensionful (WithDim d NNReal)) : ℝ :=
  ((quantity UnitChoices.SI).val : ℝ)

/-- Read an emf magnitude in coherent-SI volts. -/
def voltageInVolts (voltage : VoltageMagnitude) : ℝ :=
  coherentSIReadout voltage

/-- Read an electrical resistance in coherent-SI ohms. -/
def resistanceInOhms (resistance : ResistanceMagnitude) : ℝ :=
  coherentSIReadout resistance

/-- Read an inductance in coherent-SI henries. -/
def inductanceInHenries (inductance : InductanceMagnitude) : ℝ :=
  coherentSIReadout inductance

/-- Read an electric-current magnitude in coherent-SI amperes. -/
def currentInAmperes (current : CurrentMagnitude) : ℝ :=
  coherentSIReadout current

/-- Read an electric-current magnitude in milliamperes. -/
def currentInMilliamperes (current : CurrentMagnitude) : ℝ :=
  1000 * currentInAmperes current

/-- Read a physical time in a selected Physlib time unit. -/
def timeReadout (unit : TimeUnit) (time : TimeMagnitude) : ℝ :=
  ((time {UnitChoices.SI with time := unit}).val : ℝ)

/-- Read a physical time in seconds. -/
def timeInSeconds (time : TimeMagnitude) : ℝ :=
  timeReadout TimeUnit.seconds time

/-- Read a physical time in microseconds. -/
def timeInMicroseconds (time : TimeMagnitude) : ℝ :=
  timeReadout TimeUnit.microseconds time

/-! ## Primary-figure vocabulary -/

/-- The three labelled circuit nodes in left-to-right order. -/
inductive CircuitNode where
  | a
  | b
  | c
  deriving DecidableEq, Fintype, Repr

/-- The two switches explicitly labelled in the raster. -/
inductive SwitchLabel where
  | S1
  | S2
  deriving DecidableEq, Fintype, Repr

/-- Components individually visible in the circuit diagram. -/
inductive CircuitComponent where
  | emfSource
  | deviceResistor
  | protectiveInductor
  | switchS1
  | switchS2
  deriving DecidableEq, Fintype, Repr

/-- The two passive-component colours used in the primary raster. -/
inductive ComponentColor where
  | magenta
  | green
  deriving DecidableEq, Repr

/-- State of an ideal switch. -/
inductive SwitchState where
  | openCircuit
  | closedCircuit
  deriving DecidableEq, Repr

/-- Direction of the arrow `i` on the `a-b-c` branch. -/
inductive BranchCurrentDirection where
  | fromATowardC
  | fromCTowardA
  deriving DecidableEq, Repr

/-- The two idealized circuit configurations described by the captions. -/
inductive SeriesRLConfiguration where
  | sourceConnectedByS1
  | sourceDisconnectedAndLoopClosedByS2
  deriving DecidableEq, Repr

/-- Literal and qualitative evidence transcribed from primary image `941.png`. -/
structure SeriesRLFigure where
  componentShown : CircuitComponent → Bool
  switchShown : SwitchLabel → Bool
  switchDrawnOpen : SwitchLabel → Bool
  nodeShown : CircuitNode → Bool
  nodeOrder : List CircuitNode
  resistorEndpoints : CircuitNode × CircuitNode
  inductorEndpoints : CircuitNode × CircuitNode
  resistorLabel : String
  inductorLabel : String
  emfLabel : String
  currentArrowLabel : String
  resistorColor : ComponentColor
  inductorColor : ComponentColor
  currentArrowDirection : BranchCurrentDirection
  positiveSourceTerminalShown : Bool
  closingS1CaptionShown : Bool
  openingS1AndClosingS2CaptionShown : Bool

/-! ## Independent circuit setup and data -/

/-!
The time constant and inductor are independent physical fields.  Neither is
defined from an answer number.  `currentAfterS1Closure` is indexed by a
physical elapsed time rather than by an untyped scalar time coordinate.
-/
structure ProtectiveSeriesRLCircuit where
  unitSystem : UnitChoices
  sourceEmf : VoltageMagnitude
  sourceInternalResistance : ResistanceMagnitude
  deviceResistance : ResistanceMagnitude
  protectiveInductance : InductanceMagnitude
  designedOperatingCurrent : CurrentMagnitude
  maximumPermittedEarlyCurrent : CurrentMagnitude
  protectionInterval : TimeMagnitude
  timeConstant : TimeMagnitude
  currentAfterS1Closure : TimeMagnitude → CurrentMagnitude
  energizingSwitchState : SwitchLabel → SwitchState
  dischargeSwitchState : SwitchLabel → SwitchState
  energizingConfiguration : SeriesRLConfiguration
  dischargeConfiguration : SeriesRLConfiguration
  figure : SeriesRLFigure

/-!
All topology, labels, colours, and operating explanations visible in the
primary raster.  The physical series connection is kept separate from the
numerical safety specification.
-/
structure MatchesSuppliedSeriesRLFigure
    (setup : ProtectiveSeriesRLCircuit) : Prop where
  everyComponentShown : ∀ component,
    setup.figure.componentShown component = true
  bothSwitchesShown : ∀ switch,
    setup.figure.switchShown switch = true
  bothSwitchesDrawnOpen : ∀ switch,
    setup.figure.switchDrawnOpen switch = true
  allThreeNodesShown : ∀ node,
    setup.figure.nodeShown node = true
  nodesRunLeftToRight : setup.figure.nodeOrder = [.a, .b, .c]
  resistorRunsFromAToB : setup.figure.resistorEndpoints = (.a, .b)
  inductorRunsFromBToC : setup.figure.inductorEndpoints = (.b, .c)
  resistorIsLabelledR : setup.figure.resistorLabel = "R"
  inductorIsLabelledL : setup.figure.inductorLabel = "L"
  sourceIsLabelledScriptE : setup.figure.emfLabel = "ℰ"
  currentArrowIsLabelledI : setup.figure.currentArrowLabel = "i"
  resistorIsMagenta : setup.figure.resistorColor = .magenta
  inductorIsGreen : setup.figure.inductorColor = .green
  currentArrowPointsFromAToC :
    setup.figure.currentArrowDirection = .fromATowardC
  positiveTerminalIsShown :
    setup.figure.positiveSourceTerminalShown = true
  s1CaptionIsShown : setup.figure.closingS1CaptionShown = true
  s2CaptionIsShown :
    setup.figure.openingS1AndClosingS2CaptionShown = true
  s1EnergizesSeriesCombination :
    setup.energizingConfiguration = .sourceConnectedByS1
  dischargeLoopDisconnectsSource :
    setup.dischargeConfiguration = .sourceDisconnectedAndLoopClosedByS2

/-- Switch states for energizing and for the source-disconnected decay loop. -/
structure MatchesSeriesRLSwitchingProtocol
    (setup : ProtectiveSeriesRLCircuit) : Prop where
  s1ClosedDuringEnergizing :
    setup.energizingSwitchState .S1 = .closedCircuit
  s2OpenDuringEnergizing :
    setup.energizingSwitchState .S2 = .openCircuit
  s1OpenDuringDischarge :
    setup.dischargeSwitchState .S1 = .openCircuit
  s2ClosedDuringDischarge :
    setup.dischargeSwitchState .S2 = .closedCircuit

/-!
Numerical data from the prose and the safety requirement.  The bound is stated
throughout the first interval.  The source supplies no equality saying that the
permitted current is reached at the deadline.
-/
structure MatchesDeviceSafetySpecification
    (setup : ProtectiveSeriesRLCircuit) : Prop where
  usesSIAsCoherentUnitSystem : setup.unitSystem = UnitChoices.SI
  sourceInternalResistanceIsNegligible :
    resistanceInOhms setup.sourceInternalResistance = 0
  deviceResistanceIs175Ohms :
    resistanceInOhms setup.deviceResistance = 175
  designedOperatingCurrentIs36Milliamperes :
    currentInMilliamperes setup.designedOperatingCurrent = 36
  maximumEarlyCurrentIs4Point9Milliamperes :
    currentInMilliamperes setup.maximumPermittedEarlyCurrent = 49 / 10
  protectionIntervalIs58Microseconds :
    timeInMicroseconds setup.protectionInterval = 58
  currentStaysWithinLimitForFirst58Microseconds :
    ∀ elapsed : TimeMagnitude,
      timeInMicroseconds elapsed ≤
          timeInMicroseconds setup.protectionInterval →
        currentInMilliamperes (setup.currentAfterS1Closure elapsed) ≤
          currentInMilliamperes setup.maximumPermittedEarlyCurrent

/-- Positivity and strict separation implicit in the physical device data. -/
structure HasPhysicalSeriesRLParameters
    (setup : ProtectiveSeriesRLCircuit) : Prop where
  deviceResistancePositive :
    0 < resistanceInOhms setup.deviceResistance
  sourceEmfPositive :
    0 < voltageInVolts setup.sourceEmf
  inductancePositive :
    0 < inductanceInHenries setup.protectiveInductance
  operatingCurrentPositive :
    0 < currentInAmperes setup.designedOperatingCurrent
  permittedCurrentPositive :
    0 < currentInAmperes setup.maximumPermittedEarlyCurrent
  permittedCurrentBelowOperatingCurrent :
    currentInAmperes setup.maximumPermittedEarlyCurrent <
      currentInAmperes setup.designedOperatingCurrent
  protectionIntervalPositive :
    0 < timeInSeconds setup.protectionInterval
  timeConstantPositive :
    0 < timeInSeconds setup.timeConstant

/-! ## Governing ideal series R-L laws -/

/-!
Uniform circuit laws used to derive the requested time constant.  The
exponential argument is dimensionless because it is the ratio of two SI time
readouts.  No field states the numerical value or logarithmic formula sought
in the target.
-/
structure SatisfiesIdealSeriesRLTransientLaws
    (setup : ProtectiveSeriesRLCircuit) : Prop where
  steadyStateOhmsLaw :
    voltageInVolts setup.sourceEmf =
      currentInAmperes setup.designedOperatingCurrent *
        resistanceInOhms setup.deviceResistance
  timeConstantLaw :
    inductanceInHenries setup.protectiveInductance =
      resistanceInOhms setup.deviceResistance *
        timeInSeconds setup.timeConstant
  currentStepResponse : ∀ elapsed : TimeMagnitude,
    currentInAmperes (setup.currentAfterS1Closure elapsed) =
      currentInAmperes setup.designedOperatingCurrent *
        (1 - Real.exp
          (-(timeInSeconds elapsed / timeInSeconds setup.timeConstant)))

/-! ## Safe time-constant threshold and source answer metadata -/

/--
The microsecond threshold obtained by solving the boundary case of the stated
current inequality.  This is a lower-bound expression, not an assertion that
the actual time constant saturates the safety requirement.
-/
def limitingTimeConstantInMicroseconds : ℝ :=
  -(58 : ℝ) /
    Real.log (1 - ((49 / 10 : ℝ) / 36))

/-- The four letter labels in the source answer list. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- The numerical payload printed beside each answer label. -/
def displayedChoiceNumber : AnswerChoice → ℝ
  | .A => 220
  | .B => 390
  | .C => 750
  | .D => 280

/-- Unit strings carried by displayed choices in the source data. -/
inductive PrintedAnswerUnit where
  | microseconds
  | microhenries
  deriving DecidableEq, Repr

/-!
All four source choices are printed in microhenries.  This deliberately does
not reinterpret the unit as microseconds.
-/
def displayedChoiceUnit (_choice : AnswerChoice) : PrintedAnswerUnit :=
  .microhenries

/-- The dataset's recorded label, retained only as source metadata. -/
def recordedDatasetAnswer : AnswerChoice := .B

/-- Any design satisfying the stated early-current ceiling has at least the
limiting time constant.  This consequence does not assume that the safety
inequality is saturated at the deadline. -/
lemma safeDesign_timeConstant_at_least_limitingValue
    (setup : ProtectiveSeriesRLCircuit)
    (h_data : MatchesDeviceSafetySpecification setup)
    (h_physical : HasPhysicalSeriesRLParameters setup)
    (h_laws : SatisfiesIdealSeriesRLTransientLaws setup) :
    limitingTimeConstantInMicroseconds ≤
      timeInMicroseconds setup.timeConstant := by
  have timeInMicroseconds_eq
      (time : TimeMagnitude) :
      timeInMicroseconds time = 1_000_000 * timeInSeconds time := by
    have hScale := time.2
      UnitChoices.SI {UnitChoices.SI with time := TimeUnit.microseconds}
    have hScaleVal :=
      congrArg (fun x => ((x.val : NNReal) : ℝ)) hScale
    norm_num [timeInMicroseconds, timeInSeconds, timeReadout,
      UnitChoices.dimScale, TimeUnit.microseconds, TimeUnit.scale,
      UnitChoices.SI, TimeUnit.div_eq_val] at hScaleVal ⊢
    rw [hScaleVal]
    congr 1
    change
      TimeUnit.seconds.val / (1 / 1000000 * TimeUnit.seconds.val) =
        (1000000 : ℝ)
    field_simp [ne_of_gt TimeUnit.seconds.val_pos]
  have hIntervalSeconds :
      timeInSeconds setup.protectionInterval = 58 / 1_000_000 := by
    have hUnitConversion :=
      timeInMicroseconds_eq setup.protectionInterval
    rw [h_data.protectionIntervalIs58Microseconds] at hUnitConversion
    linarith
  have hOperatingAmps :
      currentInAmperes setup.designedOperatingCurrent = 9 / 250 := by
    have h := h_data.designedOperatingCurrentIs36Milliamperes
    norm_num [currentInMilliamperes] at h ⊢
    linarith
  have hPermittedAmps :
      currentInAmperes setup.maximumPermittedEarlyCurrent = 49 / 10_000 := by
    have h := h_data.maximumEarlyCurrentIs4Point9Milliamperes
    norm_num [currentInMilliamperes] at h ⊢
    linarith
  have hCurrentBound :
      currentInAmperes
          (setup.currentAfterS1Closure setup.protectionInterval) ≤
        49 / 10_000 := by
    have h := h_data.currentStaysWithinLimitForFirst58Microseconds
      setup.protectionInterval le_rfl
    simp only [currentInMilliamperes] at h
    rw [hPermittedAmps] at h
    norm_num at h ⊢
    linarith
  have hStep :=
    h_laws.currentStepResponse setup.protectionInterval
  rw [hOperatingAmps, hIntervalSeconds] at hStep
  have hExpLower :
      (311 / 360 : ℝ) ≤
        Real.exp
          (-(timeInSeconds setup.protectionInterval /
            timeInSeconds setup.timeConstant)) := by
    rw [hIntervalSeconds]
    nlinarith [hCurrentBound, hStep]
  have hRatioPos : (0 : ℝ) < 311 / 360 := by norm_num
  have hLogBound :
      Real.log (311 / 360) ≤
        -(timeInSeconds setup.protectionInterval /
          timeInSeconds setup.timeConstant) :=
    (Real.log_le_iff_le_exp hRatioPos).2 hExpLower
  rw [hIntervalSeconds] at hLogBound
  have hTauPos : 0 < timeInSeconds setup.timeConstant :=
    h_physical.timeConstantPositive
  have hLogNeg : Real.log (311 / 360) < 0 := by
    exact Real.log_neg hRatioPos (by norm_num)
  have hCleared :
      Real.log (311 / 360) * timeInSeconds setup.timeConstant ≤
        -(58 / 1_000_000 : ℝ) := by
    have h := mul_le_mul_of_nonneg_right hLogBound (le_of_lt hTauPos)
    calc
      Real.log (311 / 360) * timeInSeconds setup.timeConstant ≤
          (-(58 / 1_000_000 /
            timeInSeconds setup.timeConstant)) *
              timeInSeconds setup.timeConstant := h
      _ = -(58 / 1_000_000 : ℝ) := by
        field_simp [ne_of_gt hTauPos]
  rw [timeInMicroseconds_eq]
  unfold limitingTimeConstantInMicroseconds
  norm_num only
  apply (div_le_iff_of_neg hLogNeg).2
  nlinarith [hCleared]

/-!
The source safety condition is an inequality, so the strongest supported
conclusion is a lower bound on the physical time constant.  The source does
not state that the current reaches `4.9 mA` exactly at `58 μs`.  Moreover, all
four displayed answer choices carry inductance units rather than time units,
so the recorded answer is not promoted from metadata to a physical conclusion.

This declaration formalizes `thm:physics:phyx_mini_0941:target`.
-/
theorem problem_phyx_mini_0941
    (setup : ProtectiveSeriesRLCircuit)
    (h_figure : MatchesSuppliedSeriesRLFigure setup)
    (h_switching : MatchesSeriesRLSwitchingProtocol setup)
    (h_data : MatchesDeviceSafetySpecification setup)
    (h_physical : HasPhysicalSeriesRLParameters setup)
    (h_laws : SatisfiesIdealSeriesRLTransientLaws setup) :
    limitingTimeConstantInMicroseconds ≤
      timeInMicroseconds setup.timeConstant := by
  exact safeDesign_timeConstant_at_least_limitingValue
    setup h_data h_physical h_laws

end PhyXMiniProblems.ProblemPhyXMini0941
