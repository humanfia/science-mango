import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic
import Physlib.Relativity.PauliMatrices.Basic

/- USER: The assigned Lean file did not exist when this autoformalization task began. -/

/-!
# Three successive Stern–Gerlach analyzers

A beam of spin-one-half particles passes through analyzers aligned successively
with the positive `z` direction, a unit direction `nHat` in the `x`-`z` plane,
and the positive `z` direction again.  The primary figure routes the upper
output of each of the first two analyzers into the next analyzer.  Thus the
probability asked for is conditional on transmission through the first
analyzer and is the product of the `z-up` to `nHat-up` probability and the
`nHat-up` to `z-down` probability.

The directions are genuine unit vectors in three-dimensional Euclidean space.
All probabilities and the angle readout in radians are dimensionless real
numbers.  The Born and sequential-filtering laws are stated independently of
the requested numerical formula.
-/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0542

/-! ## Spin and analyzer vocabulary -/

/-- The two output channels of a spin-one-half Stern–Gerlach analyzer. -/
inductive SpinOutcome where
  | up
  | down
  deriving DecidableEq, Fintype, Repr

/-- Reversing the spin outcome along a fixed oriented analyzer axis. -/
def SpinOutcome.opposite : SpinOutcome → SpinOutcome
  | .up => .down
  | .down => .up

/-- The intrinsic spin quantum number specified for the incident particles. -/
inductive ParticleSpin where
  | oneHalf
  deriving DecidableEq, Repr

/--
An oriented analyzer axis.  Its direction points toward the channel called
`up`, so the unit-vector orientation retains the physical distinction between
spin up and spin down.
-/
structure SpinAxis where
  direction : EuclideanSpace ℝ (Fin 3)
  isUnit : ‖direction‖ = 1

/--
The dimensionless spin observable `n · σ` associated with an oriented analyzer
axis `n`.  The three matrices are PhysLean's Pauli matrices; multiplying this
observable by `ℏ / 2` would give the corresponding physical spin component.
-/
def SpinAxis.dimensionlessPauliObservable
    (axis : SpinAxis) : Matrix (Fin 2) (Fin 2) ℂ :=
  ∑ i : Fin 3,
    (axis.direction i : ℂ) • PauliMatrix.pauliMatrix (Sum.inr i)

/-- Axis symbols printed inside the three analyzer boxes in the figure. -/
inductive AnalyzerAxisLabel where
  | z
  | nHat
  deriving DecidableEq, Repr

/-- A Stern–Gerlach analyzer together with its displayed axis label. -/
structure SternGerlachAnalyzer where
  displayedAxisLabel : AnalyzerAxisLabel
  axis : SpinAxis

/-! ## Experiment and primary-figure data -/

/--
The three-analyzer experiment and its requested dimensionless probability.

`probabilityConditionedOnFirstTransmission` is an independent observable: it
is the probability, among particles emerging through the selected output of
the first analyzer, of following the selected output of the second analyzer
and then emerging through the requested output of the third analyzer.
-/
structure SternGerlachExperiment where
  particleSpin : ParticleSpin
  firstAnalyzer : SternGerlachAnalyzer
  secondAnalyzer : SternGerlachAnalyzer
  thirdAnalyzer : SternGerlachAnalyzer
  firstTransmittedOutcome : SpinOutcome
  secondTransmittedOutcome : SpinOutcome
  requestedThirdOutcome : SpinOutcome
  probabilityConditionedOnFirstTransmission : ℝ

/-- Scenario facts stated in the prose, including the physical probability range. -/
structure MatchesSpinHalfScenario
    (experiment : SternGerlachExperiment) : Prop where
  spinIsOneHalf : experiment.particleSpin = .oneHalf
  requestedProbabilityNonnegative :
    0 ≤ experiment.probabilityConditionedOnFirstTransmission
  requestedProbabilityAtMostOne :
    experiment.probabilityConditionedOnFirstTransmission ≤ 1

/--
Analyzer labels, coordinate directions, and connected output ports read from
the supplied image.  Coordinates `0`, `1`, and `2` represent `x`, `y`, and `z`.
The upper channels of the first two analyzers continue to the next box, while
the question asks about the lower (`down`) channel of the last box.
-/
structure MatchesSuppliedThreeAnalyzerFigure
    (experiment : SternGerlachExperiment) : Prop where
  firstAnalyzerLabel : experiment.firstAnalyzer.displayedAxisLabel = .z
  secondAnalyzerLabel : experiment.secondAnalyzer.displayedAxisLabel = .nHat
  thirdAnalyzerLabel : experiment.thirdAnalyzer.displayedAxisLabel = .z
  firstAxisIsPositiveZ :
    experiment.firstAnalyzer.axis.direction =
      EuclideanSpace.single (2 : Fin 3) (1 : ℝ)
  thirdAxisIsPositiveZ :
    experiment.thirdAnalyzer.axis.direction =
      EuclideanSpace.single (2 : Fin 3) (1 : ℝ)
  firstUpperPortContinues :
    experiment.firstTransmittedOutcome = .up
  secondUpperPortContinues :
    experiment.secondTransmittedOutcome = .up
  requestedPortIsThirdDown :
    experiment.requestedThirdOutcome = .down

/--
The second analyzer's unit axis lies in the `x`-`z` plane and makes the
dimensionless angle `theta`, read in radians, with the first positive `z` axis.
The usual range of the undirected Euclidean angle is recorded explicitly.
-/
structure SecondAnalyzerGeometry
    (experiment : SternGerlachExperiment) (theta : ℝ) : Prop where
  angleIsNonnegative : 0 ≤ theta
  angleAtMostPi : theta ≤ Real.pi
  nAxisLiesInXZPlane :
    experiment.secondAnalyzer.axis.direction (1 : Fin 3) = 0
  nAxisMakesThetaWithZ :
    InnerProductGeometry.angle
        experiment.firstAnalyzer.axis.direction
        experiment.secondAnalyzer.axis.direction = theta

/-! ## Governing quantum-mechanical laws -/

/--
Born transition probabilities for spin one-half measurements.

For analyzer axes separated by an undirected angle `alpha`, retaining the same
spin label has probability `cos²(alpha / 2)` and obtaining the opposite label
has probability `sin²(alpha / 2)`.  The law is general in both axes and does
not mention this problem's requested final probability.
-/
structure SpinHalfBornRule where
  transitionProbability :
    SpinAxis → SpinOutcome → SpinAxis → SpinOutcome → ℝ
  probabilityNonnegative :
    ∀ fromAxis fromOutcome toAxis toOutcome,
      0 ≤ transitionProbability fromAxis fromOutcome toAxis toOutcome
  probabilityAtMostOne :
    ∀ fromAxis fromOutcome toAxis toOutcome,
      transitionProbability fromAxis fromOutcome toAxis toOutcome ≤ 1
  sameOutcomeProbability :
    ∀ fromAxis toAxis outcome,
      transitionProbability fromAxis outcome toAxis outcome =
        Real.cos
            (InnerProductGeometry.angle
                fromAxis.direction toAxis.direction / 2) ^ 2
  oppositeOutcomeProbability :
    ∀ fromAxis toAxis outcome,
      transitionProbability fromAxis outcome toAxis outcome.opposite =
        Real.sin
            (InnerProductGeometry.angle
                fromAxis.direction toAxis.direction / 2) ^ 2

/--
The chain rule for two successive ideal filters after conditioning on passage
through the first analyzer.  In particular, no probability for entering the
first selected port is multiplied into this conditional probability.
-/
structure SatisfiesSequentialFilteringLaw
    (experiment : SternGerlachExperiment)
    (bornRule : SpinHalfBornRule) : Prop where
  conditionalChainRule :
    experiment.probabilityConditionedOnFirstTransmission =
      bornRule.transitionProbability
          experiment.firstAnalyzer.axis
          experiment.firstTransmittedOutcome
          experiment.secondAnalyzer.axis
          experiment.secondTransmittedOutcome *
        bornRule.transitionProbability
          experiment.secondAnalyzer.axis
          experiment.secondTransmittedOutcome
          experiment.thirdAnalyzer.axis
          experiment.requestedThirdOutcome

/-! ## Displayed choices and current target -/

/-- Labels of the four answer choices printed with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- The dimensionless probability expression printed beside each answer label. -/
def displayedProbability (theta : ℝ) : AnswerChoice → ℝ
  | .A => (1 : ℝ) / 4 * (1 / Real.tan theta) ^ 2
  | .B => (1 : ℝ) / 4 * Real.tan theta ^ 2
  | .C => (1 : ℝ) / 4 * Real.cos theta ^ 2
  | .D => (1 : ℝ) / 4 * Real.sin theta ^ 2

/-- A displayed choice agrees with the experiment's requested probability. -/
def IsCorrectAnswer
    (experiment : SternGerlachExperiment)
    (theta : ℝ) (choice : AnswerChoice) : Prop :=
  experiment.probabilityConditionedOnFirstTransmission =
    displayedProbability theta choice

/-!
The first selected `z-up` state reaches the selected `nHat-up` port with
probability `cos²(theta / 2)`.  That state reaches the last `z-down` port with
probability `sin²(theta / 2)`.  Their product is
`(1 / 4) * sin²(theta)`, which is displayed answer D.

This formalizes `thm:physics:phyx_mini_0542:target`.
-/
theorem final_spin_down_probability_and_recorded_answer_D
    (experiment : SternGerlachExperiment)
    (theta : ℝ)
    (bornRule : SpinHalfBornRule)
    (h_scenario : MatchesSpinHalfScenario experiment)
    (h_figure : MatchesSuppliedThreeAnalyzerFigure experiment)
    (h_geometry : SecondAnalyzerGeometry experiment theta)
    (h_filtering : SatisfiesSequentialFilteringLaw experiment bornRule) :
    experiment.probabilityConditionedOnFirstTransmission =
        (1 : ℝ) / 4 * Real.sin theta ^ 2 ∧
      IsCorrectAnswer experiment theta .D := by
  have h_first_step :
      bornRule.transitionProbability
          experiment.firstAnalyzer.axis
          experiment.firstTransmittedOutcome
          experiment.secondAnalyzer.axis
          experiment.secondTransmittedOutcome =
        Real.cos (theta / 2) ^ 2 := by
    rw [h_figure.firstUpperPortContinues, h_figure.secondUpperPortContinues]
    rw [bornRule.sameOutcomeProbability]
    rw [h_geometry.nAxisMakesThetaWithZ]
  have h_second_step :
      bornRule.transitionProbability
          experiment.secondAnalyzer.axis
          experiment.secondTransmittedOutcome
          experiment.thirdAnalyzer.axis
          experiment.requestedThirdOutcome =
        Real.sin (theta / 2) ^ 2 := by
    rw [h_figure.secondUpperPortContinues, h_figure.requestedPortIsThirdDown]
    change bornRule.transitionProbability experiment.secondAnalyzer.axis SpinOutcome.up
        experiment.thirdAnalyzer.axis SpinOutcome.up.opposite = _
    rw [bornRule.oppositeOutcomeProbability]
    rw [h_figure.thirdAxisIsPositiveZ, ← h_figure.firstAxisIsPositiveZ]
    rw [InnerProductGeometry.angle_comm, h_geometry.nAxisMakesThetaWithZ]
  have h_trig :
      Real.cos (theta / 2) ^ 2 * Real.sin (theta / 2) ^ 2 =
        (1 : ℝ) / 4 * Real.sin theta ^ 2 := by
    rw [show Real.sin theta =
        2 * Real.sin (theta / 2) * Real.cos (theta / 2) by
      rw [← Real.sin_two_mul]
      congr 1
      ring]
    ring
  have h_probability :
      experiment.probabilityConditionedOnFirstTransmission =
        (1 : ℝ) / 4 * Real.sin theta ^ 2 := by
    calc
      experiment.probabilityConditionedOnFirstTransmission =
          bornRule.transitionProbability
              experiment.firstAnalyzer.axis
              experiment.firstTransmittedOutcome
              experiment.secondAnalyzer.axis
              experiment.secondTransmittedOutcome *
            bornRule.transitionProbability
              experiment.secondAnalyzer.axis
              experiment.secondTransmittedOutcome
              experiment.thirdAnalyzer.axis
              experiment.requestedThirdOutcome :=
        h_filtering.conditionalChainRule
      _ = Real.cos (theta / 2) ^ 2 * Real.sin (theta / 2) ^ 2 := by
        rw [h_first_step, h_second_step]
      _ = (1 : ℝ) / 4 * Real.sin theta ^ 2 := h_trig
  refine ⟨h_probability, ?_⟩
  simpa [IsCorrectAnswer, displayedProbability] using h_probability

end PhyXMiniProblems.ProblemPhyXMini0542
