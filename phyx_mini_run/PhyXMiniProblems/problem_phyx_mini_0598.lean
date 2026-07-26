import Mathlib
import Physlib.Relativity.LorentzGroup.Boosts.Basic
import Physlib.Units.WithDim.Speed

/- USER: The assigned source file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0598

open Dimension

/-!
# Temporal separation from a Lorentz-transformation graph

Two inertial observers `S` and `S'` assign temporal separations `Δt` and
`Δt'` to pairs of events.  The supplied graph plots the `S`-frame temporal
separation against the `S'`-frame spatial separation.  Its vertical scale is
`Δt_a = 6.00 μs`, its right endpoint is at `Δx' = 400 m`, and its rising
straight trace begins two of the six vertical grid intervals above zero.

Signed lengths and times are unit-independent Physlib quantities.  Real
numbers below are used only for unit readouts, dimensionless ratios, grid
counts, and displayed multiple-choice values.
-/

/-! ## Dimensionful quantities and unit readouts -/

/-- A signed, unit-independent physical length. -/
abbrev SignedLengthQuantity : Type :=
  Dimensionful (WithDim L𝓭 ℝ)

/-- A signed, unit-independent physical time. -/
abbrev SignedTimeQuantity : Type :=
  Dimensionful (WithDim T𝓭 ℝ)

/-- Unit choices with time measured in microseconds and all other units SI. -/
def microsecondUnitChoices : UnitChoices :=
  { UnitChoices.SI with time := TimeUnit.microseconds }

/-- Read a signed physical length in metres. -/
def lengthInMeters (length : SignedLengthQuantity) : ℝ :=
  (length UnitChoices.SI).val

/-- Read a signed physical time in seconds. -/
def timeInSeconds (time : SignedTimeQuantity) : ℝ :=
  (time UnitChoices.SI).val

/-- Read a signed physical time in microseconds. -/
def timeInMicroseconds (time : SignedTimeQuantity) : ℝ :=
  (time microsecondUnitChoices).val

/-- The unit-independent signed length whose SI readout is `value` metres. -/
def lengthFromMeters (value : ℝ) : SignedLengthQuantity :=
  CarriesDimension.toDimensionful UnitChoices.SI ⟨value⟩

/-- Read a nonnegative physical speed in metres per second. -/
def speedInMetersPerSecond (speed : DimSpeed) : ℝ :=
  ((speed UnitChoices.SI).val : ℝ)

/-- Physlib's dimensionful vacuum speed of light, read in metres per second. -/
def vacuumSpeedOfLightInMetersPerSecond : ℝ :=
  (DimSpeed.speedOfLight UnitChoices.SI).val

/-! ## Frames and primary-figure vocabulary -/

/-- The two inertial frames occurring in the Lorentz transformation. -/
inductive InertialFrameLabel where
  | S
  | SPrime
  deriving DecidableEq, Repr

/-- Positive and negative directions along the common spatial axis. -/
inductive AxisDirection where
  | positiveX
  | negativeX
  deriving DecidableEq, Repr

/-- The two axes of the supplied graph. -/
inductive FigureAxis where
  | horizontal
  | vertical
  deriving DecidableEq, Fintype, Repr

/-- Physical quantity represented by a graph axis. -/
inductive FigureAxisQuantity where
  | primeSpatialSeparation
  | labTemporalSeparation
  deriving DecidableEq, Repr

/-- Unit printed beside a graph axis. -/
inductive FigureAxisUnit where
  | meters
  | microseconds
  deriving DecidableEq, Repr

/-- Direction of the plotted trace as the horizontal coordinate increases. -/
inductive TraceDirection where
  | rising
  | falling
  deriving DecidableEq, Repr

/-!
The graph in image 598.  The plotted function takes the physical separation
`Δx'` and returns the corresponding physical separation `Δt` measured by `S`.
The grid-count fields retain the geometry used to read the unlabeled
intercept from the raster.
-/
structure TemporalSeparationFigure where
  axisQuantity : FigureAxis → FigureAxisQuantity
  axisUnit : FigureAxis → FigureAxisUnit
  plottedLabTemporalSeparationAt :
    SignedLengthQuantity → SignedTimeQuantity
  verticalScaleDeltaTa : SignedTimeQuantity
  horizontalEndpointDeltaXPrime : SignedLengthQuantity
  horizontalMidpointDeltaXPrime : SignedLengthQuantity
  verticalGridIntervalCount : ℕ
  horizontalGridIntervalCount : ℕ
  traceInterceptGridLevel : ℕ
  traceIsStraight : Bool
  traceDirection : TraceDirection
  traceEndsAtTopRight : Bool

/-!
The independent physical quantities in the scenario.  In particular,
`primeTemporalSeparation` is an observable to be inferred; it is not defined
from the recorded answer or from the graph intercept.
-/
structure TemporalSeparationSetup where
  observerFrame : InertialFrameLabel
  primedFrame : InertialFrameLabel
  primedFrameMotionDirection : AxisDirection
  relativeSpeed : DimSpeed
  primeTemporalSeparation : SignedTimeQuantity
  figure : TemporalSeparationFigure

/-- The dimensionless relative speed `β = v/c`. -/
def speedFractionOfLight (setup : TemporalSeparationSetup) : ℝ :=
  speedInMetersPerSecond setup.relativeSpeed /
    vacuumSpeedOfLightInMetersPerSecond

/-- The Lorentz factor `γ(β)` supplied by Physlib. -/
def lorentzFactor (setup : TemporalSeparationSetup) : ℝ :=
  LorentzGroup.γ (speedFractionOfLight setup)

/-! ## Scenario assumptions and figure/data readouts -/

/-- Frame roles and the sign convention used in the time transformation. -/
structure MatchesTemporalSeparationScenario
    (setup : TemporalSeparationSetup) : Prop where
  labObserverUsesS : setup.observerFrame = .S
  primedObserverUsesSPrime : setup.primedFrame = .SPrime
  framesAreDistinct : setup.observerFrame ≠ setup.primedFrame
  primedFrameMovesAlongPositiveX :
    setup.primedFrameMotionDirection = .positiveX

/-!
Literal labels and geometric readouts from the primary image.  The intercept
is stated as two of six vertical grid intervals, rather than being replaced
by the answer sought for `Δt'`.
-/
structure MatchesTemporalSeparationFigure
    (setup : TemporalSeparationSetup) : Prop where
  horizontalAxisIsDeltaXPrime :
    setup.figure.axisQuantity .horizontal = .primeSpatialSeparation
  verticalAxisIsDeltaT :
    setup.figure.axisQuantity .vertical = .labTemporalSeparation
  horizontalAxisInMeters :
    setup.figure.axisUnit .horizontal = .meters
  verticalAxisInMicroseconds :
    setup.figure.axisUnit .vertical = .microseconds
  verticalScaleMicroseconds :
    timeInMicroseconds setup.figure.verticalScaleDeltaTa = 6
  horizontalEndpointMeters :
    lengthInMeters setup.figure.horizontalEndpointDeltaXPrime = 400
  horizontalMidpointMeters :
    lengthInMeters setup.figure.horizontalMidpointDeltaXPrime = 200
  sixVerticalGridIntervals :
    setup.figure.verticalGridIntervalCount = 6
  fourHorizontalGridIntervals :
    setup.figure.horizontalGridIntervalCount = 4
  interceptAtSecondGridLevel :
    setup.figure.traceInterceptGridLevel = 2
  traceIsStraight : setup.figure.traceIsStraight = true
  traceRises : setup.figure.traceDirection = .rising
  traceEndsAtTopRight : setup.figure.traceEndsAtTopRight = true
  interceptLiesOnTrace :
    timeInMicroseconds
        (setup.figure.plottedLabTemporalSeparationAt (lengthFromMeters 0)) =
      (setup.figure.traceInterceptGridLevel : ℝ) *
        timeInMicroseconds setup.figure.verticalScaleDeltaTa /
          (setup.figure.verticalGridIntervalCount : ℝ)
  midpointLiesOnTrace :
    timeInMicroseconds
        (setup.figure.plottedLabTemporalSeparationAt
          setup.figure.horizontalMidpointDeltaXPrime) =
      2 * timeInMicroseconds setup.figure.verticalScaleDeltaTa / 3
  endpointLiesOnTrace :
    timeInMicroseconds
        (setup.figure.plottedLabTemporalSeparationAt
          setup.figure.horizontalEndpointDeltaXPrime) =
      timeInMicroseconds setup.figure.verticalScaleDeltaTa

/-- Positivity and the subluminal regime required by the Lorentz model. -/
structure HasPhysicalRelativisticParameters
    (setup : TemporalSeparationSetup) : Prop where
  vacuumSpeedOfLightPositive :
    0 < vacuumSpeedOfLightInMetersPerSecond
  nonnegativeSpeedFraction : 0 ≤ speedFractionOfLight setup
  subluminalSpeedFraction : speedFractionOfLight setup < 1
  nonnegativePrimeTemporalSeparation :
    0 ≤ timeInSeconds setup.primeTemporalSeparation

/-! ## Governing physics -/

/-!
The inverse Lorentz time transformation in coherent SI readouts,

`Δt = γ(β) (Δt' + v Δx' / c²)`.

The graph varies `Δx'` while holding the requested `Δt'` fixed.  This is a
generic governing law for every plotted spatial separation and contains no
displayed answer value.
-/
structure SatisfiesLorentzTemporalTransformation
    (setup : TemporalSeparationSetup) : Prop where
  timeTransformation : ∀ deltaXPrime : SignedLengthQuantity,
    timeInSeconds
        (setup.figure.plottedLabTemporalSeparationAt deltaXPrime) =
      lorentzFactor setup *
        (timeInSeconds setup.primeTemporalSeparation +
          speedInMetersPerSecond setup.relativeSpeed *
              lengthInMeters deltaXPrime /
            vacuumSpeedOfLightInMetersPerSecond ^ 2)

/-! ## Displayed alternatives and current target -/

/-- Answer labels in the order printed in the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Temporal-separation value displayed for each answer, in seconds. -/
def displayedDeltaTimePrimeInSeconds : AnswerChoice → ℝ
  | .A => 2 / 1_000_000
  | .B => 13 / 10_000_000
  | .C => 63 / 100_000_000
  | .D => 316 / 100_000_000

/-- The answer label recorded by the source dataset. -/
def recordedDatasetAnswer : AnswerChoice := .C

/-!
Half of the last displayed place for each answer.  Choices A, C, and D have
half-step `5 × 10⁻⁹ s`; the less precise choice B has half-step
`5 × 10⁻⁸ s`.  In particular, matching C states rounding to the printed value
`6.3 × 10⁻⁷ s`, not the physically false exact equality with that decimal.
-/
def displayedToleranceSeconds : AnswerChoice → ℝ
  | .A => 1 / 200_000_000
  | .B => 1 / 20_000_000
  | .C => 1 / 200_000_000
  | .D => 1 / 200_000_000

/-- The computed physical `Δt'` rounds to a displayed answer value. -/
def MatchesDisplayedDeltaTimePrime
    (setup : TemporalSeparationSetup) (choice : AnswerChoice) : Prop :=
  |timeInSeconds setup.primeTemporalSeparation -
      displayedDeltaTimePrimeInSeconds choice| ≤
    displayedToleranceSeconds choice

/-- Exactly one printed alternative agrees with the computed `Δt'`. -/
def IsUniqueMatchingDeltaTimePrime
    (setup : TemporalSeparationSetup) (choice : AnswerChoice) : Prop :=
  MatchesDisplayedDeltaTimePrime setup choice ∧
    ∀ other : AnswerChoice, other ≠ choice →
      ¬ MatchesDisplayedDeltaTimePrime setup other

/-!
The Lorentz transformation and the graph determine
`Δt' ≈ 6.3 × 10⁻⁷ s`, uniquely selecting choice C.

Blueprint: `thm:physics:phyx_mini_0598:target`.
-/
theorem problem_phyx_mini_0598
    (setup : TemporalSeparationSetup)
    (scenario : MatchesTemporalSeparationScenario setup)
    (figure : MatchesTemporalSeparationFigure setup)
    (physical : HasPhysicalRelativisticParameters setup)
    (lorentzLaw : SatisfiesLorentzTemporalTransformation setup) :
    MatchesDisplayedDeltaTimePrime setup .C ∧
      IsUniqueMatchingDeltaTimePrime setup .C := by
  have timeInSeconds_eq_timeInMicroseconds_div
      (time : SignedTimeQuantity) :
      timeInSeconds time = timeInMicroseconds time / 1_000_000 := by
    have h := time.2 UnitChoices.SI microsecondUnitChoices
    rw [timeInSeconds, timeInMicroseconds, h]
    simp [microsecondUnitChoices, UnitChoices.dimScale,
      TimeUnit.microseconds, TimeUnit.scale, TimeUnit.div_eq_val,
      NNReal.smul_def]
    norm_num [TimeUnit.seconds]
    change (time UnitChoices.SI).val =
      (1_000_000 : ℝ) * (time UnitChoices.SI).val / 1_000_000
    ring
  have lightSpeed :
      vacuumSpeedOfLightInMetersPerSecond = 299_792_458 := by
    norm_num [vacuumSpeedOfLightInMetersPerSecond,
      DimSpeed.speedOfLight_in_SI]
  have zeroLength : lengthInMeters (lengthFromMeters 0) = 0 := by
    norm_num [lengthInMeters, lengthFromMeters,
      CarriesDimension.toDimensionful_apply_apply]
  have interceptMicroseconds :
      timeInMicroseconds
          (setup.figure.plottedLabTemporalSeparationAt
            (lengthFromMeters 0)) = 2 := by
    rw [figure.interceptLiesOnTrace, figure.interceptAtSecondGridLevel,
      figure.verticalScaleMicroseconds, figure.sixVerticalGridIntervals]
    norm_num
  have endpointMicroseconds :
      timeInMicroseconds
          (setup.figure.plottedLabTemporalSeparationAt
            setup.figure.horizontalEndpointDeltaXPrime) = 6 := by
    rw [figure.endpointLiesOnTrace, figure.verticalScaleMicroseconds]
  have interceptSeconds :
      timeInSeconds
          (setup.figure.plottedLabTemporalSeparationAt
            (lengthFromMeters 0)) = 2 / 1_000_000 := by
    rw [timeInSeconds_eq_timeInMicroseconds_div, interceptMicroseconds]
  have endpointSeconds :
      timeInSeconds
          (setup.figure.plottedLabTemporalSeparationAt
            setup.figure.horizontalEndpointDeltaXPrime) =
        6 / 1_000_000 := by
    rw [timeInSeconds_eq_timeInMicroseconds_div, endpointMicroseconds]
  have interceptLaw :=
    lorentzLaw.timeTransformation (lengthFromMeters 0)
  rw [interceptSeconds, zeroLength] at interceptLaw
  norm_num at interceptLaw
  have endpointLaw :=
    lorentzLaw.timeTransformation
      setup.figure.horizontalEndpointDeltaXPrime
  rw [endpointSeconds, figure.horizontalEndpointMeters, lightSpeed] at endpointLaw
  norm_num at endpointLaw
  have gammaTimesSpeed :
      lorentzFactor setup *
          speedInMetersPerSecond setup.relativeSpeed =
        (89_875_517_873_681_764 : ℝ) / 100_000_000 := by
    nlinarith [interceptLaw, endpointLaw]
  have gammaTimesBeta :
      lorentzFactor setup * speedFractionOfLight setup =
        (149_896_229 : ℝ) / 50_000_000 := by
    rw [speedFractionOfLight, lightSpeed]
    nlinarith [gammaTimesSpeed]
  have betaAbsLtOne : |speedFractionOfLight setup| < 1 := by
    rw [abs_of_nonneg physical.nonnegativeSpeedFraction]
    exact physical.subluminalSpeedFraction
  have gammaIdentity :
      lorentzFactor setup ^ 2 *
          (1 - speedFractionOfLight setup ^ 2) = 1 := by
    rw [lorentzFactor,
      LorentzGroup.γ_sq (speedFractionOfLight setup) betaAbsLtOne]
    field_simp [LorentzGroup.γ_det_not_zero
      (speedFractionOfLight setup) betaAbsLtOne]
  have gammaSquareValue :
      lorentzFactor setup ^ 2 =
        1 + ((149_896_229 : ℝ) / 50_000_000) ^ 2 := by
    calc
      lorentzFactor setup ^ 2 =
          1 +
            (lorentzFactor setup * speedFractionOfLight setup) ^ 2 := by
        nlinarith [gammaIdentity]
      _ = _ := by rw [gammaTimesBeta]
  have oneSubBetaSquarePositive :
      0 < 1 - speedFractionOfLight setup ^ 2 := by
    have positiveProduct :
        0 <
          (1 - speedFractionOfLight setup) *
            (1 + speedFractionOfLight setup) :=
      mul_pos (sub_pos.mpr physical.subluminalSpeedFraction)
        (by linarith [physical.nonnegativeSpeedFraction])
    nlinarith [positiveProduct]
  have gammaPositive : 0 < lorentzFactor setup := by
    rw [lorentzFactor, LorentzGroup.γ]
    exact one_div_pos.mpr
      (Real.sqrt_pos.2 oneSubBetaSquarePositive)
  have gammaLtUpper : lorentzFactor setup < (16 : ℝ) / 5 := by
    have numericalSquareBound :
        1 + ((149_896_229 : ℝ) / 50_000_000) ^ 2 <
          ((16 : ℝ) / 5) ^ 2 := by
      norm_num
    nlinarith [gammaSquareValue]
  have gammaGtLower : (400 : ℝ) / 127 < lorentzFactor setup := by
    have numericalSquareBound :
        ((400 : ℝ) / 127) ^ 2 <
          1 + ((149_896_229 : ℝ) / 50_000_000) ^ 2 := by
      norm_num
    nlinarith [gammaSquareValue]
  have primeTimeLower :
      (1 : ℝ) / 1_600_000 ≤
        timeInSeconds setup.primeTemporalSeparation := by
    have productNonnegative :
        0 ≤
          ((16 : ℝ) / 5 - lorentzFactor setup) *
            timeInSeconds setup.primeTemporalSeparation :=
      mul_nonneg (sub_nonneg.mpr (le_of_lt gammaLtUpper))
        physical.nonnegativePrimeTemporalSeparation
    nlinarith [interceptLaw, productNonnegative]
  have primeTimeUpper :
      timeInSeconds setup.primeTemporalSeparation ≤
        (127 : ℝ) / 200_000_000 := by
    have productNonnegative :
        0 ≤
          (lorentzFactor setup - (400 : ℝ) / 127) *
            timeInSeconds setup.primeTemporalSeparation :=
      mul_nonneg (sub_nonneg.mpr (le_of_lt gammaGtLower))
        physical.nonnegativePrimeTemporalSeparation
    nlinarith [interceptLaw, productNonnegative]
  have choiceCMatches : MatchesDisplayedDeltaTimePrime setup .C := by
    change
      |timeInSeconds setup.primeTemporalSeparation -
          (63 : ℝ) / 100_000_000| ≤
        (1 : ℝ) / 200_000_000
    rw [abs_le]
    constructor <;> nlinarith [primeTimeLower, primeTimeUpper]
  refine ⟨choiceCMatches, choiceCMatches, ?_⟩
  intro other otherNeC otherMatches
  cases other with
  | A =>
      change
        |timeInSeconds setup.primeTemporalSeparation -
            (2 : ℝ) / 1_000_000| ≤
          (1 : ℝ) / 200_000_000 at otherMatches
      rw [abs_le] at otherMatches
      nlinarith [primeTimeUpper]
  | B =>
      change
        |timeInSeconds setup.primeTemporalSeparation -
            (13 : ℝ) / 10_000_000| ≤
          (1 : ℝ) / 20_000_000 at otherMatches
      rw [abs_le] at otherMatches
      nlinarith [primeTimeUpper]
  | C => exact otherNeC rfl
  | D =>
      change
        |timeInSeconds setup.primeTemporalSeparation -
            (316 : ℝ) / 100_000_000| ≤
          (1 : ℝ) / 200_000_000 at otherMatches
      rw [abs_le] at otherMatches
      nlinarith [primeTimeUpper]

end PhyXMiniProblems.ProblemPhyXMini0598
