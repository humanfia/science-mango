import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Physlib.ClassicalMechanics.HarmonicOscillator.Solution
import Physlib.Units.WithDim.Basic

/- USER: The assigned Lean file did not exist when this autoformalization task began. -/

/-!
# Passage times for a block in simple harmonic motion

At the displayed time origin, a `500 g` block attached to a spring is moving
right from the nominal position `x = 15 cm`.  The primary graph places the
positive turning point `x = 25 cm` at `t = 0.30 s`, labels the period
`T = 2.0 s`, and shows a negative turning point at `-25 cm`.  The question asks
when, during the first displayed cycle, the block passes `x = 20 cm`.

The physical mass, positions, velocity, and durations below are unit-independent
Physlib quantities.  Physlib's one-dimensional `HarmonicOscillator` supplies
the governing trajectory; its scalar fields are connected explicitly to
coherent SI readouts.  The plotted `15 cm` start is treated as a nominal
nearest-centimetre observation, since taking every printed decimal as an exact
real equality would make it inconsistent with the exactly sinusoidal
`25 cm`, `0.30 s`, and `2.0 s` data.

Assumption/target boundary:

* `MatchesProblemAndPrimaryGraph` contains only the stated apparatus, axis
  labels, numerical data, qualitative direction, and primary-image readouts.
* `SatisfiesSimpleHarmonicMotion` connects those physical quantities to
  Physlib's general oscillator trajectory, amplitude, and period laws.
* There are no previous-part results.
* The two `20 cm` passage times, their first-cycle characterization, and the
  comparison with displayed answer choice C occur only in the conclusion of
  `problem_phyx_mini_0717`.
-/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0717

open Dimension

/-! ## Dimensionful physical quantities and coherent readouts -/

/-- A nonnegative physical mass. -/
abbrev MassQuantity : Type := Dimensionful (WithDim M𝓭 NNReal)

/-- A nonnegative physical length, used for the oscillation amplitude. -/
abbrev LengthQuantity : Type := Dimensionful (WithDim L𝓭 NNReal)

/-- A signed displacement along the horizontal spring axis. -/
abbrev SignedDisplacementQuantity : Type :=
  Dimensionful (WithDim L𝓭 ℝ)

/-- A nonnegative physical duration. -/
abbrev DurationQuantity : Type := Dimensionful (WithDim T𝓭 NNReal)

/-- A signed one-dimensional velocity along the spring axis. -/
abbrev SignedVelocityQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * T𝓭⁻¹) ℝ)

/-- Read a physical mass in kilograms. -/
def massInKilograms (mass : MassQuantity) : ℝ :=
  ((mass UnitChoices.SI).val : ℝ)

/-- Read a nonnegative length in a selected length unit. -/
def lengthReadout (unit : LengthUnit) (length : LengthQuantity) : ℝ :=
  ((length {UnitChoices.SI with length := unit}).val : ℝ)

/-- Read a signed displacement in a selected length unit. -/
def displacementReadout
    (unit : LengthUnit) (displacement : SignedDisplacementQuantity) : ℝ :=
  (displacement {UnitChoices.SI with length := unit}).val

/-- Read a duration in a selected time unit. -/
def durationReadout (unit : TimeUnit) (duration : DurationQuantity) : ℝ :=
  ((duration {UnitChoices.SI with time := unit}).val : ℝ)

/-- Read a signed velocity in coherent selected length and time units. -/
def velocityReadout
    (lengthUnit : LengthUnit) (timeUnit : TimeUnit)
    (velocity : SignedVelocityQuantity) : ℝ :=
  (velocity {UnitChoices.SI with
    length := lengthUnit, time := timeUnit}).val

/-- Metre readout of a nonnegative physical length. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.meters length

/-- Metre readout of a signed displacement. -/
def displacementInMeters (displacement : SignedDisplacementQuantity) : ℝ :=
  displacementReadout LengthUnit.meters displacement

/-- Second readout of a physical duration. -/
def durationInSeconds (duration : DurationQuantity) : ℝ :=
  durationReadout TimeUnit.seconds duration

/-- Metres-per-second readout of a signed axial velocity. -/
def velocityInMetersPerSecond (velocity : SignedVelocityQuantity) : ℝ :=
  velocityReadout LengthUnit.meters TimeUnit.seconds velocity

/-! ## Apparatus and primary-graph evidence -/

/-- The two coordinate axes shown in the supplied graph. -/
inductive GraphAxis where
  | horizontal
  | vertical
  deriving DecidableEq, Repr

/-- The physical quantity named by each graph-axis label. -/
inductive AxisQuantity where
  | time_t
  | displacement_x
  deriving DecidableEq, Repr

/-- The restoring element named in the problem. -/
inductive RestoringElement where
  | idealSpring
  deriving DecidableEq, Repr

/-- The undamped motion regime represented by the sinusoidal graph. -/
inductive MotionRegime where
  | simpleHarmonic
  deriving DecidableEq, Repr

/--
Typed quantities and qualitative rendering features read from the primary
displacement--time graph.
-/
structure DisplacementTimeGraph where
  axisQuantity : GraphAxis → AxisQuantity
  horizontalTimeUnit : TimeUnit
  verticalLengthUnit : LengthUnit
  initialTime : DurationQuantity
  initialPosition : SignedDisplacementQuantity
  maximumTime : DurationQuantity
  maximumDisplacement : LengthQuantity
  minimumDisplacement : SignedDisplacementQuantity
  annotatedPeriod : DurationQuantity
  dashedMarkerTime : DurationQuantity
  sinusoidalCurveVisible : Bool
  periodArrowVisible : Bool
  dashedMarkerReachesPositivePeak : Bool

/-!
The physical setup.  `requestedPosition` is the position named in the question,
not a claimed solution time.  The oscillator's initial velocity is independent
because the source gives only its direction, not its magnitude.
-/
structure SpringOscillationSetup where
  blockMass : MassQuantity
  initialVelocity : SignedVelocityQuantity
  requestedPosition : SignedDisplacementQuantity
  restoringElement : RestoringElement
  motionRegime : MotionRegime
  graph : DisplacementTimeGraph
  oscillator : ClassicalMechanics.HarmonicOscillator
  initialConditions :
    ClassicalMechanics.HarmonicOscillator.InitialConditions

/-!
Problem data and calibrated readouts from the primary image.  The graph itself
shows `15 cm`, `25 cm`, `-25 cm`, the dashed `0.3 s` marker, and `T = 2.0 s`;
these primary-image values supersede the caption's rough visual estimates.
-/
structure MatchesProblemAndPrimaryGraph
    (setup : SpringOscillationSetup) : Prop where
  massKilograms : massInKilograms setup.blockMass = 1 / 2
  attachedToSpring : setup.restoringElement = .idealSpring
  statedMotionRegime : setup.motionRegime = .simpleHarmonic
  horizontalAxisLabel :
    setup.graph.axisQuantity .horizontal = .time_t
  verticalAxisLabel :
    setup.graph.axisQuantity .vertical = .displacement_x
  horizontalAxisUnit : setup.graph.horizontalTimeUnit = TimeUnit.seconds
  verticalAxisUnit : setup.graph.verticalLengthUnit = LengthUnit.centimeters
  initialTimeSeconds : durationInSeconds setup.graph.initialTime = 0
  initialPositionCentimeters :
    displacementReadout LengthUnit.centimeters setup.graph.initialPosition = 15
  initiallyMovingRight : 0 < velocityInMetersPerSecond setup.initialVelocity
  maximumTimeSeconds : durationInSeconds setup.graph.maximumTime = 3 / 10
  maximumDisplacementCentimeters :
    lengthReadout LengthUnit.centimeters setup.graph.maximumDisplacement = 25
  minimumDisplacementCentimeters :
    displacementReadout LengthUnit.centimeters setup.graph.minimumDisplacement = -25
  requestedPositionCentimeters :
    displacementReadout LengthUnit.centimeters setup.requestedPosition = 20
  periodAnnotationSeconds :
    durationInSeconds setup.graph.annotatedPeriod = 2
  dashedMarkerSeconds :
    durationInSeconds setup.graph.dashedMarkerTime = 3 / 10
  dashedMarkerAtMaximumTime :
    durationInSeconds setup.graph.dashedMarkerTime =
      durationInSeconds setup.graph.maximumTime
  sinusoidalCurveShown : setup.graph.sinusoidalCurveVisible = true
  periodArrowShown : setup.graph.periodArrowVisible = true
  dashedMarkerReachesPeak :
    setup.graph.dashedMarkerReachesPositivePeak = true

/--
A scalar oscillator coordinate fits a position displayed to the nearest
centimetre when the SI readouts differ by at most half a centimetre.
-/
def FitsNearestCentimeterReading
    (modelPositionMeters displayedPositionMeters : ℝ) : Prop :=
  |modelPositionMeters - displayedPositionMeters| ≤ 1 / 200

/-!
The governing simple-harmonic-motion interface.

Physlib defines the oscillator from positive mass and spring constant, its
trajectory from arbitrary initial position and velocity, its recovered
amplitude from those initial conditions, and its period as `2 * pi / omega`.
These fields connect that general model to the dimensionful apparatus and
graph readouts.  No `20 cm` passage time or answer-choice value occurs here.
-/
structure SatisfiesSimpleHarmonicMotion
    (setup : SpringOscillationSetup) : Prop where
  oscillatorMassReadout :
    setup.oscillator.m = massInKilograms setup.blockMass
  initialPositionFitsDisplayedReading :
    FitsNearestCentimeterReading
      (setup.initialConditions.x₀ 0)
      (displacementInMeters setup.graph.initialPosition)
  initialVelocityReadout :
    setup.initialConditions.v₀ 0 =
      velocityInMetersPerSecond setup.initialVelocity
  amplitudeReadout :
    (ClassicalMechanics.HarmonicOscillator.AmplitudePhase.fromInitialConditions
        setup.oscillator setup.initialConditions).A =
      lengthInMeters setup.graph.maximumDisplacement
  positiveMaximumAtMarkedTime :
    (setup.initialConditions.trajectory setup.oscillator
        ⟨durationInSeconds setup.graph.maximumTime⟩) 0 =
      lengthInMeters setup.graph.maximumDisplacement
  oscillatorPeriodReadout :
    setup.oscillator.period = durationInSeconds setup.graph.annotatedPeriod

/-! ## Displayed choices and target conclusion -/

/-- Labels printed beside the four answer choices. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- The time in seconds printed beside each answer label. -/
def answerChoiceInSeconds : AnswerChoice → ℝ
  | .A => 41 / 100
  | .B => 46 / 100
  | .C => 51 / 100
  | .D => 56 / 100

/-- The answer label recorded in the supplied dataset metadata. -/
def recordedAnswerChoice : AnswerChoice := .C

/-- Agreement with a displayed time to within `0.01 s`. -/
def WithinOneHundredthOfDisplayedAnswer
    (timeSeconds : ℝ) (choice : AnswerChoice) : Prop :=
  |timeSeconds - answerChoiceInSeconds choice| < 1 / 100

/-!
During the first cycle `[0,T)`, the `20 cm` level is attained exactly once on
each side of the positive turning point.  Since `omega = pi rad/s`, the times
are

`0.30 - arccos (20/25) / pi` and
`0.30 + arccos (20/25) / pi` seconds.

The later time is within `0.01 s` of the recorded `0.51 s` choice and is no
farther from choice C than from any displayed alternative.  This formalizes
`thm:physics:phyx_mini_0717:target`.
-/
theorem problem_phyx_mini_0717
    (setup : SpringOscillationSetup)
    (hData : MatchesProblemAndPrimaryGraph setup)
    (hSHM : SatisfiesSimpleHarmonicMotion setup) :
    (∀ t : Time,
      0 ≤ t.val ∧ t.val < durationInSeconds setup.graph.annotatedPeriod →
        ((setup.initialConditions.trajectory setup.oscillator t) 0 =
            displacementInMeters setup.requestedPosition ↔
          t.val =
              3 / 10 - Real.arccos ((4 : ℝ) / 5) / Real.pi ∨
          t.val =
              3 / 10 + Real.arccos ((4 : ℝ) / 5) / Real.pi)) ∧
      WithinOneHundredthOfDisplayedAnswer
        (3 / 10 + Real.arccos ((4 : ℝ) / 5) / Real.pi)
        recordedAnswerChoice ∧
      ∀ choice : AnswerChoice,
        |(3 / 10 + Real.arccos ((4 : ℝ) / 5) / Real.pi) -
            answerChoiceInSeconds recordedAnswerChoice| ≤
          |(3 / 10 + Real.arccos ((4 : ℝ) / 5) / Real.pi) -
            answerChoiceInSeconds choice| := by
  have length_centimeters_eq
      (q : LengthQuantity) :
      lengthReadout LengthUnit.centimeters q = 100 * lengthInMeters q := by
    change
      ((q {UnitChoices.SI with length := LengthUnit.centimeters}).val : ℝ) =
        100 * ((q UnitChoices.SI).val : ℝ)
    rw [q.property UnitChoices.SI
      {UnitChoices.SI with length := LengthUnit.centimeters}]
    norm_num [UnitChoices.dimScale, LengthUnit.centimeters, LengthUnit.meters,
      LengthUnit.scale, LengthUnit.div_eq_val, NNReal.smul_def]
    left
    rfl
  have displacement_centimeters_eq
      (q : SignedDisplacementQuantity) :
      displacementReadout LengthUnit.centimeters q =
        100 * displacementInMeters q := by
    change
      (q {UnitChoices.SI with length := LengthUnit.centimeters}).val =
        100 * (q UnitChoices.SI).val
    rw [q.property UnitChoices.SI
      {UnitChoices.SI with length := LengthUnit.centimeters}]
    norm_num [UnitChoices.dimScale, LengthUnit.centimeters, LengthUnit.meters,
      LengthUnit.scale, LengthUnit.div_eq_val, NNReal.smul_def]
    left
    rfl
  have hMaximumMeters :
      lengthInMeters setup.graph.maximumDisplacement = 1 / 4 := by
    nlinarith [
      length_centimeters_eq setup.graph.maximumDisplacement,
      hData.maximumDisplacementCentimeters]
  have hRequestedMeters :
      displacementInMeters setup.requestedPosition = 1 / 5 := by
    nlinarith [
      displacement_centimeters_eq setup.requestedPosition,
      hData.requestedPositionCentimeters]
  have hPeriod : setup.oscillator.period = 2 :=
    hSHM.oscillatorPeriodReadout.trans hData.periodAnnotationSeconds
  have hOmega : setup.oscillator.ω = Real.pi := by
    rw [ClassicalMechanics.HarmonicOscillator.period_eq] at hPeriod
    rw [div_eq_iff setup.oscillator.ω_ne_zero] at hPeriod
    nlinarith
  let ap :=
    ClassicalMechanics.HarmonicOscillator.AmplitudePhase.fromInitialConditions
      setup.oscillator setup.initialConditions
  have hAmplitude : ap.A = 1 / 4 := by
    dsimp [ap]
    exact hSHM.amplitudeReadout.trans hMaximumMeters
  have hPeak :
      (setup.initialConditions.trajectory setup.oscillator
          ⟨(3 : ℝ) / 10⟩) 0 = 1 / 4 := by
    simpa [hData.maximumTimeSeconds, hMaximumMeters] using
      hSHM.positiveMaximumAtMarkedTime
  have hPeakNormal :
      (setup.initialConditions.trajectory setup.oscillator
          ⟨(3 : ℝ) / 10⟩) 0 =
        ap.A *
          Real.cos
            (setup.oscillator.ω * ((3 : ℝ) / 10) - ap.φ) := by
    simpa [ap] using congrArg (fun v => v 0)
      (ClassicalMechanics.HarmonicOscillator.InitialConditions.trajectory_eq_cos
        setup.oscillator setup.initialConditions ⟨(3 : ℝ) / 10⟩)
  have hCosPeak :
      Real.cos (Real.pi * ((3 : ℝ) / 10) - ap.φ) = 1 := by
    rw [hAmplitude, hOmega] at hPeakNormal
    nlinarith [hPeak, hPeakNormal]
  obtain ⟨phaseIndex, hPhase⟩ :=
    (Real.cos_eq_one_iff
      (Real.pi * ((3 : ℝ) / 10) - ap.φ)).mp hCosPeak
  have hTrajectory (t : Time) :
      (setup.initialConditions.trajectory setup.oscillator t) 0 =
        (1 / 4 : ℝ) *
          Real.cos (Real.pi * (t.val - 3 / 10)) := by
    have hNormal :
        (setup.initialConditions.trajectory setup.oscillator t) 0 =
          ap.A *
            Real.cos
              (setup.oscillator.ω * t.val - ap.φ) := by
      simpa [ap] using congrArg (fun v => v 0)
        (ClassicalMechanics.HarmonicOscillator.InitialConditions.trajectory_eq_cos
          setup.oscillator setup.initialConditions t)
    rw [hNormal, hAmplitude, hOmega]
    have hArgument :
        Real.pi * t.val - ap.φ =
          Real.pi * (t.val - 3 / 10) +
            (phaseIndex : ℝ) * (2 * Real.pi) := by
      rw [hPhase]
      ring
    rw [hArgument, Real.cos_periodic.int_mul phaseIndex]
  let a := Real.arccos ((4 : ℝ) / 5)
  have hArccosArctan :
      a = Real.arctan ((3 : ℝ) / 4) := by
    dsimp [a]
    rw [Real.arccos_eq_arctan (by norm_num)]
    have hSqrt :
        Real.sqrt (1 - ((4 : ℝ) / 5) ^ 2) = 3 / 5 := by
      rw [show (1 : ℝ) - (4 / 5) ^ 2 = (3 / 5) ^ 2 by norm_num]
      rw [Real.sqrt_sq_eq_abs,
        abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3 / 5)]
    rw [hSqrt]
    norm_num
  have hArccosPositive : 0 < a := by
    dsimp [a]
    exact Real.arccos_pos.mpr (by norm_num)
  have hArccosLtQuarterPi : a < Real.pi / 4 := by
    rw [hArccosArctan, ← Real.arctan_one]
    exact Real.arctan_strictMono (by norm_num)
  have hRoots (t : ℝ) (ht0 : 0 ≤ t) (ht2 : t < 2) :
      ((1 : ℝ) / 4 * Real.cos (Real.pi * (t - 3 / 10)) = 1 / 5 ↔
        t = 3 / 10 - a / Real.pi ∨
        t = 3 / 10 + a / Real.pi) := by
    have hArgumentLower :
        -(3 * Real.pi / 10) ≤ Real.pi * (t - 3 / 10) := by
      nlinarith [Real.pi_pos]
    have hArgumentUpper :
        Real.pi * (t - 3 / 10) < 17 * Real.pi / 10 := by
      nlinarith [Real.pi_pos]
    constructor
    · intro h
      have hCos :
          Real.cos (Real.pi * (t - 3 / 10)) = Real.cos a := by
        have hCosArccos : Real.cos a = (4 : ℝ) / 5 := by
          dsimp [a]
          exact Real.cos_arccos (by norm_num) (by norm_num)
        rw [hCosArccos]
        nlinarith
      obtain ⟨k, hk | hk⟩ := Real.cos_eq_cos_iff.mp hCos
      · have hkLt : (k : ℝ) < 1 := by
          nlinarith [Real.pi_pos]
        have hkGt : (-1 : ℝ) < (k : ℝ) := by
          nlinarith [Real.pi_pos]
        have hkZero : k = 0 := by
          norm_cast at hkLt hkGt
          omega
        subst k
        right
        simp only [Int.cast_zero, mul_zero, zero_mul] at hk
        field_simp [Real.pi_ne_zero]
        nlinarith
      · have hkLt : (k : ℝ) < 1 := by
          nlinarith [Real.pi_pos]
        have hkGt : (-1 : ℝ) < (k : ℝ) := by
          nlinarith [Real.pi_pos]
        have hkZero : k = 0 := by
          norm_cast at hkLt hkGt
          omega
        subst k
        left
        simp only [Int.cast_zero, mul_zero, zero_mul] at hk
        field_simp [Real.pi_ne_zero]
        nlinarith
    · rintro (rfl | rfl)
      · have hArgument :
            Real.pi * (3 / 10 - a / Real.pi - 3 / 10) = -a := by
          field_simp [Real.pi_ne_zero]
          ring
        rw [hArgument, Real.cos_neg]
        dsimp [a]
        rw [Real.cos_arccos] <;> norm_num
      · have hArgument :
            Real.pi * (3 / 10 + a / Real.pi - 3 / 10) = a := by
          field_simp [Real.pi_ne_zero]
          ring
        rw [hArgument]
        dsimp [a]
        rw [Real.cos_arccos] <;> norm_num
  have hTwiceArctan :
      2 * Real.arctan ((3 : ℝ) / 4) =
        Real.arctan ((24 : ℝ) / 7) := by
    rw [Real.two_mul_arctan] <;> norm_num
  have hFourTimesArctan :
      4 * Real.arctan ((3 : ℝ) / 4) =
        Real.arctan ((-336 : ℝ) / 527) + Real.pi := by
    rw [show 4 * Real.arctan ((3 : ℝ) / 4) =
      2 * (2 * Real.arctan ((3 : ℝ) / 4)) by ring, hTwiceArctan]
    rw [Real.two_mul_arctan_add_pi] <;> norm_num
  have hArctanSum :
      Real.arctan ((-336 : ℝ) / 527) +
          Real.arctan ((3 : ℝ) / 4) =
        Real.arctan ((237 : ℝ) / 3116) := by
    rw [Real.arctan_add] <;> norm_num
  have hSmallArctanPositive :
      0 < Real.arctan ((237 : ℝ) / 3116) := by
    positivity
  have hArccosLower : Real.pi / 5 < a := by
    rw [hArccosArctan]
    nlinarith [hFourTimesArctan, hArctanSum]
  have hFourTimesArctan' :
      4 * Real.arctan ((3 : ℝ) / 4) =
        Real.pi - Real.arctan ((336 : ℝ) / 527) := by
    rw [hFourTimesArctan,
      show ((-336 : ℝ) / 527) = -((336 : ℝ) / 527) by norm_num,
      Real.arctan_neg]
    ring
  have hTwiceAuxiliaryArctan :
      2 * Real.arctan ((336 : ℝ) / 527) =
        Real.arctan ((354144 : ℝ) / 164833) := by
    rw [Real.two_mul_arctan] <;> norm_num
  have hQuarterPiLtTwiceAuxiliary :
      Real.pi / 4 < 2 * Real.arctan ((336 : ℝ) / 527) := by
    rw [hTwiceAuxiliaryArctan, ← Real.arctan_one]
    exact Real.arctan_strictMono (by norm_num)
  have hArccosUpper : a < 7 * Real.pi / 32 := by
    rw [hArccosArctan]
    nlinarith [hFourTimesArctan']
  have hRatioLower : (1 : ℝ) / 5 < a / Real.pi := by
    rw [lt_div_iff₀ Real.pi_pos]
    simpa [div_eq_mul_inv, mul_comm] using hArccosLower
  have hRatioUpper : a / Real.pi < (7 : ℝ) / 32 := by
    rw [div_lt_iff₀ Real.pi_pos]
    simpa [div_eq_mul_inv, mul_comm, mul_assoc] using hArccosUpper
  have hLaterTimeLower : (1 : ℝ) / 2 < 3 / 10 + a / Real.pi := by
    linarith only [hRatioLower]
  have hLaterTimeUpper : 3 / 10 + a / Real.pi < (13 : ℝ) / 25 := by
    linarith only [hRatioUpper]
  have hWithin :
      WithinOneHundredthOfDisplayedAnswer
        (3 / 10 + a / Real.pi) recordedAnswerChoice := by
    change |(3 / 10 + a / Real.pi) - 51 / 100| < 1 / 100
    rw [abs_lt]
    constructor <;>
      linarith only [hLaterTimeLower, hLaterTimeUpper]
  refine ⟨?_, ?_, ?_⟩
  · intro t ht
    rw [hData.periodAnnotationSeconds] at ht
    rw [hTrajectory, hRequestedMeters]
    simpa [a] using hRoots t.val ht.1 ht.2
  · simpa [a] using hWithin
  · intro choice
    change |(3 / 10 + a / Real.pi) - 51 / 100| < 1 / 100 at hWithin
    cases choice
    · change |(3 / 10 + a / Real.pi) - 51 / 100| ≤
        |(3 / 10 + a / Real.pi) - 41 / 100|
      have hRight :
          |(3 / 10 + a / Real.pi) - 41 / 100| =
            (3 / 10 + a / Real.pi) - 41 / 100 :=
        abs_of_nonneg (by linarith only [hLaterTimeLower])
      rw [hRight]
      linarith only [hWithin, hLaterTimeLower]
    · change |(3 / 10 + a / Real.pi) - 51 / 100| ≤
        |(3 / 10 + a / Real.pi) - 46 / 100|
      have hRight :
          |(3 / 10 + a / Real.pi) - 46 / 100| =
            (3 / 10 + a / Real.pi) - 46 / 100 :=
        abs_of_nonneg (by linarith only [hLaterTimeLower])
      rw [hRight]
      linarith only [hWithin, hLaterTimeLower]
    · rfl
    · change |(3 / 10 + a / Real.pi) - 51 / 100| ≤
        |(3 / 10 + a / Real.pi) - 56 / 100|
      have hRight :
          |(3 / 10 + a / Real.pi) - 56 / 100| =
            -((3 / 10 + a / Real.pi) - 56 / 100) :=
        abs_of_nonpos (by linarith only [hLaterTimeUpper])
      rw [hRight]
      linarith only [hWithin, hLaterTimeUpper]

end PhyXMiniProblems.ProblemPhyXMini0717
