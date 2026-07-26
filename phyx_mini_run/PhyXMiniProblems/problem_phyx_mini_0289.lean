import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Physlib.Units.WithDim.Speed

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0289

open Dimension

/-!
# Angular frequency of a translated sinusoidal string wave

The primary figure shows the same sinusoidal string wave at an earlier solid
snapshot and a later dashed snapshot.  The crest labelled `A` moves to the
right by the distance labelled `d`.  Horizontal tick marks are 10 cm apart,
one wavelength spans four tick intervals, and the vertical height labelled
`H` is the peak-to-trough height.

Physical lengths, durations, speeds, wave numbers, and angular frequencies
are represented by Physlib's unit-independent `Dimensionful` quantities.
Real numbers below are used only for explicit unit readouts and for the
dimensionless phase of the sine function.
-/

/-! ## Dimensionful physical quantities and readouts -/

/-- A nonnegative physical length. -/
abbrev LengthQuantity : Type := Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative physical duration. -/
abbrev TimeQuantity : Type := Dimensionful (WithDim T𝓭 NNReal)

/-- A nonnegative propagation speed along the string. -/
abbrev SpeedQuantity : Type := DimSpeed

/-- A nonnegative wave number; radians are dimensionless. -/
abbrev WaveNumberQuantity : Type :=
  Dimensionful (WithDim L𝓭⁻¹ NNReal)

/-- A nonnegative angular frequency; radians are dimensionless. -/
abbrev AngularFrequencyQuantity : Type :=
  Dimensionful (WithDim T𝓭⁻¹ NNReal)

/-- Numerical readout of a physical length in the selected length unit. -/
def lengthReadout (unit : LengthUnit) (length : LengthQuantity) : ℝ :=
  ((length { UnitChoices.SI with length := unit }).val : ℝ)

/-- Numerical readout of a duration in the selected time unit. -/
def timeReadout (unit : TimeUnit) (duration : TimeQuantity) : ℝ :=
  ((duration { UnitChoices.SI with time := unit }).val : ℝ)

/-- Numerical readout of a speed in the selected length and time units. -/
def speedReadout
    (lengthUnit : LengthUnit) (timeUnit : TimeUnit)
    (speed : SpeedQuantity) : ℝ :=
  ((speed { UnitChoices.SI with
      length := lengthUnit
      time := timeUnit }).val : ℝ)

/-- Radian-per-meter readout of a wave number. -/
def waveNumberInRadiansPerMeter (waveNumber : WaveNumberQuantity) : ℝ :=
  ((waveNumber UnitChoices.SI).val : ℝ)

/-- Radian-per-second readout of an angular frequency. -/
def angularFrequencyInRadiansPerSecond
    (angularFrequency : AngularFrequencyQuantity) : ℝ :=
  ((angularFrequency UnitChoices.SI).val : ℝ)

/-! ## Primary-figure labels and physical setup -/

/-- The two depictions of the same wave in the primary figure. -/
inductive Snapshot where
  | earlier
  | later
  deriving DecidableEq, Repr

/-- Line styles distinguishing the two snapshots. -/
inductive CurveStyle where
  | solid
  | dashed
  deriving DecidableEq, Repr

/-- The coordinate axes explicitly labelled in the figure. -/
inductive Axis where
  | horizontal
  | vertical
  deriving DecidableEq, Repr

/-- Printed axis labels. -/
inductive AxisLabel where
  | x
  | y
  deriving DecidableEq, Repr

/-- Roles of the three letter labels visible in the figure. -/
inductive FigureRole where
  | trackedCrest
  | crestTranslation
  | peakToTroughHeight
  deriving DecidableEq, Repr

/-- The labels printed beside the crest and the two measured spans. -/
inductive FigureLabel where
  | A
  | d
  | H
  deriving DecidableEq, Repr

/-- Direction of propagation along the labelled horizontal axis. -/
inductive PropagationDirection where
  | positiveX
  | negativeX
  deriving DecidableEq, Repr

/-!
Independent physical quantities and scalar field for the string wave.

`displacementInMeters x t` is the signed transverse displacement in meters
at an SI position `x` and SI time `t`.  It is a scalar component readout, not
a replacement for any of the dimensionful physical quantities.
-/
structure TravelingStringWaveExperiment where
  crestTravelDistance : LengthQuantity
  elapsedTime : TimeQuantity
  tickSpacing : LengthQuantity
  peakToPeakHeight : LengthQuantity
  amplitude : LengthQuantity
  wavelength : LengthQuantity
  propagationSpeed : SpeedQuantity
  waveNumber : WaveNumberQuantity
  angularFrequency : AngularFrequencyQuantity
  crestPosition : Snapshot → LengthQuantity
  snapshotTime : Snapshot → TimeQuantity
  displacementInMeters : ℝ → ℝ → ℝ
  curveStyle : Snapshot → CurveStyle
  axisLabel : Axis → AxisLabel
  figureLabel : FigureRole → FigureLabel
  propagationDirection : PropagationDirection

/-!
Problem data and geometric readouts from the primary figure.

The first four fields transcribe the stated numerical data.  The remaining
fields record that the solid curve is earlier, the dashed curve is later,
crest `A` moves in positive `x`, the labelled crest is at the fifth tick in
the earlier snapshot, a wavelength spans four tick intervals, and `H` spans
twice the amplitude.  None constrains the requested angular frequency.
-/
structure MatchesProblemAndPrimaryFigure
    (experiment : TravelingStringWaveExperiment) : Prop where
  crestTravelDistanceCentimeters :
    lengthReadout LengthUnit.centimeters experiment.crestTravelDistance = 6
  elapsedTimeMilliseconds :
    timeReadout TimeUnit.milliseconds experiment.elapsedTime = 4
  tickSpacingCentimeters :
    lengthReadout LengthUnit.centimeters experiment.tickSpacing = 10
  peakToPeakHeightMillimeters :
    lengthReadout LengthUnit.millimeters experiment.peakToPeakHeight = 6
  earlierCurveIsSolid : experiment.curveStyle .earlier = .solid
  laterCurveIsDashed : experiment.curveStyle .later = .dashed
  horizontalAxisIsX : experiment.axisLabel .horizontal = .x
  verticalAxisIsY : experiment.axisLabel .vertical = .y
  trackedCrestLabelIsA : experiment.figureLabel .trackedCrest = .A
  translationLabelIsD : experiment.figureLabel .crestTranslation = .d
  heightLabelIsH : experiment.figureLabel .peakToTroughHeight = .H
  motionIsPositiveX : experiment.propagationDirection = .positiveX
  earlierSnapshotIsTimeOrigin :
    timeReadout TimeUnit.seconds (experiment.snapshotTime .earlier) = 0
  snapshotsSeparatedByElapsedTime :
    ∀ unit : TimeUnit,
      timeReadout unit (experiment.snapshotTime .later) =
        timeReadout unit (experiment.snapshotTime .earlier) +
          timeReadout unit experiment.elapsedTime
  crestAInitiallyAtFifthTick :
    ∀ unit : LengthUnit,
      lengthReadout unit (experiment.crestPosition .earlier) =
        5 * lengthReadout unit experiment.tickSpacing
  crestATranslatedByD :
    ∀ unit : LengthUnit,
      lengthReadout unit (experiment.crestPosition .later) =
        lengthReadout unit (experiment.crestPosition .earlier) +
          lengthReadout unit experiment.crestTravelDistance
  wavelengthSpansFourTicks :
    ∀ unit : LengthUnit,
      lengthReadout unit experiment.wavelength =
        4 * lengthReadout unit experiment.tickSpacing
  heightIsPeakToTrough :
    ∀ unit : LengthUnit,
      lengthReadout unit experiment.peakToPeakHeight =
        2 * lengthReadout unit experiment.amplitude

/-- Positivity assumptions selecting a nondegenerate traveling wave. -/
structure HasPhysicalWaveParameters
    (experiment : TravelingStringWaveExperiment) : Prop where
  elapsedTimePositive :
    0 < timeReadout TimeUnit.seconds experiment.elapsedTime
  crestTravelDistancePositive :
    0 < lengthReadout LengthUnit.meters experiment.crestTravelDistance
  tickSpacingPositive :
    0 < lengthReadout LengthUnit.meters experiment.tickSpacing
  amplitudePositive :
    0 < lengthReadout LengthUnit.meters experiment.amplitude
  wavelengthPositive :
    0 < lengthReadout LengthUnit.meters experiment.wavelength
  propagationSpeedPositive :
    0 < speedReadout LengthUnit.meters TimeUnit.seconds
      experiment.propagationSpeed
  waveNumberPositive :
    0 < waveNumberInRadiansPerMeter experiment.waveNumber
  angularFrequencyPositive :
    0 < angularFrequencyInRadiansPerSecond experiment.angularFrequency

/-!
The standard kinematic and sinusoidal-wave laws used by the problem:

* the translated crest obeys `d = v Δt` in every coherent pair of units;
* wave number and wavelength obey `k λ = 2π`;
* angular frequency obeys `ω = k v`;
* a wave traveling in positive `x` has phase `kx - ωt`.

These are general physical laws and contain neither `75π` nor any displayed
answer value.
-/
structure SatisfiesTravelingSinusoidalWaveLaws
    (experiment : TravelingStringWaveExperiment) : Prop where
  crestTranslationKinematics :
    ∀ (lengthUnit : LengthUnit) (timeUnit : TimeUnit),
      lengthReadout lengthUnit experiment.crestTravelDistance =
        speedReadout lengthUnit timeUnit experiment.propagationSpeed *
          timeReadout timeUnit experiment.elapsedTime
  waveNumberWavelengthRelation :
    waveNumberInRadiansPerMeter experiment.waveNumber *
        lengthReadout LengthUnit.meters experiment.wavelength =
      2 * Real.pi
  angularFrequencyWaveSpeedRelation :
    angularFrequencyInRadiansPerSecond experiment.angularFrequency =
      waveNumberInRadiansPerMeter experiment.waveNumber *
        speedReadout LengthUnit.meters TimeUnit.seconds
          experiment.propagationSpeed
  positiveXSinusoidalWaveform :
    ∀ (xMeters tSeconds : ℝ),
      experiment.displacementInMeters xMeters tSeconds =
        lengthReadout LengthUnit.meters experiment.amplitude *
          Real.sin
            (waveNumberInRadiansPerMeter experiment.waveNumber * xMeters -
              angularFrequencyInRadiansPerSecond experiment.angularFrequency *
                tSeconds)

/-! ## Displayed choices and formalization target -/

/-- Labels printed beside the four candidate angular frequencies. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Radian-per-second value printed beside each answer label. -/
def AnswerChoice.radiansPerSecond : AnswerChoice → ℝ
  | .A => 180
  | .B => 200
  | .C => 280
  | .D => 240

/-- The answer label recorded in the supplied dataset. -/
def recordedAnswerChoice : AnswerChoice := .D

/-!
Agreement with a value displayed to the nearest ten radians per second.
The strict half-width also excludes a midpoint tie.
-/
def MatchesNearestTenDisplay
    (angularFrequencyRadiansPerSecond : ℝ) (choice : AnswerChoice) : Prop :=
  |angularFrequencyRadiansPerSecond - choice.radiansPerSecond| < 5

/-!
The 6 cm translation in 4 ms gives speed 15 m/s, while four 10 cm
tick intervals give wavelength 0.4 m.  Hence `ω = 2πv/λ = 75π` rad/s,
which rounds to `2.4 × 10²` rad/s, recorded answer D.

This formalizes blueprint label `thm:physics:phyx_mini_0289:target`.
-/
theorem problem_phyx_mini_0289
    (experiment : TravelingStringWaveExperiment)
    (_figure : MatchesProblemAndPrimaryFigure experiment)
    (_physical : HasPhysicalWaveParameters experiment)
    (_laws : SatisfiesTravelingSinusoidalWaveLaws experiment) :
    angularFrequencyInRadiansPerSecond experiment.angularFrequency =
        75 * Real.pi ∧
      MatchesNearestTenDisplay
        (angularFrequencyInRadiansPerSecond experiment.angularFrequency) .D := by
  have hdistanceConversion :
      lengthReadout LengthUnit.meters experiment.crestTravelDistance =
        (1 / 100 : ℝ) *
          lengthReadout LengthUnit.centimeters experiment.crestTravelDistance := by
    have h := congrArg (fun q : WithDim L𝓭 NNReal => (q.val : ℝ))
      (experiment.crestTravelDistance.2
        ({ UnitChoices.SI with length := LengthUnit.centimeters }) UnitChoices.SI)
    simp [UnitChoices.dimScale, UnitChoices.SI, LengthUnit.centimeters] at h
    convert h using 1 <;>
      norm_num [lengthReadout, UnitChoices.SI, LengthUnit.centimeters]
    exact Or.inl rfl
  have helapsedTimeConversion :
      timeReadout TimeUnit.seconds experiment.elapsedTime =
        (1 / 1000 : ℝ) *
          timeReadout TimeUnit.milliseconds experiment.elapsedTime := by
    have h := congrArg (fun q : WithDim T𝓭 NNReal => (q.val : ℝ))
      (experiment.elapsedTime.2
        ({ UnitChoices.SI with time := TimeUnit.milliseconds }) UnitChoices.SI)
    simp [UnitChoices.dimScale, UnitChoices.SI, TimeUnit.milliseconds] at h
    convert h using 1 <;>
      norm_num [timeReadout, UnitChoices.SI, TimeUnit.milliseconds]
    exact Or.inl rfl
  have htickSpacingConversion :
      lengthReadout LengthUnit.meters experiment.tickSpacing =
        (1 / 100 : ℝ) *
          lengthReadout LengthUnit.centimeters experiment.tickSpacing := by
    have h := congrArg (fun q : WithDim L𝓭 NNReal => (q.val : ℝ))
      (experiment.tickSpacing.2
        ({ UnitChoices.SI with length := LengthUnit.centimeters }) UnitChoices.SI)
    simp [UnitChoices.dimScale, UnitChoices.SI, LengthUnit.centimeters] at h
    convert h using 1 <;>
      norm_num [lengthReadout, UnitChoices.SI, LengthUnit.centimeters]
    exact Or.inl rfl
  have hdistance :
      lengthReadout LengthUnit.meters experiment.crestTravelDistance = 3 / 50 := by
    calc
      lengthReadout LengthUnit.meters experiment.crestTravelDistance =
          (1 / 100 : ℝ) *
            lengthReadout LengthUnit.centimeters experiment.crestTravelDistance :=
        hdistanceConversion
      _ = 3 / 50 := by
        rw [_figure.crestTravelDistanceCentimeters]
        norm_num
  have helapsedTime :
      timeReadout TimeUnit.seconds experiment.elapsedTime = 1 / 250 := by
    calc
      timeReadout TimeUnit.seconds experiment.elapsedTime =
          (1 / 1000 : ℝ) *
            timeReadout TimeUnit.milliseconds experiment.elapsedTime :=
        helapsedTimeConversion
      _ = 1 / 250 := by
        rw [_figure.elapsedTimeMilliseconds]
        norm_num
  have htickSpacing :
      lengthReadout LengthUnit.meters experiment.tickSpacing = 1 / 10 := by
    calc
      lengthReadout LengthUnit.meters experiment.tickSpacing =
          (1 / 100 : ℝ) *
            lengthReadout LengthUnit.centimeters experiment.tickSpacing :=
        htickSpacingConversion
      _ = 1 / 10 := by
        rw [_figure.tickSpacingCentimeters]
        norm_num
  have hspeedLaw :=
    _laws.crestTranslationKinematics LengthUnit.meters TimeUnit.seconds
  rw [hdistance, helapsedTime] at hspeedLaw
  have hspeed :
      speedReadout LengthUnit.meters TimeUnit.seconds experiment.propagationSpeed = 15 := by
    nlinarith
  have hwavelength :=
    _figure.wavelengthSpansFourTicks LengthUnit.meters
  rw [htickSpacing] at hwavelength
  have hwavelengthMeters :
      lengthReadout LengthUnit.meters experiment.wavelength = 2 / 5 := by
    nlinarith
  have hwaveNumberLaw := _laws.waveNumberWavelengthRelation
  rw [hwavelengthMeters] at hwaveNumberLaw
  have hwaveNumber :
      waveNumberInRadiansPerMeter experiment.waveNumber = 5 * Real.pi := by
    nlinarith
  have hfrequencyLaw := _laws.angularFrequencyWaveSpeedRelation
  rw [hwaveNumber, hspeed] at hfrequencyLaw
  have hfrequency :
      angularFrequencyInRadiansPerSecond experiment.angularFrequency =
        75 * Real.pi := by
    nlinarith
  constructor
  · exact hfrequency
  · rw [hfrequency]
    change |(75 : ℝ) * Real.pi - 240| < 5
    have hcosLower : 0 < Real.cos (47 / 30 : ℝ) := by
      let a : ℝ := 47 / 60
      let z : ℂ := (a : ℂ) * Complex.I
      have hz : ‖z‖ ≤ 1 := by
        dsimp [z, a]
        norm_num
      have hnorm := Complex.exp_bound (x := z) (n := 8) hz (by decide)
      have hre := (Complex.abs_re_le_norm
        (Complex.exp z -
          ∑ m ∈ Finset.range 8, z ^ m / m.factorial)).trans hnorm
      dsimp [z, a] at hre
      rw [Complex.exp_ofReal_mul_I_re] at hre
      norm_num [mul_pow, pow_succ, Complex.I_sq, Complex.norm_mul,
        Complex.norm_real, Finset.sum_range_succ, Nat.factorial] at hre
      have hcos : (177 / 250 : ℝ) < Real.cos (47 / 60 : ℝ) := by
        rw [abs_le] at hre
        norm_num at hre ⊢
        linarith
      rw [show (47 / 30 : ℝ) = 2 * (47 / 60 : ℝ) by norm_num,
        Real.cos_two_mul]
      nlinarith [
        sq_nonneg (Real.cos (47 / 60 : ℝ) - (177 / 250 : ℝ))]
    have hcosUpper : Real.cos (49 / 30 : ℝ) < 0 := by
      let a : ℝ := 49 / 60
      let z : ℂ := (a : ℂ) * Complex.I
      have hz : ‖z‖ ≤ 1 := by
        dsimp [z, a]
        norm_num
      have hnorm := Complex.exp_bound (x := z) (n := 8) hz (by decide)
      have hre := (Complex.abs_re_le_norm
        (Complex.exp z -
          ∑ m ∈ Finset.range 8, z ^ m / m.factorial)).trans hnorm
      dsimp [z, a] at hre
      rw [Complex.exp_ofReal_mul_I_re] at hre
      norm_num [mul_pow, pow_succ, Complex.I_sq, Complex.norm_mul,
        Complex.norm_real, Finset.sum_range_succ, Nat.factorial] at hre
      have hcosPositive : (17 / 25 : ℝ) < Real.cos (49 / 60 : ℝ) := by
        rw [abs_le] at hre
        norm_num at hre ⊢
        linarith
      have hcos : Real.cos (49 / 60 : ℝ) < (69 / 100 : ℝ) := by
        rw [abs_le] at hre
        norm_num at hre ⊢
        linarith
      rw [show (49 / 30 : ℝ) = 2 * (49 / 60 : ℝ) by norm_num,
        Real.cos_two_mul]
      have hproduct :
          0 < ((69 / 100 : ℝ) - Real.cos (49 / 60 : ℝ)) *
            ((69 / 100 : ℝ) + Real.cos (49 / 60 : ℝ)) := by
        positivity
      nlinarith
    have hpiLower : (47 / 15 : ℝ) < Real.pi := by
      by_contra h
      have hhalf : Real.pi / 2 ≤ (47 / 30 : ℝ) := by
        linarith
      have hcosNonpositive : Real.cos (47 / 30 : ℝ) ≤ 0 := by
        have hmono := Real.cos_le_cos_of_nonneg_of_le_pi
          (x := Real.pi / 2) (y := (47 / 30 : ℝ))
          (by positivity) (by linarith [Real.two_le_pi]) hhalf
        simpa using hmono
      linarith
    have hpiUpper : Real.pi < (49 / 15 : ℝ) := by
      by_contra h
      have hhalf : (49 / 30 : ℝ) ≤ Real.pi / 2 := by
        linarith
      have hcosNonnegative : 0 ≤ Real.cos (49 / 30 : ℝ) := by
        have hmono := Real.cos_le_cos_of_nonneg_of_le_pi
          (x := (49 / 30 : ℝ)) (y := Real.pi / 2)
          (by norm_num) (by linarith [Real.pi_pos]) hhalf
        simpa using hmono
      linarith
    rw [abs_lt]
    constructor <;> nlinarith

end PhyXMiniProblems.ProblemPhyXMini0289
