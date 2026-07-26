import Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle
import Physlib.Units.WithDim.Speed

/-!
# Doppler ultrasound measurement of arterial blood speed

This file models problem `phyx_mini_0324`. A stationary pulse-echo ultrasound
transducer sends sound through a human arm and detects sound reflected by
moving arterial blood. The detected frequency varies over a pulse cycle. The
primary figure places the label `Incident ultrasound` above the artery, draws
a dashed incident ray meeting the artery boundary, and labels the angle
between the ray and the artery by `θ`.

Frequency and speed are represented by unit-independent Physlib quantities.
Real numbers occur only as named-unit readouts, angle readouts, and displayed
answer values.
-/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0324

open Dimension

/-! ## Dimensionful quantities and named-unit readouts -/

/-- A nonnegative physical acoustic frequency with inverse-time dimension. -/
abbrev FrequencyQuantity : Type :=
  Dimensionful (WithDim T𝓭⁻¹ NNReal)

/-- A nonnegative physical speed, independent of the units used to read it. -/
abbrev SpeedQuantity : Type := DimSpeed

/-- Read a physical frequency in inverse units of the selected time unit. -/
def frequencyReadout
    (timeUnit : TimeUnit) (frequency : FrequencyQuantity) : ℝ :=
  ((frequency {UnitChoices.SI with time := timeUnit}).val : ℝ)

/-- Read a physical speed in the selected length unit per selected time unit. -/
def speedReadout
    (lengthUnit : LengthUnit) (timeUnit : TimeUnit)
    (speed : SpeedQuantity) : ℝ :=
  ((speed {UnitChoices.SI with
    length := lengthUnit, time := timeUnit}).val : ℝ)

/-- Hertz readout of a physical acoustic frequency. -/
def frequencyInHertz (frequency : FrequencyQuantity) : ℝ :=
  frequencyReadout TimeUnit.seconds frequency

/-- Metres-per-second readout of a physical speed. -/
def speedInMetersPerSecond (speed : SpeedQuantity) : ℝ :=
  speedReadout LengthUnit.meters TimeUnit.seconds speed

/-- Convert a numerical degree readout into Mathlib's physical angle type. -/
def degrees (value : ℝ) : Real.Angle :=
  ((value * Real.pi / 180 : ℝ) : Real.Angle)

/-! ## Physical roles and primary-figure labels -/

/-- The acoustic propagation medium named in the problem. -/
inductive AcousticMedium where
  | humanArm
  deriving DecidableEq, Repr

/-- The physical target that returns the detected ultrasound echo. -/
inductive EchoTarget where
  | arterialBlood
  deriving DecidableEq, Repr

/-- The two region labels printed in the supplied bitmap. -/
inductive FigureRegionLabel where
  | incidentUltrasound
  | artery
  deriving DecidableEq, Repr

/-!
Discrete information visible in the primary bitmap. The image is schematic,
so it supplies an upper/lower ordering and a labelled angle but no metric
distance or pixel-derived physical length.
-/
structure UltrasoundArteryFigure where
  upperRegionLabel : FigureRegionLabel
  lowerRegionLabel : FigureRegionLabel
  showsHorizontalArteryBoundary : Bool
  showsDashedIncidentRay : Bool
  incidentRayMeetsArteryBoundary : Bool
  displayedAngle : Real.Angle
  angleIsBetweenRayAndArtery : Bool

/-!
Physical quantities throughout one blood-pulse cycle. `PulsePhase` is kept
abstract because the source specifies variation and a phase attaining the
maximum shift, but gives no time parametrization. The reflected frequencies
and blood speeds are independent physical quantities; the Doppler law below
relates them rather than defining either from the requested answer.
-/
structure PulsedBloodDopplerSetup (PulsePhase : Type) where
  medium : AcousticMedium
  echoTarget : EchoTarget
  emittedFrequency : FrequencyQuantity
  reflectedFrequencyAtSurface : PulsePhase → FrequencyQuantity
  soundSpeedInArm : SpeedQuantity
  bloodSpeedAlongArtery : PulsePhase → SpeedQuantity
  phaseOfMaximumFrequencyIncrease : PulsePhase
  beamArteryAngle : Real.Angle
  transducerIsStationary : Bool
  bloodMotionIsAlongArtery : Bool
  echoReturnsToSurfaceTransducer : Bool
  figure : UltrasoundArteryFigure

/-!
The qualitative geometry read directly from the primary image and prose. It
contains no frequency or blood-speed answer.
-/
structure MatchesPrimaryFigureAndScenario
    {PulsePhase : Type} (setup : PulsedBloodDopplerSetup PulsePhase) : Prop where
  mediumIsHumanArm : setup.medium = .humanArm
  targetIsArterialBlood : setup.echoTarget = .arterialBlood
  upperLabelIsIncidentUltrasound :
    setup.figure.upperRegionLabel = .incidentUltrasound
  lowerLabelIsArtery : setup.figure.lowerRegionLabel = .artery
  arteryBoundaryShown : setup.figure.showsHorizontalArteryBoundary = true
  dashedIncidentRayShown : setup.figure.showsDashedIncidentRay = true
  incidentRayMeetsBoundary :
    setup.figure.incidentRayMeetsArteryBoundary = true
  displayedAngleAgrees :
    setup.figure.displayedAngle = setup.beamArteryAngle
  angleHasFigureMeaning : setup.figure.angleIsBetweenRayAndArtery = true
  stationaryPulseEchoTransducer : setup.transducerIsStationary = true
  arterialFlowDirection : setup.bloodMotionIsAlongArtery = true
  echoReturnsToTransducer : setup.echoReturnsToSurfaceTransducer = true

/-!
Numerical data from the problem statement. The selected phase is characterized
by the largest measured reflected-frequency increase and has the stated
`5495 Hz` increase. No numerical value of blood speed occurs here.
-/
structure MatchesProblemReadouts
    {PulsePhase : Type} (setup : PulsedBloodDopplerSetup PulsePhase) : Prop where
  emittedFrequencyHertz :
    frequencyInHertz setup.emittedFrequency = 5_000_000
  soundSpeedMetersPerSecond :
    speedInMetersPerSecond setup.soundSpeedInArm = 1540
  beamArteryAngleDegrees : setup.beamArteryAngle = degrees 20
  maximumFrequencyIncreaseHertz :
    frequencyInHertz
          (setup.reflectedFrequencyAtSurface
            setup.phaseOfMaximumFrequencyIncrease) -
        frequencyInHertz setup.emittedFrequency = 5495
  selectedIncreaseIsMaximum :
    ∀ phase : PulsePhase,
      frequencyInHertz (setup.reflectedFrequencyAtSurface phase) -
          frequencyInHertz setup.emittedFrequency ≤
        frequencyInHertz
            (setup.reflectedFrequencyAtSurface
              setup.phaseOfMaximumFrequencyIncrease) -
          frequencyInHertz setup.emittedFrequency

/-!
Positivity, an acute beam/artery angle, and the low-Mach condition for every
pulse phase. These conditions select the physical branch on which a larger
positive Doppler increase corresponds to a larger blood-speed magnitude.
-/
structure HasPhysicalUltrasoundParameters
    {PulsePhase : Type} (setup : PulsedBloodDopplerSetup PulsePhase) : Prop where
  emittedFrequencyPositive :
    0 < frequencyInHertz setup.emittedFrequency
  reflectedFrequencyPositive :
    ∀ phase, 0 < frequencyInHertz (setup.reflectedFrequencyAtSurface phase)
  soundSpeedPositive : 0 < speedInMetersPerSecond setup.soundSpeedInArm
  acuteAngle : 0 < Real.Angle.cos setup.beamArteryAngle
  bloodIsSubsonic :
    ∀ phase,
      speedInMetersPerSecond (setup.bloodSpeedAlongArtery phase) <
        speedInMetersPerSecond setup.soundSpeedInArm

/-! ## Governing ultrasound law -/

/-!
The standard low-speed pulse-echo Doppler law used for medical ultrasound.
The factor `2` accounts for the outgoing interaction with moving blood and
the returning echo. Only the component of blood velocity parallel to the
ultrasound beam contributes, giving the factor `cos θ`. The relation is stated
in every compatible choice of length and time units and contains no answer
choice or requested numerical speed.
-/
structure SatisfiesPulseEchoDopplerLaw
    {PulsePhase : Type} (setup : PulsedBloodDopplerSetup PulsePhase) : Prop where
  frequencyIncreaseLaw :
    ∀ (phase : PulsePhase) (lengthUnit : LengthUnit) (timeUnit : TimeUnit),
      frequencyReadout timeUnit
            (setup.reflectedFrequencyAtSurface phase) -
          frequencyReadout timeUnit setup.emittedFrequency =
        2 * frequencyReadout timeUnit setup.emittedFrequency *
            speedReadout lengthUnit timeUnit
              (setup.bloodSpeedAlongArtery phase) *
            Real.Angle.cos setup.beamArteryAngle /
          speedReadout lengthUnit timeUnit setup.soundSpeedInArm

/-! ## Derived maximum speed and displayed answers -/

/-- Labels of the four speed choices printed with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Metres-per-second value printed beside each answer label. -/
def AnswerChoice.metersPerSecond : AnswerChoice → ℝ
  | .A => 3 / 5
  | .B => 7 / 10
  | .C => 4 / 5
  | .D => 9 / 10

/-- The answer label recorded in the supplied dataset metadata. -/
def recordedDatasetAnswer : AnswerChoice := .D

/-!
A physical speed matches a two-decimal-place displayed choice when its SI
readout lies within half of `0.01 m/s` of the printed value.
-/
def MatchesAnswerChoice (speed : SpeedQuantity) (choice : AnswerChoice) : Prop :=
  |speedInMetersPerSecond speed - choice.metersPerSecond| < (1 : ℝ) / 200

/-!
At the phase of greatest measured frequency increase, the pulse-echo law gives
the exact symbolic SI speed readout used for the numerical evaluation.
-/
lemma bloodSpeedAtPeakShift_formula
    {PulsePhase : Type} (setup : PulsedBloodDopplerSetup PulsePhase)
    (hFigure : MatchesPrimaryFigureAndScenario setup)
    (hReadouts : MatchesProblemReadouts setup)
    (hPhysical : HasPhysicalUltrasoundParameters setup)
    (hDoppler : SatisfiesPulseEchoDopplerLaw setup) :
    speedInMetersPerSecond
        (setup.bloodSpeedAlongArtery
          setup.phaseOfMaximumFrequencyIncrease) =
      5495 * 1540 /
        (2 * 5_000_000 * Real.Angle.cos (degrees 20)) := by
  have hLaw :=
    hDoppler.frequencyIncreaseLaw
      setup.phaseOfMaximumFrequencyIncrease
      LengthUnit.meters TimeUnit.seconds
  change
    frequencyInHertz
          (setup.reflectedFrequencyAtSurface
            setup.phaseOfMaximumFrequencyIncrease) -
        frequencyInHertz setup.emittedFrequency =
      2 * frequencyInHertz setup.emittedFrequency *
          speedInMetersPerSecond
            (setup.bloodSpeedAlongArtery
              setup.phaseOfMaximumFrequencyIncrease) *
          Real.Angle.cos setup.beamArteryAngle /
        speedInMetersPerSecond setup.soundSpeedInArm at hLaw
  rw [hReadouts.maximumFrequencyIncreaseHertz,
    hReadouts.emittedFrequencyHertz,
    hReadouts.soundSpeedMetersPerSecond,
    hReadouts.beamArteryAngleDegrees] at hLaw
  have hCos := hPhysical.acuteAngle
  rw [hReadouts.beamArteryAngleDegrees] at hCos
  apply (eq_div_iff (mul_ne_zero (by norm_num) hCos.ne')).2
  rw [eq_div_iff (by norm_num : (1540 : ℝ) ≠ 0)] at hLaw
  nlinarith

/-!
The phase with the maximum detected increase also has maximum blood speed, and
its speed is approximately `0.90054 m/s`, hence matches recorded choice D,
`0.90 m/s`.

This formalizes `thm:physics:phyx_mini_0324:target`.
-/
theorem maximumBloodSpeed_matches_recordedAnswerD
    {PulsePhase : Type} (setup : PulsedBloodDopplerSetup PulsePhase)
    (hFigure : MatchesPrimaryFigureAndScenario setup)
    (hReadouts : MatchesProblemReadouts setup)
    (hPhysical : HasPhysicalUltrasoundParameters setup)
    (hDoppler : SatisfiesPulseEchoDopplerLaw setup) :
    speedInMetersPerSecond
          (setup.bloodSpeedAlongArtery
            setup.phaseOfMaximumFrequencyIncrease) =
        5495 * 1540 /
          (2 * 5_000_000 * Real.Angle.cos (degrees 20)) ∧
      (∀ phase : PulsePhase,
        speedInMetersPerSecond (setup.bloodSpeedAlongArtery phase) ≤
          speedInMetersPerSecond
            (setup.bloodSpeedAlongArtery
              setup.phaseOfMaximumFrequencyIncrease)) ∧
      MatchesAnswerChoice
        (setup.bloodSpeedAlongArtery
          setup.phaseOfMaximumFrequencyIncrease)
        recordedDatasetAnswer := by
  refine ⟨bloodSpeedAtPeakShift_formula setup hFigure hReadouts hPhysical hDoppler, ?_, ?_⟩
  · intro phase
    have hLaw :=
      hDoppler.frequencyIncreaseLaw
        phase LengthUnit.meters TimeUnit.seconds
    have hPeakLaw :=
      hDoppler.frequencyIncreaseLaw
        setup.phaseOfMaximumFrequencyIncrease
        LengthUnit.meters TimeUnit.seconds
    change
      frequencyInHertz (setup.reflectedFrequencyAtSurface phase) -
          frequencyInHertz setup.emittedFrequency =
        2 * frequencyInHertz setup.emittedFrequency *
            speedInMetersPerSecond (setup.bloodSpeedAlongArtery phase) *
            Real.Angle.cos setup.beamArteryAngle /
          speedInMetersPerSecond setup.soundSpeedInArm at hLaw
    change
      frequencyInHertz
            (setup.reflectedFrequencyAtSurface
              setup.phaseOfMaximumFrequencyIncrease) -
          frequencyInHertz setup.emittedFrequency =
        2 * frequencyInHertz setup.emittedFrequency *
            speedInMetersPerSecond
              (setup.bloodSpeedAlongArtery
                setup.phaseOfMaximumFrequencyIncrease) *
            Real.Angle.cos setup.beamArteryAngle /
          speedInMetersPerSecond setup.soundSpeedInArm at hPeakLaw
    have hMaximum := hReadouts.selectedIncreaseIsMaximum phase
    rw [hLaw, hPeakLaw, hReadouts.emittedFrequencyHertz,
      hReadouts.soundSpeedMetersPerSecond] at hMaximum
    have hCos := hPhysical.acuteAngle
    nlinarith
  · change
      |speedInMetersPerSecond
            (setup.bloodSpeedAlongArtery
              setup.phaseOfMaximumFrequencyIncrease) -
          (9 : ℝ) / 10| < (1 : ℝ) / 200
    rw [bloodSpeedAtPeakShift_formula setup hFigure hReadouts hPhysical hDoppler]
    have hCosReal :
        Real.Angle.cos (degrees 20) = Real.cos (Real.pi / 9) := by
      simp only [degrees, Real.Angle.cos_coe]
      ring
    have hCosHalf :
        (1 : ℝ) / 2 < Real.Angle.cos (degrees 20) := by
      rw [hCosReal, ← Real.cos_pi_div_three]
      exact Real.cos_lt_cos_of_nonneg_of_le_pi
        (by positivity)
        (by nlinarith [Real.pi_pos])
        (by nlinarith [Real.pi_pos])
    have hCosCubic :
        4 * Real.Angle.cos (degrees 20) ^ 3 -
            3 * Real.Angle.cos (degrees 20) =
          (1 : ℝ) / 2 := by
      rw [hCosReal, ← Real.cos_three_mul]
      convert Real.cos_pi_div_three using 1 <;> ring
    have hCosLower :
        (939 : ℝ) / 1000 < Real.Angle.cos (degrees 20) := by
      by_contra h
      have hLe :
          Real.Angle.cos (degrees 20) ≤ (939 : ℝ) / 1000 :=
        le_of_not_gt h
      nlinarith
        [mul_nonneg (sub_nonneg.mpr hCosHalf.le)
          (sq_nonneg
            (Real.Angle.cos (degrees 20) + (939 : ℝ) / 500))]
    have hCosUpper :
        Real.Angle.cos (degrees 20) < (47 : ℝ) / 50 := by
      by_contra h
      have hGe :
          (47 : ℝ) / 50 ≤ Real.Angle.cos (degrees 20) :=
        le_of_not_gt h
      nlinarith
        [mul_nonneg (sub_nonneg.mpr hGe)
          (sq_nonneg
            (Real.Angle.cos (degrees 20) + (47 : ℝ) / 25))]
    rw [abs_lt]
    constructor
    · rw [lt_sub_iff_add_lt, lt_div_iff₀ (by positivity)]
      norm_num at hCosUpper ⊢
      nlinarith
    · rw [sub_lt_iff_lt_add, div_lt_iff₀ (by positivity)]
      norm_num at hCosLower ⊢
      nlinarith

end PhyXMiniProblems.ProblemPhyXMini0324
