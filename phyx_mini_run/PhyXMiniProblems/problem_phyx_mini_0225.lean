import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Physlib.Units.WithDim.Speed

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0225

open Dimension

/-!
# Oscillation period of a bump on a rolling tire

A car tire rolls on a flat road while a small hemispherical bump is carried
around its rim.  The bump's vertical position repeats once per revolution.
The car speed and tire radius therefore determine the oscillation period via
the no-slip rolling law and the angular-period law.

Lengths, durations, angular speeds, and translational speeds are represented
by dimensionful Physlib quantities.  Real numbers occur only as scalar
readouts in a named unit system or as the displayed multiple-choice data.
-/

/-! ## Dimensionful physical quantities and unit readouts -/

/-- A nonnegative physical length, used for the tire radius. -/
abbrev LengthQuantity : Type := Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative physical duration, used for the bump's oscillation period. -/
abbrev DurationQuantity : Type := Dimensionful (WithDim T𝓭 NNReal)

/--
The magnitude of a physical angular speed.  Radians are dimensionless, so its
physical dimension is inverse time.
-/
abbrev AngularSpeedQuantity : Type :=
  Dimensionful (WithDim T𝓭⁻¹ NNReal)

/-- A nonnegative physical translational speed. -/
abbrev SpeedQuantity : Type := DimSpeed

/-- Scalar readout of a physical length in a coherent unit system. -/
def lengthReadout (units : UnitChoices) (length : LengthQuantity) : ℝ :=
  ((length units).val : ℝ)

/-- Scalar readout of a physical duration in a coherent unit system. -/
def durationReadout (units : UnitChoices) (duration : DurationQuantity) : ℝ :=
  ((duration units).val : ℝ)

/-- Scalar readout of an angular-speed magnitude in radians per time unit. -/
def angularSpeedReadout
    (units : UnitChoices) (angularSpeed : AngularSpeedQuantity) : ℝ :=
  ((angularSpeed units).val : ℝ)

/-- Scalar readout of a translational speed in a coherent unit system. -/
def speedReadout (units : UnitChoices) (speed : SpeedQuantity) : ℝ :=
  ((speed units).val : ℝ)

/-- Read a tire radius in metres. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  lengthReadout UnitChoices.SI length

/-- Read a duration in seconds. -/
def durationInSeconds (duration : DurationQuantity) : ℝ :=
  durationReadout UnitChoices.SI duration

/-- Read an angular speed in radians per second. -/
def angularSpeedInRadiansPerSecond
    (angularSpeed : AngularSpeedQuantity) : ℝ :=
  angularSpeedReadout UnitChoices.SI angularSpeed

/-- Read a translational speed in metres per second. -/
def speedInMetersPerSecond (speed : SpeedQuantity) : ℝ :=
  speedReadout UnitChoices.SI speed

/-! ## Physical setup and primary-image labels -/

/-- The label printed beside the protrusion in the supplied image. -/
inductive FigureLabel where
  | bump
  deriving DecidableEq, Repr

/-- Distinct physical elements visible in the supplied image. -/
inductive FigureElement where
  | tire
  | bump
  | tread
  | ground
  deriving DecidableEq, Repr

/-- Qualitative image regions used to locate the marked protrusion. -/
inductive FigureRegion where
  | upperLeftRim
  | tireFace
  | belowTire
  deriving DecidableEq, Repr

/-- Shape assigned to the bump by the problem statement. -/
inductive BumpShape where
  | hemispherical
  deriving DecidableEq, Repr

/-- Relative size assigned to the bump by the problem statement. -/
inductive RelativeFeatureSize where
  | smallComparedWithTire
  deriving DecidableEq, Repr

/-- Qualitative tread geometry visible in the primary image. -/
inductive TreadPattern where
  | interconnectedChevron
  deriving DecidableEq, Repr

/-- Orientation of the tire with respect to the road. -/
inductive TireOrientation where
  | upright
  deriving DecidableEq, Repr

/-- Shape of the supporting road surface. -/
inductive GroundShape where
  | flat
  deriving DecidableEq, Repr

/-- The observer's relation to the moving car in the scenario. -/
inductive ObservationContext where
  | drivingBehindCar
  deriving DecidableEq, Repr

/-- The periodic observable whose period the question requests. -/
inductive BumpObservable where
  | verticalPositionOscillation
  deriving DecidableEq, Repr

/-- Categorical information read from the supplied tire image. -/
structure TireFigure where
  showsElement : FigureElement → Bool
  labelTarget : FigureLabel → FigureElement
  elementRegion : FigureElement → FigureRegion
  treadPattern : TreadPattern
  tireOrientation : TireOrientation
  groundShape : GroundShape
  tireContactsGround : Bool

/-!
The physical quantities of the rolling-tire observation.  In particular,
`bumpOscillationPeriod` is an unconstrained physical duration here; neither
its exact value nor any displayed answer is built into the setup.
-/
structure RollingTireBumpSetup where
  figure : TireFigure
  observationContext : ObservationContext
  bumpShape : BumpShape
  bumpRelativeSize : RelativeFeatureSize
  requestedObservable : BumpObservable
  tireRadius : LengthQuantity
  vehicleSpeed : SpeedQuantity
  tireCenterSpeed : SpeedQuantity
  tireAngularSpeed : AngularSpeedQuantity
  bumpOscillationPeriod : DurationQuantity

/-! ## Stated measurements and figure-derived data -/

/-!
Problem-text data: the observer follows the car, the tire radius is `0.300 m`,
the car speed is `3.00 m/s`, and the requested observable is the oscillation
period of the stated small hemispherical bump.  No period value occurs here.
-/
structure MatchesProblemDescription (setup : RollingTireBumpSetup) : Prop where
  observer_drives_behind :
    setup.observationContext = .drivingBehindCar
  bump_is_hemispherical :
    setup.bumpShape = .hemispherical
  bump_is_small :
    setup.bumpRelativeSize = .smallComparedWithTire
  asks_for_vertical_oscillation_period :
    setup.requestedObservable = .verticalPositionOscillation
  radius_in_metres :
    lengthInMeters setup.tireRadius = 3 / 10
  vehicle_speed_in_metres_per_second :
    speedInMetersPerSecond setup.vehicleSpeed = 3

/-!
Primary-image evidence: the text label points to a bump on the upper-left rim,
the chevron-tread tire stands upright, and it contacts a flat ground surface.
This predicate contains no kinematic or period conclusion.
-/
structure MatchesPrimaryFigure (setup : RollingTireBumpSetup) : Prop where
  tire_is_shown : setup.figure.showsElement .tire = true
  bump_is_shown : setup.figure.showsElement .bump = true
  tread_is_shown : setup.figure.showsElement .tread = true
  ground_is_shown : setup.figure.showsElement .ground = true
  bump_label_targets_bump : setup.figure.labelTarget .bump = .bump
  bump_is_on_upper_left_rim :
    setup.figure.elementRegion .bump = .upperLeftRim
  tread_is_chevron :
    setup.figure.treadPattern = .interconnectedChevron
  tire_is_upright : setup.figure.tireOrientation = .upright
  ground_is_flat : setup.figure.groundShape = .flat
  tire_contacts_ground : setup.figure.tireContactsGround = true

/-!
Physical admissibility for the quantities used in division and for the
selected positive rotation branch.  These conditions do not assign the
requested period a numerical value.
-/
structure HasPhysicalRollingParameters
    (setup : RollingTireBumpSetup) : Prop where
  radius_positive : 0 < lengthInMeters setup.tireRadius
  vehicle_speed_positive : 0 < speedInMetersPerSecond setup.vehicleSpeed
  center_speed_positive : 0 < speedInMetersPerSecond setup.tireCenterSpeed
  angular_speed_positive :
    0 < angularSpeedInRadiansPerSecond setup.tireAngularSpeed
  period_positive : 0 < durationInSeconds setup.bumpOscillationPeriod

/-! ## Governing rolling and periodic-motion laws -/

/-!
The car carries the wheel center at the vehicle speed; rolling without
slipping gives `v = ω R`; and the marked bump completes one vertical-position
cycle per full revolution, giving `ω T = 2π`.  The laws are required in every
coherent unit system and contain no numerical period or answer choice.
-/
structure SatisfiesRollingTireKinematics
    (setup : RollingTireBumpSetup) : Prop where
  tire_center_moves_with_vehicle :
    ∀ units : UnitChoices,
      speedReadout units setup.tireCenterSpeed =
        speedReadout units setup.vehicleSpeed
  rolls_without_slipping :
    ∀ units : UnitChoices,
      speedReadout units setup.tireCenterSpeed =
        angularSpeedReadout units setup.tireAngularSpeed *
          lengthReadout units setup.tireRadius
  one_revolution_per_bump_cycle :
    ∀ units : UnitChoices,
      angularSpeedReadout units setup.tireAngularSpeed *
          durationReadout units setup.bumpOscillationPeriod =
        2 * Real.pi

/-! ## Derived period and displayed answer -/

/-- Labels of the four answers displayed with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Seconds printed beside each displayed answer label. -/
def AnswerChoice.seconds : AnswerChoice → ℝ
  | .A => 116 / 125
  | .B => 207 / 250
  | .C => 91 / 125
  | .D => 157 / 250

/-- Dataset metadata: the recorded answer is choice D; this is never a premise. -/
def recordedAnswerChoice : AnswerChoice := .D

/-!
A duration agrees with a value displayed to the nearest millisecond.  The
half-millisecond tolerance models the precision of the answer list.
-/
def MatchesDisplayedPrecision
    (duration : DurationQuantity) (choice : AnswerChoice) : Prop :=
  |durationInSeconds duration - choice.seconds| ≤ 1 / 2000

/-- A displayed choice is uniquely closest to the model's physical period. -/
def IsUniqueClosestAnswer
    (duration : DurationQuantity) (choice : AnswerChoice) : Prop :=
  ∀ other : AnswerChoice, other ≠ choice →
    |durationInSeconds duration - choice.seconds| <
      |durationInSeconds duration - other.seconds|

/-!
For any physically admissible rolling setup satisfying the two kinematic
laws, eliminating angular speed gives `T = 2πR/v` in SI readouts.
-/
lemma bumpOscillationPeriod_formula
    (setup : RollingTireBumpSetup)
    (_physical : HasPhysicalRollingParameters setup)
    (_kinematics : SatisfiesRollingTireKinematics setup) :
    durationInSeconds setup.bumpOscillationPeriod =
      2 * Real.pi * lengthInMeters setup.tireRadius /
        speedInMetersPerSecond setup.vehicleSpeed := by
  have hvehicle :
      speedInMetersPerSecond setup.vehicleSpeed =
        angularSpeedInRadiansPerSecond setup.tireAngularSpeed *
          lengthInMeters setup.tireRadius := by
    calc
      speedInMetersPerSecond setup.vehicleSpeed =
          speedInMetersPerSecond setup.tireCenterSpeed := by
        symm
        exact _kinematics.tire_center_moves_with_vehicle UnitChoices.SI
      _ =
          angularSpeedInRadiansPerSecond setup.tireAngularSpeed *
            lengthInMeters setup.tireRadius :=
        _kinematics.rolls_without_slipping UnitChoices.SI
  have hperiod :
      angularSpeedInRadiansPerSecond setup.tireAngularSpeed *
          durationInSeconds setup.bumpOscillationPeriod =
        2 * Real.pi :=
    _kinematics.one_revolution_per_bump_cycle UnitChoices.SI
  apply (eq_div_iff _physical.vehicle_speed_positive.ne').2
  calc
    durationInSeconds setup.bumpOscillationPeriod *
          speedInMetersPerSecond setup.vehicleSpeed =
        durationInSeconds setup.bumpOscillationPeriod *
          (angularSpeedInRadiansPerSecond setup.tireAngularSpeed *
            lengthInMeters setup.tireRadius) := by
      rw [hvehicle]
    _ =
        (angularSpeedInRadiansPerSecond setup.tireAngularSpeed *
          durationInSeconds setup.bumpOscillationPeriod) *
            lengthInMeters setup.tireRadius := by
      ring
    _ = (2 * Real.pi) * lengthInMeters setup.tireRadius := by
      rw [hperiod]
    _ = 2 * Real.pi * lengthInMeters setup.tireRadius := by
      ring

/-!
Substituting `R = 0.300 m` and `v = 3.00 m/s` into the derived rolling-period
formula gives the exact ideal-model period `π/5 s`.
-/
lemma bumpOscillationPeriod_exact
    (setup : RollingTireBumpSetup)
    (_description : MatchesProblemDescription setup)
    (_physical : HasPhysicalRollingParameters setup)
    (_kinematics : SatisfiesRollingTireKinematics setup) :
    durationInSeconds setup.bumpOscillationPeriod = Real.pi / 5 := by
  calc
    durationInSeconds setup.bumpOscillationPeriod =
        2 * Real.pi * lengthInMeters setup.tireRadius /
          speedInMetersPerSecond setup.vehicleSpeed :=
      bumpOscillationPeriod_formula setup _physical _kinematics
    _ = Real.pi / 5 := by
      rw [_description.radius_in_metres,
        _description.vehicle_speed_in_metres_per_second]
      ring

/-!
The ideal period is `π/5 s`, approximately `0.628318 s`.  Hence it rounds to
the displayed `0.628 s` and is uniquely closest to recorded choice D.

This formalizes blueprint label `thm:physics:phyx_mini_0225:target`.
-/
theorem problem_phyx_mini_0225
    (setup : RollingTireBumpSetup)
    (_description : MatchesProblemDescription setup)
    (_figure : MatchesPrimaryFigure setup)
    (_physical : HasPhysicalRollingParameters setup)
    (_kinematics : SatisfiesRollingTireKinematics setup) :
    durationInSeconds setup.bumpOscillationPeriod = Real.pi / 5 ∧
      MatchesDisplayedPrecision setup.bumpOscillationPeriod
        recordedAnswerChoice ∧
      IsUniqueClosestAnswer setup.bumpOscillationPeriod
        recordedAnswerChoice := by
  have hpi_lower : (251 : ℝ) / 80 < Real.pi := by
    have hcos0 :
        (995188 : ℝ) / 1000000 ≤ Real.cos ((251 : ℝ) / 2560) := by
      have hbound :=
        Real.cos_bound (x := (251 : ℝ) / 2560) (by norm_num [abs_of_nonneg])
      rw [abs_le] at hbound
      norm_num [abs_of_nonneg] at hbound ⊢
      linarith
    have hcos1 :
        (980798 : ℝ) / 1000000 ≤
          Real.cos (2 * ((251 : ℝ) / 2560)) := by
      rw [Real.cos_two_mul]
      have hsquare := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 995188 / 1000000) hcos0 2
      norm_num at hsquare ⊢
      nlinarith
    have hcos2 :
        (923929 : ℝ) / 1000000 ≤
          Real.cos (2 * (2 * ((251 : ℝ) / 2560))) := by
      rw [Real.cos_two_mul]
      have hsquare := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 980798 / 1000000) hcos1 2
      norm_num at hsquare ⊢
      nlinarith
    have hcos3 :
        (707289 : ℝ) / 1000000 ≤
          Real.cos (2 * (2 * (2 * ((251 : ℝ) / 2560)))) := by
      rw [Real.cos_two_mul]
      have hsquare := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 923929 / 1000000) hcos2 2
      norm_num at hsquare ⊢
      nlinarith
    have hcos_lower :
        0 < Real.cos ((251 : ℝ) / 160) := by
      have hsquare := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 707289 / 1000000) hcos3 2
      rw [show (251 : ℝ) / 160 =
        2 * (2 * (2 * (2 * ((251 : ℝ) / 2560)))) by norm_num]
      rw [Real.cos_two_mul]
      norm_num at hsquare ⊢
      nlinarith
    have hhalf : (251 : ℝ) / 160 < Real.pi / 2 := by
      by_contra hnot
      have hroot_le : Real.pi / 2 ≤ (251 : ℝ) / 160 :=
        le_of_not_gt hnot
      have hpoint_le_pi : (251 : ℝ) / 160 ≤ Real.pi := by
        nlinarith [Real.two_le_pi]
      have hcos_nonpos :
          Real.cos ((251 : ℝ) / 160) ≤ Real.cos (Real.pi / 2) :=
        Real.cos_le_cos_of_nonneg_of_le_pi
          (by positivity) hpoint_le_pi hroot_le
      rw [Real.cos_pi_div_two] at hcos_nonpos
      linarith
    linarith
  have hpi_upper : Real.pi < (1257 : ℝ) / 400 := by
    have hcos0 :
        Real.cos ((1257 : ℝ) / 12800) ≤ (995183 : ℝ) / 1000000 := by
      have hbound :=
        Real.cos_bound (x := (1257 : ℝ) / 12800) (by norm_num [abs_of_nonneg])
      rw [abs_le] at hbound
      norm_num [abs_of_nonneg] at hbound ⊢
      linarith
    have hcos1 :
        Real.cos (2 * ((1257 : ℝ) / 12800)) ≤
          (980779 : ℝ) / 1000000 := by
      have hcos0_nonneg :
          0 ≤ Real.cos ((1257 : ℝ) / 12800) := by
        exact (Real.cos_pos_of_le_one (by norm_num [abs_of_nonneg])).le
      have hsquare :=
        pow_le_pow_left₀ hcos0_nonneg hcos0 2
      rw [Real.cos_two_mul]
      norm_num at hsquare ⊢
      nlinarith
    have hcos2 :
        Real.cos (2 * (2 * ((1257 : ℝ) / 12800))) ≤
          (923855 : ℝ) / 1000000 := by
      have hcos1_nonneg :
          0 ≤ Real.cos (2 * ((1257 : ℝ) / 12800)) := by
        exact (Real.cos_pos_of_le_one (by norm_num [abs_of_nonneg])).le
      have hsquare :=
        pow_le_pow_left₀ hcos1_nonneg hcos1 2
      rw [Real.cos_two_mul]
      norm_num at hsquare ⊢
      nlinarith
    have hcos3 :
        Real.cos (2 * (2 * (2 * ((1257 : ℝ) / 12800)))) ≤
          (707017 : ℝ) / 1000000 := by
      have hcos2_nonneg :
          0 ≤ Real.cos (2 * (2 * ((1257 : ℝ) / 12800))) := by
        exact (Real.cos_pos_of_le_one (by norm_num [abs_of_nonneg])).le
      have hsquare :=
        pow_le_pow_left₀ hcos2_nonneg hcos2 2
      rw [Real.cos_two_mul]
      norm_num at hsquare ⊢
      nlinarith
    have hcos_upper :
        Real.cos ((1257 : ℝ) / 800) < 0 := by
      have hcos3_nonneg :
          0 ≤ Real.cos (2 * (2 * (2 * ((1257 : ℝ) / 12800)))) := by
        exact (Real.cos_pos_of_le_one (by norm_num [abs_of_nonneg])).le
      have hsquare :=
        pow_le_pow_left₀ hcos3_nonneg hcos3 2
      rw [show (1257 : ℝ) / 800 =
        2 * (2 * (2 * (2 * ((1257 : ℝ) / 12800)))) by norm_num]
      rw [Real.cos_two_mul]
      norm_num at hsquare ⊢
      nlinarith
    have hhalf : Real.pi / 2 < (1257 : ℝ) / 800 := by
      by_contra hnot
      have hpoint_le_root : (1257 : ℝ) / 800 ≤ Real.pi / 2 :=
        le_of_not_gt hnot
      have hcos_nonneg :
          Real.cos (Real.pi / 2) ≤ Real.cos ((1257 : ℝ) / 800) :=
        Real.cos_le_cos_of_nonneg_of_le_pi
          (by positivity) (by nlinarith [Real.pi_pos]) hpoint_le_root
      rw [Real.cos_pi_div_two] at hcos_nonneg
      linarith
    linarith
  have hexact :
      durationInSeconds setup.bumpOscillationPeriod = Real.pi / 5 :=
    bumpOscillationPeriod_exact setup _description _physical _kinematics
  have hprecision :
      MatchesDisplayedPrecision setup.bumpOscillationPeriod
        recordedAnswerChoice := by
    unfold MatchesDisplayedPrecision
    rw [hexact]
    change |Real.pi / 5 - (157 : ℝ) / 250| ≤ (1 : ℝ) / 2000
    rw [abs_le]
    constructor <;> linarith
  refine ⟨hexact, hprecision, ?_⟩
  unfold IsUniqueClosestAnswer
  intro other hother
  rw [hexact]
  have habs :
      |Real.pi / 5 - (157 : ℝ) / 250| ≤ (1 : ℝ) / 2000 := by
    rw [abs_le]
    constructor <;> linarith
  cases other with
  | A =>
      change
        |Real.pi / 5 - (157 : ℝ) / 250| <
          |Real.pi / 5 - (116 : ℝ) / 125|
      have hright :
          |Real.pi / 5 - (116 : ℝ) / 125| =
            -(Real.pi / 5 - (116 : ℝ) / 125) :=
        abs_of_nonpos (by linarith)
      rw [hright]
      linarith
  | B =>
      change
        |Real.pi / 5 - (157 : ℝ) / 250| <
          |Real.pi / 5 - (207 : ℝ) / 250|
      have hright :
          |Real.pi / 5 - (207 : ℝ) / 250| =
            -(Real.pi / 5 - (207 : ℝ) / 250) :=
        abs_of_nonpos (by linarith)
      rw [hright]
      linarith
  | C =>
      change
        |Real.pi / 5 - (157 : ℝ) / 250| <
          |Real.pi / 5 - (91 : ℝ) / 125|
      have hright :
          |Real.pi / 5 - (91 : ℝ) / 125| =
            -(Real.pi / 5 - (91 : ℝ) / 125) :=
        abs_of_nonpos (by linarith)
      rw [hright]
      linarith
  | D =>
      exact (hother rfl).elim

end PhyXMiniProblems.ProblemPhyXMini0225
