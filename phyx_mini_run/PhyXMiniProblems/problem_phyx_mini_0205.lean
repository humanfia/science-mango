import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Physlib.Units.WithDim.Basic

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0205

open Dimension

/-!
# Maximum amplitude of a vertically oscillating diving board

The free end of a diving board executes vertical simple harmonic motion at
`2.8` cycles per second.  A pebble at that end can follow the board only while
the upward normal force required for constrained co-motion is nonnegative.

The source image supplies only qualitative apparatus information: the board
has a free end extending over a pool, and the pictured light object is at that
end.  It supplies no length or amplitude readout.  Accordingly, the numerical
amplitude is derived from simple-harmonic kinematics and vertical Newton's
second law, rather than included in the figure predicate or the laws.
-/

/-- A unit-independent physical length. -/
abbrev LengthQuantity : Type := Dimensionful (WithDim L𝓭 ℝ)

/-- A unit-independent physical time. -/
abbrev TimeQuantity : Type := Dimensionful (WithDim T𝓭 ℝ)

/-- Cyclic frequency, measured in cycles per second in SI. -/
abbrev CyclicFrequencyQuantity : Type :=
  Dimensionful (WithDim T𝓭⁻¹ ℝ)

/-- Angular frequency, measured in radians per second in SI. -/
abbrev AngularFrequencyQuantity : Type :=
  Dimensionful (WithDim T𝓭⁻¹ ℝ)

/-- A physical mass. -/
abbrev MassQuantity : Type := Dimensionful (WithDim M𝓭 ℝ)

/-- A signed acceleration along the chosen vertical axis. -/
abbrev AccelerationQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * T𝓭⁻¹ * T𝓭⁻¹) ℝ)

/-- A signed force component along the chosen vertical axis. -/
abbrev ForceQuantity : Type :=
  Dimensionful
    (WithDim (M𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹) ℝ)

/-- Read a physical length in meters. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  (length UnitChoices.SI).val

/-- Read a physical time in seconds. -/
def timeInSeconds (time : TimeQuantity) : ℝ :=
  (time UnitChoices.SI).val

/-- Read a cyclic frequency in cycles per second (hertz). -/
def frequencyInHertz (frequency : CyclicFrequencyQuantity) : ℝ :=
  (frequency UnitChoices.SI).val

/-- Read an angular frequency in radians per second. -/
def angularFrequencyInRadiansPerSecond
    (angularFrequency : AngularFrequencyQuantity) : ℝ :=
  (angularFrequency UnitChoices.SI).val

/-- Read a physical mass in kilograms. -/
def massInKilograms (mass : MassQuantity) : ℝ :=
  (mass UnitChoices.SI).val

/-- Read a signed acceleration in meters per second squared. -/
def accelerationInMetersPerSecondSquared
    (acceleration : AccelerationQuantity) : ℝ :=
  (acceleration UnitChoices.SI).val

/-- Read a signed force component in newtons. -/
def forceInNewtons (force : ForceQuantity) : ℝ :=
  (force UnitChoices.SI).val

/-- The supported and free ends of the board visible in the source image. -/
inductive BoardPoint where
  | supportedEnd
  | freeEnd
  deriving DecidableEq, Repr

/-- The motion axis singled out by the contact calculation. -/
inductive MotionAxis where
  | vertical
  | horizontal
  deriving DecidableEq, Repr

/-- Sign convention for scalar vertical components. -/
inductive VerticalPositiveDirection where
  | upward
  | downward
  deriving DecidableEq, Repr

/-- The four amplitude readings displayed as answer choices, in meters. -/
inductive AmplitudeAnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Numerical meter readout printed for each answer choice. -/
def amplitudeAnswerChoiceInMeters : AmplitudeAnswerChoice → ℝ
  | .A => 4.2 * (10 : ℝ) ^ (-2 : ℤ)
  | .B => 3.2 * (10 : ℝ) ^ (-3 : ℤ)
  | .C => 2.2 * (10 : ℝ) ^ (-2 : ℤ)
  | .D => 3.2 * (10 : ℝ) ^ (-2 : ℤ)

/--
The dimensional data and amplitude-indexed constrained-motion quantities.

For a candidate physical amplitude `A`, `boardEndDisplacement A t` and
`boardEndAcceleration A t` describe the prescribed board motion.
`pebbleAccelerationIfConstrained A t` is the acceleration the pebble would
have if it remained in contact, and `requiredNormalForce A t` is the upward
normal force required to realize that constrained motion.
-/
structure DivingBoardPebbleSetup where
  boardPointUnderPebble : BoardPoint
  motionAxis : MotionAxis
  positiveDirection : VerticalPositiveDirection
  cyclicFrequency : CyclicFrequencyQuantity
  angularFrequency : AngularFrequencyQuantity
  gravitationalAccelerationMagnitude : AccelerationQuantity
  pebbleMass : MassQuantity
  boardEndDisplacement :
    LengthQuantity → TimeQuantity → LengthQuantity
  boardEndAcceleration :
    LengthQuantity → TimeQuantity → AccelerationQuantity
  pebbleAccelerationIfConstrained :
    LengthQuantity → TimeQuantity → AccelerationQuantity
  requiredNormalForce :
    LengthQuantity → TimeQuantity → ForceQuantity
  upperTurningTime : LengthQuantity → TimeQuantity

/--
Qualitative information from the primary image and scenario: the contact body
is at the free end and the relevant motion is vertical with upward-positive
scalar components.  No requested amplitude occurs here.
-/
def MatchesDivingBoardFigure (setup : DivingBoardPebbleSetup) : Prop :=
  setup.boardPointUnderPebble = .freeEnd ∧
    setup.motionAxis = .vertical ∧
    setup.positiveDirection = .upward

/--
Measured/problem data.  The conventional terrestrial value `9.8 m/s²` is
made explicit because it is needed to distinguish the numerical choices.
-/
def HasDivingBoardProblemData (setup : DivingBoardPebbleSetup) : Prop :=
  frequencyInHertz setup.cyclicFrequency = 2.8 ∧
    accelerationInMetersPerSecondSquared
        setup.gravitationalAccelerationMagnitude = 9.8 ∧
    0 < massInKilograms setup.pebbleMass

/--
Governing laws for the prescribed board motion and the pebble's constrained
vertical dynamics.

Time is chosen so that the upper turning point is at SI time zero.  The SHM
laws are `y = A cos (ωt)` and `a = -ω²y`.  With upward positive, Newton's
second law for the constrained pebble is `N - mg = ma`.  These laws do not
state the contact threshold or the requested maximum amplitude.
-/
structure SatisfiesDivingBoardContactLaws
    (setup : DivingBoardPebbleSetup) : Prop where
  angularFrequencyConversion :
    angularFrequencyInRadiansPerSecond setup.angularFrequency =
      2 * Real.pi * frequencyInHertz setup.cyclicFrequency
  upperTurningTimeIsOrigin :
    ∀ amplitude : LengthQuantity,
      timeInSeconds (setup.upperTurningTime amplitude) = 0
  harmonicDisplacementLaw :
    ∀ (amplitude : LengthQuantity) (time : TimeQuantity),
      lengthInMeters (setup.boardEndDisplacement amplitude time) =
        lengthInMeters amplitude *
          Real.cos
            (angularFrequencyInRadiansPerSecond setup.angularFrequency *
              timeInSeconds time)
  harmonicAccelerationLaw :
    ∀ (amplitude : LengthQuantity) (time : TimeQuantity),
      accelerationInMetersPerSecondSquared
          (setup.boardEndAcceleration amplitude time) =
        -(angularFrequencyInRadiansPerSecond setup.angularFrequency) ^ 2 *
          lengthInMeters (setup.boardEndDisplacement amplitude time)
  constrainedMotionLaw :
    ∀ (amplitude : LengthQuantity) (time : TimeQuantity),
      accelerationInMetersPerSecondSquared
          (setup.pebbleAccelerationIfConstrained amplitude time) =
        accelerationInMetersPerSecondSquared
          (setup.boardEndAcceleration amplitude time)
  verticalNewtonSecondLaw :
    ∀ (amplitude : LengthQuantity) (time : TimeQuantity),
      forceInNewtons (setup.requiredNormalForce amplitude time) -
          massInKilograms setup.pebbleMass *
            accelerationInMetersPerSecondSquared
              setup.gravitationalAccelerationMagnitude =
        massInKilograms setup.pebbleMass *
          accelerationInMetersPerSecondSquared
            (setup.pebbleAccelerationIfConstrained amplitude time)

/--
A nonnegative candidate amplitude preserves contact precisely when the normal
force required for constrained co-motion is nonnegative throughout the cycle.
-/
def PreservesPebbleContact
    (setup : DivingBoardPebbleSetup) (amplitude : LengthQuantity) : Prop :=
  0 ≤ lengthInMeters amplitude ∧
    ∀ time : TimeQuantity,
      0 ≤ forceInNewtons (setup.requiredNormalForce amplitude time)

/-- A contact-preserving amplitude that dominates every other such amplitude. -/
def IsMaximumContactPreservingAmplitude
    (setup : DivingBoardPebbleSetup)
    (maximumAmplitude : LengthQuantity) : Prop :=
  PreservesPebbleContact setup maximumAmplitude ∧
    ∀ candidateAmplitude : LengthQuantity,
      PreservesPebbleContact setup candidateAmplitude →
        lengthInMeters candidateAmplitude ≤
          lengthInMeters maximumAmplitude

/--
For a board frequency of `2.8 Hz`, the greatest contact-preserving amplitude
is `g / ω² = g / (2πf)²`.  Its SI readout rounds to the displayed choice
`D`, namely `3.2 × 10⁻² m`, and that choice is closest among the four listed
readouts.
-/
theorem maximumDivingBoardAmplitude
    (setup : DivingBoardPebbleSetup)
    (hfigure : MatchesDivingBoardFigure setup)
    (hdata : HasDivingBoardProblemData setup)
    (hlaws : SatisfiesDivingBoardContactLaws setup) :
    ∃ maximumAmplitude : LengthQuantity,
      IsMaximumContactPreservingAmplitude setup maximumAmplitude ∧
        lengthInMeters maximumAmplitude =
          accelerationInMetersPerSecondSquared
              setup.gravitationalAccelerationMagnitude /
            (angularFrequencyInRadiansPerSecond
              setup.angularFrequency) ^ 2 ∧
        lengthInMeters maximumAmplitude =
          accelerationInMetersPerSecondSquared
              setup.gravitationalAccelerationMagnitude /
            (2 * Real.pi * frequencyInHertz setup.cyclicFrequency) ^ 2 ∧
        |lengthInMeters maximumAmplitude -
            amplitudeAnswerChoiceInMeters .D| <
          5 * (10 : ℝ) ^ (-4 : ℤ) ∧
        ∀ choice : AmplitudeAnswerChoice,
          |lengthInMeters maximumAmplitude -
              amplitudeAnswerChoiceInMeters .D| ≤
            |lengthInMeters maximumAmplitude -
              amplitudeAnswerChoiceInMeters choice| := by
  rcases hdata with ⟨hfrequency, hgravity, hmass⟩
  let g :=
    accelerationInMetersPerSecondSquared
      setup.gravitationalAccelerationMagnitude
  let ω :=
    angularFrequencyInRadiansPerSecond setup.angularFrequency
  let m := massInKilograms setup.pebbleMass
  have hg : g = 9.8 := hgravity
  have hg_pos : 0 < g := by
    rw [hg]
    norm_num
  have hm_pos : 0 < m := hmass
  have hω_conversion :
      ω = 2 * Real.pi * frequencyInHertz setup.cyclicFrequency :=
    hlaws.angularFrequencyConversion
  have hω_value : ω = 2 * Real.pi * 2.8 := by
    rw [hω_conversion, hfrequency]
  have hω_pos : 0 < ω := by
    rw [hω_value]
    positivity
  have hω_sq_pos : 0 < ω ^ 2 := by positivity
  let maximumAmplitude : LengthQuantity :=
    CarriesDimension.toDimensionful UnitChoices.SI
      (⟨g / ω ^ 2⟩ : WithDim L𝓭 ℝ)
  have hmaximum_value :
      lengthInMeters maximumAmplitude = g / ω ^ 2 := by
    simp [maximumAmplitude, lengthInMeters,
      CarriesDimension.toDimensionful_apply_apply]
  have hmaximum_nonnegative :
      0 ≤ lengthInMeters maximumAmplitude := by
    rw [hmaximum_value]
    positivity
  have hmaximum_preserves :
      PreservesPebbleContact setup maximumAmplitude := by
    refine ⟨hmaximum_nonnegative, ?_⟩
    intro time
    have hdisplacement :=
      hlaws.harmonicDisplacementLaw maximumAmplitude time
    change
      lengthInMeters (setup.boardEndDisplacement maximumAmplitude time) =
        lengthInMeters maximumAmplitude *
          Real.cos (ω * timeInSeconds time) at hdisplacement
    rw [hmaximum_value] at hdisplacement
    have hboard_acceleration :
        accelerationInMetersPerSecondSquared
            (setup.boardEndAcceleration maximumAmplitude time) =
          -(g * Real.cos (ω * timeInSeconds time)) := by
      calc
        accelerationInMetersPerSecondSquared
              (setup.boardEndAcceleration maximumAmplitude time) =
            -ω ^ 2 *
              lengthInMeters
                (setup.boardEndDisplacement maximumAmplitude time) := by
              exact hlaws.harmonicAccelerationLaw maximumAmplitude time
        _ = -ω ^ 2 *
              (g / ω ^ 2 *
                Real.cos (ω * timeInSeconds time)) := by
              rw [hdisplacement]
        _ = -(g * Real.cos (ω * timeInSeconds time)) := by
              field_simp [ne_of_gt hω_pos]
    have hpebble_acceleration :
        accelerationInMetersPerSecondSquared
            (setup.pebbleAccelerationIfConstrained maximumAmplitude time) =
          -(g * Real.cos (ω * timeInSeconds time)) := by
      calc
        accelerationInMetersPerSecondSquared
              (setup.pebbleAccelerationIfConstrained maximumAmplitude time) =
            accelerationInMetersPerSecondSquared
              (setup.boardEndAcceleration maximumAmplitude time) :=
                hlaws.constrainedMotionLaw maximumAmplitude time
        _ = _ := hboard_acceleration
    have hnewton :=
      hlaws.verticalNewtonSecondLaw maximumAmplitude time
    change
      forceInNewtons (setup.requiredNormalForce maximumAmplitude time) -
          m * g =
        m *
          accelerationInMetersPerSecondSquared
            (setup.pebbleAccelerationIfConstrained maximumAmplitude time)
      at hnewton
    rw [hpebble_acceleration] at hnewton
    have hcos : Real.cos (ω * timeInSeconds time) ≤ 1 :=
      Real.cos_le_one _
    have hproduct :
        0 ≤ m * g * (1 - Real.cos (ω * timeInSeconds time)) :=
      mul_nonneg (mul_nonneg hm_pos.le hg_pos.le)
        (sub_nonneg.mpr hcos)
    nlinarith
  have hmaximum_dominates :
      ∀ candidateAmplitude : LengthQuantity,
        PreservesPebbleContact setup candidateAmplitude →
          lengthInMeters candidateAmplitude ≤
            lengthInMeters maximumAmplitude := by
    intro candidateAmplitude hcandidate
    rcases hcandidate with ⟨_, hnormal_nonnegative⟩
    let upperTime := setup.upperTurningTime candidateAmplitude
    have htime_zero : timeInSeconds upperTime = 0 :=
      hlaws.upperTurningTimeIsOrigin candidateAmplitude
    have hdisplacement :
        lengthInMeters
            (setup.boardEndDisplacement candidateAmplitude upperTime) =
          lengthInMeters candidateAmplitude := by
      calc
        lengthInMeters
              (setup.boardEndDisplacement candidateAmplitude upperTime) =
            lengthInMeters candidateAmplitude *
              Real.cos (ω * timeInSeconds upperTime) := by
                exact
                  hlaws.harmonicDisplacementLaw candidateAmplitude upperTime
        _ = lengthInMeters candidateAmplitude := by
              rw [htime_zero]
              norm_num
    have hboard_acceleration :
        accelerationInMetersPerSecondSquared
            (setup.boardEndAcceleration candidateAmplitude upperTime) =
          -ω ^ 2 * lengthInMeters candidateAmplitude := by
      calc
        accelerationInMetersPerSecondSquared
              (setup.boardEndAcceleration candidateAmplitude upperTime) =
            -ω ^ 2 *
              lengthInMeters
                (setup.boardEndDisplacement candidateAmplitude upperTime) := by
                  exact
                    hlaws.harmonicAccelerationLaw candidateAmplitude upperTime
        _ = _ := by rw [hdisplacement]
    have hpebble_acceleration :
        accelerationInMetersPerSecondSquared
            (setup.pebbleAccelerationIfConstrained
              candidateAmplitude upperTime) =
          -ω ^ 2 * lengthInMeters candidateAmplitude := by
      calc
        accelerationInMetersPerSecondSquared
              (setup.pebbleAccelerationIfConstrained
                candidateAmplitude upperTime) =
            accelerationInMetersPerSecondSquared
              (setup.boardEndAcceleration candidateAmplitude upperTime) :=
                hlaws.constrainedMotionLaw candidateAmplitude upperTime
        _ = _ := hboard_acceleration
    have hnewton :=
      hlaws.verticalNewtonSecondLaw candidateAmplitude upperTime
    change
      forceInNewtons
            (setup.requiredNormalForce candidateAmplitude upperTime) -
          m * g =
        m *
          accelerationInMetersPerSecondSquared
            (setup.pebbleAccelerationIfConstrained
              candidateAmplitude upperTime)
      at hnewton
    rw [hpebble_acceleration] at hnewton
    have hnormal :
        0 ≤
          forceInNewtons
            (setup.requiredNormalForce candidateAmplitude upperTime) :=
      hnormal_nonnegative upperTime
    have hproduct :
        0 ≤ m * (g - ω ^ 2 * lengthInMeters candidateAmplitude) := by
      nlinarith
    have hacceleration_bound :
        ω ^ 2 * lengthInMeters candidateAmplitude ≤ g := by
      have :=
        (mul_nonneg_iff_of_pos_left hm_pos).mp hproduct
      linarith
    rw [hmaximum_value]
    exact
      (le_div_iff₀ hω_sq_pos).2
        (by simpa [mul_comm] using hacceleration_bound)
  have sin_lt_local {x : ℝ} (hx : 0 < x) : Real.sin x < x := by
    rcases lt_or_ge 1 x with hx_one | hx_one
    · exact (Real.sin_le_one x).trans_lt hx_one
    have habs : |x| = x := abs_of_nonneg hx.le
    have hbound :=
      le_of_abs_le
        (Real.sin_bound <| show |x| ≤ 1 by rwa [habs])
    rw [sub_le_iff_le_add', habs] at hbound
    apply hbound.trans_lt
    rw [sub_add, sub_lt_self_iff, sub_pos, div_eq_mul_inv (x ^ 3)]
    refine mul_lt_mul' ?_ (by norm_num) (by norm_num) (pow_pos hx 3)
    apply pow_le_pow_of_le_one hx.le hx_one
    simp
  have sin_gt_sub_cube_local {x : ℝ} (hx : 0 < x) (hx_one : x ≤ 1) :
      x - x ^ 3 / 4 < Real.sin x := by
    have habs : |x| = x := abs_of_nonneg hx.le
    have hbound :=
      neg_le_of_abs_le
        (Real.sin_bound <| show |x| ≤ 1 by rwa [habs])
    rw [le_sub_iff_add_le, habs] at hbound
    refine lt_of_lt_of_le ?_ hbound
    have hdifference :
        x ^ 3 / (4 : ℝ) - x ^ 3 / 6 = x ^ 3 * 12⁻¹ := by
      norm_num [div_eq_mul_inv, ← mul_sub]
    rw [add_comm, sub_add, sub_neg_eq_add, sub_lt_sub_iff_left,
      ← lt_sub_iff_add_lt', hdifference]
    refine mul_lt_mul' ?_ (by norm_num) (by norm_num) (pow_pos hx 3)
    apply pow_le_pow_of_le_one hx.le hx_one
    simp
  have pi_gt_sqrt_series_local (n : ℕ) :
      2 ^ (n + 1) *
          √(2 - Real.sqrtTwoAddSeries 0 n) <
        Real.pi := by
    have hsine :
        √(2 - Real.sqrtTwoAddSeries 0 n) / 2 *
            2 ^ (n + 2) <
          Real.pi := by
      rw [← lt_div_iff₀, ← Real.sin_pi_over_two_pow_succ]
      focus
        apply sin_lt_local
        apply div_pos Real.pi_pos
      all_goals apply pow_pos <;> norm_num
    refine lt_of_le_of_lt (le_of_eq ?_) hsine
    rw [pow_succ' _ (n + 1), ← mul_assoc, div_mul_cancel₀, mul_comm]
    simp
  have pi_lt_sqrt_series_local (n : ℕ) :
      Real.pi <
        2 ^ (n + 1) *
            √(2 - Real.sqrtTwoAddSeries 0 n) +
          1 / 4 ^ n := by
    have hsine :
        Real.pi <
          (√(2 - Real.sqrtTwoAddSeries 0 n) / 2 +
              1 / (2 ^ n) ^ 3 / 4) *
            (2 : ℝ) ^ (n + 2) := by
      rw [← div_lt_iff₀ (by simp),
        ← Real.sin_pi_over_two_pow_succ, ← sub_lt_iff_lt_add']
      calc
        Real.pi / 2 ^ (n + 2) -
              Real.sin (Real.pi / 2 ^ (n + 2)) <
            (Real.pi / 2 ^ (n + 2)) ^ 3 / 4 :=
          sub_lt_comm.1 <|
            sin_gt_sub_cube_local (by positivity) <|
              div_le_one_of_le₀
                (by
                  calc
                    Real.pi ≤ 4 := Real.pi_le_four
                    _ = 2 ^ (0 + 2) := by norm_num
                    _ ≤ 2 ^ (n + 2) := by gcongr <;> norm_num)
                (by positivity)
        _ ≤ (4 / 2 ^ (n + 2)) ^ 3 / 4 := by
          gcongr
          exact Real.pi_le_four
        _ = 1 / (2 ^ n) ^ 3 / 4 := by
          simp [add_comm n, pow_add, div_mul_eq_div_div]
          norm_num
    refine lt_of_lt_of_le hsine (le_of_eq ?_)
    rw [add_mul]
    congr 1
    · ring
    simp only [show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul,
      div_div, ← pow_add]
    rw [one_div, one_div, inv_mul_eq_iff_eq_mul₀, eq_comm,
      mul_inv_eq_iff_eq_mul₀, ← pow_add]
    · rw [add_assoc, Nat.mul_succ, add_comm, add_comm n,
        add_assoc, mul_comm n]
    all_goals norm_num
  have pi_lower_start_local (n : ℕ) {a : ℝ}
      (hseries :
        Real.sqrtTwoAddSeries ((0 : ℕ) / (1 : ℕ)) n ≤
          (2 : ℝ) - (a / (2 : ℝ) ^ (n + 1)) ^ 2) :
      a < Real.pi := by
    refine lt_of_le_of_lt ?_ (pi_gt_sqrt_series_local n)
    rw [mul_comm]
    refine
      (div_le_iff₀ (pow_pos (by simp) _)).mp
        (Real.le_sqrt_of_sq_le ?_)
    rwa [le_sub_comm,
      show (0 : ℝ) = (0 : ℕ) / (1 : ℕ) by
        rw [Nat.cast_zero, zero_div]]
  have sqrt_series_step_up_local
      (c d : ℕ) {a b n : ℕ} {z : ℝ}
      (hseries : Real.sqrtTwoAddSeries (c / d) n ≤ z)
      (hb : 0 < b) (hd : 0 < d)
      (hrational : (2 * b + a) * d ^ 2 ≤ c ^ 2 * b) :
      Real.sqrtTwoAddSeries (a / b) (n + 1) ≤ z := by
    refine le_trans ?_ hseries
    rw [Real.sqrtTwoAddSeries_succ]
    apply Real.sqrtTwoAddSeries_monotone_left
    have hb_real : 0 < (b : ℝ) := Nat.cast_pos.2 hb
    have hd_real : 0 < (d : ℝ) := Nat.cast_pos.2 hd
    rw [Real.sqrt_le_left (div_nonneg c.cast_nonneg d.cast_nonneg),
      div_pow, add_div_eq_mul_add_div _ _ (ne_of_gt hb_real),
      div_le_div_iff₀ hb_real (pow_pos hd_real _)]
    exact_mod_cast hrational
  have pi_upper_start_local (n : ℕ) {a : ℝ}
      (hseries :
        (2 : ℝ) -
            ((a - 1 / (4 : ℝ) ^ n) /
                (2 : ℝ) ^ (n + 1)) ^ 2 ≤
          Real.sqrtTwoAddSeries ((0 : ℕ) / (1 : ℕ)) n)
      (ha : (1 : ℝ) / (4 : ℝ) ^ n ≤ a) :
      Real.pi < a := by
    refine lt_of_lt_of_le (pi_lt_sqrt_series_local n) ?_
    rw [← le_sub_iff_add_le, ← le_div_iff₀', Real.sqrt_le_left,
      sub_le_comm]
    · rwa [Nat.cast_zero, zero_div] at hseries
    · exact
        div_nonneg (sub_nonneg.2 ha)
          (pow_nonneg (le_of_lt zero_lt_two) _)
    · exact pow_pos zero_lt_two _
  have sqrt_series_step_down_local
      (a b : ℕ) {c d n : ℕ} {z : ℝ}
      (hseries : z ≤ Real.sqrtTwoAddSeries (a / b) n)
      (hb : 0 < b) (hd : 0 < d)
      (hrational : a ^ 2 * d ≤ (2 * d + c) * b ^ 2) :
      z ≤ Real.sqrtTwoAddSeries (c / d) (n + 1) := by
    apply le_trans hseries
    rw [Real.sqrtTwoAddSeries_succ]
    apply Real.sqrtTwoAddSeries_monotone_left
    apply Real.le_sqrt_of_sq_le
    have hb_real : 0 < (b : ℝ) := Nat.cast_pos.2 hb
    have hd_real : 0 < (d : ℝ) := Nat.cast_pos.2 hd
    rw [div_pow, add_div_eq_mul_add_div _ _ (ne_of_gt hd_real),
      div_le_div_iff₀ (pow_pos hb_real _) hd_real]
    exact_mod_cast hrational
  have hpi_lower : (157 : ℝ) / 50 < Real.pi := by
    apply pi_lower_start_local 4
    refine
      sqrt_series_step_up_local 338 239 ?_
        (by norm_num) (by norm_num) (by norm_num)
    refine
      sqrt_series_step_up_local 704 381 ?_
        (by norm_num) (by norm_num) (by norm_num)
    refine
      sqrt_series_step_up_local 1940 989 ?_
        (by norm_num) (by norm_num) (by norm_num)
    refine
      sqrt_series_step_up_local 1447 727 ?_
        (by norm_num) (by norm_num) (by norm_num)
    simp [Real.sqrtTwoAddSeries]
    norm_num
  have hpi_upper : Real.pi < (22 : ℝ) / 7 := by
    have hpi_lt_d4 : Real.pi < (3.1416 : ℝ) := by
      apply pi_upper_start_local 9
      refine
        sqrt_series_step_down_local 4756 3363 ?_
          (by norm_num) (by norm_num) (by norm_num)
      refine
        sqrt_series_step_down_local 14965 8099 ?_
          (by norm_num) (by norm_num) (by norm_num)
      refine
        sqrt_series_step_down_local 21183 10799 ?_
          (by norm_num) (by norm_num) (by norm_num)
      refine
        sqrt_series_step_down_local 49188 24713 ?_
          (by norm_num) (by norm_num) (by norm_num)
      refine
        sqrt_series_step_down_local 43947 22000 ?_
          (by norm_num) (by norm_num) (by norm_num)
      refine
        sqrt_series_step_down_local 235667 117869 ?_
          (by norm_num) (by norm_num) (by norm_num)
      refine
        sqrt_series_step_down_local 624137 312092 ?_
          (by norm_num) (by norm_num) (by norm_num)
      refine
        sqrt_series_step_down_local 903049 451533 ?_
          (by norm_num) (by norm_num) (by norm_num)
      refine
        sqrt_series_step_down_local 849938 424971 ?_
          (by norm_num) (by norm_num) (by norm_num)
      simp [Real.sqrtTwoAddSeries]
      all_goals norm_num
    norm_num at hpi_lt_d4 ⊢
    linarith
  have hpi_sq_lower : ((157 : ℝ) / 50) ^ 2 < Real.pi ^ 2 := by
    have hproduct :
        0 <
          (Real.pi - (157 : ℝ) / 50) *
            (Real.pi + (157 : ℝ) / 50) :=
      mul_pos (sub_pos.mpr hpi_lower)
        (add_pos Real.pi_pos (by norm_num))
    nlinarith
  have hpi_sq_upper : Real.pi ^ 2 < ((22 : ℝ) / 7) ^ 2 := by
    have hproduct :
        0 <
          ((22 : ℝ) / 7 - Real.pi) *
            ((22 : ℝ) / 7 + Real.pi) :=
      mul_pos (sub_pos.mpr hpi_upper)
        (add_pos (by norm_num) Real.pi_pos)
    nlinarith
  have hdenominator_pos : 0 < (2 * Real.pi * 2.8 : ℝ) ^ 2 := by
    positivity
  have hvalue_lower :
      (315 : ℝ) / 10000 < lengthInMeters maximumAmplitude := by
    rw [hmaximum_value, hg, hω_value]
    apply (lt_div_iff₀ hdenominator_pos).2
    nlinarith [hpi_sq_upper]
  have hvalue_upper :
      lengthInMeters maximumAmplitude < (32 : ℝ) / 1000 := by
    rw [hmaximum_value, hg, hω_value]
    apply (div_lt_iff₀ hdenominator_pos).2
    nlinarith [hpi_sq_lower]
  have hchoice_close :
      |lengthInMeters maximumAmplitude -
          amplitudeAnswerChoiceInMeters .D| <
        5 * (10 : ℝ) ^ (-4 : ℤ) := by
    norm_num [amplitudeAnswerChoiceInMeters]
    rw [abs_of_neg (by nlinarith [hvalue_upper])]
    nlinarith [hvalue_lower]
  have hchoice_nearest :
      ∀ choice : AmplitudeAnswerChoice,
        |lengthInMeters maximumAmplitude -
            amplitudeAnswerChoiceInMeters .D| ≤
          |lengthInMeters maximumAmplitude -
            amplitudeAnswerChoiceInMeters choice| := by
    intro choice
    cases choice with
    | A =>
        norm_num [amplitudeAnswerChoiceInMeters]
        rw [abs_of_neg (by nlinarith [hvalue_upper])]
        rw [abs_of_neg (by nlinarith [hvalue_upper])]
        norm_num
    | B =>
        norm_num [amplitudeAnswerChoiceInMeters]
        rw [abs_of_neg (by nlinarith [hvalue_upper])]
        rw [abs_of_pos (by nlinarith [hvalue_lower])]
        nlinarith [hvalue_lower]
    | C =>
        norm_num [amplitudeAnswerChoiceInMeters]
        rw [abs_of_neg (by nlinarith [hvalue_upper])]
        rw [abs_of_pos (by nlinarith [hvalue_lower])]
        nlinarith [hvalue_lower]
    | D =>
        rfl
  refine ⟨maximumAmplitude, ?_, ?_, ?_, hchoice_close, hchoice_nearest⟩
  · exact ⟨hmaximum_preserves, hmaximum_dominates⟩
  · simpa [g, ω] using hmaximum_value
  · rw [hmaximum_value, hω_conversion]

end PhyXMiniProblems.ProblemPhyXMini0205
