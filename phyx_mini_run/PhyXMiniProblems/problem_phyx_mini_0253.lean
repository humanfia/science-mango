import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Physlib.Units.WithDim.Speed

/-!
# Phase constant from a harmonic-oscillator velocity graph

This file models problem `phyx_mini_0253`.  The primary image plots velocity
in centimetres per second against time.  Its vertical scale mark is
`v_s = 4.0 cm/s`; the mark lies four grid spacings above zero, the positive
velocity peak lies one further spacing above it, and the graph is descending
where the time axis crosses the curve at `v = v_s`.

Length, time, velocity, angular frequency, and acceleration are represented by
Physlib dimensionful quantities.  Real numbers below are coherent unit
readouts, the dimensionless phase in radians, or displayed answer values.
-/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0253

open Dimension

/-! ## Dimensionful oscillator quantities and coherent readouts -/

/-- A one-dimensional oscillator displacement or displacement amplitude. -/
abbrev OscillatorLength : Type := Dimensionful (WithDim L𝓭 ℝ)

/-- A physical time shown on the horizontal graph axis. -/
abbrev OscillatorTime : Type := Dimensionful (WithDim T𝓭 ℝ)

/-- A physical angular frequency, with radians treated as dimensionless. -/
abbrev AngularFrequency : Type := Dimensionful (WithDim T𝓭⁻¹ ℝ)

/-- A signed one-dimensional velocity. -/
abbrev OscillatorVelocity : Type :=
  Dimensionful (WithDim (L𝓭 * T𝓭⁻¹) ℝ)

/-- A signed one-dimensional acceleration, equivalently a velocity-graph slope. -/
abbrev OscillatorAcceleration : Type :=
  Dimensionful (WithDim (L𝓭 * T𝓭⁻¹ * T𝓭⁻¹) ℝ)

/-- Read a physical length in centimetres. -/
def centimetersValue (length : OscillatorLength) : ℝ :=
  (length ({ UnitChoices.SI with length := LengthUnit.centimeters } :
    UnitChoices)).val

/-- Read a physical time in seconds. -/
def secondsValue (time : OscillatorTime) : ℝ :=
  (time UnitChoices.SI).val

/-- Read an angular frequency in radians per second. -/
def radiansPerSecondValue (frequency : AngularFrequency) : ℝ :=
  (frequency UnitChoices.SI).val

/-- Read a signed velocity in centimetres per second. -/
def centimetersPerSecondValue (velocity : OscillatorVelocity) : ℝ :=
  (velocity ({ UnitChoices.SI with length := LengthUnit.centimeters } :
    UnitChoices)).val

/-- Read a signed acceleration in centimetres per second squared. -/
def centimetersPerSecondSquaredValue
    (acceleration : OscillatorAcceleration) : ℝ :=
  (acceleration ({ UnitChoices.SI with length := LengthUnit.centimeters } :
    UnitChoices)).val

/-! ## Oscillator and primary-figure data -/

/-- Physical roles of the two axes in the supplied graph. -/
inductive GraphAxisQuantity where
  | time
  | velocity
  deriving DecidableEq, Repr

/--
The oscillator quantities and the labeled/read-off features of the primary
velocity graph.

The field `phaseConstant` is not assigned an answer here.  It is constrained
only through the harmonic-oscillator laws below and is the quantity determined
by the theorem.
-/
structure VelocityGraphOscillator where
  /-- Position amplitude `x_m` in `x(t) = x_m cos (ω t + φ)`. -/
  positionAmplitude : OscillatorLength
  /-- Positive angular frequency `ω`. -/
  angularFrequency : AngularFrequency
  /-- Dimensionless phase constant `φ`, whose numerical unit is radians. -/
  phaseConstant : ℝ
  /-- Physical position function. -/
  position : OscillatorTime → OscillatorLength
  /-- Physical velocity function drawn in the figure. -/
  velocity : OscillatorTime → OscillatorVelocity
  /-- Physical acceleration, i.e. the instantaneous slope of the velocity graph. -/
  acceleration : OscillatorTime → OscillatorAcceleration
  /-- The time represented by the vertical axis of the graph. -/
  timeOrigin : OscillatorTime
  /-- Positive velocity scale mark labeled `v_s`. -/
  velocityScaleVs : OscillatorVelocity
  /-- The equally spaced vertical-grid increment. -/
  velocityGridSpacing : OscillatorVelocity
  /-- Magnitude `v_m` of the positive and negative velocity peaks. -/
  velocityAmplitude : OscillatorVelocity
  /-- Number of vertical grid spacings between zero and `v_s`. -/
  gridIntervalsZeroToVs : ℕ
  /-- Number of further grid spacings between `v_s` and the positive peak. -/
  gridIntervalsVsToPeak : ℕ
  /-- Quantity represented by the horizontal axis label `t`. -/
  horizontalAxis : GraphAxisQuantity
  /-- Quantity represented by the vertical axis label `v (cm/s)`. -/
  verticalAxis : GraphAxisQuantity

/-- Positivity and the standard positive representative convention for phase. -/
def HasPhysicalParameters (setup : VelocityGraphOscillator) : Prop :=
  0 < centimetersValue setup.positionAmplitude ∧
    0 < radiansPerSecondValue setup.angularFrequency ∧
    0 < centimetersPerSecondValue setup.velocityAmplitude ∧
    0 ≤ setup.phaseConstant ∧ setup.phaseConstant < 2 * Real.pi

/--
Readouts supplied by the primary image and the stated scale calibration.

There are four grid intervals from zero to `v_s = 4 cm/s` and one further
interval to the positive peak.  At the displayed time origin the curve has
value `v_s` and negative slope.  These are graph observations, not assumptions
of the requested phase or answer choice.
-/
def MatchesPrimaryVelocityGraph (setup : VelocityGraphOscillator) : Prop :=
  setup.horizontalAxis = .time ∧
    setup.verticalAxis = .velocity ∧
    secondsValue setup.timeOrigin = 0 ∧
    setup.gridIntervalsZeroToVs = 4 ∧
    setup.gridIntervalsVsToPeak = 1 ∧
    centimetersPerSecondValue setup.velocityGridSpacing = 1 ∧
    centimetersPerSecondValue setup.velocityScaleVs =
      setup.gridIntervalsZeroToVs *
        centimetersPerSecondValue setup.velocityGridSpacing ∧
    centimetersPerSecondValue setup.velocityAmplitude =
      centimetersPerSecondValue setup.velocityScaleVs +
        setup.gridIntervalsVsToPeak *
          centimetersPerSecondValue setup.velocityGridSpacing ∧
    centimetersPerSecondValue setup.velocityScaleVs = 4 ∧
    centimetersPerSecondValue (setup.velocity setup.timeOrigin) =
      centimetersPerSecondValue setup.velocityScaleVs ∧
    centimetersPerSecondSquaredValue
        (setup.acceleration setup.timeOrigin) < 0

/-! ## Governing harmonic-oscillator laws -/

/--
The position, velocity, and acceleration functions obey the cosine-form
simple-harmonic-motion model with the sign convention stated in the problem.
All three equations are expressed in coherent centimetre/second readouts.

In particular, differentiating `x_m cos (ω t + φ)` gives the minus sign in
the velocity law.  No phase value or answer-choice statement is included in
this governing-law interface.
-/
structure SatisfiesCosineHarmonicOscillatorLaws
    (setup : VelocityGraphOscillator) : Prop where
  position_cosine_form : ∀ time,
    centimetersValue (setup.position time) =
      centimetersValue setup.positionAmplitude *
        Real.cos
          (radiansPerSecondValue setup.angularFrequency * secondsValue time +
            setup.phaseConstant)
  velocity_is_position_derivative : ∀ time,
    centimetersPerSecondValue (setup.velocity time) =
      -(centimetersValue setup.positionAmplitude *
          radiansPerSecondValue setup.angularFrequency) *
        Real.sin
          (radiansPerSecondValue setup.angularFrequency * secondsValue time +
            setup.phaseConstant)
  acceleration_is_velocity_derivative : ∀ time,
    centimetersPerSecondSquaredValue (setup.acceleration time) =
      -(centimetersValue setup.positionAmplitude *
          radiansPerSecondValue setup.angularFrequency ^ 2) *
        Real.cos
          (radiansPerSecondValue setup.angularFrequency * secondsValue time +
            setup.phaseConstant)
  velocity_amplitude_relation :
    centimetersPerSecondValue setup.velocityAmplitude =
      centimetersValue setup.positionAmplitude *
        radiansPerSecondValue setup.angularFrequency

/-! ## Exact phase and displayed answer -/

/-- Labels of the four answers printed with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Phase in radians printed beside each answer label. -/
def AnswerChoice.radians : AnswerChoice → ℝ
  | .A => 486 / 100
  | .B => 512 / 100
  | .C => 536 / 100
  | .D => 572 / 100

/-- The answer label recorded in the supplied dataset metadata. -/
def recordedAnswerChoice : AnswerChoice := .C

/-- Agreement with a phase displayed to the nearest hundredth of a radian. -/
def MatchesAnswerChoice (phase : ℝ) (choice : AnswerChoice) : Prop :=
  |phase - choice.radians| ≤ 1 / 200

/--
The graph gives `v(0)/v_m = 4/5` on the descending branch.  With
`v = -v_m sin (ω t + φ)` and the positive representative convention, this
selects the fourth-quadrant phase `2π - arcsin (4/5)`.

This is the exact symbolic part of
`thm:physics:phyx_mini_0253:target`.
-/
lemma phaseConstant_exact
    (setup : VelocityGraphOscillator)
    (h_physical : HasPhysicalParameters setup)
    (h_figure : MatchesPrimaryVelocityGraph setup)
    (h_laws : SatisfiesCosineHarmonicOscillatorLaws setup) :
    setup.phaseConstant =
      2 * Real.pi - Real.arcsin ((4 : ℝ) / 5) := by
  rcases h_physical with
    ⟨h_positionAmplitude, h_angularFrequency, _h_velocityAmplitude,
      h_phase_nonnegative, h_phase_lt_two_pi⟩
  rcases h_figure with
    ⟨_h_horizontalAxis, _h_verticalAxis, h_timeOrigin,
      _h_gridIntervalsZeroToVs, h_gridIntervalsVsToPeak,
      h_gridSpacing, _h_scale_from_grid, h_amplitude_from_grid,
      h_velocityScale, h_velocity_at_origin, h_acceleration_at_origin⟩
  have h_velocityAmplitude :
      centimetersPerSecondValue setup.velocityAmplitude = 5 := by
    rw [h_gridIntervalsVsToPeak, h_velocityScale, h_gridSpacing] at h_amplitude_from_grid
    norm_num at h_amplitude_from_grid ⊢
    exact h_amplitude_from_grid
  have h_sin_phase : Real.sin setup.phaseConstant = -(4 / 5 : ℝ) := by
    have h_velocity_law :=
      h_laws.velocity_is_position_derivative setup.timeOrigin
    rw [h_timeOrigin, mul_zero, zero_add,
      ← h_laws.velocity_amplitude_relation] at h_velocity_law
    rw [h_velocity_at_origin, h_velocityScale, h_velocityAmplitude] at h_velocity_law
    nlinarith
  have h_cos_phase : 0 < Real.cos setup.phaseConstant := by
    have h_acceleration_law :=
      h_laws.acceleration_is_velocity_derivative setup.timeOrigin
    rw [h_timeOrigin, mul_zero, zero_add] at h_acceleration_law
    rw [h_acceleration_law] at h_acceleration_at_origin
    have h_positive_coefficient :
        0 <
          centimetersValue setup.positionAmplitude *
            radiansPerSecondValue setup.angularFrequency ^ 2 :=
      mul_pos h_positionAmplitude (sq_pos_of_pos h_angularFrequency)
    nlinarith
  have h_phase_gt_pi : Real.pi < setup.phaseConstant := by
    by_contra h_not_gt
    have h_sin_nonnegative :=
      Real.sin_nonneg_of_nonneg_of_le_pi h_phase_nonnegative
        (le_of_not_gt h_not_gt)
    nlinarith
  have h_phase_gt_three_pi_div_two :
      Real.pi + Real.pi / 2 < setup.phaseConstant := by
    by_contra h_not_gt
    have h_pi_div_two_le_phase : Real.pi / 2 ≤ setup.phaseConstant := by
      nlinarith [Real.pi_pos]
    have h_cos_nonpositive :=
      Real.cos_nonpos_of_pi_div_two_le_of_le h_pi_div_two_le_phase
        (le_of_not_gt h_not_gt)
    linarith
  have h_shift_mem_principal :
      setup.phaseConstant - 2 * Real.pi ∈
        Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor
    · nlinarith
    · nlinarith [Real.pi_pos]
  have h_sin_shift :
      Real.sin (setup.phaseConstant - 2 * Real.pi) = -(4 / 5 : ℝ) := by
    rw [Real.sin_sub, Real.cos_two_pi, Real.sin_two_pi, h_sin_phase]
    ring
  have h_arcsin_shift :=
    Real.arcsin_eq_of_sin_eq h_sin_shift h_shift_mem_principal
  rw [Real.arcsin_neg] at h_arcsin_shift
  linarith

/--
The positive phase is approximately `5.36 rad`, so the displayed answer is C.

This formalizes `thm:physics:phyx_mini_0253:target` without assuming either
the exact phase formula or the requested answer-choice conclusion.
-/
theorem phaseConstant_matches_recordedAnswerC
    (setup : VelocityGraphOscillator)
    (h_physical : HasPhysicalParameters setup)
    (h_figure : MatchesPrimaryVelocityGraph setup)
    (h_laws : SatisfiesCosineHarmonicOscillatorLaws setup) :
    0 < setup.phaseConstant ∧
      MatchesAnswerChoice setup.phaseConstant recordedAnswerChoice := by
  have double_interval (s c sl su cl cu : ℝ)
      (hs : sl ≤ s ∧ s ≤ su) (hc : cl ≤ c ∧ c ≤ cu)
      (hsl : 0 ≤ sl) (hcl : 0 ≤ cl) :
      2 * sl * cl ≤ 2 * s * c ∧
        2 * s * c ≤ 2 * su * cu ∧
        cl ^ 2 - su ^ 2 ≤ c ^ 2 - s ^ 2 ∧
        c ^ 2 - s ^ 2 ≤ cu ^ 2 - sl ^ 2 := by
    have hs0 : 0 ≤ s := le_trans hsl hs.1
    have hc0 : 0 ≤ c := le_trans hcl hc.1
    have hsu0 : 0 ≤ su := le_trans hs0 hs.2
    have hcu0 : 0 ≤ cu := le_trans hc0 hc.2
    exact
      ⟨by nlinarith [mul_le_mul hs.1 hc.1 hcl hs0],
        by nlinarith [mul_le_mul hs.2 hc.2 hc0 hsu0],
        by
          nlinarith [(sq_le_sq₀ hcl hc0).2 hc.1,
            (sq_le_sq₀ hs0 hsu0).2 hs.2],
        by
          nlinarith [(sq_le_sq₀ hc0 hcu0).2 hc.2,
            (sq_le_sq₀ hsl hs0).2 hs.1]⟩
  have h_sin_pi_lower_positive :
      0 < Real.sin (7853 / 2500 : ℝ) := by
    let a : ℝ := 7853 / 80000
    have ha : |a| ≤ 1 := by
      norm_num [a, abs_of_nonneg]
    have hsb := Real.sin_bound ha
    have hcb := Real.cos_bound ha
    rw [abs_le] at hsb hcb
    norm_num [a, abs_of_nonneg] at hsb hcb
    have hs0 :
        (980000 / 10000000 : ℝ) ≤ Real.sin a ∧
          Real.sin a ≤ 980097 / 10000000 := by
      constructor <;> linarith only [hsb.1, hsb.2]
    have hc0 :
        (9951772 / 10000000 : ℝ) ≤ Real.cos a ∧
          Real.cos a ≤ 9951869 / 10000000 := by
      constructor <;> linarith only [hcb.1, hcb.2]
    have raw1 :=
      double_interval _ _ _ _ _ _ hs0 hc0 (by norm_num) (by norm_num)
    norm_num at raw1
    have hs1 :
        (1950547 / 10000000 : ℝ) ≤ Real.sin (2 * a) ∧
          Real.sin (2 * a) ≤ 1950760 / 10000000 := by
      rw [Real.sin_two_mul]
      constructor
      · linarith only [raw1.1]
      · linarith only [raw1.2.1]
    have hc1 :
        (9807717 / 10000000 : ℝ) ≤ Real.cos (2 * a) ∧
          Real.cos (2 * a) ≤ 9807930 / 10000000 := by
      rw [Real.cos_two_mul']
      constructor
      · linarith only [raw1.2.2.1]
      · linarith only [raw1.2.2.2]
    have raw2 :=
      double_interval _ _ _ _ _ _ hs1 hc1 (by norm_num) (by norm_num)
    norm_num at raw2
    have hs2 :
        (3826082 / 10000000 : ℝ) ≤ Real.sin (4 * a) ∧
          Real.sin (4 * a) ≤ 3826584 / 10000000 := by
      rw [show (4 : ℝ) * a = 2 * (2 * a) by ring, Real.sin_two_mul]
      constructor
      · linarith only [raw2.1]
      · linarith only [raw2.2.1]
    have hc2 :
        (9238584 / 10000000 : ℝ) ≤ Real.cos (4 * a) ∧
          Real.cos (4 * a) ≤ 9239086 / 10000000 := by
      rw [show (4 : ℝ) * a = 2 * (2 * a) by ring, Real.cos_two_mul']
      constructor
      · linarith only [raw2.2.2.1]
      · linarith only [raw2.2.2.2]
    have raw3 :=
      double_interval _ _ _ _ _ _ hs2 hc2 (by norm_num) (by norm_num)
    norm_num at raw3
    have hs3 :
        (7069515 / 10000000 : ℝ) ≤ Real.sin (8 * a) ∧
          Real.sin (8 * a) ≤ 7070828 / 10000000 := by
      rw [show (8 : ℝ) * a = 2 * (4 * a) by ring, Real.sin_two_mul]
      constructor
      · linarith only [raw3.1]
      · linarith only [raw3.2.1]
    have hc3 :
        (7070868 / 10000000 : ℝ) ≤ Real.cos (8 * a) ∧
          Real.cos (8 * a) ≤ 7072181 / 10000000 := by
      rw [show (8 : ℝ) * a = 2 * (4 * a) by ring, Real.cos_two_mul']
      constructor
      · linarith only [raw3.2.2.1]
      · linarith only [raw3.2.2.2]
    have raw4 :=
      double_interval _ _ _ _ _ _ hs3 hc3 (by norm_num) (by norm_num)
    norm_num at raw4
    have hs4 :
        (9997521 / 10000000 : ℝ) ≤ Real.sin (16 * a) ∧
          Real.sin (16 * a) ≤ 10001236 / 10000000 := by
      rw [show (16 : ℝ) * a = 2 * (8 * a) by ring, Real.sin_two_mul]
      constructor
      · linarith only [raw4.1]
      · linarith only [raw4.2.1]
    have hc4 :
        (56 / 10000000 : ℝ) ≤ Real.cos (16 * a) ∧
          Real.cos (16 * a) ≤ 3771 / 10000000 := by
      rw [show (16 : ℝ) * a = 2 * (8 * a) by ring, Real.cos_two_mul']
      constructor
      · linarith only [raw4.2.2.1]
      · linarith only [raw4.2.2.2]
    have hfinal : 0 < Real.sin (32 * a) := by
      rw [show (32 : ℝ) * a = 2 * (16 * a) by ring, Real.sin_two_mul]
      have hspos : 0 < Real.sin (16 * a) :=
        lt_of_lt_of_le (by norm_num) hs4.1
      have hcpos : 0 < Real.cos (16 * a) :=
        lt_of_lt_of_le (by norm_num) hc4.1
      positivity
    convert hfinal using 1
    all_goals norm_num [a]
  have h_sin_pi_upper_negative :
      Real.sin (1571 / 500 : ℝ) < 0 := by
    let a : ℝ := 1571 / 16000
    have ha : |a| ≤ 1 := by
      norm_num [a, abs_of_nonneg]
    have hsb := Real.sin_bound ha
    have hcb := Real.cos_bound ha
    rw [abs_le] at hsb hcb
    norm_num [a, abs_of_nonneg] at hsb hcb
    have hs0 :
        (980248 / 10000000 : ℝ) ≤ Real.sin a ∧
          Real.sin a ≤ 980346 / 10000000 := by
      constructor <;> linarith only [hsb.1, hsb.2]
    have hc0 :
        (9951747 / 10000000 : ℝ) ≤ Real.cos a ∧
          Real.cos a ≤ 9951845 / 10000000 := by
      constructor <;> linarith only [hcb.1, hcb.2]
    have raw1 :=
      double_interval _ _ _ _ _ _ hs0 hc0 (by norm_num) (by norm_num)
    norm_num at raw1
    have hs1 :
        (1951036 / 10000000 : ℝ) ≤ Real.sin (2 * a) ∧
          Real.sin (2 * a) ≤ 1951251 / 10000000 := by
      rw [Real.sin_two_mul]
      constructor
      · linarith only [raw1.1]
      · linarith only [raw1.2.1]
    have hc1 :
        (9807619 / 10000000 : ℝ) ≤ Real.cos (2 * a) ∧
          Real.cos (2 * a) ≤ 9807834 / 10000000 := by
      rw [Real.cos_two_mul']
      constructor
      · linarith only [raw1.2.2.1]
      · linarith only [raw1.2.2.2]
    have raw2 :=
      double_interval _ _ _ _ _ _ hs1 hc1 (by norm_num) (by norm_num)
    norm_num at raw2
    have hs2 :
        (3827003 / 10000000 : ℝ) ≤ Real.sin (4 * a) ∧
          Real.sin (4 * a) ≤ 3827510 / 10000000 := by
      rw [show (4 : ℝ) * a = 2 * (2 * a) by ring, Real.sin_two_mul]
      constructor
      · linarith only [raw2.1]
      · linarith only [raw2.2.1]
    have hc2 :
        (9238200 / 10000000 : ℝ) ≤ Real.cos (4 * a) ∧
          Real.cos (4 * a) ≤ 9238707 / 10000000 := by
      rw [show (4 : ℝ) * a = 2 * (2 * a) by ring, Real.cos_two_mul']
      constructor
      · linarith only [raw2.2.2.1]
      · linarith only [raw2.2.2.2]
    have raw3 :=
      double_interval _ _ _ _ _ _ hs2 hc2 (by norm_num) (by norm_num)
    norm_num at raw3
    have hs3 :
        (7070923 / 10000000 : ℝ) ≤ Real.sin (8 * a) ∧
          Real.sin (8 * a) ≤ 7072249 / 10000000 := by
      rw [show (8 : ℝ) * a = 2 * (4 * a) by ring, Real.sin_two_mul]
      constructor
      · linarith only [raw3.1]
      · linarith only [raw3.2.1]
    have hc3 :
        (7069450 / 10000000 : ℝ) ≤ Real.cos (8 * a) ∧
          Real.cos (8 * a) ≤ 7070776 / 10000000 := by
      rw [show (8 : ℝ) * a = 2 * (4 * a) by ring, Real.cos_two_mul']
      constructor
      · linarith only [raw3.2.2.1]
      · linarith only [raw3.2.2.2]
    have raw4 :=
      double_interval _ _ _ _ _ _ hs3 hc3 (by norm_num) (by norm_num)
    norm_num at raw4
    have hs4 :
        (9997507 / 10000000 : ℝ) ≤ Real.sin (16 * a) ∧
          Real.sin (16 * a) ≤ 10001258 / 10000000 := by
      rw [show (16 : ℝ) * a = 2 * (8 * a) by ring, Real.sin_two_mul]
      constructor
      · linarith only [raw4.1]
      · linarith only [raw4.2.1]
    have hc4 :
        (-3959 / 10000000 : ℝ) ≤ Real.cos (16 * a) ∧
          Real.cos (16 * a) ≤ -207 / 10000000 := by
      rw [show (16 : ℝ) * a = 2 * (8 * a) by ring, Real.cos_two_mul']
      constructor
      · linarith only [raw4.2.2.1]
      · linarith only [raw4.2.2.2]
    have hfinal : Real.sin (32 * a) < 0 := by
      rw [show (32 : ℝ) * a = 2 * (16 * a) by ring, Real.sin_two_mul]
      have hspos : 0 < Real.sin (16 * a) :=
        lt_of_lt_of_le (by norm_num) hs4.1
      have hcneg : Real.cos (16 * a) < 0 :=
        lt_of_le_of_lt hc4.2 (by norm_num)
      have hprod :=
        mul_neg_of_pos_of_neg hspos hcneg
      nlinarith only [hprod]
    convert hfinal using 1
    all_goals norm_num [a]
  have h_pi_lower : (7853 / 2500 : ℝ) < Real.pi := by
    by_contra h_not_lt
    have h_pi_le : Real.pi ≤ (7853 / 2500 : ℝ) :=
      le_of_not_gt h_not_lt
    have h_difference_nonnegative :
        0 ≤ (7853 / 2500 : ℝ) - Real.pi := sub_nonneg.mpr h_pi_le
    have h_difference_le_pi :
        (7853 / 2500 : ℝ) - Real.pi ≤ Real.pi := by
      nlinarith only [Real.two_le_pi]
    have h_sin_difference_nonnegative :=
      Real.sin_nonneg_of_nonneg_of_le_pi h_difference_nonnegative
        h_difference_le_pi
    have h_sin_rewrite :
        Real.sin (7853 / 2500 : ℝ) =
          -Real.sin ((7853 / 2500 : ℝ) - Real.pi) := by
      calc
        Real.sin (7853 / 2500 : ℝ) =
            Real.sin (((7853 / 2500 : ℝ) - Real.pi) + Real.pi) := by
              congr 1
              ring
        _ = -Real.sin ((7853 / 2500 : ℝ) - Real.pi) :=
          Real.sin_add_pi _
    linarith only [h_sin_pi_lower_positive,
      h_sin_difference_nonnegative, h_sin_rewrite]
  have h_pi_upper : Real.pi < (1571 / 500 : ℝ) := by
    by_contra h_not_lt
    have h_argument_le_pi : (1571 / 500 : ℝ) ≤ Real.pi :=
      le_of_not_gt h_not_lt
    have h_sin_nonnegative :=
      Real.sin_nonneg_of_nonneg_of_le_pi (by norm_num) h_argument_le_pi
    linarith only [h_sin_pi_upper_negative, h_sin_nonnegative]
  have h_sin_arcsin_lower :
      Real.sin (1159 / 1250 : ℝ) < (4 / 5 : ℝ) := by
    let a : ℝ := 1159 / 40000
    have ha : |a| ≤ 1 := by
      norm_num [a, abs_of_nonneg]
    have hsb := Real.sin_bound ha
    have hcb := Real.cos_bound ha
    rw [abs_le] at hsb hcb
    norm_num [a, abs_of_nonneg] at hsb hcb
    have hs0 :
        (289709 / 10000000 : ℝ) ≤ Real.sin a ∧
          Real.sin a ≤ 289710 / 10000000 := by
      constructor <;> linarith only [hsb.1, hsb.2]
    have hc0 :
        (9995801 / 10000000 : ℝ) ≤ Real.cos a ∧
          Real.cos a ≤ 9995803 / 10000000 := by
      constructor <;> linarith only [hcb.1, hcb.2]
    have raw1 :=
      double_interval _ _ _ _ _ _ hs0 hc0 (by norm_num) (by norm_num)
    norm_num at raw1
    have hs1 :
        (579174 / 10000000 : ℝ) ≤ Real.sin (2 * a) ∧
          Real.sin (2 * a) ≤ 579177 / 10000000 := by
      rw [Real.sin_two_mul]
      constructor
      · linarith only [raw1.1]
      · linarith only [raw1.2.1]
    have hc1 :
        (9983210 / 10000000 : ℝ) ≤ Real.cos (2 * a) ∧
          Real.cos (2 * a) ≤ 9983215 / 10000000 := by
      rw [Real.cos_two_mul']
      constructor
      · linarith only [raw1.2.2.1]
      · linarith only [raw1.2.2.2]
    have raw2 :=
      double_interval _ _ _ _ _ _ hs1 hc1 (by norm_num) (by norm_num)
    norm_num at raw2
    have hs2 :
        (1156403 / 10000000 : ℝ) ≤ Real.sin (4 * a) ∧
          Real.sin (4 * a) ≤ 1156410 / 10000000 := by
      rw [show (4 : ℝ) * a = 2 * (2 * a) by ring, Real.sin_two_mul]
      constructor
      · linarith only [raw2.1]
      · linarith only [raw2.2.1]
    have hc2 :
        (9932903 / 10000000 : ℝ) ≤ Real.cos (4 * a) ∧
          Real.cos (4 * a) ≤ 9932914 / 10000000 := by
      rw [show (4 : ℝ) * a = 2 * (2 * a) by ring, Real.cos_two_mul']
      constructor
      · linarith only [raw2.2.2.1]
      · linarith only [raw2.2.2.2]
    have raw3 :=
      double_interval _ _ _ _ _ _ hs2 hc2 (by norm_num) (by norm_num)
    norm_num at raw3
    have hs3 :
        (2297287 / 10000000 : ℝ) ≤ Real.sin (8 * a) ∧
          Real.sin (8 * a) ≤ 2297305 / 10000000 := by
      rw [show (8 : ℝ) * a = 2 * (4 * a) by ring, Real.sin_two_mul]
      constructor
      · linarith only [raw3.1]
      · linarith only [raw3.2.1]
    have hc3 :
        (9732527 / 10000000 : ℝ) ≤ Real.cos (8 * a) ∧
          Real.cos (8 * a) ≤ 9732552 / 10000000 := by
      rw [show (8 : ℝ) * a = 2 * (4 * a) by ring, Real.cos_two_mul']
      constructor
      · linarith only [raw3.2.2.1]
      · linarith only [raw3.2.2.2]
    have raw4 :=
      double_interval _ _ _ _ _ _ hs3 hc3 (by norm_num) (by norm_num)
    norm_num at raw4
    have hs4 :
        (4471681 / 10000000 : ℝ) ≤ Real.sin (16 * a) ∧
          Real.sin (16 * a) ≤ 4471729 / 10000000 := by
      rw [show (16 : ℝ) * a = 2 * (8 * a) by ring, Real.sin_two_mul]
      constructor
      · linarith only [raw4.1]
      · linarith only [raw4.2.1]
    have hc4 :
        (8944447 / 10000000 : ℝ) ≤ Real.cos (16 * a) ∧
          Real.cos (16 * a) ≤ 8944505 / 10000000 := by
      rw [show (16 : ℝ) * a = 2 * (8 * a) by ring, Real.cos_two_mul']
      constructor
      · linarith only [raw4.2.2.1]
      · linarith only [raw4.2.2.2]
    have raw5 :=
      double_interval _ _ _ _ _ _ hs4 hc4 (by norm_num) (by norm_num)
    norm_num at raw5
    have hs5 :
        (7999342 / 10000000 : ℝ) ≤ Real.sin (32 * a) ∧
          Real.sin (32 * a) ≤ 7999481 / 10000000 := by
      rw [show (32 : ℝ) * a = 2 * (16 * a) by ring, Real.sin_two_mul]
      constructor
      · linarith only [raw5.1]
      · linarith only [raw5.2.1]
    have hfinal : Real.sin (32 * a) < (4 / 5 : ℝ) := by
      linarith only [hs5.2]
    convert hfinal using 1
    all_goals norm_num [a]
  have h_sin_arcsin_upper :
      (4 / 5 : ℝ) < Real.sin (4637 / 5000 : ℝ) := by
    let a : ℝ := 4637 / 160000
    have ha : |a| ≤ 1 := by
      norm_num [a, abs_of_nonneg]
    have hsb := Real.sin_bound ha
    have hcb := Real.cos_bound ha
    rw [abs_le] at hsb hcb
    norm_num [a, abs_of_nonneg] at hsb hcb
    have hs0 :
        (289771 / 10000000 : ℝ) ≤ Real.sin a ∧
          Real.sin a ≤ 289773 / 10000000 := by
      constructor <;> linarith only [hsb.1, hsb.2]
    have hc0 :
        (9995800 / 10000000 : ℝ) ≤ Real.cos a ∧
          Real.cos a ≤ 9995801 / 10000000 := by
      constructor <;> linarith only [hcb.1, hcb.2]
    have raw1 :=
      double_interval _ _ _ _ _ _ hs0 hc0 (by norm_num) (by norm_num)
    norm_num at raw1
    have hs1 :
        (579298 / 10000000 : ℝ) ≤ Real.sin (2 * a) ∧
          Real.sin (2 * a) ≤ 579303 / 10000000 := by
      rw [Real.sin_two_mul]
      constructor
      · linarith only [raw1.1]
      · linarith only [raw1.2.1]
    have hc1 :
        (9983204 / 10000000 : ℝ) ≤ Real.cos (2 * a) ∧
          Real.cos (2 * a) ≤ 9983208 / 10000000 := by
      rw [Real.cos_two_mul']
      constructor
      · linarith only [raw1.2.2.1]
      · linarith only [raw1.2.2.2]
    have raw2 :=
      double_interval _ _ _ _ _ _ hs1 hc1 (by norm_num) (by norm_num)
    norm_num at raw2
    have hs2 :
        (1156650 / 10000000 : ℝ) ≤ Real.sin (4 * a) ∧
          Real.sin (4 * a) ≤ 1156661 / 10000000 := by
      rw [show (4 : ℝ) * a = 2 * (2 * a) by ring, Real.sin_two_mul]
      constructor
      · linarith only [raw2.1]
      · linarith only [raw2.2.1]
    have hc2 :
        (9932877 / 10000000 : ℝ) ≤ Real.cos (4 * a) ∧
          Real.cos (4 * a) ≤ 9932886 / 10000000 := by
      rw [show (4 : ℝ) * a = 2 * (2 * a) by ring, Real.cos_two_mul']
      constructor
      · linarith only [raw2.2.2.1]
      · linarith only [raw2.2.2.2]
    have raw3 :=
      double_interval _ _ _ _ _ _ hs2 hc2 (by norm_num) (by norm_num)
    norm_num at raw3
    have hs3 :
        (2297772 / 10000000 : ℝ) ≤ Real.sin (8 * a) ∧
          Real.sin (8 * a) ≤ 2297797 / 10000000 := by
      rw [show (8 : ℝ) * a = 2 * (4 * a) by ring, Real.sin_two_mul]
      constructor
      · linarith only [raw3.1]
      · linarith only [raw3.2.1]
    have hc3 :
        (9732418 / 10000000 : ℝ) ≤ Real.cos (8 * a) ∧
          Real.cos (8 * a) ≤ 9732439 / 10000000 := by
      rw [show (8 : ℝ) * a = 2 * (4 * a) by ring, Real.cos_two_mul']
      constructor
      · linarith only [raw3.2.2.1]
      · linarith only [raw3.2.2.2]
    have raw4 :=
      double_interval _ _ _ _ _ _ hs3 hc3 (by norm_num) (by norm_num)
    norm_num at raw4
    have hs4 :
        (4472575 / 10000000 : ℝ) ≤ Real.sin (16 * a) ∧
          Real.sin (16 * a) ≤ 4472634 / 10000000 := by
      rw [show (16 : ℝ) * a = 2 * (8 * a) by ring, Real.sin_two_mul]
      constructor
      · linarith only [raw4.1]
      · linarith only [raw4.2.1]
    have hc4 :
        (8944008 / 10000000 : ℝ) ≤ Real.cos (16 * a) ∧
          Real.cos (16 * a) ≤ 8944062 / 10000000 := by
      rw [show (16 : ℝ) * a = 2 * (8 * a) by ring, Real.cos_two_mul']
      constructor
      · linarith only [raw4.2.2.1]
      · linarith only [raw4.2.2.2]
    have raw5 :=
      double_interval _ _ _ _ _ _ hs4 hc4 (by norm_num) (by norm_num)
    norm_num at raw5
    have hs5 :
        (8000549 / 10000000 : ℝ) ≤ Real.sin (32 * a) ∧
          Real.sin (32 * a) ≤ 8000704 / 10000000 := by
      rw [show (32 : ℝ) * a = 2 * (16 * a) by ring, Real.sin_two_mul]
      constructor
      · linarith only [raw5.1]
      · linarith only [raw5.2.1]
    have hfinal : (4 / 5 : ℝ) < Real.sin (32 * a) := by
      linarith only [hs5.1]
    convert hfinal using 1
    all_goals norm_num [a]
  have h_argument_lower_mem :
      (1159 / 1250 : ℝ) ∈
        Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor <;> nlinarith only [Real.pi_pos, h_pi_lower]
  have h_argument_upper_mem :
      (4637 / 5000 : ℝ) ∈
        Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor <;> nlinarith only [Real.pi_pos, h_pi_lower]
  have h_arcsin_lower :
      (1159 / 1250 : ℝ) < Real.arcsin ((4 : ℝ) / 5) := by
    by_contra h_not_lt
    have h_arcsin_le :
        Real.arcsin ((4 : ℝ) / 5) ≤ (1159 / 1250 : ℝ) :=
      le_of_not_gt h_not_lt
    have h_four_fifths_le_sin :=
      (Real.arcsin_le_iff_le_sin (by norm_num) h_argument_lower_mem).1
        h_arcsin_le
    linarith only [h_sin_arcsin_lower, h_four_fifths_le_sin]
  have h_arcsin_upper :
      Real.arcsin ((4 : ℝ) / 5) < (4637 / 5000 : ℝ) :=
    (Real.arcsin_lt_iff_lt_sin (by norm_num) h_argument_upper_mem).2
      h_sin_arcsin_upper
  have h_phase_exact :=
    phaseConstant_exact setup h_physical h_figure h_laws
  have h_phase_lower : (1071 / 200 : ℝ) < setup.phaseConstant := by
    rw [h_phase_exact]
    nlinarith only [h_pi_lower, h_arcsin_upper]
  have h_phase_upper : setup.phaseConstant < (1073 / 200 : ℝ) := by
    rw [h_phase_exact]
    nlinarith only [h_pi_upper, h_arcsin_lower]
  constructor
  · linarith only [h_phase_lower]
  · change |setup.phaseConstant - 536 / 100| ≤ (1 / 200 : ℝ)
    rw [abs_le]
    constructor
    · nlinarith only [h_phase_lower]
    · nlinarith only [h_phase_upper]

end PhyXMiniProblems.ProblemPhyXMini0253
