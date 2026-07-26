import Mathlib.Analysis.Calculus.Deriv.Basic
import Physlib.ClassicalMechanics.HarmonicOscillator.Solution
import Physlib.Units.WithDim.Basic

/- USER: The assigned source file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0278

open Dimension

/-!
# Maximum angular speed of a torsion pendulum

A metal disk is soldered to the center of a taut vertical wire whose ends are
clamped.  The supplied upper graph plots torque magnitude against angular
displacement, and the lower graph plots the disk's angular position against
time.  The disk is released from rest at `0.200 rad`; the lower trace returns
from that positive turning point to the next positive turning point at the
marked time `t_s = 0.40 s`.

Physlib dimensionful quantities retain the dimensions of torque, moment of
inertia, torsion constant, time, and angular velocity.  Radians and oscillator
phase are dimensionless, so angular coordinates and figure-axis coordinates
are represented by real numbers.  Physlib's scalar harmonic oscillator is
linked below to the rotational inertia and torsion constant by explicit SI
readout equations.
-/

/-! ## Dimensionful physical quantities and coherent SI readouts -/

/-- A nonnegative physical duration. -/
abbrev TimeQuantity : Type := Dimensionful (WithDim T𝓭 NNReal)

/-- A disk's moment of inertia, with dimension mass times length squared. -/
abbrev MomentOfInertiaQuantity : Type :=
  Dimensionful (WithDim (M𝓭 * L𝓭 * L𝓭) NNReal)

/-- A nonnegative torque magnitude, measured coherently in newton-metres. -/
abbrev TorqueMagnitudeQuantity : Type :=
  Dimensionful
    (WithDim (M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹) NNReal)

/--
The torsion constant of the wire.  A radian is dimensionless, so the physical
dimension of `N m / rad` is mass times length squared divided by time squared.
The separate name records its restoring-coefficient role.
-/
abbrev TorsionConstantQuantity : Type :=
  Dimensionful
    (WithDim (M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹) NNReal)

/-- Signed angular velocity; radians are dimensionless, so its dimension is inverse time. -/
abbrev SignedAngularVelocityQuantity : Type :=
  Dimensionful (WithDim T𝓭⁻¹ ℝ)

/-- Read a duration in seconds. -/
def timeInSeconds (duration : TimeQuantity) : ℝ :=
  ((duration UnitChoices.SI).val : ℝ)

/-- Read a moment of inertia in SI `kg m^2`. -/
def momentOfInertiaInKilogramMeterSquared
    (inertia : MomentOfInertiaQuantity) : ℝ :=
  ((inertia UnitChoices.SI).val : ℝ)

/-- Read a torque magnitude in SI newton-metres. -/
def torqueMagnitudeInNewtonMeters
    (torque : TorqueMagnitudeQuantity) : ℝ :=
  ((torque UnitChoices.SI).val : ℝ)

/-- Read a torsion constant in SI `N m / rad`. -/
def torsionConstantInNewtonMetersPerRadian
    (torsionConstant : TorsionConstantQuantity) : ℝ :=
  ((torsionConstant UnitChoices.SI).val : ℝ)

/-- Read a signed angular velocity in radians per second. -/
def angularVelocityInRadiansPerSecond
    (angularVelocity : SignedAngularVelocityQuantity) : ℝ :=
  (angularVelocity UnitChoices.SI).val

/-! ## Apparatus and primary-figure labels -/

/-- Mechanical components named in the source description. -/
inductive ApparatusComponent where
  | metalDisk
  | centralWire
  | upperClamp
  | lowerClamp
  deriving DecidableEq, Repr

/-- The two graph panels in the supplied bitmap. -/
inductive GraphPanel where
  | torqueMagnitudeVersusAngle
  | angularPositionVersusTime
  deriving DecidableEq, Repr

/-- Horizontal and vertical graph-axis roles. -/
inductive AxisDirection where
  | horizontal
  | vertical
  deriving DecidableEq, Repr

/-- Physical labels, including units, printed on the graph axes. -/
inductive FigureAxisLabel where
  | rotationAngleRadians
  | torqueMilliNewtonMeters
  | timeSeconds
  deriving DecidableEq, Repr

/-- Qualitative shapes of the two plotted traces. -/
inductive CurveKind where
  | straightIncreasingThroughOrigin
  | sinusoidal
  deriving DecidableEq, Repr

/-- Verbal geometry of the clamped disk-and-wire torsion pendulum. -/
structure TorsionPendulumApparatus where
  visible : ApparatusComponent → Bool
  wirePassesThroughDiskCenter : Bool
  wireSolderedToDisk : Bool
  wireMountedVertically : Bool
  wireClampedAtBothEnds : Bool
  wirePulledTaut : Bool

/--
Data channels and labels belonging to the supplied two-panel figure.  The
functions store the plotted torque magnitudes and angular-position trace;
their quantitative interpretation is given by readout assumptions below.
-/
structure SuppliedFigure where
  axisLabel : GraphPanel → AxisDirection → FigureAxisLabel
  curveKind : GraphPanel → CurveKind
  showsGrid : GraphPanel → Bool
  torqueScaleMarkerVisible : Bool
  timeScaleMarkerVisible : Bool
  torqueAxisScale : TorqueMagnitudeQuantity
  timeAxisScale : TimeQuantity
  torqueMagnitudeAtAngleRad : ℝ → TorqueMagnitudeQuantity
  angularTraceRadAtSeconds : ℝ → ℝ

/-! ## Physical setup and independent response functions -/

/--
The torsion-pendulum experiment and its unknown time-dependent motion.

The angular-position and angular-velocity functions are independent fields;
neither is defined from the requested maximum speed.  `scalarOscillator` is
Physlib's one-coordinate harmonic oscillator, while `amplitudePhase` is its
standard cosine parametrization.  Governing-law hypotheses below state how
these scalar objects represent this rotational system.
-/
structure TorsionPendulumSetup where
  apparatus : TorsionPendulumApparatus
  figure : SuppliedFigure
  diskMomentOfInertia : MomentOfInertiaQuantity
  wireTorsionConstant : TorsionConstantQuantity
  releaseAngleRad : ℝ
  angularPositionRadAtSeconds : ℝ → ℝ
  angularVelocityAtSeconds : ℝ → SignedAngularVelocityQuantity
  scalarOscillator : ClassicalMechanics.HarmonicOscillator
  amplitudePhase :
    ClassicalMechanics.HarmonicOscillator.AmplitudePhase

/-! ## Assumptions: source data, primary-image readouts, and governing laws -/

/--
Numerical and qualitative facts stated in the problem text.  In particular,
the disk is released from rest at `0.200 rad`, `tau_s = 0.004 N m`, and
`t_s = 0.40 s`.  No maximum-speed value or answer choice occurs here.
-/
structure MatchesProblemData (setup : TorsionPendulumSetup) : Prop where
  metalDiskPresent : setup.apparatus.visible .metalDisk = true
  centralWirePresent : setup.apparatus.visible .centralWire = true
  upperClampPresent : setup.apparatus.visible .upperClamp = true
  lowerClampPresent : setup.apparatus.visible .lowerClamp = true
  wireThroughDiskCenter : setup.apparatus.wirePassesThroughDiskCenter = true
  wireSolderedInPlace : setup.apparatus.wireSolderedToDisk = true
  verticalMount : setup.apparatus.wireMountedVertically = true
  clampedEnds : setup.apparatus.wireClampedAtBothEnds = true
  tautWire : setup.apparatus.wirePulledTaut = true
  torqueAxisScaleNewtonMeters :
    torqueMagnitudeInNewtonMeters setup.figure.torqueAxisScale = 4 / 1000
  timeAxisScaleSeconds : timeInSeconds setup.figure.timeAxisScale = 2 / 5
  releaseAngleRadians : setup.releaseAngleRad = 1 / 5
  releasedAtPositiveTurningPoint :
    setup.angularPositionRadAtSeconds 0 = setup.releaseAngleRad
  releasedFromRest :
    angularVelocityInRadiansPerSecond
        (setup.angularVelocityAtSeconds 0) = 0

/--
Quantitative and qualitative evidence transcribed from the primary bitmap.
The lower graph begins at a positive maximum, reaches the negative maximum at
half of `t_s`, and returns to the next positive maximum at `t_s`; thus the
marked horizontal scale is one oscillation period.  These are data readouts,
not assumptions about the requested maximum angular speed.
-/
structure MatchesSuppliedFigure (setup : TorsionPendulumSetup) : Prop where
  upperHorizontalAxis :
    setup.figure.axisLabel .torqueMagnitudeVersusAngle .horizontal =
      .rotationAngleRadians
  upperVerticalAxis :
    setup.figure.axisLabel .torqueMagnitudeVersusAngle .vertical =
      .torqueMilliNewtonMeters
  lowerHorizontalAxis :
    setup.figure.axisLabel .angularPositionVersusTime .horizontal =
      .timeSeconds
  lowerVerticalAxis :
    setup.figure.axisLabel .angularPositionVersusTime .vertical =
      .rotationAngleRadians
  upperTraceLinear :
    setup.figure.curveKind .torqueMagnitudeVersusAngle =
      .straightIncreasingThroughOrigin
  lowerTraceSinusoidal :
    setup.figure.curveKind .angularPositionVersusTime = .sinusoidal
  upperGridVisible :
    setup.figure.showsGrid .torqueMagnitudeVersusAngle = true
  lowerGridVisible :
    setup.figure.showsGrid .angularPositionVersusTime = true
  torqueScaleMarked : setup.figure.torqueScaleMarkerVisible = true
  timeScaleMarked : setup.figure.timeScaleMarkerVisible = true
  upperTraceStartsAtOrigin :
    torqueMagnitudeInNewtonMeters
        (setup.figure.torqueMagnitudeAtAngleRad 0) = 0
  upperTraceEndpoint :
    setup.figure.torqueMagnitudeAtAngleRad setup.releaseAngleRad =
      setup.figure.torqueAxisScale
  plottedTraceIsDiskMotion :
    ∀ t, setup.figure.angularTraceRadAtSeconds t =
      setup.angularPositionRadAtSeconds t
  lowerTraceStartsAtPositiveMaximum :
    setup.figure.angularTraceRadAtSeconds 0 = setup.releaseAngleRad
  lowerTraceNegativeMaximumAtHalfScale :
    setup.figure.angularTraceRadAtSeconds
        (timeInSeconds setup.figure.timeAxisScale / 2) =
      -setup.releaseAngleRad
  lowerTraceNextPositiveMaximumAtScale :
    setup.figure.angularTraceRadAtSeconds
        (timeInSeconds setup.figure.timeAxisScale) =
      setup.releaseAngleRad
  markedScaleIsOscillatorPeriod :
    setup.scalarOscillator.period =
      timeInSeconds setup.figure.timeAxisScale

/-- Positivity and nondegeneracy of the physical readouts. -/
structure HasPhysicalTorsionPendulumParameters
    (setup : TorsionPendulumSetup) : Prop where
  momentOfInertiaPositive :
    0 < momentOfInertiaInKilogramMeterSquared setup.diskMomentOfInertia
  torsionConstantPositive :
    0 < torsionConstantInNewtonMetersPerRadian setup.wireTorsionConstant
  releaseAnglePositive : 0 < setup.releaseAngleRad
  torqueScalePositive :
    0 < torqueMagnitudeInNewtonMeters setup.figure.torqueAxisScale
  timeScalePositive : 0 < timeInSeconds setup.figure.timeAxisScale

/--
Governing laws of the ideal undamped torsion pendulum.

The first two fields identify Physlib's positive scalar oscillator parameters
with rotational inertia and torsion constant.  The third field is the linear
torque-magnitude law shown by the upper graph.  The remaining fields express
the zero-phase cosine solution and identify angular velocity with `dtheta/dt`.
They contain no assertion about a maximum and no displayed answer value.
-/
structure SatisfiesIdealTorsionPendulumLaws
    (setup : TorsionPendulumSetup) : Prop where
  oscillatorMassParameterIsMomentOfInertia :
    setup.scalarOscillator.m =
      momentOfInertiaInKilogramMeterSquared setup.diskMomentOfInertia
  oscillatorStiffnessParameterIsTorsionConstant :
    setup.scalarOscillator.k =
      torsionConstantInNewtonMetersPerRadian setup.wireTorsionConstant
  linearTorqueMagnitudeLaw :
    ∀ θ ∈ Set.Icc (0 : ℝ) setup.releaseAngleRad,
      torqueMagnitudeInNewtonMeters
          (setup.figure.torqueMagnitudeAtAngleRad θ) =
        torsionConstantInNewtonMetersPerRadian setup.wireTorsionConstant * θ
  amplitudeMatchesReleaseAngle :
    setup.amplitudePhase.A = setup.releaseAngleRad
  releasePhaseIsZero : setup.amplitudePhase.φ = 0
  angularPositionIsHarmonicTrajectory :
    ∀ t,
      setup.angularPositionRadAtSeconds t =
        setup.amplitudePhase.A *
          Real.cos
            (setup.scalarOscillator.ω * t - setup.amplitudePhase.φ)
  angularVelocityIsTimeDerivative :
    ∀ t,
      HasDerivAt setup.angularPositionRadAtSeconds
        (angularVelocityInRadiansPerSecond
          (setup.angularVelocityAtSeconds t)) t

/-! ## Displayed answers and current target -/

/-- Labels of the four numerical choices printed with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Displayed angular-speed values in radians per second. -/
def displayedAngularSpeedRadiansPerSecond : AnswerChoice → ℝ
  | .A => 298 / 100
  | .B => 302 / 100
  | .C => 326 / 100
  | .D => 314 / 100

/-- The answer label recorded in the dataset metadata. -/
def recordedDatasetAnswer : AnswerChoice := .D

/-- Agreement with a value displayed to the nearest `0.01 rad/s`. -/
def MatchesAnswerChoice
    (angularSpeedRadiansPerSecond : ℝ) (choice : AnswerChoice) : Prop :=
  |angularSpeedRadiansPerSecond -
      displayedAngularSpeedRadiansPerSecond choice| ≤ 1 / 200

/--
The lower trace has amplitude `0.200 rad` and period `0.40 s`, so the
greatest value attained by `|dtheta/dt|` is exactly
`A (2 pi / T) = pi rad/s`.  This lies within half of the last displayed digit
of `3.14 rad/s`, and therefore matches recorded answer choice D.

This theorem formalizes `thm:physics:phyx_mini_0278:target`.
-/
theorem problem_phyx_mini_0278
    (setup : TorsionPendulumSetup)
    (hData : MatchesProblemData setup)
    (hFigure : MatchesSuppliedFigure setup)
    (hPhysical : HasPhysicalTorsionPendulumParameters setup)
    (hLaws : SatisfiesIdealTorsionPendulumLaws setup) :
    IsGreatest
        (Set.range fun t : ℝ =>
          |angularVelocityInRadiansPerSecond
            (setup.angularVelocityAtSeconds t)|)
        Real.pi ∧
      MatchesAnswerChoice Real.pi recordedDatasetAnswer := by
  have hPeriod : setup.scalarOscillator.period = (2 / 5 : ℝ) := by
    rw [hFigure.markedScaleIsOscillatorPeriod, hData.timeAxisScaleSeconds]
  have hω : setup.scalarOscillator.ω = 5 * Real.pi := by
    rw [ClassicalMechanics.HarmonicOscillator.period_eq] at hPeriod
    have hω0 : setup.scalarOscillator.ω ≠ 0 :=
      setup.scalarOscillator.ω_ne_zero
    have hmul :
        2 * Real.pi = (2 / 5 : ℝ) * setup.scalarOscillator.ω :=
      (div_eq_iff hω0).mp hPeriod
    linarith
  have hTrajectory :
      setup.angularPositionRadAtSeconds =
        fun t =>
          setup.amplitudePhase.A *
            Real.cos
              (setup.scalarOscillator.ω * t - setup.amplitudePhase.φ) :=
    funext hLaws.angularPositionIsHarmonicTrajectory
  have hVelocity (t : ℝ) :
      angularVelocityInRadiansPerSecond
          (setup.angularVelocityAtSeconds t) =
        -Real.pi * Real.sin (5 * Real.pi * t) := by
    have hFormulaDeriv :
        HasDerivAt
          (fun s : ℝ =>
            setup.amplitudePhase.A *
              Real.cos
                (setup.scalarOscillator.ω * s - setup.amplitudePhase.φ))
          (setup.amplitudePhase.A *
            (-Real.sin
                (setup.scalarOscillator.ω * t - setup.amplitudePhase.φ) *
              setup.scalarOscillator.ω))
          t := by
      simpa only [id_eq, one_mul, mul_assoc, mul_comm, mul_left_comm] using
        (((hasDerivAt_id t).const_mul setup.scalarOscillator.ω).sub_const
          setup.amplitudePhase.φ).cos.const_mul setup.amplitudePhase.A
    rw [← hTrajectory] at hFormulaDeriv
    have hUnique :=
      (hLaws.angularVelocityIsTimeDerivative t).unique hFormulaDeriv
    rw [hLaws.amplitudeMatchesReleaseAngle, hData.releaseAngleRadians,
      hLaws.releasePhaseIsZero, hω] at hUnique
    norm_num at hUnique ⊢
    nlinarith
  have hSpeed (t : ℝ) :
      |angularVelocityInRadiansPerSecond
          (setup.angularVelocityAtSeconds t)| =
        Real.pi * |Real.sin (5 * Real.pi * t)| := by
    rw [hVelocity, abs_mul, abs_neg, abs_of_pos Real.pi_pos]
  constructor
  · constructor
    · refine ⟨1 / 10, ?_⟩
      change
        |angularVelocityInRadiansPerSecond
            (setup.angularVelocityAtSeconds (1 / 10))| =
          Real.pi
      rw [hSpeed]
      have harg :
          5 * Real.pi * (1 / 10 : ℝ) = Real.pi / 2 := by
        ring
      rw [harg, Real.sin_pi_div_two, abs_one, mul_one]
    · rintro _ ⟨t, rfl⟩
      change
        |angularVelocityInRadiansPerSecond
            (setup.angularVelocityAtSeconds t)| ≤
          Real.pi
      rw [hSpeed]
      exact
        (mul_le_mul_of_nonneg_left (Real.abs_sin_le_one _) Real.pi_nonneg).trans_eq
          (mul_one Real.pi)
  · have pi_gt_sqrtTwoAddSeries (n : ℕ) :
        2 ^ (n + 1) * √(2 - Real.sqrtTwoAddSeries 0 n) < Real.pi := by
      have h :
          √(2 - Real.sqrtTwoAddSeries 0 n) / 2 * 2 ^ (n + 2) <
            Real.pi := by
        rw [← lt_div_iff₀, ← Real.sin_pi_over_two_pow_succ]
        focus
          apply Real.sin_lt
          apply div_pos Real.pi_pos
        all_goals
          apply pow_pos
          norm_num
      refine lt_of_le_of_lt (le_of_eq ?_) h
      rw [pow_succ' _ (n + 1), ← mul_assoc, div_mul_cancel₀, mul_comm]
      simp
    have pi_lower_bound_start (n : ℕ) {a : ℝ}
        (h :
          Real.sqrtTwoAddSeries ((0 : ℕ) / (1 : ℕ)) n ≤
            (2 : ℝ) - (a / (2 : ℝ) ^ (n + 1)) ^ 2) :
        a < Real.pi := by
      refine lt_of_le_of_lt ?_ (pi_gt_sqrtTwoAddSeries n)
      rw [mul_comm]
      refine
        (div_le_iff₀ (pow_pos (by simp) _)).mp
          (Real.le_sqrt_of_sq_le ?_)
      rwa [le_sub_comm, show (0 : ℝ) = (0 : ℕ) / (1 : ℕ) by
        rw [Nat.cast_zero, zero_div]]
    have sqrtTwoAddSeries_step_up
        (c d : ℕ) {a b n : ℕ} {z : ℝ}
        (hz : Real.sqrtTwoAddSeries (c / d) n ≤ z)
        (hb : 0 < b) (hd : 0 < d)
        (h : (2 * b + a) * d ^ 2 ≤ c ^ 2 * b) :
        Real.sqrtTwoAddSeries (a / b) (n + 1) ≤ z := by
      refine le_trans ?_ hz
      rw [Real.sqrtTwoAddSeries_succ]
      apply Real.sqrtTwoAddSeries_monotone_left
      have hb' : 0 < (b : ℝ) := Nat.cast_pos.2 hb
      have hd' : 0 < (d : ℝ) := Nat.cast_pos.2 hd
      rw [Real.sqrt_le_left (div_nonneg c.cast_nonneg d.cast_nonneg),
        div_pow, add_div_eq_mul_add_div _ _ (ne_of_gt hb'),
        div_le_div_iff₀ hb' (pow_pos hd' _)]
      exact_mod_cast h
    have hPiLower : (627 / 200 : ℝ) < Real.pi := by
      apply pi_lower_bound_start 3
      refine
        sqrtTwoAddSeries_step_up 338 239 ?_
          (by norm_num) (by norm_num) (by norm_num)
      refine
        sqrtTwoAddSeries_step_up 704 381 ?_
          (by norm_num) (by norm_num) (by norm_num)
      refine
        sqrtTwoAddSeries_step_up 1940 989 ?_
          (by norm_num) (by norm_num) (by norm_num)
      simp [Real.sqrtTwoAddSeries]
      norm_num
    have pi_lt_sqrtTwoAddSeries (n : ℕ) :
        Real.pi <
          2 ^ (n + 1) * √(2 - Real.sqrtTwoAddSeries 0 n) + 1 / 4 ^ n := by
      have h :
          Real.pi <
            (√(2 - Real.sqrtTwoAddSeries 0 n) / 2 +
                1 / (2 ^ n) ^ 3 / 4) *
              (2 : ℝ) ^ (n + 2) := by
        rw [← div_lt_iff₀ (by simp), ← Real.sin_pi_over_two_pow_succ,
          ← sub_lt_iff_lt_add']
        calc
          Real.pi / 2 ^ (n + 2) -
                Real.sin (Real.pi / 2 ^ (n + 2)) <
              (Real.pi / 2 ^ (n + 2)) ^ 3 / 4 :=
            sub_lt_comm.1 <| Real.sin_gt_sub_cube (by positivity) <|
              div_le_one_of_le₀ (by
                calc
                  Real.pi ≤ 4 := Real.pi_le_four
                  _ = 2 ^ (0 + 2) := by norm_num
                  _ ≤ 2 ^ (n + 2) := by
                    gcongr <;> norm_num) (by positivity)
          _ ≤ (4 / 2 ^ (n + 2)) ^ 3 / 4 := by
            gcongr
            exact Real.pi_le_four
          _ = 1 / (2 ^ n) ^ 3 / 4 := by
            simp [add_comm n, pow_add, div_mul_eq_div_div]
            norm_num
      refine lt_of_lt_of_le h (le_of_eq ?_)
      rw [add_mul]
      congr 1
      · ring
      simp only [show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul, div_div]
      rw [one_div, one_div, inv_mul_eq_iff_eq_mul₀, eq_comm,
        mul_inv_eq_iff_eq_mul₀, ← pow_add]
      · ring
      all_goals norm_num
    have pi_upper_bound_start (n : ℕ) {a : ℝ}
        (h :
          (2 : ℝ) -
                ((a - 1 / (4 : ℝ) ^ n) / (2 : ℝ) ^ (n + 1)) ^ 2 ≤
            Real.sqrtTwoAddSeries ((0 : ℕ) / (1 : ℕ)) n)
        (h₂ : (1 : ℝ) / (4 : ℝ) ^ n ≤ a) :
        Real.pi < a := by
      refine lt_of_lt_of_le (pi_lt_sqrtTwoAddSeries n) ?_
      rw [← le_sub_iff_add_le, ← le_div_iff₀', Real.sqrt_le_left,
        sub_le_comm]
      · rwa [Nat.cast_zero, zero_div] at h
      · exact
          div_nonneg (sub_nonneg.2 h₂)
            (pow_nonneg (le_of_lt zero_lt_two) _)
      · exact pow_pos zero_lt_two _
    have sqrtTwoAddSeries_step_down
        (a b : ℕ) {c d n : ℕ} {z : ℝ}
        (hz : z ≤ Real.sqrtTwoAddSeries (a / b) n)
        (hb : 0 < b) (hd : 0 < d)
        (h : a ^ 2 * d ≤ (2 * d + c) * b ^ 2) :
        z ≤ Real.sqrtTwoAddSeries (c / d) (n + 1) := by
      apply le_trans hz
      rw [Real.sqrtTwoAddSeries_succ]
      apply Real.sqrtTwoAddSeries_monotone_left
      apply Real.le_sqrt_of_sq_le
      have hb' : 0 < (b : ℝ) := Nat.cast_pos.2 hb
      have hd' : 0 < (d : ℝ) := Nat.cast_pos.2 hd
      rw [div_pow, add_div_eq_mul_add_div _ _ (ne_of_gt hd'),
        div_le_div_iff₀ (pow_pos hb' _) hd']
      exact_mod_cast h
    have hPiUpper : Real.pi < (629 / 200 : ℝ) := by
      apply pi_upper_bound_start 4
      · refine
          sqrtTwoAddSeries_step_down 4756 3363 ?_
            (by norm_num) (by norm_num) (by norm_num)
        refine
          sqrtTwoAddSeries_step_down 14965 8099 ?_
            (by norm_num) (by norm_num) (by norm_num)
        refine
          sqrtTwoAddSeries_step_down 21183 10799 ?_
            (by norm_num) (by norm_num) (by norm_num)
        refine
          sqrtTwoAddSeries_step_down 49188 24713 ?_
            (by norm_num) (by norm_num) (by norm_num)
        simp [Real.sqrtTwoAddSeries]
        norm_num
      · norm_num
    change |Real.pi - 314 / 100| ≤ (1 / 200 : ℝ)
    rw [abs_le]
    constructor <;> linarith

end PhyXMiniProblems.ProblemPhyXMini0278
