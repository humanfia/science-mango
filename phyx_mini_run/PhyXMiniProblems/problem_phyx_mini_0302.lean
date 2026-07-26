import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.Calculus.Deriv.Basic
import Physlib.SpaceAndTime.Space.LengthUnit
import Physlib.SpaceAndTime.Time.TimeUnit
import Physlib.Units.WithDim.Basic

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0302

open Dimension

/-!
# Phase of a sinusoidal string wave from an acceleration--time graph

The stated right-moving wave is

`y(x,t) = y_m sin (k*x - omega*t + phi)`.

The primary figure plots transverse acceleration `a_y` against time for the
point `x = 0`.  The vertical scale is `a_s = 400 m/s^2`, with four equal grid
intervals between zero and either scale line.  At the plotted time origin the
curve is one interval below zero and is decreasing.  Thus the graph supplies
`a_y(0) = -a_s/4 = -100 m/s^2` and a negative time derivative there.

Lengths, wave numbers, angular frequencies, velocities, and accelerations are
represented by unit-independent Physlib quantities.  Real numbers are used
only for coherent unit readouts, time coordinates measured in seconds, graph
slopes, and dimensionless radian representatives of phases.
-/

/-! ## Dimensionful quantities and coherent readouts -/

/-- Velocity has physical dimension length divided by time. -/
def velocityDimension : Dimension := L𝓭 * T𝓭⁻¹

/-- Acceleration has physical dimension length divided by time squared. -/
def accelerationDimension : Dimension := L𝓭 * T𝓭⁻¹ * T𝓭⁻¹

/-- A nonnegative transverse-displacement amplitude. -/
abbrev LengthMagnitude : Type := Dimensionful (WithDim L𝓭 NNReal)

/-- A signed axial position or transverse displacement on the string. -/
abbrev SignedLengthQuantity : Type := Dimensionful (WithDim L𝓭 ℝ)

/-- A nonnegative wave-number magnitude, carrying inverse-length dimension. -/
abbrev WaveNumberMagnitude : Type :=
  Dimensionful (WithDim L𝓭⁻¹ NNReal)

/-- A nonnegative angular-frequency magnitude, carrying inverse-time dimension. -/
abbrev AngularFrequencyMagnitude : Type :=
  Dimensionful (WithDim T𝓭⁻¹ NNReal)

/-- A signed transverse-velocity component. -/
abbrev SignedVelocityQuantity : Type :=
  Dimensionful (WithDim velocityDimension ℝ)

/-- A nonnegative transverse-acceleration magnitude. -/
abbrev AccelerationMagnitude : Type :=
  Dimensionful (WithDim accelerationDimension NNReal)

/-- A signed transverse-acceleration component. -/
abbrev SignedAccelerationQuantity : Type :=
  Dimensionful (WithDim accelerationDimension ℝ)

/-- Read a nonnegative length in a selected length unit. -/
def lengthMagnitudeReadout
    (unit : LengthUnit) (length : LengthMagnitude) : ℝ :=
  ((length {UnitChoices.SI with length := unit}).val : ℝ)

/-- Read a signed length in a selected length unit. -/
def signedLengthReadout
    (unit : LengthUnit) (length : SignedLengthQuantity) : ℝ :=
  (length {UnitChoices.SI with length := unit}).val

/-- Read wave number in inverse units of a selected length unit. -/
def waveNumberReadout
    (unit : LengthUnit) (waveNumber : WaveNumberMagnitude) : ℝ :=
  ((waveNumber {UnitChoices.SI with length := unit}).val : ℝ)

/-- Read angular frequency in inverse units of a selected time unit. -/
def angularFrequencyReadout
    (unit : TimeUnit) (frequency : AngularFrequencyMagnitude) : ℝ :=
  ((frequency {UnitChoices.SI with time := unit}).val : ℝ)

/-- Read a signed velocity in coherent selected length/time units. -/
def signedVelocityReadout
    (lengthUnit : LengthUnit) (timeUnit : TimeUnit)
    (velocity : SignedVelocityQuantity) : ℝ :=
  (velocity {UnitChoices.SI with
    length := lengthUnit, time := timeUnit}).val

/-- Read a nonnegative acceleration in coherent selected units. -/
def accelerationMagnitudeReadout
    (lengthUnit : LengthUnit) (timeUnit : TimeUnit)
    (acceleration : AccelerationMagnitude) : ℝ :=
  ((acceleration {UnitChoices.SI with
    length := lengthUnit, time := timeUnit}).val : ℝ)

/-- Read a signed acceleration in coherent selected units. -/
def signedAccelerationReadout
    (lengthUnit : LengthUnit) (timeUnit : TimeUnit)
    (acceleration : SignedAccelerationQuantity) : ℝ :=
  (acceleration {UnitChoices.SI with
    length := lengthUnit, time := timeUnit}).val

/-- Read a signed position in metres. -/
def lengthInMeters (length : SignedLengthQuantity) : ℝ :=
  signedLengthReadout LengthUnit.meters length

/-- Read wave number in radians per metre. -/
def waveNumberInRadiansPerMeter (waveNumber : WaveNumberMagnitude) : ℝ :=
  waveNumberReadout LengthUnit.meters waveNumber

/-- Read angular frequency in radians per second. -/
def angularFrequencyInRadiansPerSecond
    (frequency : AngularFrequencyMagnitude) : ℝ :=
  angularFrequencyReadout TimeUnit.seconds frequency

/-- Read a nonnegative acceleration in metres per second squared. -/
def accelerationMagnitudeInMetersPerSecondSquared
    (acceleration : AccelerationMagnitude) : ℝ :=
  accelerationMagnitudeReadout
    LengthUnit.meters TimeUnit.seconds acceleration

/-- Read a signed acceleration in metres per second squared. -/
def accelerationInMetersPerSecondSquared
    (acceleration : SignedAccelerationQuantity) : ℝ :=
  signedAccelerationReadout
    LengthUnit.meters TimeUnit.seconds acceleration

/-! ## Figure roles and independent wave data -/

/-- The two coordinate axes shown in the supplied graph. -/
inductive GraphAxis where
  | horizontal
  | vertical
  deriving DecidableEq, Repr

/-- The physical quantity printed on each graph axis. -/
inductive AxisQuantity where
  | time_t
  | transverseAcceleration_ay
  deriving DecidableEq, Repr

/-!
Labels and calibrated rendering data read from the primary image.  The time
axis has no printed unit, whereas the vertical axis explicitly displays
metres per second squared.
-/
structure TransverseAccelerationTimeFigure where
  axisQuantity : GraphAxis → AxisQuantity
  accelerationLengthUnit : LengthUnit
  accelerationTimeUnit : TimeUnit
  horizontalAxisShowsUnit : Bool
  verticalAxisShowsUnit : Bool
  verticalScaleAs : AccelerationMagnitude
  gridIntervalsFromZeroToScale : ℕ
  sinusoidalCurveVisible : Bool
  observationPosition : SignedLengthQuantity
  plottedTimeOriginInSeconds : ℝ

/-!
The physical parameters and observables of the traveling string wave.
Displacement, velocity, and acceleration are independent dimensionful fields
until the governing-law premise below is supplied.  In particular, the phase
is not defined from the requested answer.
-/
structure SinusoidalStringWaveSetup where
  displacementAmplitude : LengthMagnitude
  waveNumber : WaveNumberMagnitude
  angularFrequency : AngularFrequencyMagnitude
  phase : Real.Angle
  displacementAtSeconds :
    SignedLengthQuantity → ℝ → SignedLengthQuantity
  transverseVelocityAtSeconds :
    SignedLengthQuantity → ℝ → SignedVelocityQuantity
  transverseAccelerationAtSeconds :
    SignedLengthQuantity → ℝ → SignedAccelerationQuantity
  maximumTransverseAcceleration : AccelerationMagnitude
  figure : TransverseAccelerationTimeFigure

/-!
Primary-image evidence.  The marked levels are `a_s` and `-a_s`, each four
grid intervals from zero.  The plotted trace meets the time axis one grid
interval below zero and is decreasing at that point.  The existential scalar
is the graph slope in metres per second cubed; only its sign is read from the
figure.

No field specifies the requested phase or an answer label.
-/
structure MatchesTransverseAccelerationGraph
    (setup : SinusoidalStringWaveSetup) : Prop where
  horizontalAxisLabel :
    setup.figure.axisQuantity .horizontal = .time_t
  verticalAxisLabel :
    setup.figure.axisQuantity .vertical = .transverseAcceleration_ay
  horizontalUnitNotPrinted :
    setup.figure.horizontalAxisShowsUnit = false
  verticalUnitPrinted :
    setup.figure.verticalAxisShowsUnit = true
  accelerationUsesMeters :
    setup.figure.accelerationLengthUnit = LengthUnit.meters
  accelerationUsesSeconds :
    setup.figure.accelerationTimeUnit = TimeUnit.seconds
  sinusoidalCurveShown :
    setup.figure.sinusoidalCurveVisible = true
  observationPointIsXZero :
    lengthInMeters setup.figure.observationPosition = 0
  plottedOriginIsTZero :
    setup.figure.plottedTimeOriginInSeconds = 0
  scaleReadout :
    accelerationMagnitudeInMetersPerSecondSquared
        setup.figure.verticalScaleAs = 400
  fourGridIntervalsToScale :
    setup.figure.gridIntervalsFromZeroToScale = 4
  scaleIsAccelerationAmplitude :
    accelerationMagnitudeInMetersPerSecondSquared
        setup.maximumTransverseAcceleration =
      accelerationMagnitudeInMetersPerSecondSquared
        setup.figure.verticalScaleAs
  initialPointOneGridBelowEquilibrium :
    accelerationInMetersPerSecondSquared
        (setup.transverseAccelerationAtSeconds
          setup.figure.observationPosition
          setup.figure.plottedTimeOriginInSeconds) =
      -(accelerationMagnitudeInMetersPerSecondSquared
          setup.figure.verticalScaleAs) / 4
  curveDescendingAtOrigin :
    ∃ slopeMetersPerSecondCubed : ℝ,
      slopeMetersPerSecondCubed < 0 ∧
        HasDerivAt
          (fun timeInSeconds ↦
            accelerationInMetersPerSecondSquared
              (setup.transverseAccelerationAtSeconds
                setup.figure.observationPosition timeInSeconds))
          slopeMetersPerSecondCubed
          setup.figure.plottedTimeOriginInSeconds

/-!
Nondegeneracy and the positive representative requested by the question.
`Real.Angle.toReal` already selects the canonical representative in
`(-pi, pi]`; positivity is a branch convention, not the numerical answer.
-/
structure HasPhysicalWaveParameters
    (setup : SinusoidalStringWaveSetup) : Prop where
  displacementAmplitudePositive :
    0 < lengthMagnitudeReadout LengthUnit.meters
      setup.displacementAmplitude
  waveNumberPositive :
    0 < waveNumberInRadiansPerMeter setup.waveNumber
  angularFrequencyPositive :
    0 < angularFrequencyInRadiansPerSecond setup.angularFrequency
  phaseRepresentativePositive :
    0 < setup.phase.toReal

/-!
The governing laws for the source convention
`y(x,t) = y_m sin (k*x - omega*t + phi)`.

The derivative fields state that transverse velocity and acceleration are the
first and second time derivatives of displacement.  The final two fields give
the physical meaning of maximum transverse acceleration.  None contains the
figure's `1/4` ratio, the requested phase, or an answer choice.
-/
structure SatisfiesSinusoidalTravelingWave
    (setup : SinusoidalStringWaveSetup) : Prop where
  displacementNormalForm :
    ∀ (position : SignedLengthQuantity) (timeInSeconds : ℝ)
        (displacementUnit : LengthUnit),
      signedLengthReadout displacementUnit
          (setup.displacementAtSeconds position timeInSeconds) =
        lengthMagnitudeReadout displacementUnit
            setup.displacementAmplitude *
          Real.sin
            (waveNumberInRadiansPerMeter setup.waveNumber *
                lengthInMeters position -
              angularFrequencyInRadiansPerSecond setup.angularFrequency *
                timeInSeconds +
              setup.phase.toReal)
  transverseVelocityIsTimeDerivative :
    ∀ (position : SignedLengthQuantity) (timeInSeconds : ℝ)
        (displacementUnit : LengthUnit),
      HasDerivAt
        (fun time ↦
          signedLengthReadout displacementUnit
            (setup.displacementAtSeconds position time))
        (signedVelocityReadout displacementUnit TimeUnit.seconds
          (setup.transverseVelocityAtSeconds position timeInSeconds))
        timeInSeconds
  transverseAccelerationIsTimeDerivative :
    ∀ (position : SignedLengthQuantity) (timeInSeconds : ℝ)
        (displacementUnit : LengthUnit),
      HasDerivAt
        (fun time ↦
          signedVelocityReadout displacementUnit TimeUnit.seconds
            (setup.transverseVelocityAtSeconds position time))
        (signedAccelerationReadout displacementUnit TimeUnit.seconds
          (setup.transverseAccelerationAtSeconds position timeInSeconds))
        timeInSeconds
  maximumAccelerationBounds :
    ∀ (position : SignedLengthQuantity) (timeInSeconds : ℝ)
        (displacementUnit : LengthUnit),
      |signedAccelerationReadout displacementUnit TimeUnit.seconds
          (setup.transverseAccelerationAtSeconds position timeInSeconds)| ≤
        accelerationMagnitudeReadout displacementUnit TimeUnit.seconds
          setup.maximumTransverseAcceleration
  maximumAccelerationIsAttained :
    ∀ (position : SignedLengthQuantity) (displacementUnit : LengthUnit),
      ∃ timeInSeconds : ℝ,
        |signedAccelerationReadout displacementUnit TimeUnit.seconds
            (setup.transverseAccelerationAtSeconds position timeInSeconds)| =
          accelerationMagnitudeReadout displacementUnit TimeUnit.seconds
            setup.maximumTransverseAcceleration

/-!
Differentiating the displacement law twice gives the transverse-acceleration
normal form.  This is a derived physical law, not a premise.
-/
lemma transverse_acceleration_normal_form
    (setup : SinusoidalStringWaveSetup)
    (hLaws : SatisfiesSinusoidalTravelingWave setup)
    (position : SignedLengthQuantity) (timeInSeconds : ℝ)
    (displacementUnit : LengthUnit) :
    signedAccelerationReadout displacementUnit TimeUnit.seconds
        (setup.transverseAccelerationAtSeconds position timeInSeconds) =
      -((angularFrequencyInRadiansPerSecond setup.angularFrequency) ^ 2 *
          lengthMagnitudeReadout displacementUnit
            setup.displacementAmplitude) *
        Real.sin
          (waveNumberInRadiansPerMeter setup.waveNumber *
              lengthInMeters position -
            angularFrequencyInRadiansPerSecond setup.angularFrequency *
              timeInSeconds +
            setup.phase.toReal) := by
  have sineAffineDerivative
      (amplitude slope intercept time : ℝ) :
      HasDerivAt
        (fun x => amplitude * Real.sin (slope * x + intercept))
        (amplitude * slope * Real.cos (slope * time + intercept)) time := by
    have sinDerivativeAtZero : HasDerivAt Real.sin 1 0 := by
      rw [hasDerivAt_iff_tendsto]
      simp only [Real.sin_zero, sub_zero, smul_eq_mul, mul_one]
      apply squeeze_zero' (g := fun x : ℝ => x ^ 2)
      · exact
          Filter.Eventually.of_forall fun x =>
            mul_nonneg (inv_nonneg.mpr (norm_nonneg x)) (norm_nonneg _)
      · filter_upwards
          [Metric.closedBall_mem_nhds (0 : ℝ) zero_lt_one] with x hx
        simp only [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] at hx
        by_cases hzero : x = 0
        · simp [hzero]
        · have hpos : 0 < |x| := abs_pos.mpr hzero
          have sinBound := Real.sin_bound hx
          have triangleBound :
              |Real.sin x - x| ≤
                |Real.sin x - (x - x ^ 3 / 6)| + |x ^ 3 / 6| := by
            calc
              |Real.sin x - x| =
                  |(Real.sin x - (x - x ^ 3 / 6)) - x ^ 3 / 6| := by
                    ring_nf
              _ ≤ |Real.sin x - (x - x ^ 3 / 6)| + |x ^ 3 / 6| :=
                abs_sub _ _
          have cubeAbs : |x ^ 3 / 6| = |x| ^ 3 / 6 := by
            rw [abs_div, abs_pow]
            norm_num
          have mainBound : |Real.sin x - x| ≤ |x| ^ 3 := by
            rw [cubeAbs] at triangleBound
            nlinarith
              [abs_nonneg (Real.sin x - (x - x ^ 3 / 6)), abs_nonneg x]
          simp only [Real.norm_eq_abs]
          rw [inv_mul_le_iff₀ hpos]
          calc
            |Real.sin x - x| ≤ |x| ^ 3 := mainBound
            _ = |x| * x ^ 2 := by rw [pow_succ, sq_abs, mul_comm]
      · have squareTendsToZero :
            Filter.Tendsto (fun x : ℝ => x ^ 2) (nhds 0) (nhds (0 ^ 2)) :=
          (continuous_id.pow 2).continuousAt
        norm_num at squareTendsToZero ⊢
        exact squareTendsToZero
    have sinRemainder :
        (fun y : ℝ => Real.sin y - y) =o[nhds 0] (fun y : ℝ => y) := by
      simpa only [Real.sin_zero, sub_zero, smul_eq_mul, mul_one] using
        sinDerivativeAtZero.isLittleO
    have sinBigO :
        (fun y : ℝ => Real.sin y) =O[nhds 0] (fun y : ℝ => y) := by
      have h := sinRemainder.isBigO.add
        (Asymptotics.isBigO_refl (fun y : ℝ => y) (nhds 0))
      exact h.congr_left (fun y => by ring)
    have halfTends :
        Filter.Tendsto (fun y : ℝ => y / 2) (nhds 0) (nhds 0) := by
      have h : ContinuousAt (fun y : ℝ => y / 2) 0 :=
        continuousAt_id.div_const (2 : ℝ)
      simpa only [ContinuousAt, zero_div] using h
    have halfBigO :
        (fun y : ℝ => y / 2) =O[nhds 0] (fun y : ℝ => y) := by
      simpa [div_eq_mul_inv, mul_comm] using
        (Asymptotics.isBigO_const_mul_self (2 : ℝ)⁻¹
          (fun y : ℝ => y) (nhds 0))
    have sinHalfBigO :
        (fun y : ℝ => Real.sin (y / 2)) =O[nhds 0] (fun y : ℝ => y) := by
      have h := (sinBigO.comp_tendsto halfTends).trans halfBigO
      simpa [Function.comp_def] using h
    have sinHalfSqBigO :
        (fun y : ℝ => Real.sin (y / 2) ^ 2) =O[nhds 0]
          (fun y : ℝ => y ^ 2) := by
      have h := sinHalfBigO.mul sinHalfBigO
      simpa [pow_two] using h
    have cosSqBigO :
        (fun y : ℝ => Real.cos y - 1) =O[nhds 0]
          (fun y : ℝ => y ^ 2) := by
      have h := sinHalfSqBigO.const_mul_left (-2 : ℝ)
      apply h.congr_left
      intro y
      have hcos := Real.cos_two_mul' (y / 2)
      have hcircle := Real.sin_sq_add_cos_sq (y / 2)
      rw [show 2 * (y / 2) = y by ring] at hcos
      nlinarith
    have cosRemainder :
        (fun y : ℝ => Real.cos y - 1) =o[nhds 0] (fun y : ℝ => y) :=
      cosSqBigO.trans_isLittleO
        (Asymptotics.isLittleO_pow_id (𝕜 := ℝ) (n := 2) (by norm_num))
    have sinAt (base : ℝ) :
        HasDerivAt Real.sin (Real.cos base) base := by
      apply HasDerivAt.of_isLittleO
      have translateTends :
          Filter.Tendsto (fun y : ℝ => y - base) (nhds base) (nhds 0) := by
        have h :=
          (Filter.tendsto_id :
            Filter.Tendsto (fun y : ℝ => y) (nhds base) (nhds base)).sub_const base
        simpa using h
      have hs := sinRemainder.comp_tendsto translateTends
      have hc := cosRemainder.comp_tendsto translateTends
      have combined :=
        (hs.const_mul_left (Real.cos base)).add
          (hc.const_mul_left (Real.sin base))
      apply combined.congr_left
      intro y
      simp only [Function.comp_apply, smul_eq_mul]
      rw [show y = base + (y - base) by ring, Real.sin_add]
      ring_nf
    have affineDerivative (slope intercept time : ℝ) :
        HasDerivAt (fun x : ℝ => slope * x + intercept) slope time := by
      apply HasDerivAt.of_isLittleO
      have h :
          (fun _x : ℝ => (0 : ℝ)) =o[nhds time]
            (fun x : ℝ => x - time) :=
        Asymptotics.isLittleO_zero (fun x : ℝ => x - time) (nhds time)
      apply h.congr_left
      intro x
      simp only [smul_eq_mul]
      ring
    have inner := affineDerivative slope intercept time
    have composed :=
      (sinAt (slope * time + intercept)).isLittleO.comp_tendsto
        inner.continuousAt
    have innerBigO :
        (fun x : ℝ =>
            (slope * x + intercept) - (slope * time + intercept)) =O[nhds time]
          (fun x : ℝ => x - time) := by
      have h := Asymptotics.isBigO_const_mul_self slope
        (fun x : ℝ => x - time) (nhds time)
      apply h.congr_left
      intro x
      ring
    have sineAffine :
        HasDerivAt (fun x : ℝ => Real.sin (slope * x + intercept))
          (slope * Real.cos (slope * time + intercept)) time := by
      apply HasDerivAt.of_isLittleO
      have h := composed.trans_isBigO innerBigO
      apply h.congr_left
      intro x
      simp only [Function.comp_apply, smul_eq_mul]
      ring
    apply HasDerivAt.of_isLittleO
    have h := sineAffine.isLittleO.const_mul_left amplitude
    apply h.congr_left
    intro x
    simp only [smul_eq_mul]
    ring
  let amplitude :=
    lengthMagnitudeReadout displacementUnit setup.displacementAmplitude
  let omega :=
    angularFrequencyInRadiansPerSecond setup.angularFrequency
  let spatialPhase :=
    waveNumberInRadiansPerMeter setup.waveNumber * lengthInMeters position
  have velocityNormalForm (time : ℝ) :
      signedVelocityReadout displacementUnit TimeUnit.seconds
          (setup.transverseVelocityAtSeconds position time) =
        -(omega * amplitude) *
          Real.cos (spatialPhase - omega * time + setup.phase.toReal) := by
    have calculated :=
      sineAffineDerivative amplitude (-omega)
        (spatialPhase + setup.phase.toReal) time
    have functionsAgree :
        (fun time =>
          signedLengthReadout displacementUnit
            (setup.displacementAtSeconds position time)) =ᶠ[nhds time]
          (fun time =>
            amplitude *
              Real.sin
                (-omega * time + (spatialPhase + setup.phase.toReal))) :=
      Filter.Eventually.of_forall fun currentTime => by
        change
          signedLengthReadout displacementUnit
              (setup.displacementAtSeconds position currentTime) =
            amplitude *
              Real.sin
                (-omega * currentTime +
                  (spatialPhase + setup.phase.toReal))
        rw [hLaws.displacementNormalForm position currentTime displacementUnit]
        congr 2
        dsimp [omega, spatialPhase]
        ring
    have calculatedForDisplacement :=
      calculated.congr_of_eventuallyEq functionsAgree
    have supplied :=
      hLaws.transverseVelocityIsTimeDerivative
        position time displacementUnit
    have slopesAgree := calculatedForDisplacement.unique supplied
    rw [show
      -omega * time + (spatialPhase + setup.phase.toReal) =
        spatialPhase - omega * time + setup.phase.toReal by ring] at slopesAgree
    calc
      signedVelocityReadout displacementUnit TimeUnit.seconds
          (setup.transverseVelocityAtSeconds position time) =
          amplitude * -omega *
            Real.cos (spatialPhase - omega * time + setup.phase.toReal) :=
        slopesAgree.symm
      _ = -(omega * amplitude) *
            Real.cos (spatialPhase - omega * time + setup.phase.toReal) := by
        ring
  have calculatedVelocityDerivative :=
    sineAffineDerivative (-(omega * amplitude)) (-omega)
      (spatialPhase + setup.phase.toReal + Real.pi / 2) timeInSeconds
  have velocityFunctionsAgree :
      (fun time =>
        signedVelocityReadout displacementUnit TimeUnit.seconds
          (setup.transverseVelocityAtSeconds position time)) =ᶠ[nhds timeInSeconds]
        (fun time =>
          -(omega * amplitude) *
            Real.sin
              (-omega * time +
                (spatialPhase + setup.phase.toReal + Real.pi / 2))) :=
    Filter.Eventually.of_forall fun currentTime => by
      change
        signedVelocityReadout displacementUnit TimeUnit.seconds
            (setup.transverseVelocityAtSeconds position currentTime) =
          -(omega * amplitude) *
            Real.sin
              (-omega * currentTime +
                (spatialPhase + setup.phase.toReal + Real.pi / 2))
      rw [velocityNormalForm currentTime]
      rw [show
        -omega * currentTime +
            (spatialPhase + setup.phase.toReal + Real.pi / 2) =
          (spatialPhase - omega * currentTime + setup.phase.toReal) +
            Real.pi / 2 by ring]
      rw [Real.sin_add_pi_div_two]
  have calculatedForVelocity :=
    calculatedVelocityDerivative.congr_of_eventuallyEq velocityFunctionsAgree
  have suppliedAcceleration :=
    hLaws.transverseAccelerationIsTimeDerivative
      position timeInSeconds displacementUnit
  have slopesAgree := calculatedForVelocity.unique suppliedAcceleration
  rw [show
    -omega * timeInSeconds +
        (spatialPhase + setup.phase.toReal + Real.pi / 2) =
      (spatialPhase - omega * timeInSeconds + setup.phase.toReal) +
        Real.pi / 2 by ring,
    Real.cos_add_pi_div_two] at slopesAgree
  rw [← slopesAgree]
  ring

/-- The acceleration amplitude of the sinusoidal wave is `omega^2*y_m`. -/
lemma maximum_transverse_acceleration_eq_angularFrequency_sq_mul_amplitude
    (setup : SinusoidalStringWaveSetup)
    (hPhysical : HasPhysicalWaveParameters setup)
    (hLaws : SatisfiesSinusoidalTravelingWave setup)
    (displacementUnit : LengthUnit) :
    accelerationMagnitudeReadout displacementUnit TimeUnit.seconds
        setup.maximumTransverseAcceleration =
      (angularFrequencyInRadiansPerSecond setup.angularFrequency) ^ 2 *
        lengthMagnitudeReadout displacementUnit
          setup.displacementAmplitude := by
  let omega :=
    angularFrequencyInRadiansPerSecond setup.angularFrequency
  let amplitude :=
    lengthMagnitudeReadout displacementUnit setup.displacementAmplitude
  let maximum :=
    accelerationMagnitudeReadout displacementUnit TimeUnit.seconds
      setup.maximumTransverseAcceleration
  let position := setup.figure.observationPosition
  have homegaPositive : 0 < omega := by
    exact hPhysical.angularFrequencyPositive
  have homegaNonzero : omega ≠ 0 := ne_of_gt homegaPositive
  have hamplitudeNonnegative : 0 ≤ amplitude := by
    dsimp [amplitude, lengthMagnitudeReadout]
    positivity
  have hcoefficientNonnegative : 0 ≤ omega ^ 2 * amplitude :=
    mul_nonneg (sq_nonneg omega) hamplitudeNonnegative
  obtain ⟨attainingTime, hattained⟩ :=
    hLaws.maximumAccelerationIsAttained position displacementUnit
  have hattainedNormalForm :=
    transverse_acceleration_normal_form
      setup hLaws position attainingTime displacementUnit
  rw [hattainedNormalForm] at hattained
  have hsineBound :
      |Real.sin
          (waveNumberInRadiansPerMeter setup.waveNumber *
                lengthInMeters position -
              omega * attainingTime +
            setup.phase.toReal)| ≤ 1 :=
    abs_le.mpr
      ⟨Real.neg_one_le_sin _, Real.sin_le_one _⟩
  have hattainedAtMost :
      |-(omega ^ 2 * amplitude) *
          Real.sin
            (waveNumberInRadiansPerMeter setup.waveNumber *
                  lengthInMeters position -
                omega * attainingTime +
              setup.phase.toReal)| ≤
        omega ^ 2 * amplitude := by
    rw [abs_mul, abs_neg, abs_of_nonneg hcoefficientNonnegative]
    simpa only [mul_one] using
      mul_le_mul_of_nonneg_left hsineBound hcoefficientNonnegative
  have hmaximumLe : maximum ≤ omega ^ 2 * amplitude := by
    change
      accelerationMagnitudeReadout displacementUnit TimeUnit.seconds
          setup.maximumTransverseAcceleration ≤
        omega ^ 2 * amplitude
    rw [← hattained]
    exact hattainedAtMost
  let maximizingTime :=
    (waveNumberInRadiansPerMeter setup.waveNumber *
          lengthInMeters position +
        setup.phase.toReal - Real.pi / 2) / omega
  have hphaseAtMax :
      waveNumberInRadiansPerMeter setup.waveNumber *
            lengthInMeters position -
          omega * maximizingTime +
        setup.phase.toReal =
      Real.pi / 2 := by
    dsimp [maximizingTime]
    field_simp [homegaNonzero]
    ring
  have hboundAtMax :=
    hLaws.maximumAccelerationBounds
      position maximizingTime displacementUnit
  have hnormalAtMax :=
    transverse_acceleration_normal_form
      setup hLaws position maximizingTime displacementUnit
  rw [hnormalAtMax, hphaseAtMax, Real.sin_pi_div_two] at hboundAtMax
  have hcoefficientLe : omega ^ 2 * amplitude ≤ maximum := by
    change
      omega ^ 2 * amplitude ≤
        accelerationMagnitudeReadout displacementUnit TimeUnit.seconds
          setup.maximumTransverseAcceleration
    have hcoefficientNonnegative' :
        0 ≤
          (angularFrequencyInRadiansPerSecond setup.angularFrequency) ^ 2 *
            lengthMagnitudeReadout displacementUnit
              setup.displacementAmplitude := by
      simpa [omega, amplitude] using hcoefficientNonnegative
    simpa [omega, amplitude,
      abs_of_nonneg hcoefficientNonnegative'] using hboundAtMax
  exact le_antisymm hmaximumLe hcoefficientLe

/-!
The time derivative of acceleration has the sign of `cos` for the source's
minus-`omega*t` convention.  This derived statement connects the descending
graph to the phase quadrant without introducing a primitive scalar jerk.
-/
lemma transverse_acceleration_has_time_derivative
    (setup : SinusoidalStringWaveSetup)
    (hLaws : SatisfiesSinusoidalTravelingWave setup)
    (position : SignedLengthQuantity) (timeInSeconds : ℝ)
    (displacementUnit : LengthUnit) :
    HasDerivAt
      (fun time ↦
        signedAccelerationReadout displacementUnit TimeUnit.seconds
          (setup.transverseAccelerationAtSeconds position time))
      ((angularFrequencyInRadiansPerSecond setup.angularFrequency) ^ 3 *
          lengthMagnitudeReadout displacementUnit
            setup.displacementAmplitude *
        Real.cos
          (waveNumberInRadiansPerMeter setup.waveNumber *
              lengthInMeters position -
            angularFrequencyInRadiansPerSecond setup.angularFrequency *
              timeInSeconds +
            setup.phase.toReal))
      timeInSeconds := by
  have sineAffineDerivative
      (amplitude slope intercept time : ℝ) :
      HasDerivAt
        (fun x => amplitude * Real.sin (slope * x + intercept))
        (amplitude * slope * Real.cos (slope * time + intercept)) time := by
    have sinDerivativeAtZero : HasDerivAt Real.sin 1 0 := by
      rw [hasDerivAt_iff_tendsto]
      simp only [Real.sin_zero, sub_zero, smul_eq_mul, mul_one]
      apply squeeze_zero' (g := fun x : ℝ => x ^ 2)
      · exact
          Filter.Eventually.of_forall fun x =>
            mul_nonneg (inv_nonneg.mpr (norm_nonneg x)) (norm_nonneg _)
      · filter_upwards
          [Metric.closedBall_mem_nhds (0 : ℝ) zero_lt_one] with x hx
        simp only [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] at hx
        by_cases hzero : x = 0
        · simp [hzero]
        · have hpos : 0 < |x| := abs_pos.mpr hzero
          have sinBound := Real.sin_bound hx
          have triangleBound :
              |Real.sin x - x| ≤
                |Real.sin x - (x - x ^ 3 / 6)| + |x ^ 3 / 6| := by
            calc
              |Real.sin x - x| =
                  |(Real.sin x - (x - x ^ 3 / 6)) - x ^ 3 / 6| := by
                    ring_nf
              _ ≤ |Real.sin x - (x - x ^ 3 / 6)| + |x ^ 3 / 6| :=
                abs_sub _ _
          have cubeAbs : |x ^ 3 / 6| = |x| ^ 3 / 6 := by
            rw [abs_div, abs_pow]
            norm_num
          have mainBound : |Real.sin x - x| ≤ |x| ^ 3 := by
            rw [cubeAbs] at triangleBound
            nlinarith
              [abs_nonneg (Real.sin x - (x - x ^ 3 / 6)), abs_nonneg x]
          simp only [Real.norm_eq_abs]
          rw [inv_mul_le_iff₀ hpos]
          calc
            |Real.sin x - x| ≤ |x| ^ 3 := mainBound
            _ = |x| * x ^ 2 := by rw [pow_succ, sq_abs, mul_comm]
      · have squareTendsToZero :
            Filter.Tendsto (fun x : ℝ => x ^ 2) (nhds 0) (nhds (0 ^ 2)) :=
          (continuous_id.pow 2).continuousAt
        norm_num at squareTendsToZero ⊢
        exact squareTendsToZero
    have sinRemainder :
        (fun y : ℝ => Real.sin y - y) =o[nhds 0] (fun y : ℝ => y) := by
      simpa only [Real.sin_zero, sub_zero, smul_eq_mul, mul_one] using
        sinDerivativeAtZero.isLittleO
    have sinBigO :
        (fun y : ℝ => Real.sin y) =O[nhds 0] (fun y : ℝ => y) := by
      have h := sinRemainder.isBigO.add
        (Asymptotics.isBigO_refl (fun y : ℝ => y) (nhds 0))
      exact h.congr_left (fun y => by ring)
    have halfTends :
        Filter.Tendsto (fun y : ℝ => y / 2) (nhds 0) (nhds 0) := by
      have h : ContinuousAt (fun y : ℝ => y / 2) 0 :=
        continuousAt_id.div_const (2 : ℝ)
      simpa only [ContinuousAt, zero_div] using h
    have halfBigO :
        (fun y : ℝ => y / 2) =O[nhds 0] (fun y : ℝ => y) := by
      simpa [div_eq_mul_inv, mul_comm] using
        (Asymptotics.isBigO_const_mul_self (2 : ℝ)⁻¹
          (fun y : ℝ => y) (nhds 0))
    have sinHalfBigO :
        (fun y : ℝ => Real.sin (y / 2)) =O[nhds 0] (fun y : ℝ => y) := by
      have h := (sinBigO.comp_tendsto halfTends).trans halfBigO
      simpa [Function.comp_def] using h
    have sinHalfSqBigO :
        (fun y : ℝ => Real.sin (y / 2) ^ 2) =O[nhds 0]
          (fun y : ℝ => y ^ 2) := by
      have h := sinHalfBigO.mul sinHalfBigO
      simpa [pow_two] using h
    have cosSqBigO :
        (fun y : ℝ => Real.cos y - 1) =O[nhds 0]
          (fun y : ℝ => y ^ 2) := by
      have h := sinHalfSqBigO.const_mul_left (-2 : ℝ)
      apply h.congr_left
      intro y
      have hcos := Real.cos_two_mul' (y / 2)
      have hcircle := Real.sin_sq_add_cos_sq (y / 2)
      rw [show 2 * (y / 2) = y by ring] at hcos
      nlinarith
    have cosRemainder :
        (fun y : ℝ => Real.cos y - 1) =o[nhds 0] (fun y : ℝ => y) :=
      cosSqBigO.trans_isLittleO
        (Asymptotics.isLittleO_pow_id (𝕜 := ℝ) (n := 2) (by norm_num))
    have sinAt (base : ℝ) :
        HasDerivAt Real.sin (Real.cos base) base := by
      apply HasDerivAt.of_isLittleO
      have translateTends :
          Filter.Tendsto (fun y : ℝ => y - base) (nhds base) (nhds 0) := by
        have h :=
          (Filter.tendsto_id :
            Filter.Tendsto (fun y : ℝ => y) (nhds base) (nhds base)).sub_const base
        simpa using h
      have hs := sinRemainder.comp_tendsto translateTends
      have hc := cosRemainder.comp_tendsto translateTends
      have combined :=
        (hs.const_mul_left (Real.cos base)).add
          (hc.const_mul_left (Real.sin base))
      apply combined.congr_left
      intro y
      simp only [Function.comp_apply, smul_eq_mul]
      rw [show y = base + (y - base) by ring, Real.sin_add]
      ring_nf
    have affineDerivative (slope intercept time : ℝ) :
        HasDerivAt (fun x : ℝ => slope * x + intercept) slope time := by
      apply HasDerivAt.of_isLittleO
      have h :
          (fun _x : ℝ => (0 : ℝ)) =o[nhds time]
            (fun x : ℝ => x - time) :=
        Asymptotics.isLittleO_zero (fun x : ℝ => x - time) (nhds time)
      apply h.congr_left
      intro x
      simp only [smul_eq_mul]
      ring
    have inner := affineDerivative slope intercept time
    have composed :=
      (sinAt (slope * time + intercept)).isLittleO.comp_tendsto
        inner.continuousAt
    have innerBigO :
        (fun x : ℝ =>
            (slope * x + intercept) - (slope * time + intercept)) =O[nhds time]
          (fun x : ℝ => x - time) := by
      have h := Asymptotics.isBigO_const_mul_self slope
        (fun x : ℝ => x - time) (nhds time)
      apply h.congr_left
      intro x
      ring
    have sineAffine :
        HasDerivAt (fun x : ℝ => Real.sin (slope * x + intercept))
          (slope * Real.cos (slope * time + intercept)) time := by
      apply HasDerivAt.of_isLittleO
      have h := composed.trans_isBigO innerBigO
      apply h.congr_left
      intro x
      simp only [Function.comp_apply, smul_eq_mul]
      ring
    apply HasDerivAt.of_isLittleO
    have h := sineAffine.isLittleO.const_mul_left amplitude
    apply h.congr_left
    intro x
    simp only [smul_eq_mul]
    ring
  let amplitude :=
    lengthMagnitudeReadout displacementUnit setup.displacementAmplitude
  let omega :=
    angularFrequencyInRadiansPerSecond setup.angularFrequency
  let spatialPhase :=
    waveNumberInRadiansPerMeter setup.waveNumber * lengthInMeters position
  have calculated :=
    sineAffineDerivative (-(omega ^ 2 * amplitude)) (-omega)
      (spatialPhase + setup.phase.toReal) timeInSeconds
  have functionsAgree :
      (fun time =>
        signedAccelerationReadout displacementUnit TimeUnit.seconds
          (setup.transverseAccelerationAtSeconds position time)) =ᶠ[nhds timeInSeconds]
        (fun time =>
          -(omega ^ 2 * amplitude) *
            Real.sin
              (-omega * time + (spatialPhase + setup.phase.toReal))) :=
    Filter.Eventually.of_forall fun currentTime => by
      change
        signedAccelerationReadout displacementUnit TimeUnit.seconds
            (setup.transverseAccelerationAtSeconds position currentTime) =
          -(omega ^ 2 * amplitude) *
            Real.sin
              (-omega * currentTime +
                (spatialPhase + setup.phase.toReal))
      rw [transverse_acceleration_normal_form
        setup hLaws position currentTime displacementUnit]
      dsimp [omega, amplitude, spatialPhase]
      congr 1
      apply congrArg Real.sin
      ring
  have calculatedForAcceleration :=
    calculated.congr_of_eventuallyEq functionsAgree
  rw [show
    -omega * timeInSeconds + (spatialPhase + setup.phase.toReal) =
      spatialPhase - omega * timeInSeconds + setup.phase.toReal by ring]
    at calculatedForAcceleration
  have hslope :
      -(omega ^ 2 * amplitude) * -omega *
          Real.cos
            (spatialPhase - omega * timeInSeconds + setup.phase.toReal) =
        omega ^ 3 * amplitude *
          Real.cos
            (spatialPhase - omega * timeInSeconds + setup.phase.toReal) := by
    ring
  rw [hslope] at calculatedForAcceleration
  exact calculatedForAcceleration

/-! ## Phase consequences and displayed choices -/

/-- The initial graph ordinate and acceleration amplitude give `sin phi = 1/4`. -/
lemma initial_phase_sine_eq_one_fourth
    (setup : SinusoidalStringWaveSetup)
    (hFigure : MatchesTransverseAccelerationGraph setup)
    (hPhysical : HasPhysicalWaveParameters setup)
    (hLaws : SatisfiesSinusoidalTravelingWave setup) :
    Real.sin setup.phase.toReal = (1 : ℝ) / 4 := by
  let omega :=
    angularFrequencyInRadiansPerSecond setup.angularFrequency
  let amplitude :=
    lengthMagnitudeReadout LengthUnit.meters setup.displacementAmplitude
  let coefficient := omega ^ 2 * amplitude
  have homegaPositive : 0 < omega :=
    hPhysical.angularFrequencyPositive
  have hamplitudePositive : 0 < amplitude :=
    hPhysical.displacementAmplitudePositive
  have hcoefficientPositive : 0 < coefficient :=
    mul_pos (sq_pos_of_pos homegaPositive) hamplitudePositive
  have hnormal :=
    transverse_acceleration_normal_form
      setup hLaws setup.figure.observationPosition
        setup.figure.plottedTimeOriginInSeconds LengthUnit.meters
  rw [hFigure.observationPointIsXZero, hFigure.plottedOriginIsTZero] at hnormal
  simp only [mul_zero, sub_zero, zero_add] at hnormal
  have hmaximum :=
    maximum_transverse_acceleration_eq_angularFrequency_sq_mul_amplitude
      setup hPhysical hLaws LengthUnit.meters
  have hscale :
      accelerationMagnitudeInMetersPerSecondSquared
          setup.figure.verticalScaleAs =
        coefficient := by
    rw [← hFigure.scaleIsAccelerationAmplitude]
    exact hmaximum
  have hinitial := hFigure.initialPointOneGridBelowEquilibrium
  rw [hscale] at hinitial
  rw [hFigure.plottedOriginIsTZero] at hinitial
  change
    signedAccelerationReadout LengthUnit.meters TimeUnit.seconds
        (setup.transverseAccelerationAtSeconds
          setup.figure.observationPosition 0) =
      -coefficient / 4 at hinitial
  have hequation :
      -(coefficient) * Real.sin setup.phase.toReal =
        -coefficient / 4 := by
    rw [← hnormal, hinitial]
  nlinarith

/-!
The graph is decreasing at the origin, so the derived acceleration slope has
negative cosine.  Together with positive sine and the positive canonical
representative, this places the phase in quadrant II.
-/
lemma phase_lies_in_second_quadrant
    (setup : SinusoidalStringWaveSetup)
    (hFigure : MatchesTransverseAccelerationGraph setup)
    (hPhysical : HasPhysicalWaveParameters setup)
    (hLaws : SatisfiesSinusoidalTravelingWave setup) :
    setup.phase.toReal ∈ Set.Ioo (Real.pi / 2) Real.pi := by
  obtain ⟨slope, hslopeNegative, hslopeDerivative⟩ :=
    hFigure.curveDescendingAtOrigin
  rw [hFigure.plottedOriginIsTZero] at hslopeDerivative
  change
    HasDerivAt
      (fun time =>
        signedAccelerationReadout LengthUnit.meters TimeUnit.seconds
          (setup.transverseAccelerationAtSeconds
            setup.figure.observationPosition time))
      slope 0 at hslopeDerivative
  have hderived :=
    transverse_acceleration_has_time_derivative
      setup hLaws setup.figure.observationPosition
        setup.figure.plottedTimeOriginInSeconds LengthUnit.meters
  rw [hFigure.observationPointIsXZero, hFigure.plottedOriginIsTZero] at hderived
  simp only [mul_zero, sub_zero, zero_add] at hderived
  have hslopeEquation := hderived.unique hslopeDerivative
  let omega :=
    angularFrequencyInRadiansPerSecond setup.angularFrequency
  let amplitude :=
    lengthMagnitudeReadout LengthUnit.meters setup.displacementAmplitude
  let coefficient := omega ^ 3 * amplitude
  have hcoefficientPositive : 0 < coefficient := by
    exact mul_pos (pow_pos hPhysical.angularFrequencyPositive 3)
      hPhysical.displacementAmplitudePositive
  have hproductNegative :
      coefficient * Real.cos setup.phase.toReal < 0 := by
    change
      (angularFrequencyInRadiansPerSecond setup.angularFrequency) ^ 3 *
          lengthMagnitudeReadout LengthUnit.meters
            setup.displacementAmplitude *
        Real.cos setup.phase.toReal < 0
    rw [hslopeEquation]
    exact hslopeNegative
  have hcosineNegative : Real.cos setup.phase.toReal < 0 := by
    rcases (mul_neg_iff.mp hproductNegative) with hsign | hsign
    · exact hsign.2
    · nlinarith
  have hphaseAboveHalfPi : Real.pi / 2 < setup.phase.toReal := by
    by_contra hnot
    have hphaseAtMostHalfPi : setup.phase.toReal ≤ Real.pi / 2 :=
      le_of_not_gt hnot
    have hphaseAtLeastNegHalfPi :
        -(Real.pi / 2) ≤ setup.phase.toReal := by
      nlinarith [hPhysical.phaseRepresentativePositive, Real.pi_pos]
    have hcosineNonnegative : 0 ≤ Real.cos setup.phase.toReal :=
      Real.cos_nonneg_of_mem_Icc
        ⟨hphaseAtLeastNegHalfPi, hphaseAtMostHalfPi⟩
    linarith
  have hphaseAtMostPi : setup.phase.toReal ≤ Real.pi :=
    setup.phase.toReal_le_pi
  have hphaseBelowPi : setup.phase.toReal < Real.pi := by
    apply lt_of_le_of_ne hphaseAtMostPi
    intro hphasePi
    have hsine :=
      initial_phase_sine_eq_one_fourth setup hFigure hPhysical hLaws
    rw [hphasePi, Real.sin_pi] at hsine
    norm_num at hsine
  exact ⟨hphaseAboveHalfPi, hphaseBelowPi⟩

/-- On the selected quadrant, the exact phase is `pi - arcsin (1/4)`. -/
lemma phase_eq_pi_sub_arcsin_one_fourth
    (setup : SinusoidalStringWaveSetup)
    (hFigure : MatchesTransverseAccelerationGraph setup)
    (hPhysical : HasPhysicalWaveParameters setup)
    (hLaws : SatisfiesSinusoidalTravelingWave setup) :
    setup.phase.toReal = Real.pi - Real.arcsin ((1 : ℝ) / 4) := by
  have hquadrant :=
    phase_lies_in_second_quadrant setup hFigure hPhysical hLaws
  have hsine :=
    initial_phase_sine_eq_one_fourth setup hFigure hPhysical hLaws
  have harcsin :
      Real.arcsin
          (Real.sin (Real.pi - setup.phase.toReal)) =
        Real.pi - setup.phase.toReal :=
    Real.arcsin_sin
      (by nlinarith [hquadrant.2, Real.pi_pos])
      (by nlinarith [hquadrant.1])
  rw [Real.sin_pi_sub, hsine] at harcsin
  linarith

/-- Labels of the four phase choices printed with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Phase in radians printed beside each answer label. -/
def displayedPhaseRadians : AnswerChoice → ℝ
  | .A => 2
  | .B => 23 / 10
  | .C => 13 / 5
  | .D => 29 / 10

/-- The answer label recorded in the supplied dataset metadata. -/
def recordedDatasetAnswer : AnswerChoice := .D

/-- Agreement with a phase displayed to the nearest tenth of a radian. -/
def RoundsToDisplayedTenth
    (phase : Real.Angle) (choice : AnswerChoice) : Prop :=
  |phase.toReal - displayedPhaseRadians choice| < (1 / 20 : ℝ)

/-- A choice is the unique displayed tenth-radian value matching the phase. -/
def IsUniqueMatchingAnswerChoice
    (phase : Real.Angle) (choice : AnswerChoice) : Prop :=
  RoundsToDisplayedTenth phase choice ∧
    ∀ other : AnswerChoice,
      RoundsToDisplayedTenth phase other → other = choice

/-!
The exact positive phase is

`phi = pi - arcsin (1/4) approximately 2.8889 rad`.

It therefore rounds to `2.9 rad`, uniquely selecting answer D.  The rounded
decimal is deliberately not asserted as an exact phase equality.

This formalizes `thm:physics:phyx_mini_0302:target`.
-/
theorem problem_phyx_mini_0302
    (setup : SinusoidalStringWaveSetup)
    (hFigure : MatchesTransverseAccelerationGraph setup)
    (hPhysical : HasPhysicalWaveParameters setup)
    (hLaws : SatisfiesSinusoidalTravelingWave setup) :
    Real.sin setup.phase.toReal = (1 : ℝ) / 4 ∧
      setup.phase.toReal = Real.pi - Real.arcsin ((1 : ℝ) / 4) ∧
      RoundsToDisplayedTenth setup.phase recordedDatasetAnswer ∧
      IsUniqueMatchingAnswerChoice setup.phase recordedDatasetAnswer := by
  have hsine :=
    initial_phase_sine_eq_one_fourth setup hFigure hPhysical hLaws
  have hphase :=
    phase_eq_pi_sub_arcsin_one_fourth setup hFigure hPhysical hLaws
  have harcsinUpper :
      Real.arcsin ((1 : ℝ) / 4) < (13 : ℝ) / 50 := by
    apply (Real.arcsin_lt_iff_lt_sin (by norm_num) ?_).2
    · have hbound :=
        Real.sin_bound (x := (13 : ℝ) / 50) (by norm_num)
      rw [abs_le] at hbound
      norm_num at hbound ⊢
      linarith
    · constructor <;> nlinarith [Real.one_le_pi_div_two]
  have harcsinLower :
      (1 : ℝ) / 4 < Real.arcsin ((1 : ℝ) / 4) := by
    apply (Real.lt_arcsin_iff_sin_lt ?_ (by norm_num)).2
    · have hbound :=
        Real.sin_bound (x := (1 : ℝ) / 4) (by norm_num)
      rw [abs_le] at hbound
      norm_num at hbound ⊢
      linarith
    · constructor <;> nlinarith [Real.one_le_pi_div_two]
  have hpiLower : (311 : ℝ) / 100 < Real.pi := by
    have hsinUpper :
        Real.sin ((311 : ℝ) / 600) < (1 : ℝ) / 2 := by
      have hbound :=
        Real.sin_bound (x := (311 : ℝ) / 600) (by norm_num)
      rw [abs_le] at hbound
      norm_num at hbound ⊢
      linarith
    by_contra hnot
    have hpiLe : Real.pi ≤ (311 : ℝ) / 100 :=
      le_of_not_gt hnot
    have hmonotone :
        Real.sin (Real.pi / 6) ≤ Real.sin ((311 : ℝ) / 600) := by
      apply Real.sin_le_sin_of_le_of_le_pi_div_two
      · nlinarith [Real.pi_pos]
      · nlinarith [Real.one_le_pi_div_two]
      · nlinarith
    rw [Real.sin_pi_div_six] at hmonotone
    linarith
  have hpiUpper : Real.pi < (16 : ℝ) / 5 := by
    have hcosUpper :
        Real.cos ((4 : ℝ) / 5) < (351 : ℝ) / 500 := by
      have hbound :=
        Real.cos_bound (x := (4 : ℝ) / 5) (by norm_num)
      rw [abs_le] at hbound
      norm_num at hbound ⊢
      linarith
    have hcosNonnegative :
        0 ≤ Real.cos ((4 : ℝ) / 5) :=
      Real.cos_nonneg_of_mem_Icc (by
        constructor <;> nlinarith [Real.one_le_pi_div_two])
    have hsquare :=
      mul_self_lt_mul_self hcosNonnegative hcosUpper
    have hcosNegative : Real.cos ((8 : ℝ) / 5) < 0 := by
      rw [show (8 : ℝ) / 5 = 2 * (4 / 5) by norm_num,
        Real.cos_two_mul]
      norm_num at hsquare ⊢
      nlinarith
    by_contra hnot
    have hpiGe : (16 : ℝ) / 5 ≤ Real.pi :=
      le_of_not_gt hnot
    have hcosNonnegative' :
        0 ≤ Real.cos ((8 : ℝ) / 5) :=
      Real.cos_nonneg_of_mem_Icc (by
        constructor <;> nlinarith [Real.pi_pos])
    linarith
  have hphaseBounds :
      (57 : ℝ) / 20 < setup.phase.toReal ∧
        setup.phase.toReal < (59 : ℝ) / 20 := by
    rw [hphase]
    constructor <;> nlinarith
  have hround :
      RoundsToDisplayedTenth setup.phase recordedDatasetAnswer := by
    change |setup.phase.toReal - 29 / 10| < (1 / 20 : ℝ)
    rw [abs_lt]
    constructor <;> nlinarith [hphaseBounds.1, hphaseBounds.2]
  have hunique :
      IsUniqueMatchingAnswerChoice
        setup.phase recordedDatasetAnswer := by
    refine ⟨hround, ?_⟩
    intro other hother
    cases other with
    | A =>
        change |setup.phase.toReal - 2| < (1 / 20 : ℝ) at hother
        have hupper := (abs_lt.mp hother).2
        norm_num at hupper
        exfalso
        nlinarith [hphaseBounds.1]
    | B =>
        change |setup.phase.toReal - 23 / 10| < (1 / 20 : ℝ) at hother
        have hupper := (abs_lt.mp hother).2
        norm_num at hupper
        exfalso
        nlinarith [hphaseBounds.1]
    | C =>
        change |setup.phase.toReal - 13 / 5| < (1 / 20 : ℝ) at hother
        have hupper := (abs_lt.mp hother).2
        norm_num at hupper
        exfalso
        nlinarith [hphaseBounds.1]
    | D =>
        rfl
  exact ⟨hsine, hphase, hround, hunique⟩

end PhyXMiniProblems.ProblemPhyXMini0302
