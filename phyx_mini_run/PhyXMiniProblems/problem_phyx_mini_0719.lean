import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Physlib.ClassicalMechanics.HarmonicOscillator.Basic
import Physlib.Units.WithDim.Basic

/-!
# Frequency of an inverted rigid-rod pendulum

A point mass on a massless rigid rod is released from rest at the highest
point of its circular path.  The supplied figure gives the height drop `2 L`
and the measured speed `5.0 m/s` at the lowest point.  Mechanical-energy
conservation therefore determines the previously unknown rod length.  The
pendulum later makes small oscillations about its lowest position.  The
displayed frequency is the prediction of the local linearization of the exact
nonlinear pendulum equation at that equilibrium.

All masses, lengths, speeds, accelerations, and frequencies are represented by
Physlib unit-independent `Dimensionful (WithDim ...)` quantities.  Real
numbers occur only as coherent SI readouts and as displayed answer values.

Assumption/target boundary:

* the image supplies its labels, circular geometry, the two heights, and the
  two speeds;
* the prose supplies the ideal rod, pivot, path, and small-amplitude models;
* the governing interface supplies energy conservation, the exact sine
  restoring law, and the general linearized-oscillator frequency law;
* a separate theorem records the derivative and little-`o` remainder that
  justify the local small-angle linearization;
* the numerical frequency `0.62 Hz` and answer choice `C` occur only in the
  conclusion.
-/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0719

open Dimension
open Filter
open scoped Topology

/-! ## Dimensionful quantities and coherent SI readouts -/

/-- Acceleration has physical dimension length divided by time squared. -/
def accelerationDimension : Dimension := L𝓭 * T𝓭⁻¹ * T𝓭⁻¹

/-- A nonnegative physical mass, independent of the unit used to read it. -/
abbrev MassQuantity : Type := Dimensionful (WithDim M𝓭 NNReal)

/-- A nonnegative physical length, independent of the unit used to read it. -/
abbrev LengthQuantity : Type := Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative physical speed, with dimension length divided by time. -/
abbrev SpeedQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * T𝓭⁻¹) NNReal)

/-- A nonnegative physical acceleration magnitude. -/
abbrev AccelerationQuantity : Type :=
  Dimensionful (WithDim accelerationDimension NNReal)

/-- Cyclic frequency, with physical dimension inverse time. -/
abbrev FrequencyQuantity : Type :=
  Dimensionful (WithDim T𝓭⁻¹ NNReal)

/-- Angular frequency; radians are dimensionless, so its dimension is inverse time. -/
abbrev AngularFrequencyQuantity : Type :=
  Dimensionful (WithDim T𝓭⁻¹ NNReal)

/-- Read a nonnegative dimensionful quantity in coherent SI units. -/
def quantitySIReadout {d : Dimension}
    (quantity : Dimensionful (WithDim d NNReal)) : ℝ :=
  ((quantity UnitChoices.SI).val : ℝ)

/-- Kilogram readout of a physical mass. -/
def massInKilograms (mass : MassQuantity) : ℝ :=
  quantitySIReadout mass

/-- Meter readout of a physical length or height. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  quantitySIReadout length

/-- Meter-per-second readout of a physical speed. -/
def speedInMetersPerSecond (speed : SpeedQuantity) : ℝ :=
  quantitySIReadout speed

/-- Meter-per-second-squared readout of an acceleration magnitude. -/
def accelerationInMetersPerSecondSquared
    (acceleration : AccelerationQuantity) : ℝ :=
  quantitySIReadout acceleration

/-- Hertz readout of a cyclic frequency. -/
def frequencyInHertz (frequency : FrequencyQuantity) : ℝ :=
  quantitySIReadout frequency

/-- Radian-per-second readout of an angular frequency. -/
def angularFrequencyInRadiansPerSecond
    (frequency : AngularFrequencyQuantity) : ℝ :=
  quantitySIReadout frequency

/-! ## Primary-image labels and geometry -/

/-- Distinguished bob positions on the circular path. -/
inductive PathPosition where
  | highest
  | lowest
  deriving DecidableEq, Repr

/-- Text and mathematical labels visible in the primary image. -/
inductive FigureLabel where
  | beforeState
  | afterState
  | pivot
  | rodLengthL
  | initialHeightYi
  | initialSpeedVi
  | finalHeightYf
  | finalSpeedVf
  deriving DecidableEq, Repr

/-- Anchors to which the handwritten labels refer. -/
inductive FigureAnchor where
  | highestPoint
  | lowestPoint
  | centralPivot
  | lowestRadius
  deriving DecidableEq, Repr

/-!
Qualitative evidence read directly from the supplied bitmap.  Numerical
readouts are attached to the dimensionful quantities in
`MatchesPrimaryFigure` and `MatchesProblemData` below.
-/
structure InvertedPendulumFigure where
  showsCircularPath : Bool
  showsCentralPivot : Bool
  showsBobAt : PathPosition → Bool
  showsRodFromPivotToLowestBob : Bool
  showsMotionArrows : Bool
  arrowsTraceHighestToLowest : Bool
  labelShown : FigureLabel → Bool
  labelAnchor : FigureLabel → FigureAnchor

/-! ## Physical apparatus and approximation regimes -/

/-- Idealized model of the body attached to the moving end of the rod. -/
inductive BobModel where
  | pointMassAtRodEnd
  | extendedBody
  deriving DecidableEq, Repr

/-- Mechanical model assigned to the pendulum rod. -/
inductive RodModel where
  | masslessRigid
  | massiveOrFlexible
  deriving DecidableEq, Repr

/-- Dissipation model assigned to the central pivot. -/
inductive PivotModel where
  | frictionless
  | dissipative
  deriving DecidableEq, Repr

/-- Extent of the trajectory allowed by the rod and pivot. -/
inductive PathModel where
  | completeCircle
  | restrictedArc
  deriving DecidableEq, Repr

/-- Approximation regime for the later motion about the bottom of the arc. -/
inductive OscillationRegime where
  | smallAmplitudeAboutLowestPoint
  | finiteAmplitude
  deriving DecidableEq, Repr

/-!
Independent physical quantities and modeling choices for the experiment.
The rod length and both frequencies are unconstrained fields: none is defined
to be the requested numerical answer.
-/
structure InvertedRodPendulumSetup where
  figure : InvertedPendulumFigure
  bobMass : MassQuantity
  rodLength_L : LengthQuantity
  localGravity : AccelerationQuantity
  heightAboveLowest : PathPosition → LengthQuantity
  speedAt : PathPosition → SpeedQuantity
  /-- SI angular acceleration as a function of dimensionless angular displacement. -/
  restoringAngularAccelerationSI : ℝ → ℝ
  /-- Angular-frequency prediction of the model linearized at the bottom equilibrium. -/
  linearizedAngularFrequencyPrediction : AngularFrequencyQuantity
  /-- Cyclic-frequency prediction of the model linearized at the bottom equilibrium. -/
  linearizedFrequencyPrediction : FrequencyQuantity
  releasePosition : PathPosition
  bottomPassPosition : PathPosition
  bobModel : BobModel
  rodModel : RodModel
  pivotModel : PivotModel
  pathModel : PathModel
  laterOscillationRegime : OscillationRegime

/-! ## Figure/data readouts and physical assumptions -/

/-!
The primary-image readout.  It places `Before`, `y_i`, and `v_i` at the
highest point, `After`, `y_f`, and `v_f` at the lowest point, `L` on the
lowest radius, and identifies the central pivot.  These are geometric and
diagrammatic facts, not frequency conclusions.
-/
structure MatchesPrimaryFigure
    (setup : InvertedRodPendulumSetup) : Prop where
  circularPathShown : setup.figure.showsCircularPath = true
  centralPivotShown : setup.figure.showsCentralPivot = true
  highestBobShown : setup.figure.showsBobAt .highest = true
  lowestBobShown : setup.figure.showsBobAt .lowest = true
  lowestRadiusRodShown : setup.figure.showsRodFromPivotToLowestBob = true
  motionArrowsShown : setup.figure.showsMotionArrows = true
  arrowsRunFromHighestToLowest :
    setup.figure.arrowsTraceHighestToLowest = true
  allPrintedLabelsShown : ∀ label, setup.figure.labelShown label = true
  beforeLabelAtHighest :
    setup.figure.labelAnchor .beforeState = .highestPoint
  initialHeightLabelAtHighest :
    setup.figure.labelAnchor .initialHeightYi = .highestPoint
  initialSpeedLabelAtHighest :
    setup.figure.labelAnchor .initialSpeedVi = .highestPoint
  afterLabelAtLowest :
    setup.figure.labelAnchor .afterState = .lowestPoint
  finalHeightLabelAtLowest :
    setup.figure.labelAnchor .finalHeightYf = .lowestPoint
  finalSpeedLabelAtLowest :
    setup.figure.labelAnchor .finalSpeedVf = .lowestPoint
  pivotLabelAtPivot : setup.figure.labelAnchor .pivot = .centralPivot
  lengthLabelOnLowestRadius :
    setup.figure.labelAnchor .rodLengthL = .lowestRadius

/-!
Numerical and qualitative data stated in the prose and written on the image.
The lowest point is the zero of height, the inverted release point is `2 L`
above it, and the measured bottom speed is `5.0 m/s`.  No frequency value or
answer choice is asserted here.
-/
structure MatchesProblemData
    (setup : InvertedRodPendulumSetup) : Prop where
  releasedAtHighestPoint : setup.releasePosition = .highest
  measuredAtLowestPoint : setup.bottomPassPosition = .lowest
  initialHeightIsTwiceRodLength :
    lengthInMeters (setup.heightAboveLowest .highest) =
      2 * lengthInMeters setup.rodLength_L
  initialSpeedIsZero :
    speedInMetersPerSecond (setup.speedAt .highest) = 0
  finalHeightIsZero :
    lengthInMeters (setup.heightAboveLowest .lowest) = 0
  bottomSpeedIsFiveMetersPerSecond :
    speedInMetersPerSecond (setup.speedAt .lowest) = 5
  bobIsPointMassAtRodEnd : setup.bobModel = .pointMassAtRodEnd
  rodIsMasslessAndRigid : setup.rodModel = .masslessRigid
  pivotIsFrictionless : setup.pivotModel = .frictionless
  rodCanTraceCompleteCircle : setup.pathModel = .completeCircle
  laterMotionHasSmallAmplitude :
    setup.laterOscillationRegime = .smallAmplitudeAboutLowestPoint

/-!
The standard near-Earth textbook calibration implicit in the recorded
multiple-choice answer.  The source does not print a value of `g`, so this is
kept separate from the image and prose readouts.
-/
def UsesStandardEarthGravity
    (setup : InvertedRodPendulumSetup) : Prop :=
  accelerationInMetersPerSecondSquared setup.localGravity = 9.8

/-- Positivity and nondegeneracy conditions for the physical branch. -/
structure HasPhysicalParameters
    (setup : InvertedRodPendulumSetup) : Prop where
  bobMassPositive : 0 < massInKilograms setup.bobMass
  rodLengthPositive : 0 < lengthInMeters setup.rodLength_L
  localGravityPositive :
    0 < accelerationInMetersPerSecondSquared setup.localGravity
  angularFrequencyPositive :
    0 < angularFrequencyInRadiansPerSecond
      setup.linearizedAngularFrequencyPrediction
  cyclicFrequencyPositive :
    0 < frequencyInHertz setup.linearizedFrequencyPrediction

/-! ## Governing energy and small-oscillation laws -/

/-!
The small-angle pendulum as a generalized harmonic oscillator.  Its
generalized inertia is `m L²`, while the linearized gravitational restoring
coefficient is `m g L`; their ratio is therefore `g / L`.
-/
def pendulumOscillatorSI
    (setup : InvertedRodPendulumSetup)
    (hPhysical : HasPhysicalParameters setup) :
    ClassicalMechanics.HarmonicOscillator where
  m := massInKilograms setup.bobMass *
    lengthInMeters setup.rodLength_L ^ 2
  k := massInKilograms setup.bobMass *
    accelerationInMetersPerSecondSquared setup.localGravity *
    lengthInMeters setup.rodLength_L
  m_pos := mul_pos hPhysical.bobMassPositive
    (pow_pos hPhysical.rodLengthPositive 2)
  k_pos := mul_pos
    (mul_pos hPhysical.bobMassPositive hPhysical.localGravityPositive)
    hPhysical.rodLengthPositive

/-- The coefficient `g / L` in the equation linearized at the bottom equilibrium. -/
def pendulumLinearCoefficientSI
    (setup : InvertedRodPendulumSetup) : ℝ :=
  accelerationInMetersPerSecondSquared setup.localGravity /
    lengthInMeters setup.rodLength_L

/-!
An explicit local/asymptotic contract for the small-angle approximation.
The exact restoring acceleration vanishes at the bottom, has derivative
`-g / L` there, and differs from its linear part by `o(θ)` as `θ → 0`.
Thus no equality for a finite-amplitude nonlinear oscillation is asserted.
-/
structure HasValidPendulumLinearization
    (setup : InvertedRodPendulumSetup) : Prop where
  bottomIsEquilibrium : setup.restoringAngularAccelerationSI 0 = 0
  restoringAccelerationDerivativeAtBottom :
    HasDerivAt setup.restoringAngularAccelerationSI
      (-pendulumLinearCoefficientSI setup) 0
  nonlinearRemainderIsLittleO :
    Asymptotics.IsLittleO (𝓝 (0 : ℝ))
      (fun θ =>
        setup.restoringAngularAccelerationSI θ -
          setup.restoringAngularAccelerationSI 0 -
          (-pendulumLinearCoefficientSI setup) * θ)
      (fun θ => θ)

/-!
The governing laws used to infer the rod length and then the linearized
frequency prediction.  The first field is conservation of
`m g y + 1/2 m v²` between the two pictured states.  The second is the exact
nonlinear sine restoring law.  The final fields use Physlib's
harmonic-oscillator angular frequency only for the model obtained by local
linearization, and the general conversion `ω = 2πf`.  None substitutes
`5.0 m/s`, assigns a numerical length, or states the requested `0.62 Hz`
conclusion.
-/
structure SatisfiesInvertedPendulumLaws
    (setup : InvertedRodPendulumSetup)
    (hPhysical : HasPhysicalParameters setup) : Prop where
  mechanicalEnergyConserved :
    massInKilograms setup.bobMass *
          accelerationInMetersPerSecondSquared setup.localGravity *
          lengthInMeters (setup.heightAboveLowest .highest) +
        massInKilograms setup.bobMass *
          speedInMetersPerSecond (setup.speedAt .highest) ^ 2 / 2 =
      massInKilograms setup.bobMass *
          accelerationInMetersPerSecondSquared setup.localGravity *
          lengthInMeters (setup.heightAboveLowest .lowest) +
        massInKilograms setup.bobMass *
          speedInMetersPerSecond (setup.speedAt .lowest) ^ 2 / 2
  exactNonlinearRestoringAcceleration : ∀ θ : ℝ,
    setup.restoringAngularAccelerationSI θ =
      -pendulumLinearCoefficientSI setup * Real.sin θ
  linearizedAngularFrequencyLaw :
    HasValidPendulumLinearization setup →
      angularFrequencyInRadiansPerSecond
          setup.linearizedAngularFrequencyPrediction =
        (pendulumOscillatorSI setup hPhysical).ω
  angularToCyclicFrequency :
    angularFrequencyInRadiansPerSecond
        setup.linearizedAngularFrequencyPrediction =
      2 * Real.pi * frequencyInHertz setup.linearizedFrequencyPrediction

/-!
The exact sine law supplies the local derivative/remainder contract required
to pass from the nonlinear pendulum to its bottom-equilibrium linearization.
This is a mathematical consequence of the general governing law, not a
numerical frequency premise.
-/
theorem exactPendulumLaw_hasValidLocalLinearization
    (setup : InvertedRodPendulumSetup)
    (hPhysical : HasPhysicalParameters setup)
    (hLaws : SatisfiesInvertedPendulumLaws setup hPhysical) :
    HasValidPendulumLinearization setup := by
  have hfun : setup.restoringAngularAccelerationSI =
      fun θ => -pendulumLinearCoefficientSI setup * Real.sin θ :=
    funext hLaws.exactNonlinearRestoringAcceleration
  constructor
  · rw [hfun]
    simp
  · rw [hfun]
    simpa using (Real.hasDerivAt_sin 0).const_mul
      (-pendulumLinearCoefficientSI setup)
  · rw [hfun]
    simpa [smul_eq_mul, mul_comm] using
      ((Real.hasDerivAt_sin 0).const_mul
        (-pendulumLinearCoefficientSI setup)).isLittleO

/-! ## Displayed choices and formalization target -/

/-- Labels of the four answer choices in the source. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Frequency in hertz printed beside each source answer choice. -/
def answerFrequencyInHertz : AnswerChoice → ℝ
  | .A => 0.42
  | .B => 0.52
  | .C => 0.62
  | .D => 0.72

/-- A computed frequency rounds to a displayed hundredth of a hertz. -/
def RoundsToDisplayedHundredth
    (computedHertz displayedHertz : ℝ) : Prop :=
  |computedHertz - displayedHertz| < 0.005

/-- A displayed answer is strictly closer than every other listed choice. -/
def IsUniqueClosestAnswerChoice
    (computedHertz : ℝ) (choice : AnswerChoice) : Prop :=
  ∀ other, other ≠ choice →
    |computedHertz - answerFrequencyInHertz choice| <
      |computedHertz - answerFrequencyInHertz other|

/-!
Energy conservation fixes the rod length from the `5.0 m/s` bottom speed.
For that length, standard gravity and the locally linearized model give a
frequency prediction of approximately `0.62 Hz`, uniquely selecting answer C.
The exact nonlinear restoring law and the theorem above make the approximation
local at zero amplitude rather than an exact finite-amplitude assertion.

This declaration corresponds to
`thm:physics:phyx_mini_0719:target`.
-/
theorem invertedRodPendulumFrequency_is_answer_C
    (setup : InvertedRodPendulumSetup)
    (h_figure : MatchesPrimaryFigure setup)
    (h_data : MatchesProblemData setup)
    (h_gravity : UsesStandardEarthGravity setup)
    (h_physical : HasPhysicalParameters setup)
    (h_laws : SatisfiesInvertedPendulumLaws setup h_physical) :
    RoundsToDisplayedHundredth
        (frequencyInHertz setup.linearizedFrequencyPrediction)
        (answerFrequencyInHertz .C) ∧
      IsUniqueClosestAnswerChoice
        (frequencyInHertz setup.linearizedFrequencyPrediction) .C := by
  have h_energy := h_laws.mechanicalEnergyConserved
  change accelerationInMetersPerSecondSquared setup.localGravity = 9.8 at h_gravity
  rw [h_data.initialHeightIsTwiceRodLength,
      h_data.initialSpeedIsZero, h_data.finalHeightIsZero,
      h_data.bottomSpeedIsFiveMetersPerSecond, h_gravity] at h_energy
  have h_L : lengthInMeters setup.rodLength_L = 125 / 196 := by
    nlinarith [h_physical.bobMassPositive]
  have h_valid :=
    exactPendulumLaw_hasValidLocalLinearization setup h_physical h_laws
  have h_ω_model := h_laws.linearizedAngularFrequencyLaw h_valid
  have h_ω_sq :
      angularFrequencyInRadiansPerSecond
          setup.linearizedAngularFrequencyPrediction ^ 2 =
        accelerationInMetersPerSecondSquared setup.localGravity /
          lengthInMeters setup.rodLength_L := by
    rw [h_ω_model, ClassicalMechanics.HarmonicOscillator.ω_sq]
    dsimp [pendulumOscillatorSI]
    field_simp [h_physical.bobMassPositive.ne',
      h_physical.rodLengthPositive.ne']
  rw [h_gravity, h_L] at h_ω_sq
  norm_num at h_ω_sq
  have h_ω : angularFrequencyInRadiansPerSecond
      setup.linearizedAngularFrequencyPrediction = 98 / 25 := by
    nlinarith [h_physical.angularFrequencyPositive]
  have h_conversion := h_laws.angularToCyclicFrequency
  rw [h_ω] at h_conversion
  have h_f : frequencyInHertz setup.linearizedFrequencyPrediction =
      49 / (25 * Real.pi) :=
    (eq_div_iff (mul_ne_zero (by norm_num) Real.pi_ne_zero)).2 (by
      nlinarith [h_conversion])
  have hden_pos : 0 < (25 : ℝ) * Real.pi :=
    mul_pos (by norm_num) Real.pi_pos
  have h_sin_lt {x : ℝ} (hx : 0 < x) : Real.sin x < x := by
    rcases lt_or_ge 1 x with hx' | hx'
    · exact (Real.sin_le_one x).trans_lt hx'
    have h_abs : |x| = x := abs_of_nonneg hx.le
    have hbound := le_of_abs_le (Real.sin_bound (by rwa [h_abs]))
    rw [sub_le_iff_le_add', h_abs] at hbound
    apply hbound.trans_lt
    rw [sub_add, sub_lt_self_iff, sub_pos, div_eq_mul_inv (x ^ 3)]
    refine mul_lt_mul' ?_ (by norm_num) (by norm_num) (pow_pos hx 3)
    apply pow_le_pow_of_le_one hx.le hx'
    simp
  have h_sin_gt_sub_cube {x : ℝ} (hx : 0 < x) (hx' : x ≤ 1) :
      x - x ^ 3 / 4 < Real.sin x := by
    have h_abs : |x| = x := abs_of_nonneg hx.le
    have hbound := neg_le_of_abs_le (Real.sin_bound (by rwa [h_abs]))
    rw [le_sub_iff_add_le, h_abs] at hbound
    refine lt_of_lt_of_le ?_ hbound
    have hdiff : x ^ 3 / (4 : ℝ) - x ^ 3 / 6 = x ^ 3 * 12⁻¹ := by
      ring
    rw [add_comm, sub_add, sub_neg_eq_add, sub_lt_sub_iff_left,
      ← lt_sub_iff_add_lt', hdiff]
    refine mul_lt_mul' ?_ (by norm_num) (by norm_num) (pow_pos hx 3)
    apply pow_le_pow_of_le_one hx.le hx'
    simp
  have h_pi_lower_raw :
      (2 : ℝ) ^ (3 + 1) *
          √(2 - Real.sqrtTwoAddSeries 0 3) < Real.pi := by
    have h : √(2 - Real.sqrtTwoAddSeries 0 3) / 2 *
        (2 : ℝ) ^ (3 + 2) < Real.pi := by
      rw [← lt_div_iff₀ (by positivity),
        ← Real.sin_pi_over_two_pow_succ]
      exact h_sin_lt (by positivity)
    convert h using 1 <;> norm_num <;> ring
  have h_pi_upper_raw : Real.pi <
      (2 : ℝ) ^ (2 + 1) *
          √(2 - Real.sqrtTwoAddSeries 0 2) + 1 / (4 : ℝ) ^ 2 := by
    have h : Real.pi <
        (√(2 - Real.sqrtTwoAddSeries 0 2) / 2 +
          1 / ((2 : ℝ) ^ 2) ^ 3 / 4) * (2 : ℝ) ^ (2 + 2) := by
      rw [← div_lt_iff₀ (by positivity),
        ← Real.sin_pi_over_two_pow_succ, ← sub_lt_iff_lt_add']
      calc
        Real.pi / 2 ^ (2 + 2) - Real.sin (Real.pi / 2 ^ (2 + 2)) <
            (Real.pi / 2 ^ (2 + 2)) ^ 3 / 4 :=
          sub_lt_comm.1 <| h_sin_gt_sub_cube (by positivity)
            (div_le_one_of_le₀ (Real.pi_le_four.trans (by norm_num))
              (by positivity))
        _ ≤ (4 / 2 ^ (2 + 2)) ^ 3 / 4 := by
          gcongr
          exact Real.pi_le_four
        _ = 1 / ((2 : ℝ) ^ 2) ^ 3 / 4 := by norm_num
    convert h using 1 <;> norm_num <;> ring
  norm_num [Real.sqrtTwoAddSeries] at h_pi_lower_raw h_pi_upper_raw
  have hs2_upper : √(2 : ℝ) < 14143 / 10000 := by
    exact (Real.sqrt_lt' (by norm_num)).2 (by norm_num)
  have hs2_lower : (707 / 500 : ℝ) < √2 := by
    exact (Real.lt_sqrt (by norm_num)).2 (by norm_num)
  have hr2_upper : √(2 + √(2 : ℝ)) < 9239 / 5000 := by
    exact (Real.sqrt_lt' (by norm_num)).2 (by nlinarith [hs2_upper])
  have hr2_lower : (18477 / 10000 : ℝ) < √(2 + √2) := by
    exact (Real.lt_sqrt (by norm_num)).2 (by nlinarith [hs2_lower])
  have hr3_upper : √(2 + √(2 + √(2 : ℝ))) < 122599 / 62500 := by
    exact (Real.sqrt_lt' (by norm_num)).2 (by nlinarith [hr2_upper])
  have hchord_lower : (49 / 250 : ℝ) <
      √(2 - √(2 + √(2 + √2))) := by
    exact (Real.lt_sqrt (by norm_num)).2 (by nlinarith [hr3_upper])
  have hchord_upper : √(2 - √(2 + √(2 : ℝ))) < 1249 / 3200 := by
    exact (Real.sqrt_lt' (by norm_num)).2 (by nlinarith [hr2_lower])
  have h_pi_lower : (392 / 125 : ℝ) < Real.pi := by
    nlinarith [h_pi_lower_raw, hchord_lower]
  have h_pi_upper : Real.pi < (637 / 200 : ℝ) := by
    nlinarith [h_pi_upper_raw, hchord_upper]
  have h_f_lower : (123 / 200 : ℝ) <
      frequencyInHertz setup.linearizedFrequencyPrediction := by
    rw [h_f]
    exact (lt_div_iff₀ hden_pos).2 (by nlinarith [h_pi_upper])
  have h_f_upper : frequencyInHertz setup.linearizedFrequencyPrediction <
      (5 / 8 : ℝ) := by
    rw [h_f]
    exact (div_lt_iff₀ hden_pos).2 (by nlinarith [h_pi_lower])
  clear h_figure h_data h_gravity h_physical h_laws h_energy h_L h_valid
    h_ω_model h_ω_sq h_ω h_conversion h_f hden_pos h_sin_lt
    h_sin_gt_sub_cube h_pi_lower_raw h_pi_upper_raw hs2_upper hs2_lower
    hr2_upper hr2_lower hr3_upper hchord_lower hchord_upper h_pi_lower
    h_pi_upper
  have h_round :
      |frequencyInHertz setup.linearizedFrequencyPrediction - 0.62| <
        0.005 := by
    rw [abs_lt]
    constructor <;> nlinarith [h_f_lower, h_f_upper]
  constructor
  · simpa [RoundsToDisplayedHundredth, answerFrequencyInHertz] using h_round
  · intro other h_other
    have h_C :
        |frequencyInHertz setup.linearizedFrequencyPrediction -
          answerFrequencyInHertz .C| < 0.005 := by
      simpa [answerFrequencyInHertz] using h_round
    cases other with
    | A =>
        have h_far : (0.005 : ℝ) <
            |frequencyInHertz setup.linearizedFrequencyPrediction -
              answerFrequencyInHertz .A| := by
          rw [answerFrequencyInHertz, abs_of_pos]
          · nlinarith [h_f_lower]
          · nlinarith [h_f_lower]
        exact h_C.trans h_far
    | B =>
        have h_far : (0.005 : ℝ) <
            |frequencyInHertz setup.linearizedFrequencyPrediction -
              answerFrequencyInHertz .B| := by
          rw [answerFrequencyInHertz, abs_of_pos]
          · nlinarith [h_f_lower]
          · nlinarith [h_f_lower]
        exact h_C.trans h_far
    | C => exact (h_other rfl).elim
    | D =>
        have h_far : (0.005 : ℝ) <
            |frequencyInHertz setup.linearizedFrequencyPrediction -
              answerFrequencyInHertz .D| := by
          rw [answerFrequencyInHertz, abs_of_neg]
          · nlinarith [h_f_upper]
          · nlinarith [h_f_upper]
        exact h_C.trans h_far

end PhyXMiniProblems.ProblemPhyXMini0719
