import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Physlib.Units.WithDim.Basic

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0229

open Dimension

/-!
# Small-angle period of an equal-mass rod--ball pendulum

A uniform slender rod of mass `M` and length `L` is pivoted at its upper end.
A small ball, also of mass `M`, is treated as a point mass attached at the
lower end.  The primary figure puts the lower end at `y = 0`, marks a generic
rod point `P` at height `y`, and labels the pivot-to-lower-end distance by `L`.

The displayed value `2.68 s` is the zero-amplitude (linearized small-angle)
period, not a global exact period for arbitrary amplitudes.  Accordingly the
model below records the exact `-κ sin θ` restoring torque, its derivative and
little-o remainder at the stable equilibrium, and convergence of nonlinear
periods to the linearized period as the peak angle tends to zero.

Dimensionful physical quantities use Physlib.  Real numbers occur only as
coherent SI readouts, a signed angle in radians, an angular-frequency readout,
and displayed numerical values.
-/

/-! ## Dimensionful quantities and coherent SI readouts -/

/-- A nonnegative physical mass. -/
abbrev MassQuantity : Type := Dimensionful (WithDim M𝓭 NNReal)

/-- A nonnegative physical length. -/
abbrev LengthQuantity : Type := Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative physical duration. -/
abbrev TimeQuantity : Type := Dimensionful (WithDim T𝓭 NNReal)

/-- A nonnegative acceleration magnitude, with dimension `L T⁻²`. -/
abbrev AccelerationMagnitudeQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * T𝓭⁻¹ * T𝓭⁻¹) NNReal)

/-- A moment of inertia about the pivot, with dimension `M L²`. -/
abbrev MomentOfInertiaQuantity : Type :=
  Dimensionful (WithDim (M𝓭 * L𝓭 * L𝓭) NNReal)

/--
The nonnegative coefficient `κ` in the exact restoring torque
`τ(θ) = -κ sin θ`.  Since radians are dimensionless, `κ` has the torque
dimension `M L² T⁻²`.
-/
abbrev RestoringTorqueCoefficientQuantity : Type :=
  Dimensionful
    (WithDim (M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹) NNReal)

/-- A signed torque, with dimension `M L² T⁻²`. -/
abbrev TorqueQuantity : Type :=
  Dimensionful
    (WithDim (M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹) ℝ)

/-- Read a physical mass in kilograms. -/
def massInKilograms (mass : MassQuantity) : ℝ :=
  ((mass UnitChoices.SI).val : ℝ)

/-- Read a physical length in meters. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  ((length UnitChoices.SI).val : ℝ)

/-- Read a physical duration in seconds. -/
def timeInSeconds (time : TimeQuantity) : ℝ :=
  ((time UnitChoices.SI).val : ℝ)

/-- Read an acceleration magnitude in meters per second squared. -/
def accelerationInMetersPerSecondSquared
    (acceleration : AccelerationMagnitudeQuantity) : ℝ :=
  ((acceleration UnitChoices.SI).val : ℝ)

/-- Read a moment of inertia in kilogram meter squared. -/
def momentOfInertiaInKilogramMetersSquared
    (inertia : MomentOfInertiaQuantity) : ℝ :=
  ((inertia UnitChoices.SI).val : ℝ)

/-- Read a restoring-torque coefficient in newton meters. -/
def restoringCoefficientInNewtonMeters
    (coefficient : RestoringTorqueCoefficientQuantity) : ℝ :=
  ((coefficient UnitChoices.SI).val : ℝ)

/-- Read a signed torque in newton meters. -/
def torqueInNewtonMeters (torque : TorqueQuantity) : ℝ :=
  (torque UnitChoices.SI).val

/-! ## Physical roles and primary-figure labels -/

/-- The two massive components of the compound pendulum. -/
inductive PendulumComponent where
  | uniformRod
  | endBall
  deriving DecidableEq, Repr

/-- Distinguished points shown in the primary figure. -/
inductive FigurePoint where
  | pivot
  | pointP
  | rodLowerEnd
  deriving DecidableEq, Repr

/-- Text or mathematical labels visible in the primary figure. -/
inductive FigureLabel where
  | pivot
  | pointP
  | rodLengthL
  | verticalCoordinateY
  | zeroLevelY
  | ballMassM
  deriving DecidableEq, Repr

/-- The idealized geometry of the extended component. -/
inductive RodGeometry where
  | uniformSlender
  deriving DecidableEq, Repr

/-- The small attached ball's dynamical idealization. -/
inductive EndBallIdealization where
  | pointMassAtRodEnd
  deriving DecidableEq, Repr

/--
Physical quantities and labeled geometry for the rod--ball compound pendulum.

The coordinate `verticalHeightAboveYZero` follows the primary image: the
lower-end horizontal line is `y = 0`, while the marked point `P` has height
`y`.  The separate `distanceBelowPivot` supplies lever arms.  The nonlinear
period function is constrained only locally near zero peak angle by the laws
below; no arbitrary-amplitude small-angle equality is built into this setup.
-/
structure RodAndBallPendulumSetup where
  componentMass : PendulumComponent → MassQuantity
  rodLength : LengthQuantity
  gravitationalAccelerationMagnitude : AccelerationMagnitudeQuantity
  rodGeometry : RodGeometry
  endBallIdealization : EndBallIdealization
  pivotPoint : FigurePoint
  ballAttachmentPoint : FigurePoint
  verticalHeightAboveYZero : FigurePoint → LengthQuantity
  distanceBelowPivot : FigurePoint → LengthQuantity
  printedLabelVisible : FigureLabel → Bool
  rodCenterOfMassDistanceBelowPivot : LengthQuantity
  componentMomentOfInertiaAboutPivot :
    PendulumComponent → MomentOfInertiaQuantity
  totalMomentOfInertiaAboutPivot : MomentOfInertiaQuantity
  gravitationalRestoringCoefficient : RestoringTorqueCoefficientQuantity
  gravitationalRestoringTorque : ℝ → TorqueQuantity
  nonlinearOscillationPeriodAtPeakAngleRadians : ℝ → TimeQuantity
  linearizedAngularFrequencyRadiansPerSecond : ℝ
  linearizedSmallOscillationPeriod : TimeQuantity

/-!
Primary-image geometry and labels.  In particular, the pivot is one rod
length above the `y = 0` line, the ball is attached at the lower end, and `P`
lies strictly inside the rod.  The complementary-coordinate identity records
the image's actual convention: `y` is measured upward from the lower end.
-/
structure MatchesPrimaryPendulumFigure
    (setup : RodAndBallPendulumSetup) : Prop where
  pivotIsTopPoint : setup.pivotPoint = .pivot
  ballIsAttachedAtLowerEnd : setup.ballAttachmentPoint = .rodLowerEnd
  pivotHeightIsRodLength :
    lengthInMeters (setup.verticalHeightAboveYZero .pivot) =
      lengthInMeters setup.rodLength
  lowerEndIsYZero :
    lengthInMeters (setup.verticalHeightAboveYZero .rodLowerEnd) = 0
  pivotDistanceBelowItselfIsZero :
    lengthInMeters (setup.distanceBelowPivot .pivot) = 0
  lowerEndDistanceIsRodLength :
    lengthInMeters (setup.distanceBelowPivot .rodLowerEnd) =
      lengthInMeters setup.rodLength
  pointPIsInsideRod :
    0 < lengthInMeters (setup.verticalHeightAboveYZero .pointP) ∧
      lengthInMeters (setup.verticalHeightAboveYZero .pointP) <
        lengthInMeters setup.rodLength
  pointPCoordinatesAreComplementary :
    lengthInMeters (setup.verticalHeightAboveYZero .pointP) +
        lengthInMeters (setup.distanceBelowPivot .pointP) =
      lengthInMeters setup.rodLength
  pivotLabelVisible : setup.printedLabelVisible .pivot = true
  pointPLabelVisible : setup.printedLabelVisible .pointP = true
  rodLengthLabelVisible : setup.printedLabelVisible .rodLengthL = true
  verticalCoordinateLabelVisible :
    setup.printedLabelVisible .verticalCoordinateY = true
  zeroLevelLabelVisible : setup.printedLabelVisible .zeroLevelY = true
  ballMassLabelVisible : setup.printedLabelVisible .ballMassM = true

/-!
Problem and numerical-evaluation data.  The rod and ball have the same
positive mass, the length is `2.00 m`, and the standard textbook value
`g = 9.8 m/s²` is the environmental readout used to select among the choices.
The slender-rod and point-ball fields state the mechanical idealizations
implicit in the problem's wording.
-/
structure HasRodAndBallPendulumProblemData
    (setup : RodAndBallPendulumSetup) : Prop where
  rodIsUniformAndSlender : setup.rodGeometry = .uniformSlender
  endBallIsPointMassAtRodEnd :
    setup.endBallIdealization = .pointMassAtRodEnd
  rodLengthMeters : lengthInMeters setup.rodLength = 2
  equalComponentMasses :
    massInKilograms (setup.componentMass .uniformRod) =
      massInKilograms (setup.componentMass .endBall)
  commonMassPositive :
    0 < massInKilograms (setup.componentMass .uniformRod)
  gravitationalAccelerationMetersPerSecondSquared :
    accelerationInMetersPerSecondSquared
        setup.gravitationalAccelerationMagnitude = 49 / 5

/-! ## Exact nonlinear and local linearized governing laws -/

/--
Moment-of-inertia, gravitational-restoring, and local oscillation laws for the
compound pendulum.

The first five relations are the rigid-body and point-mass laws.  The exact
signed torque is `-κ sin θ`.  Its derivative and little-o remainder are stated
at `θ = 0`, so replacing `sin θ` by `θ` is explicitly local.  The angular
frequency and period laws concern the resulting linearized oscillator.  The
last field connects that oscillator to the nonlinear pendulum by a genuine
zero-amplitude limit rather than identifying the two periods globally.
-/
structure SatisfiesRodAndBallCompoundPendulumLaws
    (setup : RodAndBallPendulumSetup) : Prop where
  rodCenterOfMassLeverArm :
    lengthInMeters setup.rodCenterOfMassDistanceBelowPivot =
      lengthInMeters setup.rodLength / 2
  uniformRodPivotInertia :
    momentOfInertiaInKilogramMetersSquared
        (setup.componentMomentOfInertiaAboutPivot .uniformRod) =
      massInKilograms (setup.componentMass .uniformRod) *
        (lengthInMeters setup.rodLength) ^ 2 / 3
  pointMassPivotInertia :
    momentOfInertiaInKilogramMetersSquared
        (setup.componentMomentOfInertiaAboutPivot .endBall) =
      massInKilograms (setup.componentMass .endBall) *
        (lengthInMeters (setup.distanceBelowPivot .rodLowerEnd)) ^ 2
  totalInertiaIsComponentSum :
    momentOfInertiaInKilogramMetersSquared
        setup.totalMomentOfInertiaAboutPivot =
      momentOfInertiaInKilogramMetersSquared
          (setup.componentMomentOfInertiaAboutPivot .uniformRod) +
        momentOfInertiaInKilogramMetersSquared
          (setup.componentMomentOfInertiaAboutPivot .endBall)
  gravitationalRestoringCoefficientLaw :
    restoringCoefficientInNewtonMeters
        setup.gravitationalRestoringCoefficient =
      massInKilograms (setup.componentMass .uniformRod) *
          accelerationInMetersPerSecondSquared
            setup.gravitationalAccelerationMagnitude *
          lengthInMeters setup.rodCenterOfMassDistanceBelowPivot +
        massInKilograms (setup.componentMass .endBall) *
          accelerationInMetersPerSecondSquared
            setup.gravitationalAccelerationMagnitude *
          lengthInMeters (setup.distanceBelowPivot .rodLowerEnd)
  exactNonlinearRestoringTorqueLaw :
    ∀ angleRadians : ℝ,
      torqueInNewtonMeters
          (setup.gravitationalRestoringTorque angleRadians) =
        -restoringCoefficientInNewtonMeters
            setup.gravitationalRestoringCoefficient *
          Real.sin angleRadians
  restoringTorqueHasDerivativeAtStableEquilibrium :
    HasDerivAt
      (fun angleRadians : ℝ =>
        torqueInNewtonMeters
          (setup.gravitationalRestoringTorque angleRadians))
      (-restoringCoefficientInNewtonMeters
        setup.gravitationalRestoringCoefficient)
      0
  restoringTorqueNonlinearRemainderIsLittleO :
    Asymptotics.IsLittleO (nhds 0)
      (fun angleRadians : ℝ =>
        torqueInNewtonMeters
            (setup.gravitationalRestoringTorque angleRadians) +
          restoringCoefficientInNewtonMeters
              setup.gravitationalRestoringCoefficient * angleRadians)
      (fun angleRadians : ℝ => angleRadians)
  linearizedAngularFrequencyPositive :
    0 < setup.linearizedAngularFrequencyRadiansPerSecond
  linearizedAngularFrequencySquaredLaw :
    setup.linearizedAngularFrequencyRadiansPerSecond ^ 2 =
      restoringCoefficientInNewtonMeters
          setup.gravitationalRestoringCoefficient /
        momentOfInertiaInKilogramMetersSquared
          setup.totalMomentOfInertiaAboutPivot
  linearizedPeriodFrequencyLaw :
    timeInSeconds setup.linearizedSmallOscillationPeriod =
      2 * Real.pi / setup.linearizedAngularFrequencyRadiansPerSecond
  nonlinearPeriodTendsToLinearizedPeriodAtZeroAmplitude :
    Filter.Tendsto
      (fun peakAngleRadians : ℝ =>
        timeInSeconds
          (setup.nonlinearOscillationPeriodAtPeakAngleRadians
            peakAngleRadians))
      (nhds 0)
      (nhds (timeInSeconds setup.linearizedSmallOscillationPeriod))

/-! ## Displayed answers and formalization target -/

/-- Labels of the four displayed period choices. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- The period in seconds printed beside each answer label. -/
def AnswerChoice.seconds : AnswerChoice → ℝ
  | .A => 568 / 100
  | .B => 468 / 100
  | .C => 368 / 100
  | .D => 268 / 100

/-- The answer label recorded in the supplied dataset. -/
def recordedAnswerChoice : AnswerChoice := .D

/-- Agreement with a displayed value after rounding to two decimal places. -/
def MatchesDisplayedPeriod
    (period : TimeQuantity) (choice : AnswerChoice) : Prop :=
  |timeInSeconds period - choice.seconds| < 1 / 200

/--
The zero-amplitude, linearized period of the equal-mass rod--ball pendulum is
`T₀ = 2π √(8 L / (9 g))`.  With `L = 2.00 m` and `g = 9.8 m/s²`, this rounds
to `2.68 s`, recorded answer D, and D is a closest displayed choice.

The nonlinear finite-amplitude period is not claimed to equal this expression;
the governing laws relate it to `T₀` only by the zero-amplitude limit above.
This formalizes `thm:physics:phyx_mini_0229:target`.
-/
theorem rodAndEqualBallLinearizedPeriod_matches_recordedAnswerD
    (setup : RodAndBallPendulumSetup)
    (h_figure : MatchesPrimaryPendulumFigure setup)
    (h_data : HasRodAndBallPendulumProblemData setup)
    (h_laws : SatisfiesRodAndBallCompoundPendulumLaws setup) :
    timeInSeconds setup.linearizedSmallOscillationPeriod =
        2 * Real.pi *
          Real.sqrt
            (8 * lengthInMeters setup.rodLength /
              (9 * accelerationInMetersPerSecondSquared
                setup.gravitationalAccelerationMagnitude)) ∧
      MatchesDisplayedPeriod
        setup.linearizedSmallOscillationPeriod recordedAnswerChoice ∧
      ∀ choice : AnswerChoice,
        |timeInSeconds setup.linearizedSmallOscillationPeriod -
            recordedAnswerChoice.seconds| ≤
          |timeInSeconds setup.linearizedSmallOscillationPeriod -
            choice.seconds| := by
  have hLowerEnd :
      lengthInMeters (setup.distanceBelowPivot .rodLowerEnd) = 2 :=
    h_figure.lowerEndDistanceIsRodLength.trans h_data.rodLengthMeters
  have hCenter :
      lengthInMeters setup.rodCenterOfMassDistanceBelowPivot = 1 := by
    rw [h_laws.rodCenterOfMassLeverArm, h_data.rodLengthMeters]
    norm_num
  have hBallMass :
      massInKilograms (setup.componentMass .endBall) =
        massInKilograms (setup.componentMass .uniformRod) :=
    h_data.equalComponentMasses.symm
  have hInertia :
      momentOfInertiaInKilogramMetersSquared
          setup.totalMomentOfInertiaAboutPivot =
        16 * massInKilograms (setup.componentMass .uniformRod) / 3 := by
    rw [h_laws.totalInertiaIsComponentSum,
      h_laws.uniformRodPivotInertia, h_laws.pointMassPivotInertia,
      hBallMass, h_data.rodLengthMeters, hLowerEnd]
    ring
  have hRestoringCoefficient :
      restoringCoefficientInNewtonMeters
          setup.gravitationalRestoringCoefficient =
        147 * massInKilograms (setup.componentMass .uniformRod) / 5 := by
    rw [h_laws.gravitationalRestoringCoefficientLaw, hBallMass,
      h_data.gravitationalAccelerationMetersPerSecondSquared,
      hCenter, hLowerEnd]
    ring
  have hAngularFrequencySquare :
      setup.linearizedAngularFrequencyRadiansPerSecond ^ 2 =
        (441 / 80 : ℝ) := by
    rw [h_laws.linearizedAngularFrequencySquaredLaw,
      hRestoringCoefficient, hInertia]
    field_simp [ne_of_gt h_data.commonMassPositive]
    ring
  have hSqrtSquare :
      Real.sqrt (80 / 441 : ℝ) ^ 2 = 80 / 441 :=
    Real.sq_sqrt (by norm_num)
  have hSqrtPos : 0 < Real.sqrt (80 / 441 : ℝ) :=
    Real.sqrt_pos.2 (by norm_num)
  have hFrequencyTimesSqrtSquare :
      (setup.linearizedAngularFrequencyRadiansPerSecond *
          Real.sqrt (80 / 441 : ℝ)) ^ 2 = 1 := by
    rw [mul_pow, hAngularFrequencySquare, hSqrtSquare]
    norm_num
  have hFrequencyTimesSqrt :
      setup.linearizedAngularFrequencyRadiansPerSecond *
          Real.sqrt (80 / 441 : ℝ) = 1 := by
    have hProductPos :
        0 <
          setup.linearizedAngularFrequencyRadiansPerSecond *
            Real.sqrt (80 / 441 : ℝ) :=
      mul_pos h_laws.linearizedAngularFrequencyPositive hSqrtPos
    nlinarith only [hFrequencyTimesSqrtSquare, hProductPos]
  have hFrequencyInv :
      setup.linearizedAngularFrequencyRadiansPerSecond⁻¹ =
        Real.sqrt (80 / 441 : ℝ) := by
    exact inv_eq_of_mul_eq_one_right hFrequencyTimesSqrt
  have hPeriodNumeric :
      timeInSeconds setup.linearizedSmallOscillationPeriod =
        2 * Real.pi * Real.sqrt (80 / 441 : ℝ) := by
    rw [h_laws.linearizedPeriodFrequencyLaw, div_eq_mul_inv, hFrequencyInv]
  have hRadicand :
      8 * lengthInMeters setup.rodLength /
          (9 * accelerationInMetersPerSecondSquared
            setup.gravitationalAccelerationMagnitude) =
        (80 / 441 : ℝ) := by
    rw [h_data.rodLengthMeters,
      h_data.gravitationalAccelerationMetersPerSecondSquared]
    norm_num
  have hPeriodFormula :
      timeInSeconds setup.linearizedSmallOscillationPeriod =
        2 * Real.pi *
          Real.sqrt
            (8 * lengthInMeters setup.rodLength /
              (9 * accelerationInMetersPerSecondSquared
                setup.gravitationalAccelerationMagnitude)) := by
    rw [hRadicand]
    exact hPeriodNumeric

  /-
  The imported trigonometric basics do not include the later convenience
  theorems giving decimal bounds on `Real.pi`.  These local estimates derive
  the two bounds needed below from `Real.sin_bound` and exact half-angle
  identities.
  -/
  have hSinLt : ∀ {x : ℝ}, 0 < x → Real.sin x < x := by
    intro x hx
    rcases lt_or_ge 1 x with hxOne | hxOne
    · exact (Real.sin_le_one x).trans_lt hxOne
    · have hAbs : |x| = x := abs_of_nonneg hx.le
      have hBound :=
        le_of_abs_le
          (Real.sin_bound (show |x| ≤ 1 by simpa [hAbs] using hxOne))
      rw [sub_le_iff_le_add', hAbs] at hBound
      apply hBound.trans_lt
      rw [sub_add, sub_lt_self_iff, sub_pos, div_eq_mul_inv (x ^ 3)]
      refine mul_lt_mul' ?_ (by norm_num) (by norm_num) (pow_pos hx 3)
      apply pow_le_pow_of_le_one hx.le hxOne
      simp
  have hSinGtSubCube :
      ∀ {x : ℝ}, 0 < x → x ≤ 1 → x - x ^ 3 / 4 < Real.sin x := by
    intro x hx hxOne
    have hAbs : |x| = x := abs_of_nonneg hx.le
    have hBound :=
      neg_le_of_abs_le
        (Real.sin_bound (show |x| ≤ 1 by simpa [hAbs] using hxOne))
    rw [le_sub_iff_add_le, hAbs] at hBound
    refine lt_of_lt_of_le ?_ hBound
    have hDifference : x ^ 3 / (4 : ℝ) - x ^ 3 / 6 = x ^ 3 * 12⁻¹ := by
      norm_num [div_eq_mul_inv, ← mul_sub]
    rw [add_comm, sub_add, sub_neg_eq_add, sub_lt_sub_iff_left,
      ← lt_sub_iff_add_lt', hDifference]
    refine mul_lt_mul' ?_ (by norm_num) (by norm_num) (pow_pos hx 3)
    apply pow_le_pow_of_le_one hx.le hxOne
    simp

  have hPiLowerRadical :
      (128 : ℝ) *
          Real.sqrt (2 - Real.sqrtTwoAddSeries 0 6) < Real.pi := by
    have hx : 0 < Real.pi / (2 : ℝ) ^ 8 := by positivity
    have hs := hSinLt hx
    rw [Real.sin_pi_over_two_pow_succ 6] at hs
    norm_num at hs ⊢
    linarith only [hs]
  have hUpper1 : Real.sqrt (2 : ℝ) ≤ (1970 : ℝ) / 1393 := by
    rw [Real.sqrt_le_left (by norm_num)]
    norm_num
  have hUpper2 :
      Real.sqrt (2 + Real.sqrt 2) ≤ (3010 : ℝ) / 1629 := by
    rw [Real.sqrt_le_left (by norm_num)]
    nlinarith only [hUpper1]
  have hUpper3 :
      Real.sqrt (2 + Real.sqrt (2 + Real.sqrt 2)) ≤
        (11689 : ℝ) / 5959 := by
    rw [Real.sqrt_le_left (by norm_num)]
    nlinarith only [hUpper2]
  have hUpper4 :
      Real.sqrt (2 + Real.sqrt (2 + Real.sqrt (2 + Real.sqrt 2))) ≤
        (10127 : ℝ) / 5088 := by
    rw [Real.sqrt_le_left (by norm_num)]
    nlinarith only [hUpper3]
  have hUpper5 :
      Real.sqrt
          (2 + Real.sqrt
            (2 + Real.sqrt (2 + Real.sqrt (2 + Real.sqrt 2)))) ≤
        (33997 : ℝ) / 17019 := by
    rw [Real.sqrt_le_left (by norm_num)]
    nlinarith only [hUpper4]
  have hUpper6 :
      Real.sqrt
          (2 + Real.sqrt
            (2 + Real.sqrt
              (2 + Real.sqrt (2 + Real.sqrt (2 + Real.sqrt 2))))) ≤
        (23235 : ℝ) / 11621 := by
    rw [Real.sqrt_le_left (by norm_num)]
    nlinarith only [hUpper5]
  have hSeriesUpper :
      Real.sqrtTwoAddSeries 0 6 ≤ (23235 : ℝ) / 11621 := by
    norm_num [Real.sqrtTwoAddSeries]
    exact hUpper6
  have hSmallRadicalLower :
      (3.1415 : ℝ) / 128 <
        Real.sqrt (2 - Real.sqrtTwoAddSeries 0 6) := by
    rw [Real.lt_sqrt (by norm_num)]
    nlinarith only [hSeriesUpper]
  have hPiLower : (3.1415 : ℝ) < Real.pi := by
    nlinarith only [hPiLowerRadical, hSmallRadicalLower]

  have hPiUpperRadical :
      Real.pi <
        32 * Real.sqrt (2 - Real.sqrtTwoAddSeries 0 4) + 1 / 256 := by
    have hx : 0 < Real.pi / (2 : ℝ) ^ 6 := by positivity
    have hxOne : Real.pi / (2 : ℝ) ^ 6 ≤ 1 := by
      norm_num
      linarith only [Real.pi_le_four]
    have hs := hSinGtSubCube hx hxOne
    rw [Real.sin_pi_over_two_pow_succ 4] at hs
    have hCube :
        (Real.pi / (2 : ℝ) ^ 6) ^ 3 / 4 ≤
          ((4 : ℝ) / (2 : ℝ) ^ 6) ^ 3 / 4 := by
      gcongr
      exact Real.pi_le_four
    norm_num at hs hCube ⊢
    nlinarith only [hs, hCube]
  have hLower1 : (41 : ℝ) / 29 ≤ Real.sqrt 2 := by
    rw [Real.le_sqrt (by norm_num) (by norm_num)]
    norm_num
  have hLower2 :
      (109 : ℝ) / 59 ≤ Real.sqrt (2 + Real.sqrt 2) := by
    rw [Real.le_sqrt (by norm_num) (by positivity)]
    nlinarith only [hLower1]
  have hLower3 :
      (865 : ℝ) / 441 ≤
        Real.sqrt (2 + Real.sqrt (2 + Real.sqrt 2)) := by
    rw [Real.le_sqrt (by norm_num) (by positivity)]
    nlinarith only [hLower2]
  have hLower4 :
      (412 : ℝ) / 207 ≤
        Real.sqrt (2 + Real.sqrt (2 + Real.sqrt (2 + Real.sqrt 2))) := by
    rw [Real.le_sqrt (by norm_num) (by positivity)]
    nlinarith only [hLower3]
  have hSeriesLower :
      (412 : ℝ) / 207 ≤ Real.sqrtTwoAddSeries 0 4 := by
    norm_num [Real.sqrtTwoAddSeries]
    exact hLower4
  have hSmallRadicalUpper :
      Real.sqrt (2 - Real.sqrtTwoAddSeries 0 4) < (0.0983 : ℝ) := by
    rw [Real.sqrt_lt' (by norm_num)]
    nlinarith only [hSeriesLower]
  have hPiUpper : Real.pi < (3.15 : ℝ) := by
    nlinarith only [hPiUpperRadical, hSmallRadicalUpper]

  have hSqrtLower :
      (0.4259 : ℝ) < Real.sqrt (80 / 441 : ℝ) := by
    rw [Real.lt_sqrt (by norm_num)]
    norm_num
  have hSqrtUpper :
      Real.sqrt (80 / 441 : ℝ) < (0.426 : ℝ) := by
    rw [Real.sqrt_lt' (by norm_num)]
    norm_num
  have hProductLower :
      (3.1415 : ℝ) * 0.4259 <
        Real.pi * Real.sqrt (80 / 441 : ℝ) := by
    calc
      (3.1415 : ℝ) * 0.4259 < Real.pi * 0.4259 :=
        mul_lt_mul_of_pos_right hPiLower (by norm_num)
      _ < Real.pi * Real.sqrt (80 / 441 : ℝ) :=
        mul_lt_mul_of_pos_left hSqrtLower Real.pi_pos
  have hProductUpper :
      Real.pi * Real.sqrt (80 / 441 : ℝ) < (3.15 : ℝ) * 0.426 := by
    calc
      Real.pi * Real.sqrt (80 / 441 : ℝ) <
          3.15 * Real.sqrt (80 / 441 : ℝ) :=
        mul_lt_mul_of_pos_right hPiUpper (Real.sqrt_pos.2 (by norm_num))
      _ < (3.15 : ℝ) * 0.426 :=
        mul_lt_mul_of_pos_left hSqrtUpper (by norm_num)
  have hPeriodLower :
      (2.675 : ℝ) <
        timeInSeconds setup.linearizedSmallOscillationPeriod := by
    rw [hPeriodNumeric]
    nlinarith only [hProductLower]
  have hPeriodUpper :
      timeInSeconds setup.linearizedSmallOscillationPeriod < (2.685 : ℝ) := by
    rw [hPeriodNumeric]
    nlinarith only [hProductUpper]
  have hMatches :
      MatchesDisplayedPeriod
        setup.linearizedSmallOscillationPeriod recordedAnswerChoice := by
    unfold MatchesDisplayedPeriod recordedAnswerChoice AnswerChoice.seconds
    rw [abs_lt]
    constructor <;> norm_num <;>
      linarith only [hPeriodLower, hPeriodUpper]
  have hMatchesNumeric :
      |timeInSeconds setup.linearizedSmallOscillationPeriod - 268 / 100| <
        1 / 200 := by
    simpa [MatchesDisplayedPeriod, recordedAnswerChoice,
      AnswerChoice.seconds] using hMatches
  refine ⟨hPeriodFormula, hMatches, ?_⟩
  intro choice
  cases choice with
  | A =>
      simp only [recordedAnswerChoice, AnswerChoice.seconds]
      have hOtherAbs :
          |timeInSeconds setup.linearizedSmallOscillationPeriod - 568 / 100| =
            568 / 100 -
              timeInSeconds setup.linearizedSmallOscillationPeriod := by
        rw [abs_of_neg (by linarith only [hPeriodUpper])]
        ring
      rw [hOtherAbs]
      linarith only [hMatchesNumeric, hPeriodUpper]
  | B =>
      simp only [recordedAnswerChoice, AnswerChoice.seconds]
      have hOtherAbs :
          |timeInSeconds setup.linearizedSmallOscillationPeriod - 468 / 100| =
            468 / 100 -
              timeInSeconds setup.linearizedSmallOscillationPeriod := by
        rw [abs_of_neg (by linarith only [hPeriodUpper])]
        ring
      rw [hOtherAbs]
      linarith only [hMatchesNumeric, hPeriodUpper]
  | C =>
      simp only [recordedAnswerChoice, AnswerChoice.seconds]
      have hOtherAbs :
          |timeInSeconds setup.linearizedSmallOscillationPeriod - 368 / 100| =
            368 / 100 -
              timeInSeconds setup.linearizedSmallOscillationPeriod := by
        rw [abs_of_neg (by linarith only [hPeriodUpper])]
        ring
      rw [hOtherAbs]
      linarith only [hMatchesNumeric, hPeriodUpper]
  | D =>
      simp only [recordedAnswerChoice, AnswerChoice.seconds]
      exact le_rfl

end PhyXMiniProblems.ProblemPhyXMini0229
