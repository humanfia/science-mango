import Mathlib
import Physlib.Units.WithDim.Basic

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0266

open Dimension

/-!
# Least small-angle period of a uniform-rod physical pendulum

The primary figure shows a uniform rod of total length `L`, its center of mass,
and a pivot `O` a distance `x` from the center.  The two center-to-end segments
are both labelled `L/2`.  Thus the question asks for the minimum small-angle
period as the pivot is placed at an admissible point between the center and an
end of the rod.

Physical quantities are represented by Physlib's unit-independent
`Dimensionful (WithDim ...)` types.  Real numbers below are used only for
explicit SI readouts, the figure coordinate `x` measured in metres, and answer
choice values measured in seconds.
-/

/-- The physical dimension of a moment of inertia, mass times length squared. -/
def momentOfInertiaDimension : Dimension := M𝓭 * L𝓭 * L𝓭

/-- The physical dimension of an acceleration, length divided by time squared. -/
def accelerationDimension : Dimension := L𝓭 * T𝓭⁻¹ * T𝓭⁻¹

/-- A nonnegative physical length, independent of the chosen unit system. -/
abbrev LengthQuantity : Type := Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative physical mass, independent of the chosen unit system. -/
abbrev MassQuantity : Type := Dimensionful (WithDim M𝓭 NNReal)

/-- A nonnegative physical acceleration magnitude. -/
abbrev AccelerationQuantity : Type :=
  Dimensionful (WithDim accelerationDimension NNReal)

/-- A nonnegative physical moment of inertia. -/
abbrev MomentOfInertiaQuantity : Type :=
  Dimensionful (WithDim momentOfInertiaDimension NNReal)

/-- A nonnegative physical duration. -/
abbrev TimeQuantity : Type := Dimensionful (WithDim T𝓭 NNReal)

/-- Read a physical length in metres. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  ((length UnitChoices.SI).val : ℝ)

/-- Read a physical mass in kilograms. -/
def massInKilograms (mass : MassQuantity) : ℝ :=
  ((mass UnitChoices.SI).val : ℝ)

/-- Read an acceleration magnitude in metres per second squared. -/
def accelerationInMetersPerSecondSquared
    (acceleration : AccelerationQuantity) : ℝ :=
  ((acceleration UnitChoices.SI).val : ℝ)

/-- Read a moment of inertia in kilogram metre squared. -/
def momentOfInertiaInKilogramMeterSquared
    (moment : MomentOfInertiaQuantity) : ℝ :=
  ((moment UnitChoices.SI).val : ℝ)

/-- Read a physical duration in seconds. -/
def timeInSeconds (time : TimeQuantity) : ℝ :=
  ((time UnitChoices.SI).val : ℝ)

/-- Distinguished points drawn on the rod in the primary figure. -/
inductive RodFigurePoint where
  | topEnd
  | pivotO
  | centerOfMass
  | bottomEnd
  deriving DecidableEq, Repr

/-- Literal symbolic labels printed in the primary figure. -/
inductive RodFigureTextLabel where
  | pivotO
  | upperHalfLengthLOverTwo
  | pivotOffsetX
  | lowerHalfLengthLOverTwo
  deriving DecidableEq, Repr

/-- The labelled geometry visible in the physical-pendulum figure. -/
structure UniformRodPendulumFigure where
  showsPoint : RodFigurePoint → Bool
  showsTextLabel : RodFigureTextLabel → Bool
  pivotLabelAttachment : RodFigurePoint
  upperHalfLabelSegment : RodFigurePoint × RodFigurePoint
  pivotOffsetLabelSegment : RodFigurePoint × RodFigurePoint
  lowerHalfLabelSegment : RodFigurePoint × RodFigurePoint
  upperHalfLength : LengthQuantity
  lowerHalfLength : LengthQuantity

/-!
The physical system and its observables.  Neither the pivot-dependent moment
of inertia nor either period observable is defined by a formula here; the
governing laws imposing those formulas are separate hypotheses below.  The
first input to each function field is the SI readout of the figure coordinate
`x`.  The second input to the amplitude-dependent period is the positive,
dimensionless angular amplitude measured in radians.
-/
structure UniformRodPhysicalPendulum where
  figure : UniformRodPendulumFigure
  rodLength : LengthQuantity
  rodMass : MassQuantity
  localGravity : AccelerationQuantity
  centerMomentOfInertia : MomentOfInertiaQuantity
  pivotMomentOfInertiaAtOffsetMeters : ℝ → MomentOfInertiaQuantity
  limitingSmallAnglePeriodAtOffsetMeters : ℝ → TimeQuantity
  periodAtOffsetAndAmplitudeRadians : ℝ → ℝ → TimeQuantity

/-- An admissible pivot is strictly away from the center of mass and no farther
from it than either end of the rod. -/
def IsAdmissiblePivotOffsetMeters
    (setup : UniformRodPhysicalPendulum) (xMeters : ℝ) : Prop :=
  0 < xMeters ∧ xMeters ≤ lengthInMeters setup.rodLength / 2

/-!
Problem and primary-image readouts.  The `9.80 m/s²` value is the standard
near-Earth textbook gravity calibration implicit in the recorded numerical
answer.  No period or preferred pivot position occurs in these data.
-/
structure MatchesProblemAndFigureData
    (setup : UniformRodPhysicalPendulum) : Prop where
  rodLengthMeters : lengthInMeters setup.rodLength = 1.85
  localGravityMetersPerSecondSquared :
    accelerationInMetersPerSecondSquared setup.localGravity = 9.80
  figureShowsEveryPoint : ∀ point, setup.figure.showsPoint point = true
  figureShowsEveryTextLabel :
    ∀ label, setup.figure.showsTextLabel label = true
  pivotLabelMarksO : setup.figure.pivotLabelAttachment = .pivotO
  upperHalfLabelMarksTopToCenter :
    setup.figure.upperHalfLabelSegment = (.topEnd, .centerOfMass)
  pivotOffsetXMarksOToCenter :
    setup.figure.pivotOffsetLabelSegment = (.pivotO, .centerOfMass)
  lowerHalfLabelMarksCenterToBottom :
    setup.figure.lowerHalfLabelSegment = (.centerOfMass, .bottomEnd)
  upperHalfLengthMeters :
    lengthInMeters setup.figure.upperHalfLength =
      lengthInMeters setup.rodLength / 2
  lowerHalfLengthMeters :
    lengthInMeters setup.figure.lowerHalfLength =
      lengthInMeters setup.rodLength / 2

/-!
The governing physical laws, stated for every admissible figure coordinate
`x`:

* a uniform thin rod has center moment `m L² / 12`;
* the scalar parallel-axis law gives `I_O = I_cm + m x²`;
* the zero-amplitude limiting period is
  `T₀ = 2 π sqrt (I_O / (m g x))`;
* the actual amplitude-dependent period approaches `T₀` from positive angular
  amplitudes, with error `o(amplitude)`.

The final clause is an explicit local asymptotic contract for the textbook
small-angle approximation; it does not equate a finite-amplitude period to its
linearization.  These laws do not assert which offset minimizes the limiting
period or which numerical answer choice is correct.
-/
structure SatisfiesUniformRodPhysicalPendulumLaws
    (setup : UniformRodPhysicalPendulum) : Prop where
  rodLengthPositive : 0 < lengthInMeters setup.rodLength
  rodMassPositive : 0 < massInKilograms setup.rodMass
  localGravityPositive :
    0 < accelerationInMetersPerSecondSquared setup.localGravity
  uniformRodCenterMoment :
    momentOfInertiaInKilogramMeterSquared setup.centerMomentOfInertia =
      massInKilograms setup.rodMass * lengthInMeters setup.rodLength ^ 2 / 12
  parallelAxisLaw : ∀ xMeters,
    IsAdmissiblePivotOffsetMeters setup xMeters →
      momentOfInertiaInKilogramMeterSquared
          (setup.pivotMomentOfInertiaAtOffsetMeters xMeters) =
        momentOfInertiaInKilogramMeterSquared setup.centerMomentOfInertia +
          massInKilograms setup.rodMass * xMeters ^ 2
  limitingSmallAnglePhysicalPendulumPeriodLaw : ∀ xMeters,
    IsAdmissiblePivotOffsetMeters setup xMeters →
      timeInSeconds (setup.limitingSmallAnglePeriodAtOffsetMeters xMeters) =
        2 * Real.pi * Real.sqrt
          (momentOfInertiaInKilogramMeterSquared
              (setup.pivotMomentOfInertiaAtOffsetMeters xMeters) /
            (massInKilograms setup.rodMass *
              accelerationInMetersPerSecondSquared setup.localGravity *
              xMeters))
  finiteAmplitudePeriodApproachesLimit : ∀ xMeters,
    IsAdmissiblePivotOffsetMeters setup xMeters →
      Asymptotics.IsLittleO
        (nhdsWithin (0 : ℝ) (Set.Ioi 0))
        (fun amplitudeRadians =>
          timeInSeconds
              (setup.periodAtOffsetAndAmplitudeRadians
                xMeters amplitudeRadians) -
            timeInSeconds
              (setup.limitingSmallAnglePeriodAtOffsetMeters xMeters))
        (fun amplitudeRadians => amplitudeRadians)

/-- The set of small-angle periods obtainable by choosing a pivot on the
pictured center-to-end half of the rod. -/
def AchievablePeriodSeconds
    (setup : UniformRodPhysicalPendulum) : Set ℝ :=
  {periodSeconds | ∃ xMeters,
    IsAdmissiblePivotOffsetMeters setup xMeters ∧
      periodSeconds =
        timeInSeconds
          (setup.limitingSmallAnglePeriodAtOffsetMeters xMeters)}

/-- The pivot-to-center offset predicted to minimize the period.  Its
minimizing property remains a conclusion of the theorem below. -/
def minimizingPivotOffsetMeters
    (setup : UniformRodPhysicalPendulum) : ℝ :=
  lengthInMeters setup.rodLength / (2 * Real.sqrt 3)

/-- The closed-form candidate for the least period.  The theorem below must
still prove both its attainability and its lower-bound property. -/
def closedFormLeastPeriodSeconds
    (setup : UniformRodPhysicalPendulum) : ℝ :=
  2 * Real.pi * Real.sqrt
    (lengthInMeters setup.rodLength /
      (Real.sqrt 3 *
        accelerationInMetersPerSecondSquared setup.localGravity))

/-- The four period readouts printed as answer choices. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- The duration in seconds printed beside each answer choice. -/
def answerPeriodSeconds : AnswerChoice → ℝ
  | .A => 1.4
  | .B => 1.8
  | .C => 2.1
  | .D => 2.4

/-- The selected choice is strictly closer to the computed period than every
distinct listed choice. -/
def IsUniqueClosestAnswerChoice
    (periodSeconds : ℝ) (choice : AnswerChoice) : Prop :=
  ∀ other, other ≠ choice →
    |periodSeconds - answerPeriodSeconds choice| <
      |periodSeconds - answerPeriodSeconds other|

/-- For the pictured `1.85 m` uniform rod in standard gravity, the least
small-angle period occurs at `x = L / (2 sqrt 3)`, has exact value
`2 π sqrt (L / (sqrt 3 g))`, rounds to `2.1 s`, and hence selects answer C.

This is the declaration corresponding to
`thm:physics:phyx_mini_0266:target`.
-/
theorem leastPeriod_is_answer_C
    (setup : UniformRodPhysicalPendulum)
    (h_data : MatchesProblemAndFigureData setup)
    (h_laws : SatisfiesUniformRodPhysicalPendulumLaws setup) :
    IsAdmissiblePivotOffsetMeters setup
        (minimizingPivotOffsetMeters setup) ∧
      timeInSeconds
          (setup.limitingSmallAnglePeriodAtOffsetMeters
            (minimizingPivotOffsetMeters setup)) =
        closedFormLeastPeriodSeconds setup ∧
      IsLeast (AchievablePeriodSeconds setup)
        (closedFormLeastPeriodSeconds setup) ∧
      |closedFormLeastPeriodSeconds setup - answerPeriodSeconds .C| < 0.05 ∧
      IsUniqueClosestAnswerChoice (closedFormLeastPeriodSeconds setup) .C := by
  have hL : lengthInMeters setup.rodLength = (37 : ℝ) / 20 := by
    rw [h_data.rodLengthMeters]
    norm_num
  have hg :
      accelerationInMetersPerSecondSquared setup.localGravity =
        (49 : ℝ) / 5 := by
    rw [h_data.localGravityMetersPerSecondSquared]
    norm_num
  have hLpos : 0 < lengthInMeters setup.rodLength :=
    h_laws.rodLengthPositive
  have hmpos : 0 < massInKilograms setup.rodMass :=
    h_laws.rodMassPositive
  have hgpos :
      0 < accelerationInMetersPerSecondSquared setup.localGravity :=
    h_laws.localGravityPositive
  have hsqrt3pos : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
  have hsqrt3sq : Real.sqrt 3 ^ 2 = (3 : ℝ) :=
    Real.sq_sqrt (by norm_num)
  have hsqrt3ge : (1 : ℝ) ≤ Real.sqrt 3 := by
    nlinarith [Real.sqrt_nonneg (3 : ℝ)]
  have hx :
      IsAdmissiblePivotOffsetMeters setup
        (minimizingPivotOffsetMeters setup) := by
    constructor
    · exact div_pos hLpos (mul_pos (by norm_num) hsqrt3pos)
    · unfold minimizingPivotOffsetMeters
      apply (div_le_div_iff₀
        (mul_pos (by norm_num) hsqrt3pos) (by norm_num)).2
      nlinarith
  have hperiod :
      timeInSeconds
          (setup.limitingSmallAnglePeriodAtOffsetMeters
            (minimizingPivotOffsetMeters setup)) =
        closedFormLeastPeriodSeconds setup := by
    rw [h_laws.limitingSmallAnglePhysicalPendulumPeriodLaw _ hx,
      h_laws.parallelAxisLaw _ hx, h_laws.uniformRodCenterMoment]
    unfold minimizingPivotOffsetMeters closedFormLeastPeriodSeconds
    congr 2
    field_simp [ne_of_gt hmpos, ne_of_gt hgpos, ne_of_gt hsqrt3pos]
    nlinarith
  have hsqrt3Lower : (5 : ℝ) / 3 < Real.sqrt 3 := by
    nlinarith [Real.sqrt_nonneg (3 : ℝ)]
  have hsqrt3Upper : Real.sqrt 3 < (7 : ℝ) / 4 := by
    nlinarith [Real.sqrt_nonneg (3 : ℝ)]
  have hradicandLower :
      ((41 : ℝ) / 125) ^ 2 <
        lengthInMeters setup.rodLength /
          (Real.sqrt 3 *
            accelerationInMetersPerSecondSquared setup.localGravity) := by
    rw [hL, hg]
    apply (lt_div_iff₀
      (mul_pos hsqrt3pos (by norm_num : (0 : ℝ) < 49 / 5))).2
    nlinarith
  have hradicandUpper :
      lengthInMeters setup.rodLength /
          (Real.sqrt 3 *
            accelerationInMetersPerSecondSquared setup.localGravity) <
        ((17 : ℝ) / 50) ^ 2 := by
    rw [hL, hg]
    apply (div_lt_iff₀
      (mul_pos hsqrt3pos (by norm_num : (0 : ℝ) < 49 / 5))).2
    nlinarith
  have hsqrtRadicandLower :
      (41 : ℝ) / 125 <
        Real.sqrt
          (lengthInMeters setup.rodLength /
            (Real.sqrt 3 *
              accelerationInMetersPerSecondSquared setup.localGravity)) :=
    (Real.lt_sqrt (by norm_num)).2 hradicandLower
  have hsqrtRadicandUpper :
      Real.sqrt
          (lengthInMeters setup.rodLength /
            (Real.sqrt 3 *
              accelerationInMetersPerSecondSquared setup.localGravity)) <
        (17 : ℝ) / 50 :=
    (Real.sqrt_lt' (by norm_num)).2 hradicandUpper
  have hsqrtRadicandPos :
      0 <
        Real.sqrt
          (lengthInMeters setup.rodLength /
            (Real.sqrt 3 *
              accelerationInMetersPerSecondSquared setup.localGravity)) := by
    linarith
  have hproductLower :
      (3.14 : ℝ) * ((41 : ℝ) / 125) <
        Real.pi *
          Real.sqrt
            (lengthInMeters setup.rodLength /
              (Real.sqrt 3 *
                accelerationInMetersPerSecondSquared setup.localGravity)) := by
    calc
      (3.14 : ℝ) * ((41 : ℝ) / 125) <
          Real.pi * ((41 : ℝ) / 125) :=
        mul_lt_mul_of_pos_right Real.pi_gt_d2 (by norm_num)
      _ < Real.pi *
          Real.sqrt
            (lengthInMeters setup.rodLength /
              (Real.sqrt 3 *
                accelerationInMetersPerSecondSquared setup.localGravity)) :=
        mul_lt_mul_of_pos_left hsqrtRadicandLower Real.pi_pos
  have hproductUpper :
      Real.pi *
          Real.sqrt
            (lengthInMeters setup.rodLength /
              (Real.sqrt 3 *
                accelerationInMetersPerSecondSquared setup.localGravity)) <
        (3.15 : ℝ) * ((17 : ℝ) / 50) := by
    calc
      Real.pi *
          Real.sqrt
            (lengthInMeters setup.rodLength /
              (Real.sqrt 3 *
                accelerationInMetersPerSecondSquared setup.localGravity)) <
          (3.15 : ℝ) *
            Real.sqrt
              (lengthInMeters setup.rodLength /
                (Real.sqrt 3 *
                  accelerationInMetersPerSecondSquared setup.localGravity)) :=
        mul_lt_mul_of_pos_right Real.pi_lt_d2 hsqrtRadicandPos
      _ < (3.15 : ℝ) * ((17 : ℝ) / 50) :=
        mul_lt_mul_of_pos_left hsqrtRadicandUpper (by norm_num)
  have hclosedLower :
      (41 : ℝ) / 20 < closedFormLeastPeriodSeconds setup := by
    unfold closedFormLeastPeriodSeconds
    nlinarith
  have hclosedUpper :
      closedFormLeastPeriodSeconds setup < (43 : ℝ) / 20 := by
    unfold closedFormLeastPeriodSeconds
    nlinarith
  have hrounding :
      |closedFormLeastPeriodSeconds setup - answerPeriodSeconds .C| <
        0.05 := by
    rw [abs_lt]
    norm_num [answerPeriodSeconds]
    constructor <;> linarith
  refine ⟨hx, hperiod, ?_, hrounding, ?_⟩
  · constructor
    · refine ⟨minimizingPivotOffsetMeters setup, hx, ?_⟩
      exact hperiod.symm
    · rintro periodSeconds ⟨xMeters, hxMeters, rfl⟩
      rw [h_laws.limitingSmallAnglePhysicalPendulumPeriodLaw _ hxMeters,
        h_laws.parallelAxisLaw _ hxMeters,
        h_laws.uniformRodCenterMoment]
      unfold closedFormLeastPeriodSeconds
      apply mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ?_) (by positivity)
      have hxMetersPos : 0 < xMeters := hxMeters.1
      have hcore :
          lengthInMeters setup.rodLength * xMeters ≤
            Real.sqrt 3 *
              (lengthInMeters setup.rodLength ^ 2 / 12 + xMeters ^ 2) := by
        nlinarith [mul_nonneg (Real.sqrt_nonneg (3 : ℝ))
          (sq_nonneg
            (2 * Real.sqrt 3 * xMeters -
              lengthInMeters setup.rodLength))]
      rw [div_le_div_iff₀
        (mul_pos hsqrt3pos hgpos)
        (mul_pos (mul_pos hmpos hgpos) hxMetersPos)]
      calc
        lengthInMeters setup.rodLength *
              (massInKilograms setup.rodMass *
                accelerationInMetersPerSecondSquared setup.localGravity *
                xMeters) =
            (massInKilograms setup.rodMass *
                accelerationInMetersPerSecondSquared setup.localGravity) *
              (lengthInMeters setup.rodLength * xMeters) := by ring
        _ ≤
            (massInKilograms setup.rodMass *
                accelerationInMetersPerSecondSquared setup.localGravity) *
              (Real.sqrt 3 *
                (lengthInMeters setup.rodLength ^ 2 / 12 + xMeters ^ 2)) :=
          mul_le_mul_of_nonneg_left hcore
            (mul_nonneg hmpos.le hgpos.le)
        _ =
            (massInKilograms setup.rodMass *
                  lengthInMeters setup.rodLength ^ 2 / 12 +
                massInKilograms setup.rodMass * xMeters ^ 2) *
              (Real.sqrt 3 *
                accelerationInMetersPerSecondSquared setup.localGravity) := by
          ring
  · intro other hother
    cases other with
    | A =>
        norm_num [answerPeriodSeconds] at hrounding ⊢
        have hdistance :
            (1 : ℝ) / 20 <
              |closedFormLeastPeriodSeconds setup - (7 : ℝ) / 5| := by
          rw [abs_of_pos (by linarith [hclosedLower])]
          linarith [hclosedLower]
        exact hrounding.trans hdistance
    | B =>
        norm_num [answerPeriodSeconds] at hrounding ⊢
        have hdistance :
            (1 : ℝ) / 20 <
              |closedFormLeastPeriodSeconds setup - (9 : ℝ) / 5| := by
          rw [abs_of_pos (by linarith [hclosedLower])]
          linarith [hclosedLower]
        exact hrounding.trans hdistance
    | C =>
        exact (hother rfl).elim
    | D =>
        norm_num [answerPeriodSeconds] at hrounding ⊢
        have hdistance :
            (1 : ℝ) / 20 <
              |closedFormLeastPeriodSeconds setup - (12 : ℝ) / 5| := by
          rw [abs_of_neg (by linarith [hclosedUpper])]
          linarith [hclosedUpper]
        exact hrounding.trans hdistance

end PhyXMiniProblems.ProblemPhyXMini0266
