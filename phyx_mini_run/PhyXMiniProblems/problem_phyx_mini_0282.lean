import Mathlib
import Physlib.ClassicalMechanics.HarmonicOscillator.Solution
import Physlib.Units.WithDim.Basic

/-!
# Reversible physical pendulum with adjustable pivot

The primary figure shows a single rigid pendulum body with fixed pivot `A`,
its center of mass, and an adjustable second pivot `B` in that order along the
body.  The arrow labelled `L` runs from `A` to `B`.  When the body is suspended
from either pivot, its measured period is `1.80 s`.

Physical lengths, times, masses, accelerations, moments of inertia, and
restoring-torque coefficients are represented by Physlib's unit-independent
`Dimensionful (WithDim ...)` quantities.  Real numbers occur only as coherent
SI readouts and as the displayed multiple-choice values.

Assumption/target boundary:

* Figure data specify the labelled points, the `A`--center-of-mass--`B`
  ordering, the two center-of-mass offsets, the pivot separation `L`, and the
  fixed/adjustable roles of the pivots.
* Problem data specify the restored common period `1.80 s`, standard terrestrial
  gravity, the rigid-body small-angle model, and positivity.
* Governing laws specify the parallel-axis relation, gravitational restoring
  coefficient, and the Physlib harmonic-oscillator realization at each pivot.
* The equivalent-simple-pendulum formula for `L`, its numerical proximity to
  `0.804 m`, and selection of answer D are conclusions only.
-/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0282

open Dimension

/-! ## Dimensionful physical quantities and SI readouts -/

/-- A nonnegative physical length, independent of the chosen unit system. -/
abbrev LengthQuantity : Type := Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative physical duration. -/
abbrev TimeQuantity : Type := Dimensionful (WithDim T𝓭 NNReal)

/-- A nonnegative physical mass. -/
abbrev MassQuantity : Type := Dimensionful (WithDim M𝓭 NNReal)

/-- A nonnegative acceleration magnitude, of dimension `L T⁻²`. -/
abbrev AccelerationQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * T𝓭⁻¹ * T𝓭⁻¹) NNReal)

/-- A scalar moment of inertia, of dimension `M L²`. -/
abbrev MomentOfInertiaQuantity : Type :=
  Dimensionful (WithDim (M𝓭 * L𝓭 * L𝓭) NNReal)

/--
The coefficient of angular displacement in a linearized restoring torque.
Radians are dimensionless, so this has dimension `M L² T⁻²`.
-/
abbrev RotationalStiffnessQuantity : Type :=
  Dimensionful
    (WithDim (M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹) NNReal)

/-- Read a physical length in metres. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  ((length UnitChoices.SI).val : ℝ)

/-- Read a physical duration in seconds. -/
def timeInSeconds (time : TimeQuantity) : ℝ :=
  ((time UnitChoices.SI).val : ℝ)

/-- Read a physical mass in kilograms. -/
def massInKilograms (mass : MassQuantity) : ℝ :=
  ((mass UnitChoices.SI).val : ℝ)

/-- Read an acceleration in metres per second squared. -/
def accelerationInMetersPerSecondSquared
    (acceleration : AccelerationQuantity) : ℝ :=
  ((acceleration UnitChoices.SI).val : ℝ)

/-- Read a moment of inertia in kilogram metres squared. -/
def momentOfInertiaInKilogramMetersSquared
    (inertia : MomentOfInertiaQuantity) : ℝ :=
  ((inertia UnitChoices.SI).val : ℝ)

/-- Read a linearized restoring coefficient in newton metres per radian. -/
def rotationalStiffnessInNewtonMeters
    (stiffness : RotationalStiffnessQuantity) : ℝ :=
  ((stiffness UnitChoices.SI).val : ℝ)

/-! ## Physical and primary-figure roles -/

/-- The two alternative suspension points named in the problem. -/
inductive Pivot where
  | A
  | B
  deriving DecidableEq, Repr

/-- Distinguished points drawn on the pendulum body. -/
inductive FigurePoint where
  | pivotA
  | centerOfMass
  | pivotB
  deriving DecidableEq, Repr

/-- Literal text labels visible in the primary image. -/
inductive FigureLabel where
  | A
  | centerOfMass
  | B
  | separationL
  deriving DecidableEq, Repr

/-- Mechanical role assigned to each candidate pivot. -/
inductive PivotMobility where
  | fixed
  | adjustableAlongScale
  deriving DecidableEq, Repr

/-- Relative order of the three marked points along the pendulum body. -/
inductive AxialOrder where
  | A_centerOfMass_B
  | other
  deriving DecidableEq, Repr

/-- The rigid-body approximation used for the pendulum. -/
inductive BodyTreatment where
  | rigid
  | deformable
  deriving DecidableEq, Repr

/-- The oscillation approximation under which the textbook period law holds. -/
inductive OscillationRegime where
  | linearizedSmallAngle
  | finiteAmplitude
  deriving DecidableEq, Repr

/--
Readout of the supplied image.  Its distance fields are genuine physical
lengths; Booleans record only visibility of graphical features.
-/
structure ReversiblePendulumFigure where
  showsPoint : FigurePoint → Bool
  showsLabel : FigureLabel → Bool
  distanceBetween : FigurePoint → FigurePoint → LengthQuantity
  pointOrderAlongBody : AxialOrder
  separationArrowEndpoints : FigurePoint × FigurePoint
  pivotMobility : Pivot → PivotMobility
  scaleContainsPivot : Pivot → Bool
  dashedAxisPassesThrough : FigurePoint
  oscillationArrowVisible : Bool

/--
The single pendulum body, its two suspension configurations, and their
observables.  No field defines `pivotSeparationL` from the requested numerical
answer.
-/
structure ReversiblePhysicalPendulum where
  figure : ReversiblePendulumFigure
  bodyTreatment : BodyTreatment
  oscillationRegime : OscillationRegime
  bodyMass : MassQuantity
  localGravity : AccelerationQuantity
  centerMomentOfInertia : MomentOfInertiaQuantity
  centerOfMassDistanceFromPivot : Pivot → LengthQuantity
  pivotSeparationL : LengthQuantity
  pivotMomentOfInertia : Pivot → MomentOfInertiaQuantity
  gravitationalRestoringCoefficient : Pivot → RotationalStiffnessQuantity
  linearizedAngularOscillator :
    Pivot → ClassicalMechanics.HarmonicOscillator
  periodAtPivot : Pivot → TimeQuantity

/-! ## Figure readouts and problem data -/

/--
Geometric and qualitative facts visible in the primary image.  In particular,
the center of mass lies strictly closer to `B` than to `A`, so the equal-period
pivots have unequal center-of-mass offsets.  This excludes the degenerate
midpoint case without assigning a numerical value to `L`.
-/
structure MatchesPrimaryFigure
    (setup : ReversiblePhysicalPendulum) : Prop where
  everyPointVisible : ∀ point, setup.figure.showsPoint point = true
  everyLabelVisible : ∀ label, setup.figure.showsLabel label = true
  markedPointOrder : setup.figure.pointOrderAlongBody = .A_centerOfMass_B
  separationArrowRunsFromAToB :
    setup.figure.separationArrowEndpoints = (.pivotA, .pivotB)
  distanceAToCenterOfMass :
    setup.figure.distanceBetween .pivotA .centerOfMass =
      setup.centerOfMassDistanceFromPivot .A
  distanceCenterOfMassToB :
    setup.figure.distanceBetween .centerOfMass .pivotB =
      setup.centerOfMassDistanceFromPivot .B
  distanceAToB :
    setup.figure.distanceBetween .pivotA .pivotB = setup.pivotSeparationL
  centerOfMassBetweenPivots :
    lengthInMeters setup.pivotSeparationL =
      lengthInMeters (setup.centerOfMassDistanceFromPivot .A) +
        lengthInMeters (setup.centerOfMassDistanceFromPivot .B)
  centerOfMassStrictlyCloserToB :
    lengthInMeters (setup.centerOfMassDistanceFromPivot .B) <
      lengthInMeters (setup.centerOfMassDistanceFromPivot .A)
  pivotAIsFixed : setup.figure.pivotMobility .A = .fixed
  pivotBIsAdjustable :
    setup.figure.pivotMobility .B = .adjustableAlongScale
  scaleMarksPivotB : setup.figure.scaleContainsPivot .B = true
  dashedAxisThroughA : setup.figure.dashedAxisPassesThrough = .pivotA
  oscillationArrowShown : setup.figure.oscillationArrowVisible = true

/--
Textual data and standard textbook calibrations.  Suspending from `B` restores
the complete physical period observed at `A`; it does not assume any value for
the required pivot separation.
-/
structure HasReversiblePendulumProblemData
    (setup : ReversiblePhysicalPendulum) : Prop where
  rigidBody : setup.bodyTreatment = .rigid
  smallAngleModel : setup.oscillationRegime = .linearizedSmallAngle
  periodAtASeconds : timeInSeconds (setup.periodAtPivot .A) = 9 / 5
  periodRestoredAtB : setup.periodAtPivot .B = setup.periodAtPivot .A
  standardGravity :
    accelerationInMetersPerSecondSquared setup.localGravity = 49 / 5
  bodyMassPositive : 0 < massInKilograms setup.bodyMass
  centerMomentOfInertiaPositive :
    0 < momentOfInertiaInKilogramMetersSquared setup.centerMomentOfInertia
  centerOfMassOffsetsPositive : ∀ pivot,
    0 < lengthInMeters (setup.centerOfMassDistanceFromPivot pivot)
  pivotSeparationPositive : 0 < lengthInMeters setup.pivotSeparationL

/-! ## Governing physical laws -/

/--
The physical-pendulum laws at each suspension point:

* the parallel-axis theorem gives `I_p = I_com + m d_p²`;
* gravity gives the linearized restoring coefficient `m g d_p`;
* those two dimensionful quantities supply the generalized inertia and
  stiffness of Physlib's scalar harmonic oscillator; and
* the observed physical duration equals that oscillator's period.

No field states the conjugate-pivot separation formula or a numerical answer.
-/
structure SatisfiesReversiblePhysicalPendulumLaws
    (setup : ReversiblePhysicalPendulum) : Prop where
  parallelAxisLaw : ∀ pivot,
    momentOfInertiaInKilogramMetersSquared
        (setup.pivotMomentOfInertia pivot) =
      momentOfInertiaInKilogramMetersSquared setup.centerMomentOfInertia +
        massInKilograms setup.bodyMass *
          lengthInMeters (setup.centerOfMassDistanceFromPivot pivot) ^ 2
  gravitationalRestoringLaw : ∀ pivot,
    rotationalStiffnessInNewtonMeters
        (setup.gravitationalRestoringCoefficient pivot) =
      massInKilograms setup.bodyMass *
        accelerationInMetersPerSecondSquared setup.localGravity *
        lengthInMeters (setup.centerOfMassDistanceFromPivot pivot)
  oscillatorGeneralizedInertia : ∀ pivot,
    (setup.linearizedAngularOscillator pivot).m =
      momentOfInertiaInKilogramMetersSquared
        (setup.pivotMomentOfInertia pivot)
  oscillatorGravitationalStiffness : ∀ pivot,
    (setup.linearizedAngularOscillator pivot).k =
      rotationalStiffnessInNewtonMeters
        (setup.gravitationalRestoringCoefficient pivot)
  smallAnglePeriodLaw : ∀ pivot,
    timeInSeconds (setup.periodAtPivot pivot) =
      (setup.linearizedAngularOscillator pivot).period

/-! ## Requested distance and displayed answers -/

/--
Equivalent simple-pendulum length computed from the period at `A` and local
gravity.  Its equality with the physical separation `L` remains a theorem.
-/
def equivalentSimplePendulumLengthMeters
    (setup : ReversiblePhysicalPendulum) : ℝ :=
  accelerationInMetersPerSecondSquared setup.localGravity *
      timeInSeconds (setup.periodAtPivot .A) ^ 2 /
    (4 * Real.pi ^ 2)

/-- Labels of the four displayed answer choices. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Distance in metres printed beside each answer choice. -/
def answerLengthMeters : AnswerChoice → ℝ
  | .A => 96 / 125
  | .B => 393 / 500
  | .C => 413 / 500
  | .D => 201 / 250

/-- The answer label recorded in the supplied dataset metadata. -/
def recordedAnswerChoice : AnswerChoice := .D

/-- A displayed choice is strictly closer than every distinct alternative. -/
def IsUniqueClosestAnswerChoice
    (lengthMeters : ℝ) (choice : AnswerChoice) : Prop :=
  ∀ other, other ≠ choice →
    |lengthMeters - answerLengthMeters choice| <
      |lengthMeters - answerLengthMeters other|

/--
Equal small-angle periods about the two unequal, opposite-side pivots make
their separation the equivalent simple-pendulum length.  With `T = 1.80 s`
and `g = 9.8 m/s²`, this length lies within half a millimetre of `0.804 m` and
is uniquely closest to recorded answer D.

This is the declaration corresponding to
`thm:physics:phyx_mini_0282:target`.
-/
theorem pivotSeparation_is_answer_D
    (setup : ReversiblePhysicalPendulum)
    (h_figure : MatchesPrimaryFigure setup)
    (h_data : HasReversiblePendulumProblemData setup)
    (h_laws : SatisfiesReversiblePhysicalPendulumLaws setup) :
    lengthInMeters setup.pivotSeparationL =
        equivalentSimplePendulumLengthMeters setup ∧
      |lengthInMeters setup.pivotSeparationL -
          answerLengthMeters recordedAnswerChoice| < 1 / 2000 ∧
      IsUniqueClosestAnswerChoice
        (lengthInMeters setup.pivotSeparationL) recordedAnswerChoice := by
  let M : ℝ := massInKilograms setup.bodyMass
  let g : ℝ :=
    accelerationInMetersPerSecondSquared setup.localGravity
  let I : ℝ :=
    momentOfInertiaInKilogramMetersSquared setup.centerMomentOfInertia
  let a : ℝ :=
    lengthInMeters (setup.centerOfMassDistanceFromPivot .A)
  let b : ℝ :=
    lengthInMeters (setup.centerOfMassDistanceFromPivot .B)
  let L : ℝ := lengthInMeters setup.pivotSeparationL
  let oscillatorA := setup.linearizedAngularOscillator .A
  let oscillatorB := setup.linearizedAngularOscillator .B

  have hM : 0 < M := by
    simpa [M] using h_data.bodyMassPositive
  have hg : 0 < g := by
    simp only [g, h_data.standardGravity]
    norm_num
  have hIpos : 0 < I := by
    simpa [I] using h_data.centerMomentOfInertiaPositive
  have ha : 0 < a := by
    simpa [a] using h_data.centerOfMassOffsetsPositive .A
  have hb : 0 < b := by
    simpa [b] using h_data.centerOfMassOffsetsPositive .B
  have hba : b < a := by
    simpa [a, b] using h_figure.centerOfMassStrictlyCloserToB
  have hL : L = a + b := by
    simpa [L, a, b] using h_figure.centerOfMassBetweenPivots

  have hperiodReadout :
      timeInSeconds (setup.periodAtPivot .B) =
        timeInSeconds (setup.periodAtPivot .A) :=
    congrArg timeInSeconds h_data.periodRestoredAtB
  have hperiodOscillator : oscillatorA.period = oscillatorB.period := by
    rw [← h_laws.smallAnglePeriodLaw .A,
      ← h_laws.smallAnglePeriodLaw .B]
    exact hperiodReadout.symm
  have hω : oscillatorA.ω = oscillatorB.ω := by
    rw [ClassicalMechanics.HarmonicOscillator.period_eq,
      ClassicalMechanics.HarmonicOscillator.period_eq] at hperiodOscillator
    field_simp [oscillatorA.ω_ne_zero, oscillatorB.ω_ne_zero] at hperiodOscillator
    nlinarith [Real.pi_pos]
  have hfrequencyRatio :
      oscillatorA.k / oscillatorA.m =
        oscillatorB.k / oscillatorB.m := by
    rw [← oscillatorA.ω_sq, ← oscillatorB.ω_sq, hω]

  have hparallelA :
      momentOfInertiaInKilogramMetersSquared
          (setup.pivotMomentOfInertia .A) = I + M * a ^ 2 := by
    simpa [I, M, a] using h_laws.parallelAxisLaw .A
  have hparallelB :
      momentOfInertiaInKilogramMetersSquared
          (setup.pivotMomentOfInertia .B) = I + M * b ^ 2 := by
    simpa [I, M, b] using h_laws.parallelAxisLaw .B
  have hrestoringA :
      rotationalStiffnessInNewtonMeters
          (setup.gravitationalRestoringCoefficient .A) = M * g * a := by
    simpa [M, g, a] using h_laws.gravitationalRestoringLaw .A
  have hrestoringB :
      rotationalStiffnessInNewtonMeters
          (setup.gravitationalRestoringCoefficient .B) = M * g * b := by
    simpa [M, g, b] using h_laws.gravitationalRestoringLaw .B
  have hratio :
      M * g * a / (I + M * a ^ 2) =
        M * g * b / (I + M * b ^ 2) := by
    rw [← hrestoringA, ← hrestoringB, ← hparallelA, ← hparallelB]
    rw [← h_laws.oscillatorGravitationalStiffness .A,
      ← h_laws.oscillatorGravitationalStiffness .B,
      ← h_laws.oscillatorGeneralizedInertia .A,
      ← h_laws.oscillatorGeneralizedInertia .B]
    exact hfrequencyRatio
  have hdenA : I + M * a ^ 2 ≠ 0 := by
    positivity
  have hdenB : I + M * b ^ 2 ≠ 0 := by
    positivity
  have hcross :
      (M * g * a) * (I + M * b ^ 2) =
        (M * g * b) * (I + M * a ^ 2) :=
    (div_eq_div_iff hdenA hdenB).mp hratio
  have hMg : M * g ≠ 0 := mul_ne_zero hM.ne' hg.ne'
  have hreduced :
      a * (I + M * b ^ 2) = b * (I + M * a ^ 2) := by
    apply mul_left_cancel₀ hMg
    calc
      M * g * (a * (I + M * b ^ 2)) =
          (M * g * a) * (I + M * b ^ 2) := by ring
      _ = (M * g * b) * (I + M * a ^ 2) := hcross
      _ = M * g * (b * (I + M * a ^ 2)) := by ring
  have hfactor : (a - b) * (I - M * a * b) = 0 := by
    calc
      (a - b) * (I - M * a * b) =
          a * (I + M * b ^ 2) - b * (I + M * a ^ 2) := by ring
      _ = 0 := sub_eq_zero.mpr hreduced
  have hab : a - b ≠ 0 := sub_ne_zero.mpr (ne_of_gt hba)
  have hI : I = M * a * b := by
    rcases mul_eq_zero.mp hfactor with habzero | hIzero
    · exact (hab habzero).elim
    · exact sub_eq_zero.mp hIzero

  have hωsq :
      oscillatorA.ω ^ 2 =
        M * g * a / (I + M * a ^ 2) := by
    rw [oscillatorA.ω_sq]
    rw [h_laws.oscillatorGravitationalStiffness .A,
      hrestoringA,
      h_laws.oscillatorGeneralizedInertia .A,
      hparallelA]
  have hMa : M * a ≠ 0 := mul_ne_zero hM.ne' ha.ne'
  have hfrequencyLength : oscillatorA.ω ^ 2 * (a + b) = g := by
    rw [hωsq, hI]
    field_simp
    apply mul_left_cancel₀ hMa
    ring
  have hperiodA :
      (9 / 5 : ℝ) = 2 * Real.pi / oscillatorA.ω := by
    calc
      (9 / 5 : ℝ) =
          timeInSeconds (setup.periodAtPivot .A) :=
        h_data.periodAtASeconds.symm
      _ = oscillatorA.period := h_laws.smallAnglePeriodLaw .A
      _ = 2 * Real.pi / oscillatorA.ω :=
        ClassicalMechanics.HarmonicOscillator.period_eq oscillatorA
  have hperiodProduct :
      (9 / 5 : ℝ) * oscillatorA.ω = 2 * Real.pi :=
    (eq_div_iff oscillatorA.ω_ne_zero).mp hperiodA
  have hperiodSquare :
      (9 / 5 : ℝ) ^ 2 * oscillatorA.ω ^ 2 =
        4 * Real.pi ^ 2 := by
    calc
      (9 / 5 : ℝ) ^ 2 * oscillatorA.ω ^ 2 =
          ((9 / 5 : ℝ) * oscillatorA.ω) ^ 2 := by ring
      _ = (2 * Real.pi) ^ 2 :=
        congrArg (fun x : ℝ => x ^ 2) hperiodProduct
      _ = 4 * Real.pi ^ 2 := by ring

  have hseparationFormula :
      L = g * (9 / 5 : ℝ) ^ 2 / (4 * Real.pi ^ 2) := by
    rw [hL]
    calc
      a + b = (a + b) * (4 * Real.pi ^ 2) /
          (4 * Real.pi ^ 2) := by
        field_simp [Real.pi_ne_zero]
      _ = (a + b) *
          ((9 / 5 : ℝ) ^ 2 * oscillatorA.ω ^ 2) /
            (4 * Real.pi ^ 2) := by rw [hperiodSquare]
      _ = (oscillatorA.ω ^ 2 * (a + b)) * (9 / 5 : ℝ) ^ 2 /
          (4 * Real.pi ^ 2) := by ring
      _ = g * (9 / 5 : ℝ) ^ 2 / (4 * Real.pi ^ 2) := by
        rw [hfrequencyLength]
  have hformula :
      lengthInMeters setup.pivotSeparationL =
        equivalentSimplePendulumLengthMeters setup := by
    change L = _
    rw [equivalentSimplePendulumLengthMeters,
      h_data.standardGravity, h_data.periodAtASeconds]
    simpa [g, h_data.standardGravity] using hseparationFormula

  have hcloseFormula :
      |equivalentSimplePendulumLengthMeters setup -
          answerLengthMeters recordedAnswerChoice| < 1 / 2000 := by
    rw [equivalentSimplePendulumLengthMeters,
      h_data.standardGravity, h_data.periodAtASeconds]
    change
      |(49 / 5 : ℝ) * (9 / 5) ^ 2 / (4 * Real.pi ^ 2) - 201 / 250| <
        1 / 2000
    have hdenPi : 0 < 4 * Real.pi ^ 2 := by positivity
    rw [abs_lt]
    constructor
    · apply sub_lt_iff_lt_add.mp
      apply (lt_div_iff₀ hdenPi).2
      nlinarith only [Real.pi_pos, Real.pi_lt_d6,
        sq_nonneg (Real.pi - 3.141593)]
    · apply sub_lt_iff_lt_add.mpr
      apply (div_lt_iff₀ hdenPi).2
      nlinarith only [Real.pi_pos, Real.pi_gt_d6,
        sq_nonneg (Real.pi - 3.141592)]
  have hclose :
      |lengthInMeters setup.pivotSeparationL -
          answerLengthMeters recordedAnswerChoice| < 1 / 2000 := by
    rw [hformula]
    exact hcloseFormula

  refine ⟨hformula, hclose, ?_⟩
  intro other hother
  have hbounds := abs_lt.mp hclose
  simp only [recordedAnswerChoice, answerLengthMeters] at hclose hbounds
  change other ≠ .D at hother
  cases other with
  | A =>
      change
        |lengthInMeters setup.pivotSeparationL - 201 / 250| <
          |lengthInMeters setup.pivotSeparationL - 96 / 125|
      have hpositive :
          0 < lengthInMeters setup.pivotSeparationL - 96 / 125 := by
        linarith only [hbounds.1]
      rw [abs_of_pos hpositive]
      exact lt_trans hclose (by linarith only [hbounds.1])
  | B =>
      change
        |lengthInMeters setup.pivotSeparationL - 201 / 250| <
          |lengthInMeters setup.pivotSeparationL - 393 / 500|
      have hpositive :
          0 < lengthInMeters setup.pivotSeparationL - 393 / 500 := by
        linarith only [hbounds.1]
      rw [abs_of_pos hpositive]
      exact lt_trans hclose (by linarith only [hbounds.1])
  | C =>
      change
        |lengthInMeters setup.pivotSeparationL - 201 / 250| <
          |lengthInMeters setup.pivotSeparationL - 413 / 500|
      have hnegative :
          lengthInMeters setup.pivotSeparationL - 413 / 500 < 0 := by
        linarith only [hbounds.2]
      rw [abs_of_neg hnegative]
      exact lt_trans hclose (by linarith only [hbounds.2])
  | D =>
      exact (hother rfl).elim

end PhyXMiniProblems.ProblemPhyXMini0282
