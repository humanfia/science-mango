import Mathlib
import Physlib.Units.WithDim.Basic

/- USER: The assigned source file did not exist when this autoformalization task began. -/

/-!
# Acceleration of an asteroid pushed by three astronauts

Three astronauts use jet backpacks while applying the three planar forces
`F₁`, `F₂`, and `F₃` to a `120 kg` asteroid.  In the primary image, positive
`x` points right and positive `y` points up.  The `F₁` arrow is `30°`
counterclockwise from positive `x`, `F₂` lies along positive `x`, and `F₃` is
`60°` clockwise from positive `x`.

Mass, planar forces, and planar acceleration are unit-independent Physlib
dimensionful quantities.  Real numbers occur only as coherent-SI readouts,
radian angle readouts, schematic figure data, and displayed answer values.

Assumption/target boundary:

* `MatchesProblemReadouts` contains the stated mass, force magnitudes, and
  angles.
* `MatchesPrimaryFigure` records only labels and qualitative geometry visible
  in the raster.
* `MatchesFigureForceGeometry` converts that geometry into Cartesian force
  components.
* `SatisfiesNewtonianDynamics` states force addition and Newton's second law.
* There are no previous-part results.
* The requested acceleration, `0.88 m/s²`, and answer C occur only in the
  conclusions and the separate displayed-answer table.
-/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0755

open Dimension

/-! ## Dimensionful quantities and coherent-SI readouts -/

/-- The physical dimension of acceleration, `L T⁻²`. -/
def accelerationDimension : Dimension :=
  L𝓭 * T𝓭⁻¹ * T𝓭⁻¹

/-- The physical dimension of force, `M L T⁻²`. -/
def forceDimension : Dimension :=
  M𝓭 * accelerationDimension

/-- A unit-independent nonnegative physical mass. -/
abbrev MassQuantity : Type :=
  Dimensionful (WithDim M𝓭 NNReal)

/-- A unit-independent force vector in the plane of the supplied figure. -/
abbrev PlanarForceQuantity : Type :=
  Dimensionful
    (WithDim forceDimension (EuclideanSpace ℝ (Fin 2)))

/-- A unit-independent acceleration vector in the plane of the figure. -/
abbrev PlanarAccelerationQuantity : Type :=
  Dimensionful
    (WithDim accelerationDimension (EuclideanSpace ℝ (Fin 2)))

/-- Coordinate `0`, the positive horizontal axis pointing right. -/
def xAxis : Fin 2 := 0

/-- Coordinate `1`, the positive vertical axis pointing up. -/
def yAxis : Fin 2 := 1

/-- Coherent-SI kilogram readout of a physical mass. -/
def massInKilograms (mass : MassQuantity) : ℝ :=
  ((mass UnitChoices.SI).val : ℝ)

/-- Coherent-SI planar-force readout, whose coordinates are in newtons. -/
def forceVectorInNewtons
    (force : PlanarForceQuantity) : EuclideanSpace ℝ (Fin 2) :=
  (force UnitChoices.SI).val

/-- Euclidean magnitude in newtons of a physical planar force. -/
def forceMagnitudeInNewtons (force : PlanarForceQuantity) : ℝ :=
  ‖forceVectorInNewtons force‖

/-- Coherent-SI acceleration vector, in metres per second squared. -/
def accelerationVectorInMetersPerSecondSquared
    (acceleration : PlanarAccelerationQuantity) :
    EuclideanSpace ℝ (Fin 2) :=
  (acceleration UnitChoices.SI).val

/-- Euclidean acceleration magnitude in metres per second squared. -/
def accelerationMagnitudeInMetersPerSecondSquared
    (acceleration : PlanarAccelerationQuantity) : ℝ :=
  ‖accelerationVectorInMetersPerSecondSquared acceleration‖

/-! ## Named physical and figure content -/

/-- The three astronauts shown pushing the asteroid. -/
inductive AstronautLabel where
  | one
  | two
  | three
  deriving DecidableEq, Fintype, Repr

/-- The three force-vector labels printed in the primary image. -/
inductive AppliedForceLabel where
  | F1
  | F2
  | F3
  deriving DecidableEq, Fintype, Repr

/-- The force label associated with each astronaut's push. -/
def forceExertedBy : AstronautLabel → AppliedForceLabel
  | .one => .F1
  | .two => .F2
  | .three => .F3

/-- The two named angles printed between the oblique arrows and positive `x`. -/
inductive FigureAngleLabel where
  | theta1
  | theta3
  deriving DecidableEq, Fintype, Repr

/-- Coordinate-axis labels printed over the asteroid. -/
inductive DiagramAxis where
  | x
  | y
  deriving DecidableEq, Fintype, Repr

/-- Qualitative directions needed to describe the axes and force arrows. -/
inductive ArrowDirection where
  | right
  | up
  | upperRight
  | lowerRight
  deriving DecidableEq, Repr

/-- Sense in which an angle is measured from the positive `x`-axis. -/
inductive RotationSense where
  | counterclockwise
  | clockwise
  deriving DecidableEq, Repr

/-- The qualitative force direction visibly associated with each arrow. -/
def expectedForceDirection : AppliedForceLabel → ArrowDirection
  | .F1 => .upperRight
  | .F2 => .right
  | .F3 => .lowerRight

/-- The force arrow whose inclination is denoted by each angle label. -/
def forceForAngle : FigureAngleLabel → AppliedForceLabel
  | .theta1 => .F1
  | .theta3 => .F3

/-- The rotation sense visibly associated with each angle label. -/
def expectedRotationSense : FigureAngleLabel → RotationSense
  | .theta1 => .counterclockwise
  | .theta3 => .clockwise

/-- Literal and qualitative content transcribed from image `755.png`. -/
structure AsteroidPushFigure where
  showsAstronaut : AstronautLabel → Bool
  showsJetBackpackExhaust : AstronautLabel → Bool
  showsAxis : DiagramAxis → Bool
  positiveAxisDirection : DiagramAxis → ArrowDirection
  showsForceArrow : AppliedForceLabel → Bool
  forceArrowDirection : AppliedForceLabel → ArrowDirection
  forceArrowStartsAtAxesIntersection : AppliedForceLabel → Bool
  showsAngle : FigureAngleLabel → Bool
  angleIsMeasuredFromPositiveXAxis : FigureAngleLabel → Bool
  angleRotationSense : FigureAngleLabel → RotationSense

/-!
Independent physical fields of the experiment.  In particular, acceleration
and resultant force are not defined from any answer value; the hypotheses
below constrain them through the physical laws.
-/
structure AsteroidPushSetup where
  figure : AsteroidPushFigure
  guidedTowardProcessingDock : Bool
  astronautUsesJetBackpack : AstronautLabel → Bool
  asteroidMass : MassQuantity
  appliedForce : AppliedForceLabel → PlanarForceQuantity
  resultantForce : PlanarForceQuantity
  theta1Radians : ℝ
  theta3Radians : ℝ
  asteroidAcceleration : PlanarAccelerationQuantity

/-! ## Scenario, data, figure geometry, and governing laws -/

/-- Qualitative physical scenario stated in the prose. -/
structure MatchesAsteroidGuidanceScenario
    (setup : AsteroidPushSetup) : Prop where
  guidedTowardDock : setup.guidedTowardProcessingDock = true
  eachAstronautUsesJetBackpack :
    ∀ astronaut, setup.astronautUsesJetBackpack astronaut = true

/-!
Numerical readouts stated in the problem.  Degrees have been converted to
radians.  No acceleration value or answer label occurs in this record.
-/
structure MatchesProblemReadouts (setup : AsteroidPushSetup) : Prop where
  asteroidMassKilograms : massInKilograms setup.asteroidMass = 120
  force1MagnitudeNewtons :
    forceMagnitudeInNewtons (setup.appliedForce .F1) = 32
  force2MagnitudeNewtons :
    forceMagnitudeInNewtons (setup.appliedForce .F2) = 55
  force3MagnitudeNewtons :
    forceMagnitudeInNewtons (setup.appliedForce .F3) = 41
  theta1IsThirtyDegrees : setup.theta1Radians = Real.pi / 6
  theta3IsSixtyDegrees : setup.theta3Radians = Real.pi / 3

/-!
Primary-image evidence.  In particular, both labelled angles use positive
`x` as their reference ray; this reading follows the raster rather than the
auxiliary caption's incompatible mention of the `y`-axis.
-/
structure MatchesPrimaryFigure (setup : AsteroidPushSetup) : Prop where
  everyAstronautShown : ∀ astronaut, setup.figure.showsAstronaut astronaut = true
  everyJetExhaustShown :
    ∀ astronaut, setup.figure.showsJetBackpackExhaust astronaut = true
  bothAxesShown : ∀ axis, setup.figure.showsAxis axis = true
  positiveXAxisPointsRight :
    setup.figure.positiveAxisDirection .x = .right
  positiveYAxisPointsUp :
    setup.figure.positiveAxisDirection .y = .up
  everyForceArrowShown :
    ∀ force, setup.figure.showsForceArrow force = true
  displayedForceDirections :
    ∀ force,
      setup.figure.forceArrowDirection force = expectedForceDirection force
  arrowsShareAxesIntersection :
    ∀ force,
      setup.figure.forceArrowStartsAtAxesIntersection force = true
  bothAnglesShown : ∀ angle, setup.figure.showsAngle angle = true
  anglesUsePositiveXAxis :
    ∀ angle,
      setup.figure.angleIsMeasuredFromPositiveXAxis angle = true
  displayedRotationSenses :
    ∀ angle,
      setup.figure.angleRotationSense angle = expectedRotationSense angle

/-!
Cartesian realization of the primary-image arrow geometry.  The negative
`y` component of `F₃` expresses its clockwise inclination below positive `x`.
These are general component laws in terms of the independently supplied
magnitudes and angles, not acceleration conclusions.
-/
structure MatchesFigureForceGeometry (setup : AsteroidPushSetup) : Prop where
  force1XComponent :
    forceVectorInNewtons (setup.appliedForce .F1) xAxis =
      forceMagnitudeInNewtons (setup.appliedForce .F1) *
        Real.cos setup.theta1Radians
  force1YComponent :
    forceVectorInNewtons (setup.appliedForce .F1) yAxis =
      forceMagnitudeInNewtons (setup.appliedForce .F1) *
        Real.sin setup.theta1Radians
  force2XComponent :
    forceVectorInNewtons (setup.appliedForce .F2) xAxis =
      forceMagnitudeInNewtons (setup.appliedForce .F2)
  force2YComponent :
    forceVectorInNewtons (setup.appliedForce .F2) yAxis = 0
  force3XComponent :
    forceVectorInNewtons (setup.appliedForce .F3) xAxis =
      forceMagnitudeInNewtons (setup.appliedForce .F3) *
        Real.cos setup.theta3Radians
  force3YComponent :
    forceVectorInNewtons (setup.appliedForce .F3) yAxis =
      -(forceMagnitudeInNewtons (setup.appliedForce .F3) *
        Real.sin setup.theta3Radians)

/-!
Governing Newtonian dynamics: the resultant is the vector sum of the three
applied forces, and the net force equals mass times acceleration in coherent
SI components.  No requested numerical acceleration occurs in these laws.
-/
structure SatisfiesNewtonianDynamics (setup : AsteroidPushSetup) : Prop where
  resultantIsVectorSum :
    forceVectorInNewtons setup.resultantForce =
      forceVectorInNewtons (setup.appliedForce .F1) +
        forceVectorInNewtons (setup.appliedForce .F2) +
        forceVectorInNewtons (setup.appliedForce .F3)
  newtonsSecondLaw :
    forceVectorInNewtons setup.resultantForce =
      massInKilograms setup.asteroidMass •
        accelerationVectorInMetersPerSecondSquared
          setup.asteroidAcceleration

/-! ## Exact result and displayed answer choices -/

/-!
Closed unrounded acceleration magnitude obtained from the stated force
components and `120 kg` mass.  This expression contains no setup acceleration
field and therefore does not define the requested physical observable into
the assumptions.
-/
noncomputable def exactAccelerationMagnitudeInMetersPerSecondSquared : ℝ :=
  Real.sqrt
      ((32 * Real.cos (Real.pi / 6) + 55 +
          41 * Real.cos (Real.pi / 3)) ^ 2 +
        (32 * Real.sin (Real.pi / 6) -
          41 * Real.sin (Real.pi / 3)) ^ 2) /
    120

/-- The four acceleration-answer labels displayed with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Acceleration magnitude in `m/s²` printed beside each displayed choice. -/
def AnswerChoice.accelerationMetersPerSecondSquared : AnswerChoice → ℝ
  | .A => 0.76
  | .B => 0.82
  | .C => 0.88
  | .D => 0.92

/-- The answer label recorded in the supplied dataset metadata. -/
def recordedAnswerChoice : AnswerChoice := .C

/-- Absolute discrepancy from one displayed acceleration magnitude. -/
def answerChoiceErrorMetersPerSecondSquared
    (setup : AsteroidPushSetup) (choice : AnswerChoice) : ℝ :=
  |accelerationMagnitudeInMetersPerSecondSquared
      setup.asteroidAcceleration -
    choice.accelerationMetersPerSecondSquared|

/-- Agreement with a value displayed to the nearest `0.01 m/s²`. -/
def MatchesDisplayedAcceleration
    (setup : AsteroidPushSetup) (choice : AnswerChoice) : Prop :=
  answerChoiceErrorMetersPerSecondSquared setup choice ≤ (1 : ℝ) / 200

/-- A displayed value is strictly closer than every alternative. -/
def IsUniqueClosestAccelerationChoice
    (setup : AsteroidPushSetup) (choice : AnswerChoice) : Prop :=
  ∀ other, other ≠ choice →
    answerChoiceErrorMetersPerSecondSquared setup choice <
      answerChoiceErrorMetersPerSecondSquared setup other

/-- The governing assumptions determine the exact unrounded acceleration. -/
lemma accelerationMagnitude_eq_exactExpression
    (setup : AsteroidPushSetup)
    (_scenario : MatchesAsteroidGuidanceScenario setup)
    (_readouts : MatchesProblemReadouts setup)
    (_figure : MatchesPrimaryFigure setup)
    (_geometry : MatchesFigureForceGeometry setup)
    (_dynamics : SatisfiesNewtonianDynamics setup) :
    accelerationMagnitudeInMetersPerSecondSquared
        setup.asteroidAcceleration =
      exactAccelerationMagnitudeInMetersPerSecondSquared := by
  have hForceSum :
      forceVectorInNewtons (setup.appliedForce .F1) +
          forceVectorInNewtons (setup.appliedForce .F2) +
          forceVectorInNewtons (setup.appliedForce .F3) =
        (120 : ℝ) •
          accelerationVectorInMetersPerSecondSquared
            setup.asteroidAcceleration := by
    calc
      _ = forceVectorInNewtons setup.resultantForce :=
        _dynamics.resultantIsVectorSum.symm
      _ = massInKilograms setup.asteroidMass •
            accelerationVectorInMetersPerSecondSquared
              setup.asteroidAcceleration :=
        _dynamics.newtonsSecondLaw
      _ = _ := by rw [_readouts.asteroidMassKilograms]
  have hAccelerationX :
      accelerationVectorInMetersPerSecondSquared
          setup.asteroidAcceleration xAxis =
        (32 * Real.cos (Real.pi / 6) + 55 +
            41 * Real.cos (Real.pi / 3)) / 120 := by
    have hComponent := congrArg (fun vector => vector xAxis) hForceSum
    simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul] at hComponent
    rw [_geometry.force1XComponent, _geometry.force2XComponent,
      _geometry.force3XComponent, _readouts.force1MagnitudeNewtons,
      _readouts.force2MagnitudeNewtons, _readouts.force3MagnitudeNewtons,
      _readouts.theta1IsThirtyDegrees, _readouts.theta3IsSixtyDegrees] at hComponent
    linarith
  have hAccelerationY :
      accelerationVectorInMetersPerSecondSquared
          setup.asteroidAcceleration yAxis =
        (32 * Real.sin (Real.pi / 6) -
            41 * Real.sin (Real.pi / 3)) / 120 := by
    have hComponent := congrArg (fun vector => vector yAxis) hForceSum
    simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul] at hComponent
    rw [_geometry.force1YComponent, _geometry.force2YComponent,
      _geometry.force3YComponent, _readouts.force1MagnitudeNewtons,
      _readouts.force3MagnitudeNewtons, _readouts.theta1IsThirtyDegrees,
      _readouts.theta3IsSixtyDegrees] at hComponent
    linarith
  unfold accelerationMagnitudeInMetersPerSecondSquared
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_two]
  simp only [Real.norm_eq_abs, sq_abs]
  change
    Real.sqrt
        ((accelerationVectorInMetersPerSecondSquared
              setup.asteroidAcceleration xAxis) ^ 2 +
          (accelerationVectorInMetersPerSecondSquared
              setup.asteroidAcceleration yAxis) ^ 2) =
      exactAccelerationMagnitudeInMetersPerSecondSquared
  rw [hAccelerationX, hAccelerationY]
  unfold exactAccelerationMagnitudeInMetersPerSecondSquared
  calc
    Real.sqrt
        (((32 * Real.cos (Real.pi / 6) + 55 +
              41 * Real.cos (Real.pi / 3)) / 120) ^ 2 +
          ((32 * Real.sin (Real.pi / 6) -
              41 * Real.sin (Real.pi / 3)) / 120) ^ 2) =
        Real.sqrt
          (((32 * Real.cos (Real.pi / 6) + 55 +
                41 * Real.cos (Real.pi / 3)) ^ 2 +
            (32 * Real.sin (Real.pi / 6) -
                41 * Real.sin (Real.pi / 3)) ^ 2) / (120 : ℝ) ^ 2) := by
      congr 1
      ring
    _ =
        Real.sqrt
            ((32 * Real.cos (Real.pi / 6) + 55 +
                41 * Real.cos (Real.pi / 3)) ^ 2 +
              (32 * Real.sin (Real.pi / 6) -
                41 * Real.sin (Real.pi / 3)) ^ 2) /
          Real.sqrt ((120 : ℝ) ^ 2) := by
      rw [Real.sqrt_div (by positivity)]
    _ = _ := by norm_num

/-!
The exact value is approximately `0.8753 m/s²`, so it rounds to the displayed
value `0.88 m/s²` and that value is uniquely closest among the four choices.
-/
lemma exactAcceleration_selects_choice_C
    (setup : AsteroidPushSetup)
    (hExact :
      accelerationMagnitudeInMetersPerSecondSquared
          setup.asteroidAcceleration =
        exactAccelerationMagnitudeInMetersPerSecondSquared) :
    MatchesDisplayedAcceleration setup .C ∧
      IsUniqueClosestAccelerationChoice setup .C := by
  have hClosedForm :
      exactAccelerationMagnitudeInMetersPerSecondSquared =
        Real.sqrt (7985 + 1760 * Real.sqrt 3) / 120 := by
    unfold exactAccelerationMagnitudeInMetersPerSecondSquared
    rw [Real.cos_pi_div_six, Real.cos_pi_div_three,
      Real.sin_pi_div_six, Real.sin_pi_div_three]
    congr 1
    congr 1
    ring_nf
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  have hSqrtThreeLower : (19 / 11 : ℝ) < Real.sqrt 3 := by
    rw [Real.lt_sqrt (by norm_num)]
    norm_num
  have hSqrtThreeUpper : Real.sqrt 3 < (7 / 4 : ℝ) := by
    rw [Real.sqrt_lt' (by norm_num)]
    norm_num
  have hRadicandLower :
      (105 : ℝ) ^ 2 < 7985 + 1760 * Real.sqrt 3 := by
    nlinarith
  have hRadicandUpper :
      7985 + 1760 * Real.sqrt 3 < (106 : ℝ) ^ 2 := by
    nlinarith
  have hRootLower :
      (105 : ℝ) < Real.sqrt (7985 + 1760 * Real.sqrt 3) := by
    rw [Real.lt_sqrt (by norm_num)]
    exact hRadicandLower
  have hRootUpper :
      Real.sqrt (7985 + 1760 * Real.sqrt 3) < (106 : ℝ) := by
    rw [Real.sqrt_lt' (by norm_num)]
    exact hRadicandUpper
  have hAccelerationLower :
      (7 / 8 : ℝ) <
        accelerationMagnitudeInMetersPerSecondSquared
          setup.asteroidAcceleration := by
    rw [hExact, hClosedForm]
    linarith
  have hAccelerationUpper :
      accelerationMagnitudeInMetersPerSecondSquared
          setup.asteroidAcceleration < (53 / 60 : ℝ) := by
    rw [hExact, hClosedForm]
    linarith
  constructor
  · unfold MatchesDisplayedAcceleration
    unfold answerChoiceErrorMetersPerSecondSquared
    simp only [AnswerChoice.accelerationMetersPerSecondSquared]
    rw [abs_le]
    constructor <;> norm_num at * <;> linarith
  · unfold IsUniqueClosestAccelerationChoice
    intro other hOther
    unfold answerChoiceErrorMetersPerSecondSquared
    fin_cases other
    · simp only [AnswerChoice.accelerationMetersPerSecondSquared]
      have hAlternativeErrorPositive :
          0 <
            accelerationMagnitudeInMetersPerSecondSquared
                setup.asteroidAcceleration -
              0.76 := by
        norm_num at *
        linarith
      rw [abs_of_pos hAlternativeErrorPositive]
      rw [abs_lt]
      constructor <;> norm_num at * <;> linarith
    · simp only [AnswerChoice.accelerationMetersPerSecondSquared]
      have hAlternativeErrorPositive :
          0 <
            accelerationMagnitudeInMetersPerSecondSquared
                setup.asteroidAcceleration -
              0.82 := by
        norm_num at *
        linarith
      rw [abs_of_pos hAlternativeErrorPositive]
      rw [abs_lt]
      constructor <;> norm_num at * <;> linarith
    · exact (hOther rfl).elim
    · simp only [AnswerChoice.accelerationMetersPerSecondSquared]
      have hAlternativeErrorNegative :
          accelerationMagnitudeInMetersPerSecondSquared
                setup.asteroidAcceleration -
              0.92 < 0 := by
        norm_num at *
        linarith
      rw [abs_of_neg hAlternativeErrorNegative]
      rw [abs_lt]
      constructor <;> norm_num at * <;> linarith

/-!
The asteroid's unrounded acceleration magnitude is the norm of the three
stated force vectors divided by its mass; it is displayed as `0.88 m/s²`,
answer C.

Blueprint: `thm:physics:phyx_mini_0755:target`.
-/
theorem problem_phyx_mini_0755
    (setup : AsteroidPushSetup)
    (_scenario : MatchesAsteroidGuidanceScenario setup)
    (_readouts : MatchesProblemReadouts setup)
    (_figure : MatchesPrimaryFigure setup)
    (_geometry : MatchesFigureForceGeometry setup)
    (_dynamics : SatisfiesNewtonianDynamics setup) :
    accelerationMagnitudeInMetersPerSecondSquared
          setup.asteroidAcceleration =
        exactAccelerationMagnitudeInMetersPerSecondSquared ∧
      MatchesDisplayedAcceleration setup .C ∧
      IsUniqueClosestAccelerationChoice setup .C := by
  have hExact :=
    accelerationMagnitude_eq_exactExpression setup _scenario _readouts _figure
      _geometry _dynamics
  exact ⟨hExact, exactAcceleration_selects_choice_C setup hExact⟩

end PhyXMiniProblems.ProblemPhyXMini0755
