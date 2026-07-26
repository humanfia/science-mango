import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Real.Sqrt
import Physlib.Units.WithDim.Speed

/- USER: The assigned source file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0686

open Dimension

/-!
# Speed of a horizontally launched stone at water impact

A stone is launched horizontally from a cliff of height `50.0 m` with speed
`18.0 m/s`.  The primary figure fixes a two-dimensional coordinate convention:
positive `x` points right and positive `y` points up.  Gravity therefore has a
negative `y` component, and the stone's velocity immediately before impact
points down and right.

Positions, lengths, times, vector velocities, vector accelerations, and scalar
speeds are represented by Physlib dimensionful quantities.  Real numbers occur
only as coherent-SI coordinate readouts, schematic figure coordinates, and
displayed answer values.
-/

/-! ## Dimensionful quantities and coherent-SI readouts -/

/-- The physical dimension of velocity, `L T⁻¹`. -/
def velocityDimension : Dimension := L𝓭 * T𝓭⁻¹

/-- The physical dimension of acceleration, `L T⁻²`. -/
def accelerationDimension : Dimension := L𝓭 * T𝓭⁻¹ * T𝓭⁻¹

/-- A nonnegative physical length. -/
abbrev LengthQuantity : Type := Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative physical duration. -/
abbrev TimeQuantity : Type := Dimensionful (WithDim T𝓭 NNReal)

/-- A signed position vector in the plane. -/
abbrev PlanarPositionQuantity : Type :=
  Dimensionful (WithDim L𝓭 (EuclideanSpace ℝ (Fin 2)))

/-- A signed velocity vector in the plane. -/
abbrev PlanarVelocityQuantity : Type :=
  Dimensionful
    (WithDim velocityDimension (EuclideanSpace ℝ (Fin 2)))

/-- A signed acceleration vector in the plane. -/
abbrev PlanarAccelerationQuantity : Type :=
  Dimensionful
    (WithDim accelerationDimension (EuclideanSpace ℝ (Fin 2)))

/-- The coordinate index carrying the figure's `x` label. -/
def xAxis : Fin 2 := 0

/-- The coordinate index carrying the figure's `y` label. -/
def yAxis : Fin 2 := 1

/-- Metre readout of a nonnegative physical length. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  ((length UnitChoices.SI).val : ℝ)

/-- Second readout of a nonnegative physical duration. -/
def timeInSeconds (time : TimeQuantity) : ℝ :=
  ((time UnitChoices.SI).val : ℝ)

/-- Coherent-SI position vector, whose coordinates are measured in metres. -/
def positionInMeters (position : PlanarPositionQuantity) :
    EuclideanSpace ℝ (Fin 2) :=
  (position UnitChoices.SI).val

/-- Coherent-SI velocity vector, in metres per second. -/
def velocityInMetersPerSecond (velocity : PlanarVelocityQuantity) :
    EuclideanSpace ℝ (Fin 2) :=
  (velocity UnitChoices.SI).val

/-- Coherent-SI acceleration vector, in metres per second squared. -/
def accelerationInMetersPerSecondSquared
    (acceleration : PlanarAccelerationQuantity) :
    EuclideanSpace ℝ (Fin 2) :=
  (acceleration UnitChoices.SI).val

/-- Metres-per-second readout of a nonnegative physical speed. -/
def speedInMetersPerSecond (speed : DimSpeed) : ℝ :=
  ((speed UnitChoices.SI).val : ℝ)

/-! ## Physical roles and primary-figure transcription -/

/-- The kind of projectile named in the prose. -/
inductive ProjectileKind where
  | stone
  deriving DecidableEq, Repr

/-- Qualitative arrow directions visible in the primary image. -/
inductive ArrowDirection where
  | up
  | right
  | down
  | downRight
  deriving DecidableEq, Repr

/-- Objects and distinguished points visible in the cliff diagram. -/
inductive FigureElement where
  | student
  | launchPoint
  | cliffBase
  | waterSurface
  | impactPoint
  deriving DecidableEq, Repr

/-- Vector and distance labels printed in the primary image. -/
inductive FigureQuantityLabel where
  | initialVelocity_vi
  | finalVelocity_v
  | gravity_g
  | cliffHeight_h
  deriving DecidableEq, Repr

/-- Literal qualitative and schematic-coordinate content of image `686.png`. -/
structure CliffProjectileFigure where
  horizontalPosition : FigureElement → ℝ
  verticalPosition : FigureElement → ℝ
  positiveXAxisDirection : ArrowDirection
  positiveYAxisDirection : ArrowDirection
  initialVelocityArrowDirection : ArrowDirection
  finalVelocityArrowDirection : ArrowDirection
  gravityArrowDirection : ArrowDirection
  showsDashedTrajectory : Bool
  showsLabel : FigureQuantityLabel → Bool

/--
Independent physical quantities in the launch-and-impact experiment.

In particular, `impactSpeed` is an independent field.  It is related to the
impact velocity only by the governing-law premise below and is not defined
from the recorded numerical answer.
-/
structure HorizontalCliffProjectileSetup where
  projectileKind : ProjectileKind
  figure : CliffProjectileFigure
  launchPosition : PlanarPositionQuantity
  impactPosition : PlanarPositionQuantity
  cliffHeight : LengthQuantity
  flightTime : TimeQuantity
  initialVelocity : PlanarVelocityQuantity
  gravitationalAcceleration : PlanarAccelerationQuantity
  impactVelocity : PlanarVelocityQuantity
  impactSpeed : DimSpeed

/--
Primary-image evidence: the student is at the cliff-top launch point, the
water and impact point are below it, the impact is to the right, and the
three vector arrows have the directions drawn in the raster image.
-/
structure MatchesPrimaryFigure
    (setup : HorizontalCliffProjectileSetup) : Prop where
  studentAtLaunchHorizontally :
    setup.figure.horizontalPosition .student =
      setup.figure.horizontalPosition .launchPoint
  studentAtLaunchVertically :
    setup.figure.verticalPosition .student =
      setup.figure.verticalPosition .launchPoint
  cliffBaseUnderLaunch :
    setup.figure.horizontalPosition .cliffBase =
      setup.figure.horizontalPosition .launchPoint
  cliffBaseBelowLaunch :
    setup.figure.verticalPosition .cliffBase <
      setup.figure.verticalPosition .launchPoint
  impactAtWaterLevel :
    setup.figure.verticalPosition .impactPoint =
      setup.figure.verticalPosition .waterSurface
  impactBelowLaunch :
    setup.figure.verticalPosition .impactPoint <
      setup.figure.verticalPosition .launchPoint
  impactRightOfLaunch :
    setup.figure.horizontalPosition .launchPoint <
      setup.figure.horizontalPosition .impactPoint
  positiveXAxisPointsRight : setup.figure.positiveXAxisDirection = .right
  positiveYAxisPointsUp : setup.figure.positiveYAxisDirection = .up
  initialVelocityPointsRight :
    setup.figure.initialVelocityArrowDirection = .right
  finalVelocityPointsDownAndRight :
    setup.figure.finalVelocityArrowDirection = .downRight
  gravityPointsDown : setup.figure.gravityArrowDirection = .down
  dashedTrajectoryShown : setup.figure.showsDashedTrajectory = true
  initialVelocityLabelShown :
    setup.figure.showsLabel .initialVelocity_vi = true
  finalVelocityLabelShown :
    setup.figure.showsLabel .finalVelocity_v = true
  gravityLabelShown : setup.figure.showsLabel .gravity_g = true
  heightLabelShown : setup.figure.showsLabel .cliffHeight_h = true

/--
Numerical and geometric data stated in the prose.  The two component equations
express that the `18.0 m/s` launch is horizontal in the figure's coordinates.
The final speed and every answer choice remain absent from these premises.
-/
structure MatchesProblemDescription
    (setup : HorizontalCliffProjectileSetup) : Prop where
  projectileIsStone : setup.projectileKind = .stone
  cliffHeightMeters : lengthInMeters setup.cliffHeight = 50.0
  launchVelocityXMetersPerSecond :
    velocityInMetersPerSecond setup.initialVelocity xAxis = 18.0
  launchVelocityYMetersPerSecond :
    velocityInMetersPerSecond setup.initialVelocity yAxis = 0
  launchIsHeightAboveImpact :
    positionInMeters setup.launchPosition yAxis -
        positionInMeters setup.impactPosition yAxis =
      lengthInMeters setup.cliffHeight

/-- Standard near-Earth gravitational acceleration in the drawn coordinates. -/
structure UsesStandardNearEarthGravity
    (setup : HorizontalCliffProjectileSetup) : Prop where
  noHorizontalGravity :
    accelerationInMetersPerSecondSquared
        setup.gravitationalAcceleration xAxis = 0
  downwardGravityMetersPerSecondSquared :
    accelerationInMetersPerSecondSquared
        setup.gravitationalAcceleration yAxis = -9.80

/-- Positivity conditions selecting a physically meaningful flight. -/
structure HasPhysicalProjectileParameters
    (setup : HorizontalCliffProjectileSetup) : Prop where
  cliffHeightPositive : 0 < lengthInMeters setup.cliffHeight
  flightTimePositive : 0 < timeInSeconds setup.flightTime
  impactSpeedNonnegative : 0 ≤ speedInMetersPerSecond setup.impactSpeed

/-! ## Governing no-drag, uniform-gravity laws -/

/-
The two vector equations are the standard constant-acceleration kinematic
laws evaluated at impact.  The last clause is the physical definition of
scalar speed as the Euclidean norm of the velocity vector.  These are general
laws: no clause contains the numerical landing speed or selects an answer.
-/
structure SatisfiesUniformGravityProjectileLaws
    (setup : HorizontalCliffProjectileSetup) : Prop where
  positionAtImpact :
    positionInMeters setup.impactPosition =
      positionInMeters setup.launchPosition +
        timeInSeconds setup.flightTime •
          velocityInMetersPerSecond setup.initialVelocity +
        ((1 / 2 : ℝ) * timeInSeconds setup.flightTime ^ 2) •
          accelerationInMetersPerSecondSquared
            setup.gravitationalAcceleration
  velocityAtImpact :
    velocityInMetersPerSecond setup.impactVelocity =
      velocityInMetersPerSecond setup.initialVelocity +
        timeInSeconds setup.flightTime •
          accelerationInMetersPerSecondSquared
            setup.gravitationalAcceleration
  impactSpeedIsVelocityNorm :
    speedInMetersPerSecond setup.impactSpeed =
      ‖velocityInMetersPerSecond setup.impactVelocity‖

/-! ## Exact result and displayed answer choices -/

/-
The unrounded SI speed obtained by combining horizontal-velocity conservation,
the vertical constant-gravity relation, and the Euclidean norm.  This closed
scalar expression uses only stated/calibrated data; the independent physical
field `setup.impactSpeed` is not defined to equal it.
-/
noncomputable def exactImpactSpeedInMetersPerSecond : ℝ :=
  Real.sqrt
    ((18.0 : ℝ) ^ 2 + 2 * (9.80 : ℝ) * (50.0 : ℝ))

/-- Labels of the four speed choices printed with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Speed in metres per second printed beside each displayed choice. -/
def AnswerChoice.speedMetersPerSecond : AnswerChoice → ℝ
  | .A => 28.4
  | .B => 31.6
  | .C => 36.1
  | .D => 38.3

/-- The answer label recorded by the supplied dataset metadata. -/
def recordedAnswerChoice : AnswerChoice := .C

/-- Absolute error between the modeled impact speed and a displayed choice. -/
def answerChoiceErrorMetersPerSecond
    (setup : HorizontalCliffProjectileSetup) (choice : AnswerChoice) : ℝ :=
  |speedInMetersPerSecond setup.impactSpeed - choice.speedMetersPerSecond|

/-- Agreement with a speed displayed to the nearest tenth of a metre per second. -/
def MatchesDisplayedImpactSpeed
    (setup : HorizontalCliffProjectileSetup) (choice : AnswerChoice) : Prop :=
  answerChoiceErrorMetersPerSecond setup choice ≤ (1 : ℝ) / 20

/-- A displayed choice is strictly closer to the modeled speed than all others. -/
def IsUniqueClosestImpactSpeedChoice
    (setup : HorizontalCliffProjectileSetup) (choice : AnswerChoice) : Prop :=
  ∀ other, other ≠ choice →
    answerChoiceErrorMetersPerSecond setup choice <
      answerChoiceErrorMetersPerSecond setup other

/-- The governing laws determine the exact, unrounded impact-speed readout. -/
lemma impactSpeed_eq_exactExpression
    (setup : HorizontalCliffProjectileSetup)
    (_figure : MatchesPrimaryFigure setup)
    (_description : MatchesProblemDescription setup)
    (_gravity : UsesStandardNearEarthGravity setup)
    (_physical : HasPhysicalProjectileParameters setup)
    (_laws : SatisfiesUniformGravityProjectileLaws setup) :
    speedInMetersPerSecond setup.impactSpeed =
      exactImpactSpeedInMetersPerSecond := by
  have hPositionY :=
    congrArg (fun v : EuclideanSpace ℝ (Fin 2) => v yAxis)
      _laws.positionAtImpact
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul] at hPositionY
  rw [_description.launchVelocityYMetersPerSecond,
    _gravity.downwardGravityMetersPerSecondSquared] at hPositionY
  have hTimeSq :
      timeInSeconds setup.flightTime ^ 2 = (500 / 49 : ℝ) := by
    nlinarith [_description.launchIsHeightAboveImpact,
      _description.cliffHeightMeters]
  have hVelocityX :=
    congrArg (fun v : EuclideanSpace ℝ (Fin 2) => v xAxis)
      _laws.velocityAtImpact
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul] at hVelocityX
  rw [_description.launchVelocityXMetersPerSecond,
    _gravity.noHorizontalGravity] at hVelocityX
  norm_num [xAxis] at hVelocityX
  have hVelocityY :=
    congrArg (fun v : EuclideanSpace ℝ (Fin 2) => v yAxis)
      _laws.velocityAtImpact
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul] at hVelocityY
  rw [_description.launchVelocityYMetersPerSecond,
    _gravity.downwardGravityMetersPerSecondSquared] at hVelocityY
  norm_num [yAxis] at hVelocityY
  calc
    speedInMetersPerSecond setup.impactSpeed =
        ‖velocityInMetersPerSecond setup.impactVelocity‖ :=
      _laws.impactSpeedIsVelocityNorm
    _ = Real.sqrt
          ((18.0 : ℝ) ^ 2 +
            (9.80 * timeInSeconds setup.flightTime) ^ 2) := by
      rw [EuclideanSpace.norm_eq, Fin.sum_univ_two]
      simp only [Real.norm_eq_abs, sq_abs]
      rw [hVelocityX, hVelocityY]
      norm_num
      ring_nf
    _ = exactImpactSpeedInMetersPerSecond := by
      unfold exactImpactSpeedInMetersPerSecond
      norm_num
      apply congrArg Real.sqrt
      nlinarith [hTimeSq]

/-!
The exact expression is approximately `36.11 m/s`; hence it rounds to the
displayed value `36.1 m/s` and is closer to choice C than to the other choices.
-/
lemma exactImpactSpeed_selects_choice_C
    (setup : HorizontalCliffProjectileSetup)
    (hExact : speedInMetersPerSecond setup.impactSpeed =
      exactImpactSpeedInMetersPerSecond) :
    MatchesDisplayedImpactSpeed setup .C ∧
      IsUniqueClosestImpactSpeedChoice setup .C := by
  have hSqrtSq : Real.sqrt (1304 : ℝ) ^ 2 = 1304 :=
    Real.sq_sqrt (by norm_num)
  have hSqrtNonnegative : 0 ≤ Real.sqrt (1304 : ℝ) :=
    Real.sqrt_nonneg _
  have hSqrtLower : (36.1 : ℝ) < Real.sqrt 1304 := by
    nlinarith only [hSqrtSq, hSqrtNonnegative]
  have hSqrtUpper : Real.sqrt (1304 : ℝ) < 36.15 := by
    nlinarith only [hSqrtSq, hSqrtNonnegative]
  have hExactValue :
      exactImpactSpeedInMetersPerSecond = Real.sqrt 1304 := by
    norm_num [exactImpactSpeedInMetersPerSecond]
  constructor
  · simp only [MatchesDisplayedImpactSpeed,
      answerChoiceErrorMetersPerSecond, AnswerChoice.speedMetersPerSecond,
      hExact, hExactValue]
    rw [abs_of_pos (sub_pos.mpr hSqrtLower)]
    linarith
  · intro other hOther
    fin_cases other
    · simp only [answerChoiceErrorMetersPerSecond,
        AnswerChoice.speedMetersPerSecond, hExact, hExactValue]
      rw [abs_of_pos (sub_pos.mpr hSqrtLower)]
      rw [abs_of_pos
        (by linarith : Real.sqrt 1304 - (28.4 : ℝ) > 0)]
      norm_num
    · simp only [answerChoiceErrorMetersPerSecond,
        AnswerChoice.speedMetersPerSecond, hExact, hExactValue]
      rw [abs_of_pos (sub_pos.mpr hSqrtLower)]
      rw [abs_of_pos
        (by linarith : Real.sqrt 1304 - (31.6 : ℝ) > 0)]
      norm_num
    · exact (hOther rfl).elim
    · simp only [answerChoiceErrorMetersPerSecond,
        AnswerChoice.speedMetersPerSecond, hExact, hExactValue]
      rw [abs_of_pos (sub_pos.mpr hSqrtLower)]
      rw [abs_of_neg
        (by linarith : Real.sqrt 1304 - (38.3 : ℝ) < 0)]
      linarith

/-!
The stone lands at the exact unrounded speed
`sqrt (18^2 + 2 * 9.8 * 50) m/s`, which is displayed as `36.1 m/s`, answer C.

Blueprint: `thm:physics:phyx_mini_0686:target`.
-/
theorem problem_phyx_mini_0686
    (setup : HorizontalCliffProjectileSetup)
    (_figure : MatchesPrimaryFigure setup)
    (_description : MatchesProblemDescription setup)
    (_gravity : UsesStandardNearEarthGravity setup)
    (_physical : HasPhysicalProjectileParameters setup)
    (_laws : SatisfiesUniformGravityProjectileLaws setup) :
    speedInMetersPerSecond setup.impactSpeed =
        exactImpactSpeedInMetersPerSecond ∧
      MatchesDisplayedImpactSpeed setup .C ∧
      IsUniqueClosestImpactSpeedChoice setup .C := by
  have hExact :=
    impactSpeed_eq_exactExpression setup _figure _description
      _gravity _physical _laws
  exact ⟨hExact, exactImpactSpeed_selects_choice_C setup hExact⟩

end PhyXMiniProblems.ProblemPhyXMini0686
