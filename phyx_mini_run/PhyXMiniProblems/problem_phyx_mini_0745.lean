import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle
import Physlib.Units.WithDim.Speed

/- USER: The assigned source file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0745

open Dimension

/-!
# Initial speed of a ball landing on a roof

A ball is launched from the reference level and lands on a horizontal roof
`4.00 s` later, `20.0 m` above its release point.  Immediately before impact
its down-and-right velocity makes a `60.0 degree` acute angle with the roof.
The supplied image also labels the horizontal launch-to-building distance by
`d` and the roof height by `h`.

Lengths, elapsed time, scalar speed, vector position, vector velocity, and
vector acceleration are represented by unit-independent Physlib quantities.
Real numbers occur only as coherent-unit readouts, schematic drawing
coordinates, dimensionless angle representatives, and displayed answer
values.

Assumption/target split:

* governing laws: endpoint position and velocity equations for constant
  gravitational acceleration, the norm relation between velocity and speed,
  and the geometric relation between the landing velocity and its angle with
  a horizontal roof;
* previous-part results: none;
* figure/data readouts: elapsed time `4.00 s`, height `h = 20.0 m`, landing
  angle `theta = 60.0 degrees`, the horizontal distance `d`, a horizontal
  roof and reference line, the building, dashed parabolic trajectory, and the
  down-and-right landing tangent;
* current target conclusions: the exact initial-speed expression, agreement
  with `26.0 m/s` to the displayed precision, and unique selection of choice
  C.
-/

/-! ## Dimensionful quantities and coherent-unit readouts -/

/-- The physical dimension of velocity, `L T^-1`. -/
def velocityDimension : Dimension := L𝓭 * T𝓭⁻¹

/-- The physical dimension of acceleration, `L T^-2`. -/
def accelerationDimension : Dimension := L𝓭 * T𝓭⁻¹ * T𝓭⁻¹

/-- A nonnegative physical length, used for the labels `h` and `d`. -/
abbrev LengthQuantity : Type := Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative physical elapsed time. -/
abbrev TimeQuantity : Type := Dimensionful (WithDim T𝓭 NNReal)

/-- A signed planar position vector. -/
abbrev PlanarPositionQuantity : Type :=
  Dimensionful (WithDim L𝓭 (EuclideanSpace ℝ (Fin 2)))

/-- A signed planar velocity vector. -/
abbrev PlanarVelocityQuantity : Type :=
  Dimensionful
    (WithDim velocityDimension (EuclideanSpace ℝ (Fin 2)))

/-- A signed planar acceleration vector. -/
abbrev PlanarAccelerationQuantity : Type :=
  Dimensionful
    (WithDim accelerationDimension (EuclideanSpace ℝ (Fin 2)))

/-- The coordinate index pointing horizontally to the right. -/
def xAxis : Fin 2 := 0

/-- The coordinate index pointing vertically upward. -/
def yAxis : Fin 2 := 1

/-- Read a nonnegative physical scalar in a coherent unit system. -/
def nonnegativeReadout {dimension : Dimension}
    (units : UnitChoices)
    (quantity : Dimensionful (WithDim dimension NNReal)) : ℝ :=
  ((quantity units).val : ℝ)

/-- Read a dimensionful planar vector in a coherent unit system. -/
def vectorReadout {dimension : Dimension}
    (units : UnitChoices)
    (quantity : Dimensionful
      (WithDim dimension (EuclideanSpace ℝ (Fin 2)))) :
    EuclideanSpace ℝ (Fin 2) :=
  (quantity units).val

/-- Metre readout of a nonnegative physical length. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  nonnegativeReadout UnitChoices.SI length

/-- Second readout of a physical elapsed time. -/
def timeInSeconds (time : TimeQuantity) : ℝ :=
  nonnegativeReadout UnitChoices.SI time

/-- Metres-per-second readout of a physical scalar speed. -/
def speedInMetersPerSecond (speed : DimSpeed) : ℝ :=
  ((speed UnitChoices.SI).val : ℝ)

/-- Cartesian position readout in metres. -/
def positionInMeters (position : PlanarPositionQuantity) :
    EuclideanSpace ℝ (Fin 2) :=
  vectorReadout UnitChoices.SI position

/-- Cartesian velocity readout in metres per second. -/
def velocityInMetersPerSecond (velocity : PlanarVelocityQuantity) :
    EuclideanSpace ℝ (Fin 2) :=
  vectorReadout UnitChoices.SI velocity

/-- Cartesian acceleration readout in metres per second squared. -/
def accelerationInMetersPerSecondSquared
    (acceleration : PlanarAccelerationQuantity) :
    EuclideanSpace ℝ (Fin 2) :=
  vectorReadout UnitChoices.SI acceleration

/-- Convert a degree readout to an angle modulo `2 * pi`. -/
noncomputable def degrees (value : ℝ) : Real.Angle :=
  ((value * Real.pi / 180 : ℝ) : Real.Angle)

/-! ## Physical roles and primary-image transcription -/

/-- The idealized projectile model intended by the kinematics problem. -/
inductive ProjectileModel where
  | constantGravityNegligibleDrag
  deriving DecidableEq, Repr

/-- The projectile named in the prose. -/
inductive ProjectileKind where
  | ball
  deriving DecidableEq, Repr

/-- The surface on which the ball lands. -/
inductive LandingSurface where
  | horizontalRoof
  deriving DecidableEq, Repr

/-- Geometrically significant points in image `745.png`. -/
inductive FigurePoint where
  | launchPoint
  | buildingBase
  | roofLandingPoint
  | roofRightEnd
  deriving DecidableEq, Fintype, Repr

/-- Literal symbolic labels shown in the supplied image. -/
inductive FigureLabel where
  | heightH
  | distanceD
  | landingAngleTheta
  deriving DecidableEq, Fintype, Repr

/-- Visible components retained from the primary bitmap. -/
inductive FigureElement where
  | building
  | windows
  | horizontalReferenceLine
  | horizontalRoof
  | dashedParabolicTrajectory
  | landingTangentLine
  deriving DecidableEq, Fintype, Repr

/-- Qualitative directions of the two trajectory segments shown by arrows. -/
inductive ArrowDirection where
  | upRight
  | downRight
  deriving DecidableEq, Repr

/-!
Schematic coordinates and incidences transcribed from the raster image.
These coordinates describe the drawing and are not calibrated metre readouts.
-/
structure RoofProjectileFigure where
  horizontalCoordinate : FigurePoint → ℝ
  verticalCoordinate : FigurePoint → ℝ
  showsElement : FigureElement → Bool
  showsLabel : FigureLabel → Bool
  launchSegmentDirection : ArrowDirection
  landingSegmentDirection : ArrowDirection
  heightLabelEndpoints : FigurePoint × FigurePoint
  distanceLabelEndpoints : FigurePoint × FigurePoint
  angleLabelVertex : FigurePoint
  angleIsBetweenLandingTangentAndRoof : Bool

/-!
Independent physical quantities of the launch-and-landing experiment.  The
initial speed is a genuine dimensionful observable; it is not defined from an
answer choice or from the solved numerical expression below.
-/
structure RoofLandingProjectileSetup where
  model : ProjectileModel
  projectileKind : ProjectileKind
  landingSurface : LandingSurface
  launchPosition : PlanarPositionQuantity
  landingPosition : PlanarPositionQuantity
  roofHeight : LengthQuantity
  horizontalDistance : LengthQuantity
  elapsedFlightTime : TimeQuantity
  initialVelocity : PlanarVelocityQuantity
  landingVelocity : PlanarVelocityQuantity
  initialSpeed : DimSpeed
  gravitationalAcceleration : PlanarAccelerationQuantity
  landingPathAngle : Real.Angle
  figure : RoofProjectileFigure

/-! ## Problem readouts, figure evidence, and physical branch -/

/-!
The numerical data and physical incidences stated in the prose.  The final two
equations identify `h` and `d` as the vertical and horizontal displacements
from release to the roof.  No clause constrains the unknown initial speed.
-/
structure MatchesProblemDescription
    (setup : RoofLandingProjectileSetup) : Prop where
  idealProjectileModel : setup.model = .constantGravityNegligibleDrag
  projectileIsBall : setup.projectileKind = .ball
  landsOnHorizontalRoof : setup.landingSurface = .horizontalRoof
  elapsedTimeSeconds : timeInSeconds setup.elapsedFlightTime = 4
  roofHeightMeters : lengthInMeters setup.roofHeight = 20
  landingAngleDegrees : setup.landingPathAngle = degrees 60
  verticalDisplacementIsHeight :
    positionInMeters setup.landingPosition yAxis -
        positionInMeters setup.launchPosition yAxis =
      lengthInMeters setup.roofHeight
  horizontalDisplacementIsDistance :
    positionInMeters setup.landingPosition xAxis -
        positionInMeters setup.launchPosition xAxis =
      lengthInMeters setup.horizontalDistance

/-!
Primary-image evidence: launch and building base share the dashed reference
level, the landing point and roof share a horizontal level, the building base
is directly under the landing point, and the labelled spans are `h` and `d`.
-/
structure MatchesPrimaryFigure
    (setup : RoofLandingProjectileSetup) : Prop where
  everyElementShown : ∀ element, setup.figure.showsElement element = true
  everyLabelShown : ∀ label, setup.figure.showsLabel label = true
  launchIsLeftOfBuilding :
    setup.figure.horizontalCoordinate .launchPoint <
      setup.figure.horizontalCoordinate .buildingBase
  launchAndBuildingBaseShareReferenceLevel :
    setup.figure.verticalCoordinate .launchPoint =
      setup.figure.verticalCoordinate .buildingBase
  buildingBaseDirectlyBelowLanding :
    setup.figure.horizontalCoordinate .buildingBase =
      setup.figure.horizontalCoordinate .roofLandingPoint
  landingIsAboveBuildingBase :
    setup.figure.verticalCoordinate .buildingBase <
      setup.figure.verticalCoordinate .roofLandingPoint
  roofIsHorizontal :
    setup.figure.verticalCoordinate .roofLandingPoint =
      setup.figure.verticalCoordinate .roofRightEnd
  roofExtendsRightward :
    setup.figure.horizontalCoordinate .roofLandingPoint <
      setup.figure.horizontalCoordinate .roofRightEnd
  launchArrowPointsUpAndRight :
    setup.figure.launchSegmentDirection = .upRight
  landingArrowPointsDownAndRight :
    setup.figure.landingSegmentDirection = .downRight
  heightLabelRunsFromBaseToRoof :
    setup.figure.heightLabelEndpoints =
      (.buildingBase, .roofLandingPoint)
  distanceLabelRunsFromLaunchToBuilding :
    setup.figure.distanceLabelEndpoints =
      (.launchPoint, .buildingBase)
  angleLabelIsAtLanding :
    setup.figure.angleLabelVertex = .roofLandingPoint
  angleIsTangentToRoof :
    setup.figure.angleIsBetweenLandingTangentAndRoof = true

/-- The standard near-Earth gravitational acceleration used by the answer key. -/
structure UsesStandardNearEarthGravity
    (setup : RoofLandingProjectileSetup) : Prop where
  noHorizontalAcceleration :
    accelerationInMetersPerSecondSquared
        setup.gravitationalAcceleration xAxis = 0
  downwardAccelerationMetersPerSecondSquared :
    accelerationInMetersPerSecondSquared
        setup.gravitationalAcceleration yAxis = -(49 / 5)

/-!
Positivity and direction conditions select the physical branch drawn in the
figure.  They contain no numerical conclusion about the initial speed.
-/
structure HasPhysicalProjectileParameters
    (setup : RoofLandingProjectileSetup) : Prop where
  roofHeightPositive : 0 < lengthInMeters setup.roofHeight
  horizontalDistancePositive : 0 < lengthInMeters setup.horizontalDistance
  elapsedTimePositive : 0 < timeInSeconds setup.elapsedFlightTime
  launchMovesRight :
    0 < velocityInMetersPerSecond setup.initialVelocity xAxis
  launchMovesUp :
    0 < velocityInMetersPerSecond setup.initialVelocity yAxis
  landingMovesRight :
    0 < velocityInMetersPerSecond setup.landingVelocity xAxis
  landingMovesDown :
    velocityInMetersPerSecond setup.landingVelocity yAxis < 0
  measuredAngleHasPositiveTangent :
    0 < Real.Angle.tan setup.landingPathAngle

/-! ## Governing constant-gravity laws -/

/-!
The two endpoint kinematic equations hold in every coherent unit system.  The
third law identifies scalar speed with the Euclidean norm of velocity.  The
last law says that, for the selected down-and-right branch, the magnitude of
the vertical landing component is `tan(theta)` times its horizontal component.
None of these general laws contains `26`, a displayed choice, or the solved
initial-speed formula.
-/
structure SatisfiesUniformGravityProjectileLaws
    (setup : RoofLandingProjectileSetup) : Prop where
  positionAtLanding : ∀ units : UnitChoices,
    vectorReadout units setup.landingPosition =
      vectorReadout units setup.launchPosition +
        nonnegativeReadout units setup.elapsedFlightTime •
          vectorReadout units setup.initialVelocity +
        ((1 / 2 : ℝ) *
            nonnegativeReadout units setup.elapsedFlightTime ^ 2) •
          vectorReadout units setup.gravitationalAcceleration
  velocityAtLanding : ∀ units : UnitChoices,
    vectorReadout units setup.landingVelocity =
      vectorReadout units setup.initialVelocity +
        nonnegativeReadout units setup.elapsedFlightTime •
          vectorReadout units setup.gravitationalAcceleration
  initialSpeedIsVelocityNorm : ∀ units : UnitChoices,
    nonnegativeReadout units setup.initialSpeed =
      ‖vectorReadout units setup.initialVelocity‖
  landingDirectionMakesMeasuredAngleWithRoof : ∀ units : UnitChoices,
    -(vectorReadout units setup.landingVelocity yAxis) =
      vectorReadout units setup.landingVelocity xAxis *
        Real.Angle.tan setup.landingPathAngle

/-! ## Exact calculation and displayed answer -/

/-!
The exact unrounded SI speed determined by `h = 20`, `t = 4`,
`g = 9.8`, and the `60 degree` landing direction.  Its local components are
named to expose the calculation rather than to define the physical observable.
-/
noncomputable def computedInitialSpeedInMetersPerSecond : ℝ :=
  let flightTime : ℝ := 4
  let height : ℝ := 20
  let gravity : ℝ := 49 / 5
  let landingAngle : Real.Angle := degrees 60
  let initialVerticalSpeed : ℝ :=
    height / flightTime + gravity * flightTime / 2
  let landingDownwardSpeed : ℝ :=
    gravity * flightTime - initialVerticalSpeed
  let horizontalSpeed : ℝ :=
    landingDownwardSpeed / Real.Angle.tan landingAngle
  Real.sqrt (horizontalSpeed ^ 2 + initialVerticalSpeed ^ 2)

/-- The constant-gravity and landing-angle laws determine the exact speed. -/
lemma initialSpeed_eq_computedExpression
    (setup : RoofLandingProjectileSetup)
    (_description : MatchesProblemDescription setup)
    (_gravity : UsesStandardNearEarthGravity setup)
    (_physical : HasPhysicalProjectileParameters setup)
    (_laws : SatisfiesUniformGravityProjectileLaws setup) :
    speedInMetersPerSecond setup.initialSpeed =
      computedInitialSpeedInMetersPerSecond := by
  have ht :
      nonnegativeReadout UnitChoices.SI setup.elapsedFlightTime = 4 :=
    _description.elapsedTimeSeconds
  have hh :
      nonnegativeReadout UnitChoices.SI setup.roofHeight = 20 :=
    _description.roofHeightMeters
  have hay :
      vectorReadout UnitChoices.SI setup.gravitationalAcceleration yAxis =
        -(49 / 5) :=
    _gravity.downwardAccelerationMetersPerSecondSquared
  have hax :
      vectorReadout UnitChoices.SI setup.gravitationalAcceleration xAxis = 0 :=
    _gravity.noHorizontalAcceleration
  have hdisp :
      vectorReadout UnitChoices.SI setup.landingPosition yAxis -
          vectorReadout UnitChoices.SI setup.launchPosition yAxis =
        20 := by
    calc
      _ = nonnegativeReadout UnitChoices.SI setup.roofHeight :=
        _description.verticalDisplacementIsHeight
      _ = 20 := hh
  have hposY :=
    congrArg (fun v => v yAxis)
      (_laws.positionAtLanding UnitChoices.SI)
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul] at hposY
  have hviY :
      vectorReadout UnitChoices.SI setup.initialVelocity yAxis =
        (123 / 5 : ℝ) := by
    rw [ht, hay] at hposY
    nlinarith [hdisp]
  have hvelY :=
    congrArg (fun v => v yAxis)
      (_laws.velocityAtLanding UnitChoices.SI)
  have hvelX :=
    congrArg (fun v => v xAxis)
      (_laws.velocityAtLanding UnitChoices.SI)
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul] at hvelY hvelX
  rw [ht, hay, hviY] at hvelY
  rw [ht, hax] at hvelX
  norm_num at hvelY hvelX
  have hdir :=
    _laws.landingDirectionMakesMeasuredAngleWithRoof UnitChoices.SI
  rw [_description.landingAngleDegrees, hvelY, hvelX] at hdir
  have htan : 0 < Real.Angle.tan (degrees 60) := by
    simpa [_description.landingAngleDegrees] using
      _physical.measuredAngleHasPositiveTangent
  have hviX :
      vectorReadout UnitChoices.SI setup.initialVelocity xAxis =
        (73 / 5 : ℝ) / Real.Angle.tan (degrees 60) := by
    apply (eq_div_iff (ne_of_gt htan)).2
    nlinarith [hdir]
  have hspeed :
      speedInMetersPerSecond setup.initialSpeed =
        ‖vectorReadout UnitChoices.SI setup.initialVelocity‖ :=
    _laws.initialSpeedIsVelocityNorm UnitChoices.SI
  rw [hspeed, EuclideanSpace.norm_eq]
  simp only [Fin.sum_univ_two, Real.norm_eq_abs, sq_abs]
  change Real.sqrt (_ ^ 2 + _ ^ 2) = _
  rw [show vectorReadout UnitChoices.SI setup.initialVelocity (0 : Fin 2) =
        (73 / 5 : ℝ) / Real.Angle.tan (degrees 60) by
      simpa [xAxis] using hviX]
  rw [show vectorReadout UnitChoices.SI setup.initialVelocity (1 : Fin 2) =
        (123 / 5 : ℝ) by
      simpa [yAxis] using hviY]
  norm_num [computedInitialSpeedInMetersPerSecond]

/-- Labels of the four initial-speed choices printed by the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Metres-per-second value printed beside an answer label. -/
def AnswerChoice.speedInMetersPerSecond : AnswerChoice → ℝ
  | .A => 20
  | .B => 23
  | .C => 26
  | .D => 29

/-- The answer label recorded by the supplied dataset metadata. -/
def recordedAnswerChoice : AnswerChoice := .C

/-- Error between the physical initial speed and a displayed answer. -/
def answerChoiceErrorInMetersPerSecond
    (setup : RoofLandingProjectileSetup) (choice : AnswerChoice) : ℝ :=
  |speedInMetersPerSecond setup.initialSpeed - choice.speedInMetersPerSecond|

/-- Agreement with a speed displayed to the nearest tenth of a metre per second. -/
def MatchesDisplayedInitialSpeed
    (setup : RoofLandingProjectileSetup) (choice : AnswerChoice) : Prop :=
  answerChoiceErrorInMetersPerSecond setup choice ≤ (1 : ℝ) / 20

/-- A displayed choice is strictly closer than every other printed choice. -/
def IsUniqueClosestInitialSpeedChoice
    (setup : RoofLandingProjectileSetup) (choice : AnswerChoice) : Prop :=
  ∀ other, other ≠ choice →
    answerChoiceErrorInMetersPerSecond setup choice <
      answerChoiceErrorInMetersPerSecond setup other

/-!
The exact value is approximately `26.004 m/s`; hence it agrees with the
displayed `26.0 m/s` and uniquely selects answer C.

This formalizes `thm:physics:phyx_mini_0745:target`.
-/
theorem problem_phyx_mini_0745
    (setup : RoofLandingProjectileSetup)
    (_description : MatchesProblemDescription setup)
    (_figure : MatchesPrimaryFigure setup)
    (_gravity : UsesStandardNearEarthGravity setup)
    (_physical : HasPhysicalProjectileParameters setup)
    (_laws : SatisfiesUniformGravityProjectileLaws setup) :
    speedInMetersPerSecond setup.initialSpeed =
        computedInitialSpeedInMetersPerSecond ∧
      MatchesDisplayedInitialSpeed setup .C ∧
      IsUniqueClosestInitialSpeedChoice setup .C := by
  have htan : Real.Angle.tan (degrees 60) = Real.sqrt 3 := by
    rw [degrees, Real.Angle.tan_coe]
    rw [show (60 : ℝ) * Real.pi / 180 = Real.pi / 3 by ring]
    exact Real.tan_pi_div_three
  have hsqrt3pos : 0 < Real.sqrt 3 :=
    Real.sqrt_pos.2 (by norm_num)
  have hsqrt3sq : Real.sqrt 3 ^ 2 = 3 :=
    Real.sq_sqrt (by norm_num)
  have hcomputed :
      computedInitialSpeedInMetersPerSecond = Real.sqrt (50716 / 75) := by
    dsimp [computedInitialSpeedInMetersPerSecond]
    rw [htan]
    congr 1
    norm_num
    field_simp [ne_of_gt hsqrt3pos]
    nlinarith [hsqrt3sq]
  have hlower : (26 : ℝ) < Real.sqrt (50716 / 75) := by
    rw [Real.lt_sqrt (by norm_num)]
    norm_num
  have hupper : Real.sqrt (50716 / 75) < (521 / 20 : ℝ) := by
    rw [Real.sqrt_lt (by norm_num) (by norm_num)]
    norm_num
  have hspeed :=
    initialSpeed_eq_computedExpression setup _description _gravity
      _physical _laws
  have hspeedLower :
      (26 : ℝ) < speedInMetersPerSecond setup.initialSpeed := by
    rw [hspeed, hcomputed]
    exact hlower
  have hspeedUpper :
      speedInMetersPerSecond setup.initialSpeed < (521 / 20 : ℝ) := by
    rw [hspeed, hcomputed]
    exact hupper
  refine ⟨hspeed, ?_, ?_⟩
  · unfold MatchesDisplayedInitialSpeed answerChoiceErrorInMetersPerSecond
    simp only [AnswerChoice.speedInMetersPerSecond]
    rw [abs_of_nonneg (by nlinarith [hspeedLower])]
    nlinarith [hspeedUpper]
  · intro other hother
    unfold answerChoiceErrorInMetersPerSecond
    fin_cases other
    · simp only [AnswerChoice.speedInMetersPerSecond]
      rw [abs_of_nonneg (by nlinarith [hspeedLower])]
      rw [abs_of_nonneg (by nlinarith [hspeedLower])]
      nlinarith
    · simp only [AnswerChoice.speedInMetersPerSecond]
      rw [abs_of_nonneg (by nlinarith [hspeedLower])]
      rw [abs_of_nonneg (by nlinarith [hspeedLower])]
      nlinarith
    · exact (hother rfl).elim
    · simp only [AnswerChoice.speedInMetersPerSecond]
      rw [abs_of_nonneg (by nlinarith [hspeedLower])]
      rw [abs_of_nonpos (by nlinarith [hspeedUpper])]
      nlinarith [hspeedUpper]

end PhyXMiniProblems.ProblemPhyXMini0745
