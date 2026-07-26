import Mathlib
import Physlib.Units.WithDim.Speed

/- USER: The assigned source file did not exist when this autoformalization task began. -/

/-!
# Package landing in a moving shipping cart

An open `50.0 kg` cart rolls left at `5.00 m/s` on a frictionless horizontal
floor.  A `15.0 kg` package leaves a chute at `3.00 m/s`, directed down and to
the right along a line inclined by `37 degrees` to the horizontal.  The chute
exit is `4.00 m` above the bottom of the cart.  After its projectile flight the
package lands in the cart and the two bodies roll together.

Masses, lengths, times, scalar speeds, signed horizontal velocities, planar
positions, planar velocities, and planar accelerations are unit-independent
Physlib quantities.  Real values occur only at coherent-unit readout
boundaries, for the dimensionless angle in degrees, for schematic figure
coordinates, and for displayed answer values.

Assumption/target split:

* governing laws: decomposition of the chute-exit velocity, constant-gravity
  projectile kinematics, absence of horizontal gravitational acceleration,
  horizontal momentum conservation during capture, and the generic relation
  between signed final velocity and speed magnitude;
* previous-part results: none;
* figure/data readouts: masses `50.0 kg` and `15.0 kg`, speeds `5.00 m/s` and
  `3.00 m/s`, chute angle `37 degrees`, height `4.00 m`, and the arrows and
  geometry transcribed from image `768.png`;
* current target conclusions: the exact final-speed expression, its rounding
  to `3.29 m/s`, and the unique selection of answer choice B.
-/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0768

open Dimension

/-! ## Dimensionful quantities and coherent-unit readouts -/

/-- The physical dimension of velocity, `L T⁻¹`. -/
def velocityDimension : Dimension := L𝓭 * T𝓭⁻¹

/-- The physical dimension of acceleration, `L T⁻²`. -/
def accelerationDimension : Dimension := L𝓭 * T𝓭⁻¹ * T𝓭⁻¹

/-- A nonnegative physical mass, independent of the chosen unit system. -/
abbrev MassQuantity : Type := Dimensionful (WithDim M𝓭 NNReal)

/-- A nonnegative physical length. -/
abbrev LengthQuantity : Type := Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative physical duration. -/
abbrev TimeQuantity : Type := Dimensionful (WithDim T𝓭 NNReal)

/-- A nonnegative physical speed magnitude. -/
abbrev SpeedQuantity : Type := DimSpeed

/-- A signed velocity component along the horizontal floor. -/
abbrev SignedVelocityQuantity : Type :=
  Dimensionful (WithDim velocityDimension ℝ)

/-- A signed physical position vector in the plane of the figure. -/
abbrev PlanarPositionQuantity : Type :=
  Dimensionful (WithDim L𝓭 (EuclideanSpace ℝ (Fin 2)))

/-- A signed physical velocity vector in the plane of the figure. -/
abbrev PlanarVelocityQuantity : Type :=
  Dimensionful
    (WithDim velocityDimension (EuclideanSpace ℝ (Fin 2)))

/-- A signed physical acceleration vector in the plane of the figure. -/
abbrev PlanarAccelerationQuantity : Type :=
  Dimensionful
    (WithDim accelerationDimension (EuclideanSpace ℝ (Fin 2)))

/-- Coordinate `0`, horizontal and positive to the right. -/
def xAxis : Fin 2 := 0

/-- Coordinate `1`, vertical and positive upward. -/
def yAxis : Fin 2 := 1

/-- Read a nonnegative dimensionful scalar in a coherent unit system. -/
def nonnegativeReadout {dimension : Dimension}
    (units : UnitChoices)
    (quantity : Dimensionful (WithDim dimension NNReal)) : ℝ :=
  ((quantity units).val : ℝ)

/-- Read a signed dimensionful scalar in a coherent unit system. -/
def signedReadout {dimension : Dimension}
    (units : UnitChoices)
    (quantity : Dimensionful (WithDim dimension ℝ)) : ℝ :=
  (quantity units).val

/-- Read a dimensionful planar vector in a coherent unit system. -/
def planarVectorReadout {dimension : Dimension}
    (units : UnitChoices)
    (quantity : Dimensionful
      (WithDim dimension (EuclideanSpace ℝ (Fin 2)))) :
    EuclideanSpace ℝ (Fin 2) :=
  (quantity units).val

/-- Read a physical mass in a selected mass unit. -/
def massReadout (unit : MassUnit) (mass : MassQuantity) : ℝ :=
  nonnegativeReadout {UnitChoices.SI with mass := unit} mass

/-- Read a physical length in a selected length unit. -/
def lengthReadout (unit : LengthUnit) (length : LengthQuantity) : ℝ :=
  nonnegativeReadout {UnitChoices.SI with length := unit} length

/-- Read a physical duration in a selected time unit. -/
def timeReadout (unit : TimeUnit) (time : TimeQuantity) : ℝ :=
  nonnegativeReadout {UnitChoices.SI with time := unit} time

/-- Read a speed in coherent selected length and time units. -/
def speedReadout
    (lengthUnit : LengthUnit) (timeUnit : TimeUnit)
    (speed : SpeedQuantity) : ℝ :=
  nonnegativeReadout
    {UnitChoices.SI with length := lengthUnit, time := timeUnit} speed

/-- Read a signed velocity in coherent selected length and time units. -/
def signedVelocityReadout
    (lengthUnit : LengthUnit) (timeUnit : TimeUnit)
    (velocity : SignedVelocityQuantity) : ℝ :=
  signedReadout
    {UnitChoices.SI with length := lengthUnit, time := timeUnit} velocity

/-- Read a planar position in a selected length unit. -/
def positionVectorReadout
    (lengthUnit : LengthUnit) (position : PlanarPositionQuantity) :
    EuclideanSpace ℝ (Fin 2) :=
  planarVectorReadout
    {UnitChoices.SI with length := lengthUnit} position

/-- Read a planar velocity in coherent selected length and time units. -/
def velocityVectorReadout
    (lengthUnit : LengthUnit) (timeUnit : TimeUnit)
    (velocity : PlanarVelocityQuantity) :
    EuclideanSpace ℝ (Fin 2) :=
  planarVectorReadout
    {UnitChoices.SI with length := lengthUnit, time := timeUnit} velocity

/-- Read a planar acceleration in coherent selected length and time units. -/
def accelerationVectorReadout
    (lengthUnit : LengthUnit) (timeUnit : TimeUnit)
    (acceleration : PlanarAccelerationQuantity) :
    EuclideanSpace ℝ (Fin 2) :=
  planarVectorReadout
    {UnitChoices.SI with length := lengthUnit, time := timeUnit} acceleration

/-- Kilogram readout used in the stated data and final calculation. -/
def massInKilograms (mass : MassQuantity) : ℝ :=
  massReadout MassUnit.kilograms mass

/-- Metre readout used for the displayed vertical separation. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.meters length

/-- Second readout of the package flight time. -/
def timeInSeconds (time : TimeQuantity) : ℝ :=
  timeReadout TimeUnit.seconds time

/-- Metres-per-second readout of a scalar speed. -/
def speedInMetersPerSecond (speed : SpeedQuantity) : ℝ :=
  speedReadout LengthUnit.meters TimeUnit.seconds speed

/-- Metres-per-second readout of a signed horizontal velocity. -/
def signedVelocityInMetersPerSecond
    (velocity : SignedVelocityQuantity) : ℝ :=
  signedVelocityReadout LengthUnit.meters TimeUnit.seconds velocity

/-- Cartesian metre readout of a planar position. -/
def positionInMeters (position : PlanarPositionQuantity) :
    EuclideanSpace ℝ (Fin 2) :=
  positionVectorReadout LengthUnit.meters position

/-- Cartesian metres-per-second readout of a planar velocity. -/
def velocityInMetersPerSecond (velocity : PlanarVelocityQuantity) :
    EuclideanSpace ℝ (Fin 2) :=
  velocityVectorReadout LengthUnit.meters TimeUnit.seconds velocity

/-- Cartesian metres-per-second-squared readout of a planar acceleration. -/
def accelerationInMetersPerSecondSquared
    (acceleration : PlanarAccelerationQuantity) :
    EuclideanSpace ℝ (Fin 2) :=
  accelerationVectorReadout LengthUnit.meters TimeUnit.seconds acceleration

/-- Convert a dimensionless angle readout in degrees to radians. -/
def degreesToRadians (degrees : ℝ) : ℝ :=
  degrees * Real.pi / 180

/-! ## Physical roles and primary-image vocabulary -/

/-- Idealization used for the airborne package. -/
inductive ProjectileModel where
  | constantNearEarthGravityNegligibleDrag
  deriving DecidableEq, Repr

/-- Condition of the horizontal floor supporting the cart. -/
inductive FloorCondition where
  | frictionless
  | resistive
  deriving DecidableEq, Repr

/-- Outcome of the package--cart encounter. -/
inductive CaptureOutcome where
  | packageCapturedBodiesRollTogether
  | packageReboundsOrEscapes
  deriving DecidableEq, Repr

/-- Qualitative directions distinguished by the two grey arrows. -/
inductive MotionDirection where
  | left
  | downRight
  deriving DecidableEq, Repr

/-- The two motion arrows visible in image `768.png`. -/
inductive FigureArrow where
  | cartMotion
  | packageMotion
  deriving DecidableEq, Fintype, Repr

/-- Visible physical objects and geometric annotations. -/
inductive FigureElement where
  | inclinedChute
  | package
  | openCart
  | horizontalFloor
  | verticalHeightArrow
  | chuteAngleArc
  deriving DecidableEq, Fintype, Repr

/-- Literal numerical labels printed in the supplied raster. -/
inductive FigureLabel where
  | angle37Degrees
  | height4Meters
  deriving DecidableEq, Fintype, Repr

/-- Distinguished endpoints used by the height annotation. -/
inductive FigurePoint where
  | chuteExit
  | floorBelowChuteExit
  | cartBottom
  deriving DecidableEq, Fintype, Repr

/-- Qualitative and schematic content transcribed from the primary raster. -/
structure ShippingCartFigure where
  showsElement : FigureElement → Bool
  showsLabel : FigureLabel → Bool
  showsArrow : FigureArrow → Bool
  arrowDirection : FigureArrow → MotionDirection
  horizontalCoordinate : FigurePoint → ℝ
  verticalCoordinate : FigurePoint → ℝ
  heightArrowEndpoints : FigurePoint × FigurePoint
  chuteDescendsToRight : Bool
  packageShownAtChuteExit : Bool
  cartShownOpenAtTop : Bool
  packageLandingPointInsideCart : Bool

/-!
Independent physical quantities and intermediate states in the two-stage
model.  `finalCartSpeed` is an unconstrained observable here; no answer-choice
value or solved numerical expression is stored in the setup.
-/
structure ShippingCartCaptureSetup where
  cartMass : MassQuantity
  packageMass : MassQuantity
  chuteExitHeight : LengthQuantity
  packageFlightTime : TimeQuantity
  initialCartSpeed : SpeedQuantity
  chuteExitSpeed : SpeedQuantity
  finalCartSpeed : SpeedQuantity
  initialCartHorizontalVelocity : SignedVelocityQuantity
  commonFinalHorizontalVelocity : SignedVelocityQuantity
  chuteExitPosition : PlanarPositionQuantity
  packageLandingPosition : PlanarPositionQuantity
  cartBottomPosition : PlanarPositionQuantity
  packageVelocityAtChuteExit : PlanarVelocityQuantity
  packageVelocityAtImpact : PlanarVelocityQuantity
  gravitationalAcceleration : PlanarAccelerationQuantity
  chuteInclinationDegrees : ℝ
  projectileModel : ProjectileModel
  floorCondition : FloorCondition
  captureOutcome : CaptureOutcome
  figure : ShippingCartFigure

/-! ## Source data, figure evidence, geometry, and physical branch -/

/-!
The five numerical givens in the prose.  Neither final speed nor common final
velocity is constrained here.
-/
structure MatchesProblemReadouts
    (setup : ShippingCartCaptureSetup) : Prop where
  cartMassKilograms : massInKilograms setup.cartMass = 50
  packageMassKilograms : massInKilograms setup.packageMass = 15
  initialCartSpeedMetersPerSecond :
    speedInMetersPerSecond setup.initialCartSpeed = 5
  chuteExitSpeedMetersPerSecond :
    speedInMetersPerSecond setup.chuteExitSpeed = 3
  chuteExitHeightMeters : lengthInMeters setup.chuteExitHeight = 4
  chuteInclinationAngleDegrees : setup.chuteInclinationDegrees = 37

/-! The qualitative idealizations and encounter outcome stated in the prose. -/
structure MatchesQualitativeScenario
    (setup : ShippingCartCaptureSetup) : Prop where
  constantGravityProjectile :
    setup.projectileModel = .constantNearEarthGravityNegligibleDrag
  floorIsFrictionless : setup.floorCondition = .frictionless
  packageIsCaptured :
    setup.captureOutcome = .packageCapturedBodiesRollTogether

/-!
Primary-image evidence: a right-descending chute and package lie above and to
the left of an open cart; the package arrow points down-right, the cart arrow
points left, and the `37 degrees` and `4.00 m` annotations are present.
-/
structure MatchesPrimaryFigure
    (setup : ShippingCartCaptureSetup) : Prop where
  everyElementShown : ∀ element, setup.figure.showsElement element = true
  everyLabelShown : ∀ label, setup.figure.showsLabel label = true
  everyMotionArrowShown : ∀ arrow, setup.figure.showsArrow arrow = true
  packageArrowPointsDownRight :
    setup.figure.arrowDirection .packageMotion = .downRight
  cartArrowPointsLeft : setup.figure.arrowDirection .cartMotion = .left
  chuteDescendsRight : setup.figure.chuteDescendsToRight = true
  packageAtExit : setup.figure.packageShownAtChuteExit = true
  cartOpenAtTop : setup.figure.cartShownOpenAtTop = true
  landingInsideCart : setup.figure.packageLandingPointInsideCart = true
  heightArrowRunsDownFromExit :
    setup.figure.heightArrowEndpoints =
      (.chuteExit, .floorBelowChuteExit)
  floorPointDirectlyBelowExit :
    setup.figure.horizontalCoordinate .floorBelowChuteExit =
      setup.figure.horizontalCoordinate .chuteExit
  exitAboveFloor :
    setup.figure.verticalCoordinate .floorBelowChuteExit <
      setup.figure.verticalCoordinate .chuteExit
  cartLiesRightOfChuteExit :
    setup.figure.horizontalCoordinate .chuteExit <
      setup.figure.horizontalCoordinate .cartBottom
  cartBottomAtFloorLevel :
    setup.figure.verticalCoordinate .cartBottom =
      setup.figure.verticalCoordinate .floorBelowChuteExit

/-!
Physical geometry associated with the `4.00 m` annotation and capture point.
The package moves to the right while falling from the chute exit to the cart.
-/
structure MatchesPhysicalGeometry
    (setup : ShippingCartCaptureSetup) : Prop where
  verticalSeparationIsExitHeight :
    positionInMeters setup.chuteExitPosition yAxis -
        positionInMeters setup.cartBottomPosition yAxis =
      lengthInMeters setup.chuteExitHeight
  landingAtCartBottomHeight :
    positionInMeters setup.packageLandingPosition yAxis =
      positionInMeters setup.cartBottomPosition yAxis
  landingIsRightOfChuteExit :
    positionInMeters setup.chuteExitPosition xAxis <
      positionInMeters setup.packageLandingPosition xAxis

/-!
Positivity and direction conditions selecting the physical branch in the
figure.  They contain no numerical claim about the final speed.
-/
structure HasPhysicalParameters
    (setup : ShippingCartCaptureSetup) : Prop where
  cartMassPositive : 0 < massInKilograms setup.cartMass
  packageMassPositive : 0 < massInKilograms setup.packageMass
  chuteExitHeightPositive : 0 < lengthInMeters setup.chuteExitHeight
  flightTimePositive : 0 < timeInSeconds setup.packageFlightTime
  initialCartSpeedPositive : 0 < speedInMetersPerSecond setup.initialCartSpeed
  chuteExitSpeedPositive : 0 < speedInMetersPerSecond setup.chuteExitSpeed
  packageLeavesRightward :
    0 < velocityInMetersPerSecond setup.packageVelocityAtChuteExit xAxis
  packageLeavesDownward :
    velocityInMetersPerSecond setup.packageVelocityAtChuteExit yAxis < 0
  packageImpactsWhileMovingRight :
    0 < velocityInMetersPerSecond setup.packageVelocityAtImpact xAxis
  packageImpactsWhileMovingDown :
    velocityInMetersPerSecond setup.packageVelocityAtImpact yAxis < 0
  finalMotionRemainsLeftward :
    signedVelocityInMetersPerSecond
      setup.commonFinalHorizontalVelocity < 0

/-! ## Governing laws -/

/-!
The stated directions and chute angle determine the initial signed cart
velocity and the two components of the package's chute-exit velocity.  These
relations hold in every coherent choice of length and time units and contain
no post-capture speed value.
-/
structure SatisfiesInitialVelocityGeometry
    (setup : ShippingCartCaptureSetup) : Prop where
  cartMovesLeft :
    ∀ (lengthUnit : LengthUnit) (timeUnit : TimeUnit),
      signedVelocityReadout lengthUnit timeUnit
          setup.initialCartHorizontalVelocity =
        -speedReadout lengthUnit timeUnit setup.initialCartSpeed
  packageExitHorizontalComponent :
    ∀ (lengthUnit : LengthUnit) (timeUnit : TimeUnit),
      velocityVectorReadout lengthUnit timeUnit
          setup.packageVelocityAtChuteExit xAxis =
        speedReadout lengthUnit timeUnit setup.chuteExitSpeed *
          Real.cos (degreesToRadians setup.chuteInclinationDegrees)
  packageExitVerticalComponent :
    ∀ (lengthUnit : LengthUnit) (timeUnit : TimeUnit),
      velocityVectorReadout lengthUnit timeUnit
          setup.packageVelocityAtChuteExit yAxis =
        -(speedReadout lengthUnit timeUnit setup.chuteExitSpeed *
          Real.sin (degreesToRadians setup.chuteInclinationDegrees))
  packageExitSpeedIsVelocityNorm :
    ∀ (lengthUnit : LengthUnit) (timeUnit : TimeUnit),
      ‖velocityVectorReadout lengthUnit timeUnit
          setup.packageVelocityAtChuteExit‖ =
        speedReadout lengthUnit timeUnit setup.chuteExitSpeed

/-! The standard gravitational field used for the package's flight. -/
structure UsesStandardNearEarthGravity
    (setup : ShippingCartCaptureSetup) : Prop where
  noHorizontalAcceleration :
    accelerationInMetersPerSecondSquared
        setup.gravitationalAcceleration xAxis = 0
  downwardAccelerationMetersPerSecondSquared :
    accelerationInMetersPerSecondSquared
        setup.gravitationalAcceleration yAxis = -(49 / 5)

/-!
Endpoint position and velocity equations for constant acceleration.  The
height datum participates through the independent physical-geometry
predicate; in particular, it determines the flight time and vertical impact
velocity but does not alter the conserved horizontal component.
-/
structure SatisfiesProjectileMotion
    (setup : ShippingCartCaptureSetup) : Prop where
  positionAtLanding : ∀ units : UnitChoices,
    planarVectorReadout units setup.packageLandingPosition =
      planarVectorReadout units setup.chuteExitPosition +
        nonnegativeReadout units setup.packageFlightTime •
          planarVectorReadout units setup.packageVelocityAtChuteExit +
        ((1 / 2 : ℝ) *
            nonnegativeReadout units setup.packageFlightTime ^ 2) •
          planarVectorReadout units setup.gravitationalAcceleration
  velocityAtImpact : ∀ units : UnitChoices,
    planarVectorReadout units setup.packageVelocityAtImpact =
      planarVectorReadout units setup.packageVelocityAtChuteExit +
        nonnegativeReadout units setup.packageFlightTime •
          planarVectorReadout units setup.gravitationalAcceleration

/-!
During the short completely inelastic capture, the frictionless floor supplies
no horizontal impulse, so horizontal momentum is conserved.  The floor may
supply a vertical impulse; no false vertical-momentum conservation law is
assumed.  The last field is only the generic definition of speed as the
magnitude of the common horizontal velocity.
-/
structure SatisfiesInelasticCaptureLaws
    (setup : ShippingCartCaptureSetup) : Prop where
  horizontalMomentumConservation :
    ∀ (massUnit : MassUnit) (lengthUnit : LengthUnit)
        (timeUnit : TimeUnit),
      massReadout massUnit setup.cartMass *
          signedVelocityReadout lengthUnit timeUnit
            setup.initialCartHorizontalVelocity +
        massReadout massUnit setup.packageMass *
          velocityVectorReadout lengthUnit timeUnit
            setup.packageVelocityAtImpact xAxis =
      (massReadout massUnit setup.cartMass +
          massReadout massUnit setup.packageMass) *
        signedVelocityReadout lengthUnit timeUnit
          setup.commonFinalHorizontalVelocity
  finalSpeedIsMagnitudeOfCommonVelocity :
    ∀ (lengthUnit : LengthUnit) (timeUnit : TimeUnit),
      speedReadout lengthUnit timeUnit setup.finalCartSpeed =
        |signedVelocityReadout lengthUnit timeUnit
          setup.commonFinalHorizontalVelocity|

/-! ## Derived physical relations -/

/-!
Gravity has no horizontal component, so the package retains the horizontal
component supplied by the chute until impact.
-/
lemma package_horizontal_velocity_at_impact
    (setup : ShippingCartCaptureSetup)
    (hReadouts : MatchesProblemReadouts setup)
    (hInitial : SatisfiesInitialVelocityGeometry setup)
    (hGravity : UsesStandardNearEarthGravity setup)
    (hProjectile : SatisfiesProjectileMotion setup) :
    velocityInMetersPerSecond setup.packageVelocityAtImpact xAxis =
      3 * Real.cos (degreesToRadians 37) := by
  have hImpact :=
    congrArg (fun v : EuclideanSpace ℝ (Fin 2) => v xAxis)
      (hProjectile.velocityAtImpact
        {UnitChoices.SI with
          length := LengthUnit.meters
          time := TimeUnit.seconds})
  have hImpactX :
      velocityInMetersPerSecond setup.packageVelocityAtImpact xAxis =
        velocityInMetersPerSecond setup.packageVelocityAtChuteExit xAxis +
          timeInSeconds setup.packageFlightTime *
            accelerationInMetersPerSecondSquared
              setup.gravitationalAcceleration xAxis := by
    simpa [velocityInMetersPerSecond, velocityVectorReadout,
      accelerationInMetersPerSecondSquared, accelerationVectorReadout,
      timeInSeconds, timeReadout] using hImpact
  rw [hGravity.noHorizontalAcceleration, mul_zero, add_zero] at hImpactX
  calc
    velocityInMetersPerSecond setup.packageVelocityAtImpact xAxis =
        velocityInMetersPerSecond setup.packageVelocityAtChuteExit xAxis :=
      hImpactX
    _ = speedInMetersPerSecond setup.chuteExitSpeed *
          Real.cos (degreesToRadians setup.chuteInclinationDegrees) := by
      exact hInitial.packageExitHorizontalComponent
        LengthUnit.meters TimeUnit.seconds
    _ = 3 * Real.cos (degreesToRadians 37) := by
      rw [hReadouts.chuteExitSpeedMetersPerSecond,
        hReadouts.chuteInclinationAngleDegrees]

/-!
Substitution into horizontal momentum conservation gives the signed common
velocity.  The negative sign selected by the data means the loaded cart still
moves left.
-/
lemma common_final_horizontal_velocity_exact
    (setup : ShippingCartCaptureSetup)
    (hReadouts : MatchesProblemReadouts setup)
    (hInitial : SatisfiesInitialVelocityGeometry setup)
    (hGravity : UsesStandardNearEarthGravity setup)
    (hProjectile : SatisfiesProjectileMotion setup)
    (hCapture : SatisfiesInelasticCaptureLaws setup) :
    signedVelocityInMetersPerSecond
        setup.commonFinalHorizontalVelocity =
      ((50 : ℝ) * (-5) +
          15 * (3 * Real.cos (degreesToRadians 37))) / (50 + 15) := by
  have hPackageImpact :=
    package_horizontal_velocity_at_impact
      setup hReadouts hInitial hGravity hProjectile
  have hMomentum :=
    hCapture.horizontalMomentumConservation
      MassUnit.kilograms LengthUnit.meters TimeUnit.seconds
  change
    massInKilograms setup.cartMass *
          signedVelocityInMetersPerSecond
            setup.initialCartHorizontalVelocity +
        massInKilograms setup.packageMass *
          velocityInMetersPerSecond setup.packageVelocityAtImpact xAxis =
      (massInKilograms setup.cartMass +
          massInKilograms setup.packageMass) *
        signedVelocityInMetersPerSecond
          setup.commonFinalHorizontalVelocity at hMomentum
  have hCart := hInitial.cartMovesLeft LengthUnit.meters TimeUnit.seconds
  change
    signedVelocityInMetersPerSecond
        setup.initialCartHorizontalVelocity =
      -speedInMetersPerSecond setup.initialCartSpeed at hCart
  rw [hReadouts.cartMassKilograms, hReadouts.packageMassKilograms,
    hCart, hReadouts.initialCartSpeedMetersPerSecond,
    hPackageImpact] at hMomentum
  linarith

/-! ## Displayed choices and final target -/

/-- Labels attached to the four final speeds printed in the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Displayed final speed for each choice, in metres per second. -/
def displayedSpeedInMetersPerSecond : AnswerChoice → ℝ
  | .A => 215 / 100
  | .B => 329 / 100
  | .C => 408 / 100
  | .D => 414 / 100

/-- The answer label recorded by the dataset; it is metadata, not a premise. -/
def recordedDatasetAnswer : AnswerChoice := .B

/-- Agreement of an actual speed with a displayed value to the nearest `0.01 m/s`. -/
def RoundsToNearestHundredth
    (actualSpeed displayedSpeed : ℝ) : Prop :=
  |actualSpeed - displayedSpeed| < (1 / 200 : ℝ)

/-- The physical final speed rounds to the number printed by a choice. -/
def MatchesAnswerChoice
    (setup : ShippingCartCaptureSetup) (choice : AnswerChoice) : Prop :=
  RoundsToNearestHundredth
    (speedInMetersPerSecond setup.finalCartSpeed)
    (displayedSpeedInMetersPerSecond choice)

/-- The selected displayed speed is strictly closer than every other choice. -/
def IsUniqueClosestDisplayedChoice
    (setup : ShippingCartCaptureSetup) (choice : AnswerChoice) : Prop :=
  ∀ other, other ≠ choice →
    |speedInMetersPerSecond setup.finalCartSpeed -
        displayedSpeedInMetersPerSecond choice| <
      |speedInMetersPerSecond setup.finalCartSpeed -
        displayedSpeedInMetersPerSecond other|

/-!
The final speed is the magnitude of the horizontal-momentum quotient.  Its
value rounds to `3.29 m/s`, making B the unique closest displayed choice.

This is the Lean declaration corresponding to blueprint label
`thm:physics:phyx_mini_0768:target`.
-/
theorem final_cart_speed_after_package_capture
    (setup : ShippingCartCaptureSetup)
    (hReadouts : MatchesProblemReadouts setup)
    (hScenario : MatchesQualitativeScenario setup)
    (hFigure : MatchesPrimaryFigure setup)
    (hGeometry : MatchesPhysicalGeometry setup)
    (hPhysical : HasPhysicalParameters setup)
    (hInitial : SatisfiesInitialVelocityGeometry setup)
    (hGravity : UsesStandardNearEarthGravity setup)
    (hProjectile : SatisfiesProjectileMotion setup)
    (hCapture : SatisfiesInelasticCaptureLaws setup) :
    speedInMetersPerSecond setup.finalCartSpeed =
        |((50 : ℝ) * (-5) +
            15 * (3 * Real.cos (degreesToRadians 37))) / (50 + 15)| ∧
      MatchesAnswerChoice setup .B ∧
      IsUniqueClosestDisplayedChoice setup .B := by
  let θ : ℝ := degreesToRadians 37
  have hθ_nonneg : 0 ≤ θ := by
    dsimp [θ, degreesToRadians]
    positivity
  have hθ_lt : θ < (323 / 500 : ℝ) := by
    dsimp [θ, degreesToRadians]
    nlinarith [Real.pi_lt_d4]
  have hθ_sq : θ ^ 2 < (323 / 500 : ℝ) ^ 2 :=
    (sq_lt_sq₀ hθ_nonneg (by norm_num)).2 hθ_lt
  have hHalfBase :=
    Real.one_sub_sq_div_two_le_cos (x := θ / 2)
  have hHalfLower :
      (4739 / 5000 : ℝ) < Real.cos (θ / 2) := by
    nlinarith [hHalfBase, hθ_sq]
  have hHalfNonneg : 0 ≤ Real.cos (θ / 2) := by
    linarith
  have hHalfSq :
      (4739 / 5000 : ℝ) ^ 2 < Real.cos (θ / 2) ^ 2 :=
    (sq_lt_sq₀ (by norm_num) hHalfNonneg).2 hHalfLower
  have hDouble :
      Real.cos θ = 2 * Real.cos (θ / 2) ^ 2 - 1 := by
    calc
      Real.cos θ = Real.cos (2 * (θ / 2)) := by
        congr 1
        ring
      _ = 2 * Real.cos (θ / 2) ^ 2 - 1 :=
        Real.cos_two_mul (θ / 2)
  have hCosLower : (1991 / 2500 : ℝ) < Real.cos θ := by
    nlinarith [hDouble, hHalfSq]
  have hPiFifthLtTheta : Real.pi / 5 < θ := by
    dsimp [θ, degreesToRadians]
    nlinarith [Real.pi_pos]
  have hThetaLeHalfPi : θ ≤ Real.pi / 2 := by
    dsimp [θ, degreesToRadians]
    nlinarith [Real.pi_pos]
  have hCosLtExact :=
    Real.cos_lt_cos_of_nonneg_of_le_pi_div_two
      (x := Real.pi / 5) (y := θ) (by positivity)
      hThetaLeHalfPi hPiFifthLtTheta
  rw [Real.cos_pi_div_five] at hCosLtExact
  have hSqrt5Sq : Real.sqrt 5 ^ 2 = 5 := by
    norm_num
  have hSqrt5Lt : Real.sqrt 5 < (56 / 25 : ℝ) := by
    nlinarith [Real.sqrt_nonneg 5, hSqrt5Sq]
  have hCosUpper : Real.cos θ < (81 / 100 : ℝ) := by
    nlinarith [hCosLtExact, hSqrt5Lt]
  change
    (1991 / 2500 : ℝ) < Real.cos (degreesToRadians 37) at hCosLower
  change
    Real.cos (degreesToRadians 37) < (81 / 100 : ℝ) at hCosUpper

  have hCommon :=
    common_final_horizontal_velocity_exact
      setup hReadouts hInitial hGravity hProjectile hCapture
  have hSpeedExact :=
    hCapture.finalSpeedIsMagnitudeOfCommonVelocity
      LengthUnit.meters TimeUnit.seconds
  change
    speedInMetersPerSecond setup.finalCartSpeed =
      |signedVelocityInMetersPerSecond
        setup.commonFinalHorizontalVelocity| at hSpeedExact
  rw [hCommon] at hSpeedExact
  have hQuotientNeg :
      ((50 : ℝ) * (-5) +
          15 * (3 * Real.cos (degreesToRadians 37))) / (50 + 15) < 0 := by
    nlinarith [hCosUpper]
  have hSpeedFormula :
      speedInMetersPerSecond setup.finalCartSpeed =
        (250 - 45 * Real.cos (degreesToRadians 37)) / 65 := by
    rw [hSpeedExact, abs_of_neg hQuotientNeg]
    ring
  have hSpeedLower :
      (657 / 200 : ℝ) <
        speedInMetersPerSecond setup.finalCartSpeed := by
    nlinarith [hSpeedFormula, hCosUpper]
  have hSpeedUpper :
      speedInMetersPerSecond setup.finalCartSpeed <
        (659 / 200 : ℝ) := by
    nlinarith [hSpeedFormula, hCosLower]
  have hRoundAbs :
      |speedInMetersPerSecond setup.finalCartSpeed - (329 / 100 : ℝ)| <
        (1 / 200 : ℝ) := by
    rw [abs_lt]
    constructor <;> linarith

  refine ⟨hSpeedExact, ?_, ?_⟩
  · exact hRoundAbs
  · intro other hne
    fin_cases other
    · change
        |speedInMetersPerSecond setup.finalCartSpeed - (329 / 100 : ℝ)| <
          |speedInMetersPerSecond setup.finalCartSpeed - (215 / 100 : ℝ)|
      refine hRoundAbs.trans ?_
      rw [abs_of_pos (by linarith [hSpeedLower])]
      linarith [hSpeedLower]
    · exact (hne rfl).elim
    · change
        |speedInMetersPerSecond setup.finalCartSpeed - (329 / 100 : ℝ)| <
          |speedInMetersPerSecond setup.finalCartSpeed - (408 / 100 : ℝ)|
      refine hRoundAbs.trans ?_
      rw [abs_of_neg (by linarith [hSpeedUpper])]
      linarith [hSpeedUpper]
    · change
        |speedInMetersPerSecond setup.finalCartSpeed - (329 / 100 : ℝ)| <
          |speedInMetersPerSecond setup.finalCartSpeed - (414 / 100 : ℝ)|
      refine hRoundAbs.trans ?_
      rw [abs_of_neg (by linarith [hSpeedUpper])]
      linarith [hSpeedUpper]

end PhyXMiniProblems.ProblemPhyXMini0768
