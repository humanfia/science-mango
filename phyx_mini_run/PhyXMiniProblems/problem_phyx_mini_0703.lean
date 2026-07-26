import Mathlib
import Physlib.Units.WithDim.Basic

/- USER: The assigned source file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0703

open Dimension

/-!
# Two rockets joined by a rigid tunnel

Two rockets are treated as point masses docked at opposite ends of a rigid,
negligible-mass tunnel.  Their equal and opposite transverse thrusts have zero
resultant force but nonzero torque about the common center of mass.

All dimensional physical quantities below are unit-independent Physlib
`Dimensionful` values.  Real numbers are used only for coherent-SI readouts,
signed planar components, and displayed answer values.  In particular, the
angular velocity at the observation time is an independent field constrained
only by the rotational laws; it is not defined from answer choice C.
-/

/-! ## Dimensionful quantities and coherent-SI readouts -/

/-- The two-dimensional Euclidean vector space of the supplied diagram. -/
abbrev PlanarVector : Type := EuclideanSpace ℝ (Fin 2)

/-- A nonnegative, unit-independent physical mass. -/
abbrev MassQuantity : Type :=
  Dimensionful (WithDim M𝓭 NNReal)

/-- A nonnegative, unit-independent physical length. -/
abbrev LengthQuantity : Type :=
  Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative, unit-independent time coordinate or elapsed duration. -/
abbrev TimeQuantity : Type :=
  Dimensionful (WithDim T𝓭 NNReal)

/-- The physical dimension of force, `mass * length / time²`. -/
def forceDimension : Dimension :=
  M𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹

/-- A unit-independent planar force vector. -/
abbrev ForceVectorQuantity : Type :=
  Dimensionful (WithDim forceDimension PlanarVector)

/-- The physical dimension of a moment of inertia, `mass * length²`. -/
def momentOfInertiaDimension : Dimension :=
  M𝓭 * L𝓭 * L𝓭

/-- A nonnegative, unit-independent moment of inertia. -/
abbrev MomentOfInertiaQuantity : Type :=
  Dimensionful (WithDim momentOfInertiaDimension NNReal)

/-- The physical dimension of torque, `mass * length² / time²`. -/
def torqueDimension : Dimension :=
  M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹

/-- A signed torque about the axis normal to the diagram. -/
abbrev SignedTorqueQuantity : Type :=
  Dimensionful (WithDim torqueDimension ℝ)

/-- Signed angular velocity; radians are dimensionless. -/
abbrev AngularVelocityQuantity : Type :=
  Dimensionful (WithDim T𝓭⁻¹ ℝ)

/-- Signed angular acceleration; radians are dimensionless. -/
abbrev AngularAccelerationQuantity : Type :=
  Dimensionful (WithDim (T𝓭⁻¹ * T𝓭⁻¹) ℝ)

/-- Unit-independent center-of-mass velocity in the diagram plane. -/
abbrev VelocityVectorQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * T𝓭⁻¹) PlanarVector)

/-- Coherent-SI readout of a nonnegative dimensionful scalar. -/
def nonnegativeSIReadout {d : Dimension}
    (quantity : Dimensionful (WithDim d NNReal)) : ℝ :=
  ((quantity UnitChoices.SI).val : ℝ)

/-- Coherent-SI readout of a signed dimensionful scalar. -/
def signedSIReadout {d : Dimension}
    (quantity : Dimensionful (WithDim d ℝ)) : ℝ :=
  (quantity UnitChoices.SI).val

/-- Coherent-SI readout of a dimensionful planar vector. -/
def vectorSIReadout {d : Dimension}
    (quantity : Dimensionful (WithDim d PlanarVector)) : PlanarVector :=
  (quantity UnitChoices.SI).val

/-- Mass readout in kilograms. -/
def massInKilograms (mass : MassQuantity) : ℝ :=
  nonnegativeSIReadout mass

/-- Length or longitudinal-position readout in metres. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  nonnegativeSIReadout length

/-- Time readout in seconds. -/
def timeInSeconds (time : TimeQuantity) : ℝ :=
  nonnegativeSIReadout time

/-- Moment-of-inertia readout in kilogram metres squared. -/
def inertiaInKilogramMetersSquared
    (inertia : MomentOfInertiaQuantity) : ℝ :=
  nonnegativeSIReadout inertia

/-- Signed torque readout in newton metres. -/
def torqueInNewtonMeters (torque : SignedTorqueQuantity) : ℝ :=
  signedSIReadout torque

/-- Signed angular-velocity readout in radians per second. -/
def angularVelocityInRadiansPerSecond
    (angularVelocity : AngularVelocityQuantity) : ℝ :=
  signedSIReadout angularVelocity

/-- Signed angular-acceleration readout in radians per second squared. -/
def angularAccelerationInRadiansPerSecondSquared
    (angularAcceleration : AngularAccelerationQuantity) : ℝ :=
  signedSIReadout angularAcceleration

/-- Unit vector along the tunnel's labelled longitudinal `x` axis. -/
def longitudinalAxis : PlanarVector :=
  EuclideanSpace.single 0 1

/-- Unit vector in the positive transverse direction in the diagram plane. -/
def positiveTransverseAxis : PlanarVector :=
  EuclideanSpace.single 1 1

/-- The signed normal component of the planar cross product. -/
def planarCrossZ (left right : PlanarVector) : ℝ :=
  left 0 * right 1 - left 1 * right 0

/-! ## Physical roles and primary-figure vocabulary -/

/-- The two rockets labelled `1` and `2` in the figure. -/
inductive Rocket where
  | rocket1
  | rocket2
  deriving DecidableEq, Fintype, Repr

/-- The two physical ends of the connecting tunnel. -/
inductive TunnelEnd where
  | left
  | right
  deriving DecidableEq, Fintype, Repr

/-- Sense of rotation about the normal axis of the supplied diagram. -/
inductive RotationSense where
  | clockwise
  | counterclockwise
  deriving DecidableEq, Repr

/-- Mechanical treatment assigned to the connecting tunnel. -/
inductive TunnelModel where
  | rigidNegligibleMass
  | other
  deriving DecidableEq, Repr

/-- Spatial treatment assigned to each rocket in the rotational model. -/
inductive RocketMassModel where
  | pointMassAtDock
  | extendedBody
  deriving DecidableEq, Repr

/-- Time dependence assigned to the thrust during the observation interval. -/
inductive EngineThrustModel where
  | constantDuringObservation
  | timeDependent
  deriving DecidableEq, Repr

/-!
Literal and qualitative content of image 703.  The dimensional fields are the
values printed beside the objects and arrows.  The center-of-mass marker and
the two lever-arm labels are visible, but the image prints no numerical values
for them.
-/
structure DockedRocketsFigure where
  massLabel : Rocket → MassQuantity
  thrustArrow : Rocket → ForceVectorQuantity
  positionLabel : Rocket → LengthQuantity
  tunnelLengthLabel : LengthQuantity
  centerOfMassMarkerCoordinate : LengthQuantity
  centerOfMassMarkerVisible : Bool
  leverArmLabelVisible : Rocket → Bool
  thrustLabelVisible : Rocket → Bool
  exhaustVisible : Rocket → Bool
  longitudinalAxisVisible : Bool
  curvedRotationArrowVisible : Bool
  curvedRotationArrowSense : RotationSense

/-! ## Independent physical setup -/

/-!
The fields record the physical assembly, its forces, the center-of-mass
geometry, and its time-dependent motion.  None is defined from a displayed
answer.  Relations among these independent fields are stated separately as
geometry and dynamics laws below.
-/
structure DockedRocketsSetup where
  rocketMass : Rocket → MassQuantity
  rocketEnd : Rocket → TunnelEnd
  rocketMassModel : Rocket → RocketMassModel
  positionAlongTunnel : Rocket → LengthQuantity
  thrustForce : Rocket → ForceVectorQuantity
  tunnelLength : LengthQuantity
  tunnelMass : MassQuantity
  tunnelModel : TunnelModel
  engineThrustModel : EngineThrustModel
  engineIgnitionTime : Rocket → TimeQuantity
  zeroElapsedTime : TimeQuantity
  observationElapsedTime : TimeQuantity
  centerOfMassCoordinate : LengthQuantity
  leverArmDistance : Rocket → LengthQuantity
  netExternalForce : ForceVectorQuantity
  momentOfInertiaAboutCenterOfMass : MomentOfInertiaQuantity
  netTorqueAboutCenterOfMass : SignedTorqueQuantity
  angularAcceleration : AngularAccelerationQuantity
  centerOfMassVelocityAfterIgnition : TimeQuantity → VelocityVectorQuantity
  angularVelocityAfterIgnition : TimeQuantity → AngularVelocityQuantity
  figure : DockedRocketsFigure

/-! ## Scenario assumptions and figure/data readouts -/

/-- Qualitative physical setup stated in the prose. -/
structure MatchesDockedRocketsScenario
    (setup : DockedRocketsSetup) : Prop where
  rocket1AtLeftEnd : setup.rocketEnd .rocket1 = .left
  rocket2AtRightEnd : setup.rocketEnd .rocket2 = .right
  rocketsAreEndpointPointMasses :
    ∀ rocket, setup.rocketMassModel rocket = .pointMassAtDock
  tunnelIsRigidAndNegligibleMass :
    setup.tunnelModel = .rigidNegligibleMass
  thrustIsConstantDuringObservation :
    setup.engineThrustModel = .constantDuringObservation
  enginesStartSimultaneously :
    setup.engineIgnitionTime .rocket1 =
      setup.engineIgnitionTime .rocket2
  initiallyNoCenterOfMassMotion :
    vectorSIReadout
        (setup.centerOfMassVelocityAfterIgnition setup.zeroElapsedTime) = 0
  initiallyNoRotation :
    angularVelocityInRadiansPerSecond
        (setup.angularVelocityAfterIgnition setup.zeroElapsedTime) = 0

/-!
Exact labels and arrow directions supplied by image 703 and the problem text.
The transverse basis is chosen so rocket 2's arrow is positive.  Consequently
rocket 1's equal arrow is negative, exactly encoding the depicted opposite
thrusts rather than only their magnitudes.
-/
structure MatchesDockedRocketsFigureAndData
    (setup : DockedRocketsSetup) : Prop where
  figureMassesArePhysicalMasses :
    ∀ rocket, setup.figure.massLabel rocket = setup.rocketMass rocket
  figureForcesArePhysicalForces :
    ∀ rocket, setup.figure.thrustArrow rocket = setup.thrustForce rocket
  figurePositionsArePhysicalPositions :
    ∀ rocket,
      setup.figure.positionLabel rocket = setup.positionAlongTunnel rocket
  figureTunnelLengthIsPhysicalLength :
    setup.figure.tunnelLengthLabel = setup.tunnelLength
  figureCenterMarkerIsPhysicalCenter :
    setup.figure.centerOfMassMarkerCoordinate =
      setup.centerOfMassCoordinate
  rocket1MassKilograms :
    massInKilograms (setup.rocketMass .rocket1) = 100000
  rocket2MassKilograms :
    massInKilograms (setup.rocketMass .rocket2) = 200000
  tunnelLengthMeters : lengthInMeters setup.tunnelLength = 90
  rocket1PositionMeters :
    lengthInMeters (setup.positionAlongTunnel .rocket1) = 0
  rocket2PositionMeters :
    lengthInMeters (setup.positionAlongTunnel .rocket2) = 90
  rocket1ThrustVectorNewtons :
    vectorSIReadout (setup.thrustForce .rocket1) =
      (-50000 : ℝ) • positiveTransverseAxis
  rocket2ThrustVectorNewtons :
    vectorSIReadout (setup.thrustForce .rocket2) =
      (50000 : ℝ) • positiveTransverseAxis
  zeroElapsedTimeSeconds : timeInSeconds setup.zeroElapsedTime = 0
  observationElapsedTimeSeconds :
    timeInSeconds setup.observationElapsedTime = 30
  centerOfMassMarkerVisible :
    setup.figure.centerOfMassMarkerVisible = true
  bothLeverArmLabelsVisible :
    ∀ rocket, setup.figure.leverArmLabelVisible rocket = true
  bothThrustLabelsVisible :
    ∀ rocket, setup.figure.thrustLabelVisible rocket = true
  bothExhaustPlumesVisible :
    ∀ rocket, setup.figure.exhaustVisible rocket = true
  longitudinalAxisVisible : setup.figure.longitudinalAxisVisible = true
  curvedRotationArrowVisible :
    setup.figure.curvedRotationArrowVisible = true
  depictedRotationIsCounterclockwise :
    setup.figure.curvedRotationArrowSense = .counterclockwise

/-- Positivity and ordering assumptions selecting the physical configuration. -/
structure HasPhysicalDockedRocketsParameters
    (setup : DockedRocketsSetup) : Prop where
  rocketMassesPositive :
    ∀ rocket, 0 < massInKilograms (setup.rocketMass rocket)
  tunnelMassNonnegative : 0 ≤ massInKilograms setup.tunnelMass
  tunnelLengthPositive : 0 < lengthInMeters setup.tunnelLength
  observationAfterIgnition :
    timeInSeconds setup.zeroElapsedTime <
      timeInSeconds setup.observationElapsedTime
  centerOfMassBetweenRockets :
    lengthInMeters (setup.positionAlongTunnel .rocket1) <
        lengthInMeters setup.centerOfMassCoordinate ∧
      lengthInMeters setup.centerOfMassCoordinate <
        lengthInMeters (setup.positionAlongTunnel .rocket2)
  leverArmsPositive :
    ∀ rocket, 0 < lengthInMeters (setup.leverArmDistance rocket)
  inertiaPositive :
    0 < inertiaInKilogramMetersSquared
      setup.momentOfInertiaAboutCenterOfMass

/-! ## Governing geometry and rotational dynamics -/

/-!
Center-of-mass and endpoint geometry for two point masses on a massless rigid
tunnel.  The first law is the defining mass-moment balance, not the derived
numerical center coordinate requested along the solution route.
-/
structure SatisfiesTwoRocketCenterOfMassGeometry
    (setup : DockedRocketsSetup) : Prop where
  endpointsSpanTunnel :
    lengthInMeters (setup.positionAlongTunnel .rocket2) -
        lengthInMeters (setup.positionAlongTunnel .rocket1) =
      lengthInMeters setup.tunnelLength
  centerOfMassBalance :
    (massInKilograms (setup.rocketMass .rocket1) +
        massInKilograms (setup.rocketMass .rocket2)) *
        lengthInMeters setup.centerOfMassCoordinate =
      massInKilograms (setup.rocketMass .rocket1) *
          lengthInMeters (setup.positionAlongTunnel .rocket1) +
        massInKilograms (setup.rocketMass .rocket2) *
          lengthInMeters (setup.positionAlongTunnel .rocket2)
  rocket1LeverArm :
    lengthInMeters (setup.leverArmDistance .rocket1) =
      lengthInMeters setup.centerOfMassCoordinate -
        lengthInMeters (setup.positionAlongTunnel .rocket1)
  rocket2LeverArm :
    lengthInMeters (setup.leverArmDistance .rocket2) =
      lengthInMeters (setup.positionAlongTunnel .rocket2) -
        lengthInMeters setup.centerOfMassCoordinate

/-!
Governing laws for the massless-tunnel, point-mass approximation:

* the net external force is the sum of the two thrust vectors;
* `I = m₁ r₁² + m₂ r₂²` about the center of mass;
* torque is the sum of the two signed planar lever-arm cross products;
* `I α = τ`; and
* constant angular acceleration integrates to
  `ω(t) = ω(0) + α (t - 0)` during the observation interval.

No field states either the requested angular velocity or any answer-choice
value.
-/
structure SatisfiesConstantThrustRotationalDynamics
    (setup : DockedRocketsSetup) : Prop where
  resultantForceLaw :
    vectorSIReadout setup.netExternalForce =
      vectorSIReadout (setup.thrustForce .rocket1) +
        vectorSIReadout (setup.thrustForce .rocket2)
  pointMassMomentOfInertia :
    inertiaInKilogramMetersSquared
        setup.momentOfInertiaAboutCenterOfMass =
      massInKilograms (setup.rocketMass .rocket1) *
          lengthInMeters (setup.leverArmDistance .rocket1) ^ 2 +
        massInKilograms (setup.rocketMass .rocket2) *
          lengthInMeters (setup.leverArmDistance .rocket2) ^ 2
  torqueFromThrustCouple :
    torqueInNewtonMeters setup.netTorqueAboutCenterOfMass =
      planarCrossZ
          ((lengthInMeters (setup.positionAlongTunnel .rocket1) -
              lengthInMeters setup.centerOfMassCoordinate) •
            longitudinalAxis)
          (vectorSIReadout (setup.thrustForce .rocket1)) +
        planarCrossZ
          ((lengthInMeters (setup.positionAlongTunnel .rocket2) -
              lengthInMeters setup.centerOfMassCoordinate) •
            longitudinalAxis)
          (vectorSIReadout (setup.thrustForce .rocket2))
  rotationalNewtonLaw :
    inertiaInKilogramMetersSquared
          setup.momentOfInertiaAboutCenterOfMass *
        angularAccelerationInRadiansPerSecondSquared
          setup.angularAcceleration =
      torqueInNewtonMeters setup.netTorqueAboutCenterOfMass
  constantAngularAccelerationLaw : ∀ elapsedTime,
    timeInSeconds setup.zeroElapsedTime ≤ timeInSeconds elapsedTime →
    timeInSeconds elapsedTime ≤
        timeInSeconds setup.observationElapsedTime →
    angularVelocityInRadiansPerSecond
        (setup.angularVelocityAfterIgnition elapsedTime) =
      angularVelocityInRadiansPerSecond
          (setup.angularVelocityAfterIgnition setup.zeroElapsedTime) +
        angularAccelerationInRadiansPerSecondSquared
            setup.angularAcceleration *
          (timeInSeconds elapsedTime -
            timeInSeconds setup.zeroElapsedTime)

/-! ## Derived route quantities -/

/-- The unequal masses put the center of mass 60 m from rocket 1. -/
lemma centerOfMass_and_leverArm_readouts
    (setup : DockedRocketsSetup)
    (_figure : MatchesDockedRocketsFigureAndData setup)
    (_physical : HasPhysicalDockedRocketsParameters setup)
    (_geometry : SatisfiesTwoRocketCenterOfMassGeometry setup) :
    lengthInMeters setup.centerOfMassCoordinate = 60 ∧
      lengthInMeters (setup.leverArmDistance .rocket1) = 60 ∧
      lengthInMeters (setup.leverArmDistance .rocket2) = 30 := by
  have hbalance := _geometry.centerOfMassBalance
  have hcm : lengthInMeters setup.centerOfMassCoordinate = 60 := by
    norm_num [_figure.rocket1MassKilograms, _figure.rocket2MassKilograms,
      _figure.rocket1PositionMeters, _figure.rocket2PositionMeters] at hbalance ⊢
    linarith [hbalance]
  constructor
  · exact hcm
  constructor
  · rw [_geometry.rocket1LeverArm, hcm, _figure.rocket1PositionMeters]
    norm_num
  · rw [_geometry.rocket2LeverArm, hcm, _figure.rocket2PositionMeters]
    norm_num

/-- The point-mass moment of inertia is `5.40 × 10⁸ kg m²`. -/
lemma momentOfInertia_readout_eq
    (setup : DockedRocketsSetup)
    (_figure : MatchesDockedRocketsFigureAndData setup)
    (_physical : HasPhysicalDockedRocketsParameters setup)
    (_geometry : SatisfiesTwoRocketCenterOfMassGeometry setup)
    (_dynamics : SatisfiesConstantThrustRotationalDynamics setup) :
    inertiaInKilogramMetersSquared
        setup.momentOfInertiaAboutCenterOfMass = 540000000 := by
  rcases centerOfMass_and_leverArm_readouts setup _figure _physical _geometry with
    ⟨_, hr₁, hr₂⟩
  rw [_dynamics.pointMassMomentOfInertia,
    _figure.rocket1MassKilograms, _figure.rocket2MassKilograms, hr₁, hr₂]
  norm_num

/-- The equal transverse thrusts form a `4.50 × 10⁶ N m` torque couple. -/
lemma netTorque_readout_eq
    (setup : DockedRocketsSetup)
    (_figure : MatchesDockedRocketsFigureAndData setup)
    (_physical : HasPhysicalDockedRocketsParameters setup)
    (_geometry : SatisfiesTwoRocketCenterOfMassGeometry setup)
    (_dynamics : SatisfiesConstantThrustRotationalDynamics setup) :
    torqueInNewtonMeters setup.netTorqueAboutCenterOfMass = 4500000 := by
  obtain ⟨hcm, _, _⟩ :=
    centerOfMass_and_leverArm_readouts setup _figure _physical _geometry
  norm_num [_dynamics.torqueFromThrustCouple,
    _figure.rocket1PositionMeters, _figure.rocket2PositionMeters, hcm,
    _figure.rocket1ThrustVectorNewtons, _figure.rocket2ThrustVectorNewtons,
    planarCrossZ, longitudinalAxis, positiveTransverseAxis]

/-- The governing laws give angular acceleration `1/120 rad/s²`. -/
lemma angularAcceleration_readout_eq
    (setup : DockedRocketsSetup)
    (_figure : MatchesDockedRocketsFigureAndData setup)
    (_physical : HasPhysicalDockedRocketsParameters setup)
    (_geometry : SatisfiesTwoRocketCenterOfMassGeometry setup)
    (_dynamics : SatisfiesConstantThrustRotationalDynamics setup) :
    angularAccelerationInRadiansPerSecondSquared
        setup.angularAcceleration = 1 / 120 := by
  have h := _dynamics.rotationalNewtonLaw
  rw [momentOfInertia_readout_eq setup _figure _physical _geometry _dynamics,
    netTorque_readout_eq setup _figure _physical _geometry _dynamics] at h
  norm_num at h ⊢
  linarith [h]

/-!
Under the stated constant-thrust laws, starting from rest and integrating for
30 seconds gives `ω = 1/4 rad/s`.  This declaration makes the physical
consequence available independently of the dataset's recorded answer.
-/
theorem constantThrustPrediction_angularVelocity_after_thirty_seconds
    (setup : DockedRocketsSetup)
    (_scenario : MatchesDockedRocketsScenario setup)
    (_figure : MatchesDockedRocketsFigureAndData setup)
    (_physical : HasPhysicalDockedRocketsParameters setup)
    (_geometry : SatisfiesTwoRocketCenterOfMassGeometry setup)
    (_dynamics : SatisfiesConstantThrustRotationalDynamics setup) :
    angularVelocityInRadiansPerSecond
        (setup.angularVelocityAfterIgnition setup.observationElapsedTime) =
      1 / 4 := by
  have h := _dynamics.constantAngularAccelerationLaw
    setup.observationElapsedTime
    (by
      rw [_figure.zeroElapsedTimeSeconds, _figure.observationElapsedTimeSeconds]
      norm_num)
    (by exact le_rfl)
  rw [_scenario.initiallyNoRotation,
    angularAcceleration_readout_eq setup _figure _physical _geometry _dynamics,
    _figure.observationElapsedTimeSeconds, _figure.zeroElapsedTimeSeconds] at h
  norm_num at h ⊢
  exact h

/-! ## Answer choices and recorded-answer metadata -/

/-- Labels of the four displayed answer choices. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-!
The decimal printed for each choice, interpreted in radians per second because
the source question asks for angular velocity.  These values are display data,
not governing laws.
-/
def displayedAngularVelocityRadiansPerSecond : AnswerChoice → ℝ
  | .A => 850 / 100000
  | .B => 800 / 100000
  | .C => 833 / 100000
  | .D => 733 / 100000

/-!
The answer label recorded by the dataset.  It is source metadata only: no
physical theorem identifies the observed angular velocity with this choice.
Numerically, choice C is a three-decimal-place presentation of the angular
acceleration `1/120 rad/s²`, whereas the source asks for angular velocity after
30 seconds.  The physically supported answer to that question is the
preceding theorem's `1/4 rad/s`.
-/
def recordedAnswerChoice : AnswerChoice := .C

end PhyXMiniProblems.ProblemPhyXMini0703
