import Mathlib
import Physlib.Units.WithDim.Basic
import Physlib.Units.WithDim.Energy
import Physlib.ClassicalMechanics.RigidBody.SolidSphere
import Physlib.ClassicalMechanics.RigidBody.KineticEnergy

/- USER: The assigned source file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0788

open Dimension

/-!
# Landing speed of a rolling solid ball after a cliff

A uniform solid ball initially rolls to the right at `25.0 m/s`, without
slipping, up the hill in the supplied figure.  At the horizontal top it leaves
the ramp and falls through the displayed height `28.0 m`.  Rolling resistance
is neglected and total mechanical energy is conserved.

Physical mass, length, speed, acceleration, angular speed, and energy are
represented by unit-independent Physlib quantities.  Real numbers below are
only coherent-SI readouts, qualitative bitmap data, or displayed answer-choice
values.

Assumption/target split:

* governing laws: the Physlib uniform-solid-sphere model, `v = r omega` while
  in contact, translational/rotational/potential energy formulae, conservation
  of total mechanical energy, torque-free spin during flight, and the
  horizontal-launch free-fall speed relation;
* previous-part results: none;
* figure/data readouts: initial speed `25.0 m/s`, cliff drop `28.0 m`, aligned
  initial and landing levels, a rightward launch arrow, and a horizontal top;
* current target conclusions: the intermediate edge speed, the landing-speed
  formula and exact squared value, rounding to `28.0 m/s`, and choice `B`.

No target landing-speed value is a field or hypothesis below.
-/

/-! ## Dimensionful physical quantities and coherent-SI readouts -/

/-- Speed has physical dimension `L T⁻¹`. -/
def speedDimension : Dimension := L𝓭 * T𝓭⁻¹

/-- Linear acceleration has physical dimension `L T⁻²`. -/
def accelerationDimension : Dimension := L𝓭 * T𝓭⁻¹ * T𝓭⁻¹

/-- Angular speed has inverse-time dimension; radians are dimensionless. -/
def angularSpeedDimension : Dimension := T𝓭⁻¹

/-- A nonnegative, unit-independent physical mass. -/
abbrev MassQuantity : Type := Dimensionful (WithDim M𝓭 NNReal)

/-- A nonnegative, unit-independent physical length or height. -/
abbrev LengthQuantity : Type := Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative, unit-independent center-of-mass speed. -/
abbrev SpeedQuantity : Type :=
  Dimensionful (WithDim speedDimension NNReal)

/-- A nonnegative gravitational-acceleration magnitude. -/
abbrev AccelerationQuantity : Type :=
  Dimensionful (WithDim accelerationDimension NNReal)

/-- A nonnegative spin angular-speed magnitude. -/
abbrev AngularSpeedQuantity : Type :=
  Dimensionful (WithDim angularSpeedDimension NNReal)

/-- Mechanical energy, with physical dimension `M L² T⁻²`. -/
abbrev EnergyQuantity : Type := DimEnergy

/-- Read a physical mass in coherent-SI kilograms. -/
def massInKilograms (mass : MassQuantity) : ℝ :=
  ((mass UnitChoices.SI).val : ℝ)

/-- The nonnegative SI mass used to instantiate Physlib's solid sphere. -/
def massInKilogramsNNReal (mass : MassQuantity) : NNReal :=
  (mass UnitChoices.SI).val

/-- Read a physical length in coherent-SI metres. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  ((length UnitChoices.SI).val : ℝ)

/-- The nonnegative SI radius used to instantiate Physlib's solid sphere. -/
def lengthInMetersNNReal (length : LengthQuantity) : NNReal :=
  (length UnitChoices.SI).val

/-- Read a physical speed in coherent-SI metres per second. -/
def speedInMetersPerSecond (speed : SpeedQuantity) : ℝ :=
  ((speed UnitChoices.SI).val : ℝ)

/-- Read acceleration in coherent-SI metres per second squared. -/
def accelerationInMetersPerSecondSquared
    (acceleration : AccelerationQuantity) : ℝ :=
  ((acceleration UnitChoices.SI).val : ℝ)

/-- Read angular speed in radians per coherent-SI second. -/
def angularSpeedInRadiansPerSecond
    (angularSpeed : AngularSpeedQuantity) : ℝ :=
  ((angularSpeed UnitChoices.SI).val : ℝ)

/-- Read a physical energy in joules, calibrated by Physlib's joule. -/
def energyInJoules (energy : EnergyQuantity) : ℝ :=
  (energy UnitChoices.SI).val /
    (DimEnergy.joule UnitChoices.SI).val

/-! ## Motion stages, physical roles, and primary-figure vocabulary -/

/-- The three instants needed by the energy and projectile calculation. -/
inductive MotionStage where
  | initialBottom
  | cliffEdge
  | beforeLanding
  deriving DecidableEq, Fintype, Repr

/-- Coarse center-of-mass velocity directions stated or implied by the image. -/
inductive MotionDirection where
  | horizontalRight
  | downwardAndRight
  | other
  deriving DecidableEq, Repr

/-- Contact status of the ball at a modeled instant. -/
inductive ContactRegime where
  | rollingWithoutSlip
  | airborne
  deriving DecidableEq, Repr

/-- The mass distribution stated in the prose. -/
inductive BallMassDistribution where
  | uniformSolidSphere
  | other
  deriving DecidableEq, Repr

/-- Treatment of dissipative rolling resistance. -/
inductive RollingResistanceModel where
  | neglected
  | included
  deriving DecidableEq, Repr

/-- The post-edge center-of-mass motion model. -/
inductive AirborneMotionModel where
  | uniformGravityProjectile
  | other
  deriving DecidableEq, Repr

/-- Distinct visible features of primary image `788.png`. -/
inductive FigureFeature where
  | orangeBallAtBottomLeft
  | curvedHill
  | horizontalInitialSurface
  | verticalCliff
  | landingSurface
  | initialVelocityArrow
  | cliffDropArrow
  deriving DecidableEq, Fintype, Repr

/-- Literal and qualitative information transcribed from the supplied raster. -/
structure RollingBallCliffFigure where
  featureShown : FigureFeature → Bool
  initialVelocityArrowPointsRight : Bool
  cliffDropArrowPointsDown : Bool
  hillTopTangentIsHorizontal : Bool
  cliffFaceIsVertical : Bool
  initialAndLandingSurfacesAreAligned : Bool
  printedInitialSpeedMetersPerSecond : ℝ
  printedCliffDropMeters : ℝ

/-!
The unknown speed at `beforeLanding` is an independent physical observable.
All energies are likewise independent quantities related to the motion only by
the governing-law predicates below.  Nothing is defined from choice `B`.
-/
structure RollingBallCliffSetup where
  figure : RollingBallCliffFigure
  ballMass : MassQuantity
  ballRadius : LengthQuantity
  gravitationalAcceleration : AccelerationQuantity
  cliffDrop : LengthQuantity
  centerHeightAboveLandingLevel : MotionStage → LengthQuantity
  centerOfMassSpeed : MotionStage → SpeedQuantity
  spinAngularSpeed : MotionStage → AngularSpeedQuantity
  direction : MotionStage → MotionDirection
  contactRegime : MotionStage → ContactRegime
  massDistribution : BallMassDistribution
  rollingResistanceModel : RollingResistanceModel
  airborneMotionModel : AirborneMotionModel
  rigidBodySI : RigidBody 3
  spinAxis : Fin 3
  angularVelocityVectorRadiansPerSecond : MotionStage → Fin 3 → ℝ
  translationalKineticEnergy : MotionStage → EnergyQuantity
  rotationalKineticEnergy : MotionStage → EnergyQuantity
  gravitationalPotentialEnergy : MotionStage → EnergyQuantity
  totalMechanicalEnergy : MotionStage → EnergyQuantity

/-! ## Scenario, figure readouts, and physical nondegeneracy -/

/-- Qualitative content stated in the problem text. -/
structure MatchesProblemScenario (setup : RollingBallCliffSetup) : Prop where
  ballIsUniformAndSolid :
    setup.massDistribution = .uniformSolidSphere
  rollingResistanceIsNeglected :
    setup.rollingResistanceModel = .neglected
  initiallyRollsWithoutSlip :
    setup.contactRegime .initialBottom = .rollingWithoutSlip
  stillRollsWithoutSlipAtEdge :
    setup.contactRegime .cliffEdge = .rollingWithoutSlip
  airborneBeforeLanding :
    setup.contactRegime .beforeLanding = .airborne
  movingHorizontallyAtTop :
    setup.direction .cliffEdge = .horizontalRight
  projectileMotionAfterEdge :
    setup.airborneMotionModel = .uniformGravityProjectile

/-!
Figure evidence and its connection to physical readouts.  Heights use the
common initial/landing level as zero, so the center-of-mass height change from
the edge to either aligned surface is the labeled cliff drop.
-/
structure MatchesPrimaryFigure (setup : RollingBallCliffSetup) : Prop where
  everyFeatureShown :
    ∀ feature : FigureFeature, setup.figure.featureShown feature = true
  initialArrowPointsRight :
    setup.figure.initialVelocityArrowPointsRight = true
  dropArrowPointsDown : setup.figure.cliffDropArrowPointsDown = true
  horizontalTop : setup.figure.hillTopTangentIsHorizontal = true
  verticalCliff : setup.figure.cliffFaceIsVertical = true
  alignedGroundLevels :
    setup.figure.initialAndLandingSurfacesAreAligned = true
  printedInitialSpeed :
    setup.figure.printedInitialSpeedMetersPerSecond = 25.0
  physicalInitialSpeedMatchesLabel :
    speedInMetersPerSecond
      (setup.centerOfMassSpeed .initialBottom) =
        setup.figure.printedInitialSpeedMetersPerSecond
  printedCliffDrop : setup.figure.printedCliffDropMeters = 28.0
  physicalDropMatchesLabel :
    lengthInMeters setup.cliffDrop = setup.figure.printedCliffDropMeters
  initialDirectionMatchesArrow :
    setup.direction .initialBottom = .horizontalRight
  initialHeightIsReferenceLevel :
    lengthInMeters
      (setup.centerHeightAboveLandingLevel .initialBottom) = 0
  landingHeightIsReferenceLevel :
    lengthInMeters
      (setup.centerHeightAboveLandingLevel .beforeLanding) = 0
  cliffEdgeHeightMatchesDrop :
    lengthInMeters
      (setup.centerHeightAboveLandingLevel .cliffEdge) =
        lengthInMeters setup.cliffDrop

/-- The standard near-Earth gravitational acceleration used numerically. -/
structure UsesStandardEarthGravity (setup : RollingBallCliffSetup) : Prop where
  gravitationalAccelerationSI :
    accelerationInMetersPerSecondSquared
      setup.gravitationalAcceleration = 9.8

/-- Positivity needed to select the physical branches and use the sphere law. -/
structure HasPhysicalParameters (setup : RollingBallCliffSetup) : Prop where
  massPositive : 0 < massInKilograms setup.ballMass
  radiusPositive : 0 < lengthInMeters setup.ballRadius
  gravityPositive :
    0 < accelerationInMetersPerSecondSquared
      setup.gravitationalAcceleration
  cliffDropPositive : 0 < lengthInMeters setup.cliffDrop
  initialSpeedPositive :
    0 < speedInMetersPerSecond
      (setup.centerOfMassSpeed .initialBottom)

/-! ## Governing rigid-body, rolling, energy, and flight laws -/

/-!
The abstract physical ball is identified with Physlib's actual solid-sphere
rigid body in SI coordinates.  Its spin vector lies along one fixed axis, so
`RigidBody.rotationalKineticEnergy` uses the library's `2/5 m R²` inertia
tensor rather than an ad hoc scalar alias.
-/
structure SatisfiesUniformSolidSphereModel
    (setup : RollingBallCliffSetup) : Prop where
  rigidBodyIsSolidSphere :
    setup.rigidBodySI =
      RigidBody.solidSphere 3
        (massInKilogramsNNReal setup.ballMass)
        (lengthInMetersNNReal setup.ballRadius)
  spinVectorLiesAlongAxis :
    ∀ (stage : MotionStage) (component : Fin 3),
      setup.angularVelocityVectorRadiansPerSecond stage component =
        if component = setup.spinAxis then
          angularSpeedInRadiansPerSecond (setup.spinAngularSpeed stage)
        else 0

/-- No-slip coupling holds only while the ball is still touching the hill. -/
structure SatisfiesRollingWithoutSlipKinematics
    (setup : RollingBallCliffSetup) : Prop where
  initialNoSlipRelation :
    speedInMetersPerSecond
        (setup.centerOfMassSpeed .initialBottom) =
      lengthInMeters setup.ballRadius *
        angularSpeedInRadiansPerSecond
          (setup.spinAngularSpeed .initialBottom)
  edgeNoSlipRelation :
    speedInMetersPerSecond
        (setup.centerOfMassSpeed .cliffEdge) =
      lengthInMeters setup.ballRadius *
        angularSpeedInRadiansPerSecond
          (setup.spinAngularSpeed .cliffEdge)

/-!
The standard energy formulae and the stated conservation law.  These equations
are uniform in the motion stage and contain no specialized landing speed.
-/
structure SatisfiesMechanicalEnergyLaws
    (setup : RollingBallCliffSetup) : Prop where
  translationalEnergyFormula : ∀ stage : MotionStage,
    energyInJoules (setup.translationalKineticEnergy stage) =
      (1 / 2 : ℝ) * massInKilograms setup.ballMass *
        speedInMetersPerSecond (setup.centerOfMassSpeed stage) ^ 2
  rotationalEnergyUsesPhyslib : ∀ stage : MotionStage,
    energyInJoules (setup.rotationalKineticEnergy stage) =
      setup.rigidBodySI.rotationalKineticEnergy
        (setup.angularVelocityVectorRadiansPerSecond stage)
  gravitationalPotentialEnergyFormula : ∀ stage : MotionStage,
    energyInJoules (setup.gravitationalPotentialEnergy stage) =
      massInKilograms setup.ballMass *
        accelerationInMetersPerSecondSquared
          setup.gravitationalAcceleration *
        lengthInMeters (setup.centerHeightAboveLandingLevel stage)
  totalEnergyIsComponentSum : ∀ stage : MotionStage,
    energyInJoules (setup.totalMechanicalEnergy stage) =
      energyInJoules (setup.translationalKineticEnergy stage) +
        energyInJoules (setup.rotationalKineticEnergy stage) +
        energyInJoules (setup.gravitationalPotentialEnergy stage)
  totalMechanicalEnergyConserved : ∀ stage : MotionStage,
    energyInJoules (setup.totalMechanicalEnergy stage) =
      energyInJoules
        (setup.totalMechanicalEnergy .initialBottom)

/-!
After the center of mass leaves horizontally, uniform gravity changes its
translational speed while exerting no torque about the ball's center.  The
speed-squared relation is the standard constant-gravity projectile law for a
vertical drop.  It is stated generically in the physical parameters, not with
the requested numerical answer.
-/
structure SatisfiesTorqueFreeProjectileLaws
    (setup : RollingBallCliffSetup) : Prop where
  spinIsConstantDuringFlight :
    angularSpeedInRadiansPerSecond
        (setup.spinAngularSpeed .beforeLanding) =
      angularSpeedInRadiansPerSecond
        (setup.spinAngularSpeed .cliffEdge)
  speedSquaredAfterVerticalDrop :
    speedInMetersPerSecond
          (setup.centerOfMassSpeed .beforeLanding) ^ 2 =
      speedInMetersPerSecond
          (setup.centerOfMassSpeed .cliffEdge) ^ 2 +
        2 * accelerationInMetersPerSecondSquared
          setup.gravitationalAcceleration *
        lengthInMeters setup.cliffDrop

/-! ## Derived relations and displayed answer metadata -/

/-- Energy conservation while rolling gives the edge-speed relation. -/
lemma cliffEdge_speed_squared_from_rolling_energy
    (setup : RollingBallCliffSetup)
    (_scenario : MatchesProblemScenario setup)
    (_figure : MatchesPrimaryFigure setup)
    (_physical : HasPhysicalParameters setup)
    (_sphere : SatisfiesUniformSolidSphereModel setup)
    (_rolling : SatisfiesRollingWithoutSlipKinematics setup)
    (_energy : SatisfiesMechanicalEnergyLaws setup) :
    speedInMetersPerSecond
          (setup.centerOfMassSpeed .cliffEdge) ^ 2 =
      speedInMetersPerSecond
          (setup.centerOfMassSpeed .initialBottom) ^ 2 -
        (10 / 7 : ℝ) *
          accelerationInMetersPerSecondSquared
            setup.gravitationalAcceleration *
          lengthInMeters setup.cliffDrop := by
  have hr : lengthInMetersNNReal setup.ballRadius ≠ 0 := by
    intro hr0
    have hr0' : lengthInMeters setup.ballRadius = 0 := by
      simpa [lengthInMeters, lengthInMetersNNReal] using
        congrArg ((↑) : NNReal → ℝ) hr0
    linarith [_physical.radiusPositive]
  have hrpos :
      0 < (lengthInMetersNNReal setup.ballRadius : ℝ) :=
    by
      simpa [lengthInMeters, lengthInMetersNNReal] using
        _physical.radiusPositive
  let cycleCoordinates : Space 3 ≃ₗᵢ[ℝ] Space 3 :=
    { toFun := fun x => ⟨![x 1, x 2, x 0]⟩
      invFun := fun x => ⟨![x 2, x 0, x 1]⟩
      left_inv := by
        intro x
        ext i
        fin_cases i <;> rfl
      right_inv := by
        intro x
        ext i
        fin_cases i <;> rfl
      map_add' := by
        intro x y
        ext i
        fin_cases i <;> rfl
      map_smul' := by
        intro c x
        ext i
        fin_cases i <;> rfl
      norm_map' := by
        intro x
        rw [Space.norm_eq, Space.norm_eq]
        congr 1
        simp [Fin.sum_univ_succ]
        ring }
  have cycleCoordinates_norm (x : Space 3) :
      ‖cycleCoordinates x‖ = ‖x‖ :=
    cycleCoordinates.norm_map x
  have coordinate_square_cycle (i : Fin 3) :
      ∫ x in Metric.closedBall (0 : Space 3)
          (lengthInMetersNNReal setup.ballRadius : ℝ),
          (cycleCoordinates x i) ^ 2 ∂MeasureTheory.volume =
        ∫ x in Metric.closedBall (0 : Space 3)
          (lengthInMetersNNReal setup.ballRadius : ℝ),
          (x i) ^ 2 ∂MeasureTheory.volume := by
    have hpreimage :
        cycleCoordinates ⁻¹' Metric.closedBall (0 : Space 3)
            (lengthInMetersNNReal setup.ballRadius : ℝ) =
          Metric.closedBall (0 : Space 3)
            (lengthInMetersNNReal setup.ballRadius : ℝ) := by
      ext x
      simp only [Set.mem_preimage, Metric.mem_closedBall, dist_zero_right,
        cycleCoordinates_norm]
    have hchange :=
      cycleCoordinates.measurePreserving.setIntegral_preimage_emb
        cycleCoordinates.toHomeomorph.measurableEmbedding
        (fun x : Space 3 => (x i) ^ 2)
        (Metric.closedBall (0 : Space 3)
          (lengthInMetersNNReal setup.ballRadius : ℝ))
    rw [hpreimage] at hchange
    exact hchange
  have coordinate_square_zero_eq_one :
      ∫ x in Metric.closedBall (0 : Space 3)
          (lengthInMetersNNReal setup.ballRadius : ℝ), (x 0) ^ 2 ∂MeasureTheory.volume =
        ∫ x in Metric.closedBall (0 : Space 3)
          (lengthInMetersNNReal setup.ballRadius : ℝ), (x 1) ^ 2 ∂MeasureTheory.volume := by
    simpa [cycleCoordinates] using (coordinate_square_cycle 0).symm
  have coordinate_square_one_eq_two :
      ∫ x in Metric.closedBall (0 : Space 3)
          (lengthInMetersNNReal setup.ballRadius : ℝ), (x 1) ^ 2 ∂MeasureTheory.volume =
        ∫ x in Metric.closedBall (0 : Space 3)
          (lengthInMetersNNReal setup.ballRadius : ℝ), (x 2) ^ 2 ∂MeasureTheory.volume := by
    simpa [cycleCoordinates] using (coordinate_square_cycle 1).symm
  have integral_norm_squared :
      ∫ x in Metric.closedBall (0 : Space 3)
          (lengthInMetersNNReal setup.ballRadius : ℝ), ‖x‖ ^ 2 ∂MeasureTheory.volume =
        (3 / 5 : ℝ) *
          MeasureTheory.volume.real (Metric.closedBall (0 : Space 3)
            (lengthInMetersNNReal setup.ballRadius : ℝ)) *
          (lengthInMetersNNReal setup.ballRadius : ℝ) ^ 2 := by
    let radialCutoff : ℝ → ℝ := fun r =>
      if r ≤ (lengthInMetersNNReal setup.ballRadius : ℝ) then r ^ 2 else 0
    have hradial :=
      MeasureTheory.integral_fun_norm_addHaar (E := Space 3)
        MeasureTheory.volume radialCutoff
    simp only [Space.finrank_eq_dim, Nat.reduceSub, nsmul_eq_mul,
      smul_eq_mul] at hradial
    have hleft :
        ∫ x in Metric.closedBall (0 : Space 3)
            (lengthInMetersNNReal setup.ballRadius : ℝ), ‖x‖ ^ 2 ∂MeasureTheory.volume =
          ∫ x : Space 3, radialCutoff ‖x‖ ∂MeasureTheory.volume := by
      rw [← MeasureTheory.integral_indicator measurableSet_closedBall]
      apply MeasureTheory.integral_congr_ae
      filter_upwards with x
      simp [Set.indicator, radialCutoff, Metric.mem_closedBall,
        dist_zero_right]
    have hinner :
        ∫ y in Set.Ioi (0 : ℝ), y ^ 2 * radialCutoff y =
          (lengthInMetersNNReal setup.ballRadius : ℝ) ^ 5 / 5 := by
      calc
        ∫ y in Set.Ioi (0 : ℝ), y ^ 2 * radialCutoff y =
            ∫ y in Set.Ioi (0 : ℝ),
              (Set.Iic (lengthInMetersNNReal setup.ballRadius : ℝ)).indicator
                (fun y => y ^ 4) y := by
          apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
          intro y _hy
          by_cases hyr :
              y ≤ (lengthInMetersNNReal setup.ballRadius : ℝ)
          · simp [radialCutoff, hyr]
            ring
          · simp [radialCutoff, hyr]
        _ = ∫ y in
              Set.Ioi (0 : ℝ) ∩
                Set.Iic (lengthInMetersNNReal setup.ballRadius : ℝ),
              y ^ 4 :=
          MeasureTheory.setIntegral_indicator measurableSet_Iic
        _ = ∫ y in Set.Ioc (0 : ℝ)
              (lengthInMetersNNReal setup.ballRadius : ℝ), y ^ 4 := by
          congr 1
        _ = ∫ y in (0 : ℝ)..
              (lengthInMetersNNReal setup.ballRadius : ℝ), y ^ 4 := by
          rw [intervalIntegral.integral_of_le hrpos.le]
        _ = (lengthInMetersNNReal setup.ballRadius : ℝ) ^ 5 / 5 := by
          norm_num
    have hvolume :=
      MeasureTheory.Measure.addHaar_real_closedBall MeasureTheory.volume
        (0 : Space 3) hrpos.le
    simp only [Space.finrank_eq_dim] at hvolume
    rw [hleft, hradial, hinner, hvolume]
    ring
  have coordinate_square_integrable (i : Fin 3) :
      MeasureTheory.IntegrableOn
        (fun x : Space 3 => (x i) ^ 2)
        (Metric.closedBall (0 : Space 3)
          (lengthInMetersNNReal setup.ballRadius : ℝ)) :=
    ContinuousOn.integrableOn_compact
      (isCompact_closedBall (0 : Space 3)
        (lengthInMetersNNReal setup.ballRadius : ℝ))
      (by fun_prop)
  have norm_squared_integrable :
      MeasureTheory.IntegrableOn
        (fun x : Space 3 => ‖x‖ ^ 2)
        (Metric.closedBall (0 : Space 3)
          (lengthInMetersNNReal setup.ballRadius : ℝ)) :=
    ContinuousOn.integrableOn_compact
      (isCompact_closedBall (0 : Space 3)
        (lengthInMetersNNReal setup.ballRadius : ℝ))
      (by fun_prop)
  have integral_norm_squared_eq_coordinate_sum :
      ∫ x in Metric.closedBall (0 : Space 3)
          (lengthInMetersNNReal setup.ballRadius : ℝ), ‖x‖ ^ 2 ∂MeasureTheory.volume =
        (∫ x in Metric.closedBall (0 : Space 3)
            (lengthInMetersNNReal setup.ballRadius : ℝ), (x 0) ^ 2 ∂MeasureTheory.volume) +
        (∫ x in Metric.closedBall (0 : Space 3)
            (lengthInMetersNNReal setup.ballRadius : ℝ), (x 1) ^ 2 ∂MeasureTheory.volume) +
        ∫ x in Metric.closedBall (0 : Space 3)
            (lengthInMetersNNReal setup.ballRadius : ℝ), (x 2) ^ 2 ∂MeasureTheory.volume := by
    calc
      ∫ x in Metric.closedBall (0 : Space 3)
          (lengthInMetersNNReal setup.ballRadius : ℝ), ‖x‖ ^ 2 ∂MeasureTheory.volume =
          ∫ x in Metric.closedBall (0 : Space 3)
            (lengthInMetersNNReal setup.ballRadius : ℝ),
            ((x 0) ^ 2 + (x 1) ^ 2) + (x 2) ^ 2 ∂MeasureTheory.volume := by
        apply MeasureTheory.setIntegral_congr_fun measurableSet_closedBall
        intro x _hx
        change ‖x‖ ^ 2 =
          ((x 0) ^ 2 + (x 1) ^ 2) + (x 2) ^ 2
        rw [Space.norm_sq_eq]
        norm_num [Fin.sum_univ_succ]
        ring
      _ = _ := by
        have hzero_add_one :
            ∫ x in Metric.closedBall (0 : Space 3)
                (lengthInMetersNNReal setup.ballRadius : ℝ),
                (x 0) ^ 2 + (x 1) ^ 2 ∂MeasureTheory.volume =
              (∫ x in Metric.closedBall (0 : Space 3)
                  (lengthInMetersNNReal setup.ballRadius : ℝ),
                  (x 0) ^ 2 ∂MeasureTheory.volume) +
                ∫ x in Metric.closedBall (0 : Space 3)
                  (lengthInMetersNNReal setup.ballRadius : ℝ),
                  (x 1) ^ 2 ∂MeasureTheory.volume := by
          simpa only [Pi.add_apply] using
            (MeasureTheory.integral_add
              (coordinate_square_integrable 0)
              (coordinate_square_integrable 1))
        have hsum :
            ∫ x in Metric.closedBall (0 : Space 3)
                (lengthInMetersNNReal setup.ballRadius : ℝ),
                ((x 0) ^ 2 + (x 1) ^ 2) + (x 2) ^ 2
                  ∂MeasureTheory.volume =
              (∫ x in Metric.closedBall (0 : Space 3)
                  (lengthInMetersNNReal setup.ballRadius : ℝ),
                  (x 0) ^ 2 + (x 1) ^ 2 ∂MeasureTheory.volume) +
                ∫ x in Metric.closedBall (0 : Space 3)
                  (lengthInMetersNNReal setup.ballRadius : ℝ),
                  (x 2) ^ 2 ∂MeasureTheory.volume := by
          simpa only [Pi.add_apply] using
            (MeasureTheory.integral_add
              ((coordinate_square_integrable 0).add
                (coordinate_square_integrable 1))
              (coordinate_square_integrable 2))
        rw [hsum, hzero_add_one]
  have coordinate_square_integral (i : Fin 3) :
      ∫ x in Metric.closedBall (0 : Space 3)
          (lengthInMetersNNReal setup.ballRadius : ℝ), (x i) ^ 2 ∂MeasureTheory.volume =
        (1 / 5 : ℝ) *
          MeasureTheory.volume.real (Metric.closedBall (0 : Space 3)
            (lengthInMetersNNReal setup.ballRadius : ℝ)) *
          (lengthInMetersNNReal setup.ballRadius : ℝ) ^ 2 := by
    have hzero :
        ∫ x in Metric.closedBall (0 : Space 3)
            (lengthInMetersNNReal setup.ballRadius : ℝ), (x 0) ^ 2 ∂MeasureTheory.volume =
          (1 / 5 : ℝ) *
            MeasureTheory.volume.real (Metric.closedBall (0 : Space 3)
              (lengthInMetersNNReal setup.ballRadius : ℝ)) *
            (lengthInMetersNNReal setup.ballRadius : ℝ) ^ 2 := by
      calc
        ∫ x in Metric.closedBall (0 : Space 3)
            (lengthInMetersNNReal setup.ballRadius : ℝ), (x 0) ^ 2 ∂MeasureTheory.volume =
            (1 / 3 : ℝ) *
              ((∫ x in Metric.closedBall (0 : Space 3)
                  (lengthInMetersNNReal setup.ballRadius : ℝ),
                  (x 0) ^ 2 ∂MeasureTheory.volume) +
                (∫ x in Metric.closedBall (0 : Space 3)
                  (lengthInMetersNNReal setup.ballRadius : ℝ),
                  (x 1) ^ 2 ∂MeasureTheory.volume) +
                ∫ x in Metric.closedBall (0 : Space 3)
                  (lengthInMetersNNReal setup.ballRadius : ℝ),
                  (x 2) ^ 2 ∂MeasureTheory.volume) := by
            rw [coordinate_square_zero_eq_one,
              coordinate_square_one_eq_two]
            ring
        _ = (1 / 3 : ℝ) *
              (∫ x in Metric.closedBall (0 : Space 3)
                (lengthInMetersNNReal setup.ballRadius : ℝ),
                ‖x‖ ^ 2 ∂MeasureTheory.volume) := by
            rw [integral_norm_squared_eq_coordinate_sum]
        _ = _ := by
            rw [integral_norm_squared]
            ring
    fin_cases i
    · exact hzero
    · simpa using
        coordinate_square_zero_eq_one.symm.trans hzero
    · simpa using
        coordinate_square_one_eq_two.symm.trans
          (coordinate_square_zero_eq_one.symm.trans hzero)
  have ball_volume_ne_zero :
      MeasureTheory.volume.real (Metric.closedBall (0 : Space 3)
        (lengthInMetersNNReal setup.ballRadius : ℝ)) ≠ 0 := by
    refine (MeasureTheory.measureReal_ne_zero_iff ?_).mpr ?_
    · exact MeasureTheory.measure_closedBall_lt_top.ne
    · exact
        (Metric.measure_closedBall_pos MeasureTheory.volume
          (0 : Space 3)
          (r := (lengthInMetersNNReal setup.ballRadius : ℝ))
          hrpos).ne'
  have solid_sphere_inertia_axis (axis : Fin 3) :
      (RigidBody.solidSphere 3
          (massInKilogramsNNReal setup.ballMass)
          (lengthInMetersNNReal setup.ballRadius)).inertiaTensor axis axis =
        (2 / 5 : ℝ) *
          (massInKilogramsNNReal setup.ballMass : ℝ) *
          (lengthInMetersNNReal setup.ballRadius : ℝ) ^ 2 := by
    have hintegral :
        ∫ x in Metric.closedBall (0 : Space 3)
            (lengthInMetersNNReal setup.ballRadius : ℝ),
            (∑ k : Fin 3, (x k) ^ 2) - x axis * x axis ∂MeasureTheory.volume =
          (2 / 5 : ℝ) *
            MeasureTheory.volume.real (Metric.closedBall (0 : Space 3)
              (lengthInMetersNNReal setup.ballRadius : ℝ)) *
            (lengthInMetersNNReal setup.ballRadius : ℝ) ^ 2 := by
      calc
        ∫ x in Metric.closedBall (0 : Space 3)
            (lengthInMetersNNReal setup.ballRadius : ℝ),
            (∑ k : Fin 3, (x k) ^ 2) - x axis * x axis ∂MeasureTheory.volume =
            ∫ x in Metric.closedBall (0 : Space 3)
              (lengthInMetersNNReal setup.ballRadius : ℝ),
              ‖x‖ ^ 2 - (x axis) ^ 2 ∂MeasureTheory.volume := by
          apply MeasureTheory.setIntegral_congr_fun measurableSet_closedBall
          intro x _hx
          change (∑ k : Fin 3, (x k) ^ 2) - x axis * x axis =
            ‖x‖ ^ 2 - (x axis) ^ 2
          rw [Space.norm_sq_eq]
          ring
        _ = (∫ x in Metric.closedBall (0 : Space 3)
                (lengthInMetersNNReal setup.ballRadius : ℝ),
                ‖x‖ ^ 2 ∂MeasureTheory.volume) -
              ∫ x in Metric.closedBall (0 : Space 3)
                (lengthInMetersNNReal setup.ballRadius : ℝ),
                (x axis) ^ 2 ∂MeasureTheory.volume := by
          rw [MeasureTheory.integral_sub norm_squared_integrable
            (coordinate_square_integrable axis)]
        _ = _ := by
          rw [integral_norm_squared, coordinate_square_integral]
          ring
    change
      (massInKilogramsNNReal setup.ballMass : ℝ) /
          MeasureTheory.volume.real (Metric.closedBall (0 : Space 3)
            (lengthInMetersNNReal setup.ballRadius : ℝ)) *
          (∫ x in Metric.closedBall (0 : Space 3)
            (lengthInMetersNNReal setup.ballRadius : ℝ),
            (if axis = axis then 1 else 0) *
                (∑ k : Fin 3, (x k) ^ 2) -
              x axis * x axis ∂MeasureTheory.volume) =
        (2 / 5 : ℝ) *
          (massInKilogramsNNReal setup.ballMass : ℝ) *
          (lengthInMetersNNReal setup.ballRadius : ℝ) ^ 2
    simp only [if_pos, one_mul]
    rw [hintegral]
    field_simp [ball_volume_ne_zero]
  have sparse_axis_quadratic
      (inertia : Matrix (Fin 3) (Fin 3) ℝ)
      (axis : Fin 3) (omega : ℝ) :
      dotProduct
        (fun component : Fin 3 =>
          if component = axis then omega else 0)
        (Matrix.mulVec inertia
          (fun component : Fin 3 =>
            if component = axis then omega else 0)) =
        omega ^ 2 * inertia axis axis := by
    fin_cases axis <;>
      simp [dotProduct, Matrix.mulVec] <;>
      ring
  have rotational_energy_formula
      (stage : MotionStage)
      (hNoSlip :
        speedInMetersPerSecond (setup.centerOfMassSpeed stage) =
          lengthInMeters setup.ballRadius *
            angularSpeedInRadiansPerSecond (setup.spinAngularSpeed stage)) :
      energyInJoules (setup.rotationalKineticEnergy stage) =
        (1 / 5 : ℝ) * massInKilograms setup.ballMass *
          speedInMetersPerSecond (setup.centerOfMassSpeed stage) ^ 2 := by
    rw [_energy.rotationalEnergyUsesPhyslib stage,
      _sphere.rigidBodyIsSolidSphere,
      RigidBody.rotationalKineticEnergy]
    have hω :
        setup.angularVelocityVectorRadiansPerSecond stage =
          fun component =>
            if component = setup.spinAxis then
              angularSpeedInRadiansPerSecond (setup.spinAngularSpeed stage)
            else 0 :=
      funext (_sphere.spinVectorLiesAlongAxis stage)
    rw [hω]
    rw [sparse_axis_quadratic, solid_sphere_inertia_axis]
    rw [hNoSlip]
    simp only [massInKilograms, massInKilogramsNNReal,
      lengthInMeters, lengthInMetersNNReal]
    ring
  clear sparse_axis_quadratic solid_sphere_inertia_axis
    ball_volume_ne_zero coordinate_square_integral
    integral_norm_squared_eq_coordinate_sum norm_squared_integrable
    coordinate_square_integrable integral_norm_squared
    coordinate_square_one_eq_two coordinate_square_zero_eq_one
    coordinate_square_cycle cycleCoordinates_norm cycleCoordinates
    hrpos hr
  have hconserved :=
    _energy.totalMechanicalEnergyConserved .cliffEdge
  rw [_energy.totalEnergyIsComponentSum .cliffEdge,
    _energy.totalEnergyIsComponentSum .initialBottom,
    _energy.translationalEnergyFormula .cliffEdge,
    _energy.translationalEnergyFormula .initialBottom,
    rotational_energy_formula .cliffEdge _rolling.edgeNoSlipRelation,
    rotational_energy_formula .initialBottom _rolling.initialNoSlipRelation,
    _energy.gravitationalPotentialEnergyFormula .cliffEdge,
    _energy.gravitationalPotentialEnergyFormula .initialBottom,
    _figure.cliffEdgeHeightMatchesDrop,
    _figure.initialHeightIsReferenceLevel] at hconserved
  nlinarith [_physical.massPositive]

/-- With `v₀ = 25 m/s`, `h = 28 m`, and `g = 9.8 m/s²`, the edge speed
has squared SI readout `233`; its positive square root is about `15.3 m/s`. -/
lemma cliffEdge_speed_squared_eq_233
    (setup : RollingBallCliffSetup)
    (_scenario : MatchesProblemScenario setup)
    (_figure : MatchesPrimaryFigure setup)
    (_gravity : UsesStandardEarthGravity setup)
    (_physical : HasPhysicalParameters setup)
    (_sphere : SatisfiesUniformSolidSphereModel setup)
    (_rolling : SatisfiesRollingWithoutSlipKinematics setup)
    (_energy : SatisfiesMechanicalEnergyLaws setup) :
    speedInMetersPerSecond
      (setup.centerOfMassSpeed .cliffEdge) ^ 2 = 233 := by
  have h := cliffEdge_speed_squared_from_rolling_energy setup
    _scenario _figure _physical _sphere _rolling _energy
  rw [_figure.physicalInitialSpeedMatchesLabel,
    _figure.printedInitialSpeed,
    _gravity.gravitationalAccelerationSI,
    _figure.physicalDropMatchesLabel,
    _figure.printedCliffDrop] at h
  norm_num at h ⊢
  exact h

/-- Combining rolling energy with the vertical-drop law eliminates the
intermediate edge speed. -/
lemma landing_speed_squared_from_initial_data
    (setup : RollingBallCliffSetup)
    (_scenario : MatchesProblemScenario setup)
    (_figure : MatchesPrimaryFigure setup)
    (_physical : HasPhysicalParameters setup)
    (_sphere : SatisfiesUniformSolidSphereModel setup)
    (_rolling : SatisfiesRollingWithoutSlipKinematics setup)
    (_energy : SatisfiesMechanicalEnergyLaws setup)
    (_flight : SatisfiesTorqueFreeProjectileLaws setup) :
    speedInMetersPerSecond
          (setup.centerOfMassSpeed .beforeLanding) ^ 2 =
      speedInMetersPerSecond
          (setup.centerOfMassSpeed .initialBottom) ^ 2 +
        (4 / 7 : ℝ) *
          accelerationInMetersPerSecondSquared
            setup.gravitationalAcceleration *
          lengthInMeters setup.cliffDrop := by
  calc
    speedInMetersPerSecond
          (setup.centerOfMassSpeed .beforeLanding) ^ 2 =
        speedInMetersPerSecond
            (setup.centerOfMassSpeed .cliffEdge) ^ 2 +
          2 * accelerationInMetersPerSecondSquared
            setup.gravitationalAcceleration *
          lengthInMeters setup.cliffDrop :=
      _flight.speedSquaredAfterVerticalDrop
    _ = speedInMetersPerSecond
            (setup.centerOfMassSpeed .initialBottom) ^ 2 +
          (4 / 7 : ℝ) *
            accelerationInMetersPerSecondSquared
              setup.gravitationalAcceleration *
            lengthInMeters setup.cliffDrop := by
      rw [cliffEdge_speed_squared_from_rolling_energy setup
        _scenario _figure _physical _sphere _rolling _energy]
      ring

/-- Exact squared landing speed in coherent SI units: `781.8 = 3909/5`. -/
theorem landing_speed_squared_eq_3909_over_5
    (setup : RollingBallCliffSetup)
    (_scenario : MatchesProblemScenario setup)
    (_figure : MatchesPrimaryFigure setup)
    (_gravity : UsesStandardEarthGravity setup)
    (_physical : HasPhysicalParameters setup)
    (_sphere : SatisfiesUniformSolidSphereModel setup)
    (_rolling : SatisfiesRollingWithoutSlipKinematics setup)
    (_energy : SatisfiesMechanicalEnergyLaws setup)
    (_flight : SatisfiesTorqueFreeProjectileLaws setup) :
    speedInMetersPerSecond
      (setup.centerOfMassSpeed .beforeLanding) ^ 2 = 3909 / 5 := by
  have h := landing_speed_squared_from_initial_data setup
    _scenario _figure _physical _sphere _rolling _energy _flight
  rw [_figure.physicalInitialSpeedMatchesLabel,
    _figure.printedInitialSpeed,
    _gravity.gravitationalAccelerationSI,
    _figure.physicalDropMatchesLabel,
    _figure.printedCliffDrop] at h
  norm_num at h ⊢
  exact h

/-- The four multiple-choice labels in the source. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Displayed speed, in metres per second, attached to each answer choice. -/
def displayedAnswerSpeedMetersPerSecond : AnswerChoice → ℝ
  | .A => 21.0
  | .B => 28.0
  | .C => 15.3
  | .D => 13.6

/-- A generic numerical readout rounds to the displayed nearest tenth. -/
def RoundsToNearestTenth (actual displayed : ℝ) : Prop :=
  |actual - displayed| < 1 / 20

/--
The landing speed is approximately `28.0 m/s`, and among the displayed
options this uniquely selects answer choice `B`.

This is the Lean declaration corresponding to blueprint label
`thm:physics:phyx_mini_0788:target`.
-/
theorem landing_speed_selects_choice_B
    (setup : RollingBallCliffSetup)
    (_scenario : MatchesProblemScenario setup)
    (_figure : MatchesPrimaryFigure setup)
    (_gravity : UsesStandardEarthGravity setup)
    (_physical : HasPhysicalParameters setup)
    (_sphere : SatisfiesUniformSolidSphereModel setup)
    (_rolling : SatisfiesRollingWithoutSlipKinematics setup)
    (_energy : SatisfiesMechanicalEnergyLaws setup)
    (_flight : SatisfiesTorqueFreeProjectileLaws setup) :
    RoundsToNearestTenth
        (speedInMetersPerSecond
          (setup.centerOfMassSpeed .beforeLanding))
        (displayedAnswerSpeedMetersPerSecond .B) ∧
      ∀ choice : AnswerChoice,
        RoundsToNearestTenth
            (speedInMetersPerSecond
              (setup.centerOfMassSpeed .beforeLanding))
            (displayedAnswerSpeedMetersPerSecond choice) →
          choice = .B := by
  have hsq := landing_speed_squared_eq_3909_over_5 setup
    _scenario _figure _gravity _physical _sphere _rolling _energy _flight
  have hspeed_nonnegative :
      0 ≤ speedInMetersPerSecond
        (setup.centerOfMassSpeed .beforeLanding) := by
    change 0 ≤
      (((setup.centerOfMassSpeed .beforeLanding UnitChoices.SI).val :
        NNReal) : ℝ)
    exact NNReal.coe_nonneg _
  constructor
  · norm_num [RoundsToNearestTenth,
      displayedAnswerSpeedMetersPerSecond]
    rw [abs_lt]
    constructor <;> nlinarith
  · intro choice hchoice
    fin_cases choice
    · norm_num [RoundsToNearestTenth,
        displayedAnswerSpeedMetersPerSecond] at hchoice
      rw [abs_lt] at hchoice
      exfalso
      nlinarith
    · rfl
    · norm_num [RoundsToNearestTenth,
        displayedAnswerSpeedMetersPerSecond] at hchoice
      rw [abs_lt] at hchoice
      exfalso
      nlinarith
    · norm_num [RoundsToNearestTenth,
        displayedAnswerSpeedMetersPerSecond] at hchoice
      rw [abs_lt] at hchoice
      exfalso
      nlinarith

end PhyXMiniProblems.ProblemPhyXMini0788
