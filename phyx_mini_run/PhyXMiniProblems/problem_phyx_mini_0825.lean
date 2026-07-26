import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Physlib.ClassicalMechanics.RigidBody.SolidSphere
import Physlib.Units.WithDim.Basic

/- USER: The assigned source file did not exist when this autoformalization task began. -/

/-!
# Friction on a solid bowling ball rolling down an incline

A bowling ball of mass `M` and radius `R` rolls without slipping down a ramp
whose angle to the horizontal is `β`.  The ball is modeled as a uniform solid
sphere; the visible finger holes in the supplied figure are ignored.

Physical quantities are unit-independent Physlib `Dimensionful` values.  Real
numbers occur only at coherent-SI readout boundaries, for the angle in radians,
and in the dimensionless numerical coefficients displayed in the answers.

Assumption/target split:

* governing laws: Newton's tangential translation law, the torque of the
  tangential contact force, Newton's rotational law, the no-slip acceleration
  relation, and agreement of the scalar axial inertia with Physlib's inertia
  tensor;
* previous-part results: none;
* figure/data readouts: the ball and its finger holes, the inclined ramp, the
  dashed horizontal reference, the `β` angle marker, and the label `M`; the
  problem additionally specifies a uniform solid-sphere model with the holes
  ignored and rolling without slipping;
* target conclusion: the magnitude of the friction force is
  `(2/7) M g sin β`, answer choice B.

The signed tangential force component is positive down the ramp.  Consequently
the uphill direction of the friction force is not assumed: it must emerge as a
negative signed component from the governing laws.
-/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0825

open Dimension

/-! ## Dimensionful quantities and coherent-SI readouts -/

/-- A nonnegative, unit-independent physical mass. -/
abbrev MassQuantity : Type :=
  Dimensionful (WithDim M𝓭 NNReal)

/-- A nonnegative physical length, used for the bowling-ball radius. -/
abbrev LengthQuantity : Type :=
  Dimensionful (WithDim L𝓭 NNReal)

/-- The physical dimension of linear acceleration, `L T⁻²`. -/
def accelerationDimension : Dimension :=
  L𝓭 * T𝓭⁻¹ * T𝓭⁻¹

/-- A nonnegative gravitational-acceleration magnitude. -/
abbrev AccelerationMagnitudeQuantity : Type :=
  Dimensionful (WithDim accelerationDimension NNReal)

/-- A signed linear-acceleration component along the ramp. -/
abbrev SignedAccelerationQuantity : Type :=
  Dimensionful (WithDim accelerationDimension ℝ)

/-- The physical dimension of angular acceleration; radians are dimensionless. -/
def angularAccelerationDimension : Dimension :=
  T𝓭⁻¹ * T𝓭⁻¹

/-- A signed angular-acceleration component about the rolling axis. -/
abbrev SignedAngularAccelerationQuantity : Type :=
  Dimensionful (WithDim angularAccelerationDimension ℝ)

/-- The physical dimension of force, `M L T⁻²`. -/
def forceDimension : Dimension :=
  M𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹

/-- A signed force component along the ramp. -/
abbrev SignedForceQuantity : Type :=
  Dimensionful (WithDim forceDimension ℝ)

/-- The physical dimension of torque, `M L² T⁻²`. -/
def torqueDimension : Dimension :=
  forceDimension * L𝓭

/-- A signed torque component about the rolling axis. -/
abbrev SignedTorqueQuantity : Type :=
  Dimensionful (WithDim torqueDimension ℝ)

/-- The physical dimension of an axial moment of inertia, `M L²`. -/
def momentOfInertiaDimension : Dimension :=
  M𝓭 * L𝓭 * L𝓭

/-- A nonnegative scalar moment of inertia about the rolling axis. -/
abbrev MomentOfInertiaQuantity : Type :=
  Dimensionful (WithDim momentOfInertiaDimension NNReal)

/-- Read a nonnegative dimensionful quantity in coherent SI units. -/
def nonnegativeSIReadout {dimension : Dimension}
    (quantity : Dimensionful (WithDim dimension NNReal)) : ℝ :=
  ((quantity UnitChoices.SI).val : ℝ)

/-- Read a signed dimensionful scalar component in coherent SI units. -/
def signedSIReadout {dimension : Dimension}
    (quantity : Dimensionful (WithDim dimension ℝ)) : ℝ :=
  (quantity UnitChoices.SI).val

/-- Kilogram readout of the ball's mass. -/
def massInKilograms (mass : MassQuantity) : ℝ :=
  nonnegativeSIReadout mass

/-- Metre readout of the ball's radius. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  nonnegativeSIReadout length

/-- Metre-per-second-squared readout of a nonnegative acceleration. -/
def accelerationMagnitudeInMetersPerSecondSquared
    (acceleration : AccelerationMagnitudeQuantity) : ℝ :=
  nonnegativeSIReadout acceleration

/-- Metre-per-second-squared readout of a signed rampwise acceleration. -/
def signedAccelerationInMetersPerSecondSquared
    (acceleration : SignedAccelerationQuantity) : ℝ :=
  signedSIReadout acceleration

/-- Radian-per-second-squared readout of a signed angular acceleration. -/
def angularAccelerationInRadiansPerSecondSquared
    (acceleration : SignedAngularAccelerationQuantity) : ℝ :=
  signedSIReadout acceleration

/-- Newton readout of a signed rampwise force component. -/
def signedForceInNewtons (force : SignedForceQuantity) : ℝ :=
  signedSIReadout force

/-- Newton-metre readout of a signed torque component. -/
def signedTorqueInNewtonMeters (torque : SignedTorqueQuantity) : ℝ :=
  signedSIReadout torque

/-- Kilogram-metre-squared readout of a scalar axial moment of inertia. -/
def momentOfInertiaInKilogramMetersSquared
    (inertia : MomentOfInertiaQuantity) : ℝ :=
  nonnegativeSIReadout inertia

/-! ## Primary-figure vocabulary -/

/-- Visible geometric or physical parts of the supplied bitmap. -/
inductive FigurePart where
  | bowlingBall
  | fingerHoles
  | inclinedRamp
  | dashedHorizontalReference
  | inclinationAngleMarker
  deriving DecidableEq, Fintype, Repr

/-- Literal symbolic labels printed in the supplied bitmap. -/
inductive FigureLabel where
  | massM
  | inclinationBeta
  deriving DecidableEq, Fintype, Repr

/-- The qualitative placement of the depicted ball. -/
inductive DepictedBallPlacement where
  | restingOnInclinedRamp
  | elsewhere
  deriving DecidableEq, Repr

/-- Qualitative and symbolic information read directly from image `825.png`. -/
structure BowlingBallInclineFigure where
  showsPart : FigurePart → Bool
  showsLabel : FigureLabel → Bool
  labelRefersTo : FigureLabel → FigurePart
  depictedBallPlacement : DepictedBallPlacement
  rampRisesToTheRight : Bool
  angleMarkerUsesRampAndHorizontal : Bool
  markedInclinationRadians : ℝ

/-! ## Independent physical setup -/

/-- The rigid-body idealization stipulated in the problem text. -/
inductive BallModel where
  | uniformSolidSphere
  | other
  deriving DecidableEq, Repr

/-- Tangential contact behavior between the ball and ramp. -/
inductive ContactRegime where
  | rollingWithoutSlipping
  | slipping
  deriving DecidableEq, Repr

/-- Orientation used for signed tangential scalar components. -/
inductive TangentialPositiveDirection where
  | downRamp
  | upRamp
  deriving DecidableEq, Repr

/-- Orientation used for signed angular scalar components. -/
inductive AngularPositiveDirection where
  | rollingDownRamp
  | rollingUpRamp
  deriving DecidableEq, Repr

/-!
Every unknown observable is an independent physical quantity.  In particular,
the friction component is not defined from an answer choice.  `rigidBodySI`
uses Physlib's SI-coordinate rigid-body interface, while the corresponding
mass, radius, force, acceleration, torque, and scalar inertia remain
unit-independent quantities.
-/
structure RollingBowlingBallSetup where
  figure : BowlingBallInclineFigure
  ballModel : BallModel
  fingerHolesIgnored : Bool
  contactRegime : ContactRegime
  tangentialPositiveDirection : TangentialPositiveDirection
  angularPositiveDirection : AngularPositiveDirection
  ballMass : MassQuantity
  ballRadius : LengthQuantity
  inclinationBetaRadians : ℝ
  gravitationalAcceleration : AccelerationMagnitudeQuantity
  tangentialFrictionForce : SignedForceQuantity
  centerOfMassAccelerationAlongRamp : SignedAccelerationQuantity
  angularAccelerationAboutRollingAxis : SignedAngularAccelerationQuantity
  frictionTorqueAboutCenter : SignedTorqueQuantity
  axialMomentOfInertia : MomentOfInertiaQuantity
  rigidBodySI : RigidBody 3
  rollingAxis : Fin 3

/-! ## Figure evidence and problem data -/

/-- Labels, geometry, and placement transcribed from the primary bitmap. -/
structure MatchesPrimaryFigure (setup : RollingBowlingBallSetup) : Prop where
  everyPartIsShown :
    ∀ part : FigurePart, setup.figure.showsPart part = true
  everyLabelIsShown :
    ∀ label : FigureLabel, setup.figure.showsLabel label = true
  massLabelRefersToBall :
    setup.figure.labelRefersTo .massM = .bowlingBall
  betaLabelRefersToAngleMarker :
    setup.figure.labelRefersTo .inclinationBeta = .inclinationAngleMarker
  ballIsOnRamp :
    setup.figure.depictedBallPlacement = .restingOnInclinedRamp
  rampRisesRightward :
    setup.figure.rampRisesToTheRight = true
  betaIsBetweenRampAndHorizontal :
    setup.figure.angleMarkerUsesRampAndHorizontal = true
  markedAngleIsSetupBeta :
    setup.figure.markedInclinationRadians = setup.inclinationBetaRadians

/-!
The text identifies `M` as the ball's mass, specifies rolling without slip,
and replaces the visibly perforated bowling ball by a uniform solid sphere.
The equality to `RigidBody.solidSphere` is model identification, not an
assumption about the requested friction force.
-/
structure MatchesBowlingBallProblemData
    (setup : RollingBowlingBallSetup) : Prop where
  ballIsUniformSolidSphere :
    setup.ballModel = .uniformSolidSphere
  visibleFingerHolesAreIgnored :
    setup.fingerHolesIgnored = true
  ballRollsWithoutSlipping :
    setup.contactRegime = .rollingWithoutSlipping
  downRampIsTangentiallyPositive :
    setup.tangentialPositiveDirection = .downRamp
  rollingDownRampIsAngularlyPositive :
    setup.angularPositiveDirection = .rollingDownRamp
  rigidBodyIsPhyslibSolidSphere :
    setup.rigidBodySI =
      RigidBody.solidSphere 3
        (setup.ballMass UnitChoices.SI).val
        (setup.ballRadius UnitChoices.SI).val

/-- Positivity and angle bounds selecting the depicted physical branch. -/
structure HasPhysicalBowlingBallParameters
    (setup : RollingBowlingBallSetup) : Prop where
  positiveMass :
    0 < massInKilograms setup.ballMass
  positiveRadius :
    0 < lengthInMeters setup.ballRadius
  positiveGravity :
    0 < accelerationMagnitudeInMetersPerSecondSquared
      setup.gravitationalAcceleration
  positiveInclination :
    0 < setup.inclinationBetaRadians
  inclinationIsAcute :
    setup.inclinationBetaRadians < Real.pi / 2

/-! ## Governing translational, rotational, and no-slip laws -/

/-!
The signed force and acceleration components are positive down the ramp, and
the signed angular quantities are positive in the corresponding rolling-down
direction.  Thus the torque law contains a minus sign: a positive down-ramp
contact force produces torque opposite the rolling-down orientation.

No field below contains the solved friction value or assumes that friction is
uphill.  The solid-sphere inertia coefficient is supplied by Physlib's
`RigidBody.solidSphere_inertiaTensor`, after using the model-identification and
tensor-entry fields.
-/
structure SatisfiesRollingSphereDynamics
    (setup : RollingBowlingBallSetup) : Prop where
  axialMomentMatchesPhyslibTensor :
    momentOfInertiaInKilogramMetersSquared setup.axialMomentOfInertia =
      setup.rigidBodySI.inertiaTensor setup.rollingAxis setup.rollingAxis
  tangentialNewtonsSecondLaw :
    massInKilograms setup.ballMass *
          accelerationMagnitudeInMetersPerSecondSquared
            setup.gravitationalAcceleration *
          Real.sin setup.inclinationBetaRadians +
        signedForceInNewtons setup.tangentialFrictionForce =
      massInKilograms setup.ballMass *
        signedAccelerationInMetersPerSecondSquared
          setup.centerOfMassAccelerationAlongRamp
  frictionTorqueLaw :
    signedTorqueInNewtonMeters setup.frictionTorqueAboutCenter =
      -(signedForceInNewtons setup.tangentialFrictionForce *
        lengthInMeters setup.ballRadius)
  rotationalNewtonsSecondLaw :
    signedTorqueInNewtonMeters setup.frictionTorqueAboutCenter =
      momentOfInertiaInKilogramMetersSquared setup.axialMomentOfInertia *
        angularAccelerationInRadiansPerSecondSquared
          setup.angularAccelerationAboutRollingAxis
  noSlipAccelerationLaw :
    signedAccelerationInMetersPerSecondSquared
        setup.centerOfMassAccelerationAlongRamp =
      lengthInMeters setup.ballRadius *
        angularAccelerationInRadiansPerSecondSquared
          setup.angularAccelerationAboutRollingAxis

/-! ## Solid-sphere inertia and the requested friction magnitude -/

/--
Physlib's uniform-solid-sphere tensor formula gives the familiar scalar axial
moment of inertia `I = (2/5) M R²` for the modeled bowling ball.
-/
lemma axialMomentOfInertia_eq_twoFifths_mass_mul_radius_sq
    (setup : RollingBowlingBallSetup)
    (_data : MatchesBowlingBallProblemData setup)
    (_physical : HasPhysicalBowlingBallParameters setup)
    (_laws : SatisfiesRollingSphereDynamics setup) :
    momentOfInertiaInKilogramMetersSquared setup.axialMomentOfInertia =
      (2 / 5 : ℝ) * massInKilograms setup.ballMass *
        lengthInMeters setup.ballRadius ^ 2 := by
  have radius_ne_zero : (setup.ballRadius UnitChoices.SI).val ≠ 0 := by
    intro radius_eq_zero
    have radius_readout_eq_zero :
        lengthInMeters setup.ballRadius = 0 := by
      simp [lengthInMeters, nonnegativeSIReadout, radius_eq_zero]
    linarith [_physical.positiveRadius]
  let massSI : NNReal := (setup.ballMass UnitChoices.SI).val
  let radiusSI : NNReal := (setup.ballRadius UnitChoices.SI).val
  have radiusSI_pos : 0 < (radiusSI : ℝ) := by
    exact_mod_cast (show 0 < radiusSI from pos_iff_ne_zero.mpr radius_ne_zero)
  have radiusSI_nonneg : 0 ≤ (radiusSI : ℝ) := radiusSI_pos.le
  let ball : Set (Space 3) :=
    Metric.closedBall (0 : Space 3) (radiusSI : ℝ)
  have ball_measurable : MeasurableSet ball := by
    exact measurableSet_closedBall
  have coordinate_sq_integrable (i : Fin 3) :
      MeasureTheory.IntegrableOn (fun x : Space 3 => x i ^ 2) ball := by
    exact
      ContinuousOn.integrableOn_compact
        (isCompact_closedBall (0 : Space 3) (radiusSI : ℝ)) (by fun_prop)
  have norm_sq_integrable :
      MeasureTheory.IntegrableOn (fun x : Space 3 => ‖x‖ ^ 2) ball := by
    exact
      ContinuousOn.integrableOn_compact
        (isCompact_closedBall (0 : Space 3) (radiusSI : ℝ)) (by fun_prop)
  have coordinate_sq_integrals_equal (i j : Fin 3) :
      (∫ x in ball, x i ^ 2 ∂MeasureTheory.volume) =
        ∫ x in ball, x j ^ 2 ∂MeasureTheory.volume := by
    let swapCoordinates : Space 3 ≃ₗᵢ[ℝ] Space 3 :=
      Space.basis.equiv Space.basis (Equiv.swap i j)
    have swapCoordinates_apply_j (x : Space 3) :
        swapCoordinates x j = x i := by
      change
        (Space.basis.repr.symm
          ((LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Equiv.swap i j))
            (Space.basis.repr x))) j = x i
      rw [Space.basis_repr_symm_apply]
      rw [LinearIsometryEquiv.piLpCongrLeft_apply]
      change x ((Equiv.swap i j).symm j) = x i
      simp
    have transformed :=
      (LinearIsometryEquiv.measurePreserving swapCoordinates).setIntegral_preimage_emb
        swapCoordinates.toHomeomorph.measurableEmbedding
        (fun x : Space 3 => x j ^ 2) ball
    have ball_preimage :
        swapCoordinates ⁻¹' ball = ball := by
      simp [ball, swapCoordinates]
    rw [ball_preimage] at transformed
    simpa only [swapCoordinates_apply_j] using transformed
  have radial_integral :
      (∫ x in ball, ‖x‖ ^ 2 ∂MeasureTheory.volume) =
        (4 / 5 : ℝ) * Real.pi * (radiusSI : ℝ) ^ 5 := by
    let radialCutoff : ℝ → ℝ := fun r =>
      (Set.Iic (radiusSI : ℝ)).indicator (fun s => s ^ 2) r
    have radial_formula :=
      MeasureTheory.integral_fun_norm_addHaar
        (μ := (MeasureTheory.volume : MeasureTheory.Measure (Space 3))) radialCutoff
    have cutoff_integral :
        (∫ r : ℝ in Set.Ioi 0,
            r ^ 2 * radialCutoff r ∂MeasureTheory.volume) =
          (radiusSI : ℝ) ^ 5 / 5 := by
      have integrand_eq :
          (fun r : ℝ => r ^ 2 * radialCutoff r) =
            (Set.Iic (radiusSI : ℝ)).indicator (fun r => r ^ 4) := by
        funext r
        by_cases hr : r ∈ Set.Iic (radiusSI : ℝ)
        · simp [radialCutoff, hr]
          ring
        · simp [radialCutoff, hr]
      rw [integrand_eq, MeasureTheory.setIntegral_indicator
        (measurableSet_Iic : MeasurableSet (Set.Iic (radiusSI : ℝ))),
        Set.Ioi_inter_Iic, ← intervalIntegral.integral_of_le radiusSI_nonneg,
        integral_pow]
      norm_num
    calc
      (∫ x in ball, ‖x‖ ^ 2 ∂MeasureTheory.volume) =
          ∫ x : Space 3, radialCutoff ‖x‖ ∂MeasureTheory.volume := by
        rw [← MeasureTheory.integral_indicator ball_measurable]
        apply MeasureTheory.integral_congr_ae
        filter_upwards with x
        by_cases hx :
            x ∈ Metric.closedBall (0 : Space 3) (radiusSI : ℝ)
        · have hnorm : ‖x‖ ≤ (radiusSI : ℝ) := by
            simpa [Metric.mem_closedBall, dist_zero_right] using hx
          simp [ball, hx, radialCutoff, hnorm]
        · have hnorm : ¬ ‖x‖ ≤ (radiusSI : ℝ) := by
            simpa [Metric.mem_closedBall, dist_zero_right] using hx
          simp [ball, hx, radialCutoff, hnorm]
      _ =
          3 * MeasureTheory.volume.real (Metric.ball (0 : Space 3) 1) *
            ∫ r : ℝ in Set.Ioi 0,
              r ^ 2 * radialCutoff r ∂MeasureTheory.volume := by
        rw [mul_assoc]
        simpa [Space.finrank_eq_dim, nsmul_eq_mul, smul_eq_mul] using
          radial_formula
      _ = (4 / 5 : ℝ) * Real.pi * (radiusSI : ℝ) ^ 5 := by
        rw [cutoff_integral, Space.volume_metricBall_three_real]
        ring
  have radial_integral_eq_coordinate_sum :
      (∫ x in ball, ‖x‖ ^ 2 ∂MeasureTheory.volume) =
        (∫ x in ball, x (0 : Fin 3) ^ 2 ∂MeasureTheory.volume) +
        (∫ x in ball, x (1 : Fin 3) ^ 2 ∂MeasureTheory.volume) +
        (∫ x in ball, x (2 : Fin 3) ^ 2 ∂MeasureTheory.volume) := by
    calc
      (∫ x in ball, ‖x‖ ^ 2 ∂MeasureTheory.volume) =
          ∫ x in ball,
            (x (0 : Fin 3) ^ 2 + x (1 : Fin 3) ^ 2) +
              x (2 : Fin 3) ^ 2 ∂MeasureTheory.volume := by
        apply MeasureTheory.setIntegral_congr_fun ball_measurable
        intro x _
        change ‖x‖ ^ 2 =
          (x (0 : Fin 3) ^ 2 + x (1 : Fin 3) ^ 2) + x (2 : Fin 3) ^ 2
        simpa [Fin.sum_univ_three] using Space.norm_sq_eq x
      _ =
          (∫ x in ball, x (0 : Fin 3) ^ 2 ∂MeasureTheory.volume) +
          (∫ x in ball, x (1 : Fin 3) ^ 2 ∂MeasureTheory.volume) +
          (∫ x in ball, x (2 : Fin 3) ^ 2 ∂MeasureTheory.volume) := by
        calc
          (∫ x in ball,
              (x (0 : Fin 3) ^ 2 + x (1 : Fin 3) ^ 2) +
                x (2 : Fin 3) ^ 2 ∂MeasureTheory.volume) =
              (∫ x in ball,
                x (0 : Fin 3) ^ 2 + x (1 : Fin 3) ^ 2
                  ∂MeasureTheory.volume) +
                ∫ x in ball, x (2 : Fin 3) ^ 2
                  ∂MeasureTheory.volume := by
            change
              (∫ x : Space 3,
                (((fun y : Space 3 =>
                    y (0 : Fin 3) ^ 2 + y (1 : Fin 3) ^ 2) +
                  fun y : Space 3 => y (2 : Fin 3) ^ 2) x)
                  ∂MeasureTheory.volume.restrict ball) =
                (∫ x in ball,
                  x (0 : Fin 3) ^ 2 + x (1 : Fin 3) ^ 2
                    ∂MeasureTheory.volume) +
                  ∫ x in ball, x (2 : Fin 3) ^ 2
                    ∂MeasureTheory.volume
            exact
              MeasureTheory.integral_add
                ((coordinate_sq_integrable 0).add (coordinate_sq_integrable 1))
                (coordinate_sq_integrable 2)
          _ = _ := by
            change
              (∫ x : Space 3,
                ((fun y : Space 3 => y (0 : Fin 3) ^ 2) +
                  fun y : Space 3 => y (1 : Fin 3) ^ 2) x
                  ∂MeasureTheory.volume.restrict ball) +
                ∫ x in ball, x (2 : Fin 3) ^ 2
                  ∂MeasureTheory.volume = _
            exact congrArg
              (fun value : ℝ =>
                value +
                  ∫ x in ball, x (2 : Fin 3) ^ 2
                    ∂MeasureTheory.volume)
              (MeasureTheory.integral_add
                (coordinate_sq_integrable 0) (coordinate_sq_integrable 1))
  have coordinate_sq_integral (i : Fin 3) :
      (∫ x in ball, x i ^ 2 ∂MeasureTheory.volume) =
        (4 / 15 : ℝ) * Real.pi * (radiusSI : ℝ) ^ 5 := by
    have h0i := coordinate_sq_integrals_equal 0 i
    have h01 := coordinate_sq_integrals_equal 0 1
    have h02 := coordinate_sq_integrals_equal 0 2
    rw [radial_integral] at radial_integral_eq_coordinate_sum
    nlinarith
  have inertia_integral (i : Fin 3) :
      (∫ x in ball,
          ((∑ k : Fin 3, x k ^ 2) - x i * x i)
            ∂MeasureTheory.volume) =
        (8 / 15 : ℝ) * Real.pi * (radiusSI : ℝ) ^ 5 := by
    calc
      (∫ x in ball,
          ((∑ k : Fin 3, x k ^ 2) - x i * x i)
            ∂MeasureTheory.volume) =
          (∫ x in ball, ‖x‖ ^ 2 - x i ^ 2 ∂MeasureTheory.volume) := by
        apply MeasureTheory.setIntegral_congr_fun ball_measurable
        intro x _
        change (∑ k : Fin 3, x k ^ 2) - x i * x i =
          ‖x‖ ^ 2 - x i ^ 2
        rw [Space.norm_sq_eq]
        ring
      _ =
          (∫ x in ball, ‖x‖ ^ 2 ∂MeasureTheory.volume) -
            ∫ x in ball, x i ^ 2 ∂MeasureTheory.volume := by
        rw [MeasureTheory.integral_sub norm_sq_integrable
          (coordinate_sq_integrable i)]
      _ = (8 / 15 : ℝ) * Real.pi * (radiusSI : ℝ) ^ 5 := by
        rw [radial_integral, coordinate_sq_integral]
        ring
  have ball_volume :
      MeasureTheory.volume.real ball =
        (4 / 3 : ℝ) * Real.pi * (radiusSI : ℝ) ^ 3 := by
    simp only [ball]
    rw [MeasureTheory.Measure.real,
      InnerProductSpace.volume_closedBall_of_dim_odd
        (E := Space 3) (k := 1) (by simp [Space.finrank_eq_dim])]
    simp [Space.finrank_eq_dim]
    rw [ENNReal.toReal_ofReal]
    · ring
    · positivity
  have tensor_entry :
      (RigidBody.solidSphere 3 massSI radiusSI).inertiaTensor
          setup.rollingAxis setup.rollingAxis =
        (2 / 5 : ℝ) * (massSI : ℝ) * (radiusSI : ℝ) ^ 2 := by
    simp only [RigidBody.inertiaTensor, RigidBody.solidSphere,
      LinearMap.coe_mk, AddHom.coe_mk, ContMDiffMap.coeFn_mk]
    rw [show Metric.closedBall (0 : Space 3) (radiusSI : ℝ) = ball by rfl]
    simp only [if_true, one_mul]
    rw [inertia_integral, ball_volume]
    have pi_ne_zero : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
    field_simp
    ring
  calc
    momentOfInertiaInKilogramMetersSquared setup.axialMomentOfInertia =
        setup.rigidBodySI.inertiaTensor setup.rollingAxis setup.rollingAxis :=
      _laws.axialMomentMatchesPhyslibTensor
    _ =
        (RigidBody.solidSphere 3
          (setup.ballMass UnitChoices.SI).val
          (setup.ballRadius UnitChoices.SI).val).inertiaTensor
          setup.rollingAxis setup.rollingAxis := by
      rw [_data.rigidBodyIsPhyslibSolidSphere]
    _ =
        (2 / 5 : ℝ) * massInKilograms setup.ballMass *
          lengthInMeters setup.ballRadius ^ 2 := by
      simpa [massSI, radiusSI, massInKilograms, lengthInMeters,
        nonnegativeSIReadout] using tensor_entry

/-- Labels of the four displayed multiple-choice answers. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-!
The force magnitudes printed in the four answer choices.  This records the
question's answer metadata only; it does not identify any choice as correct.
-/
def AnswerChoice.displayedMagnitudeInNewtons
    (choice : AnswerChoice) (setup : RollingBowlingBallSetup) : ℝ :=
  match choice with
  | .A =>
      (2 / 9 : ℝ) * massInKilograms setup.ballMass *
        accelerationMagnitudeInMetersPerSecondSquared
          setup.gravitationalAcceleration *
        Real.sin setup.inclinationBetaRadians
  | .B =>
      (2 / 7 : ℝ) * massInKilograms setup.ballMass *
        accelerationMagnitudeInMetersPerSecondSquared
          setup.gravitationalAcceleration *
        Real.sin setup.inclinationBetaRadians
  | .C =>
      (2 / 5 : ℝ) * massInKilograms setup.ballMass *
        accelerationMagnitudeInMetersPerSecondSquared
          setup.gravitationalAcceleration *
        Real.cos setup.inclinationBetaRadians
  | .D =>
      (2 / 3 : ℝ) * massInKilograms setup.ballMass *
        accelerationMagnitudeInMetersPerSecondSquared
          setup.gravitationalAcceleration *
        Real.cos setup.inclinationBetaRadians

/--
The magnitude of the static friction force is `(2/7) M g sin β`, which is the
formula printed as answer choice B.  The absolute value converts the independent
signed down-ramp component into the requested force magnitude.
-/
theorem frictionForceMagnitude_eq_twoSevenths_mass_gravity_sin_beta
    (setup : RollingBowlingBallSetup)
    (_figure : MatchesPrimaryFigure setup)
    (_data : MatchesBowlingBallProblemData setup)
    (_physical : HasPhysicalBowlingBallParameters setup)
    (_laws : SatisfiesRollingSphereDynamics setup) :
    |signedForceInNewtons setup.tangentialFrictionForce| =
      (2 / 7 : ℝ) * massInKilograms setup.ballMass *
        accelerationMagnitudeInMetersPerSecondSquared
          setup.gravitationalAcceleration *
        Real.sin setup.inclinationBetaRadians := by
  have inertia_eq :=
    axialMomentOfInertia_eq_twoFifths_mass_mul_radius_sq
      setup _data _physical _laws
  have friction_rotation :
      -(signedForceInNewtons setup.tangentialFrictionForce *
          lengthInMeters setup.ballRadius) =
        ((2 / 5 : ℝ) * massInKilograms setup.ballMass *
            lengthInMeters setup.ballRadius ^ 2) *
          angularAccelerationInRadiansPerSecondSquared
            setup.angularAccelerationAboutRollingAxis := by
    calc
      -(signedForceInNewtons setup.tangentialFrictionForce *
          lengthInMeters setup.ballRadius) =
          signedTorqueInNewtonMeters setup.frictionTorqueAboutCenter :=
        _laws.frictionTorqueLaw.symm
      _ =
          momentOfInertiaInKilogramMetersSquared
              setup.axialMomentOfInertia *
            angularAccelerationInRadiansPerSecondSquared
              setup.angularAccelerationAboutRollingAxis :=
        _laws.rotationalNewtonsSecondLaw
      _ = _ := by rw [inertia_eq]
  have radius_ne_zero : lengthInMeters setup.ballRadius ≠ 0 :=
    ne_of_gt _physical.positiveRadius
  have friction_acceleration_times_radius :
      (-signedForceInNewtons setup.tangentialFrictionForce) *
          lengthInMeters setup.ballRadius =
        ((2 / 5 : ℝ) * massInKilograms setup.ballMass *
            signedAccelerationInMetersPerSecondSquared
              setup.centerOfMassAccelerationAlongRamp) *
          lengthInMeters setup.ballRadius := by
    calc
      (-signedForceInNewtons setup.tangentialFrictionForce) *
          lengthInMeters setup.ballRadius =
          -(signedForceInNewtons setup.tangentialFrictionForce *
            lengthInMeters setup.ballRadius) := by ring
      _ =
          ((2 / 5 : ℝ) * massInKilograms setup.ballMass *
              lengthInMeters setup.ballRadius ^ 2) *
            angularAccelerationInRadiansPerSecondSquared
              setup.angularAccelerationAboutRollingAxis :=
        friction_rotation
      _ =
          ((2 / 5 : ℝ) * massInKilograms setup.ballMass *
              (lengthInMeters setup.ballRadius *
                angularAccelerationInRadiansPerSecondSquared
                  setup.angularAccelerationAboutRollingAxis)) *
            lengthInMeters setup.ballRadius := by ring
      _ =
          ((2 / 5 : ℝ) * massInKilograms setup.ballMass *
              signedAccelerationInMetersPerSecondSquared
                setup.centerOfMassAccelerationAlongRamp) *
            lengthInMeters setup.ballRadius := by
        rw [← _laws.noSlipAccelerationLaw]
  have friction_acceleration :
      -signedForceInNewtons setup.tangentialFrictionForce =
        (2 / 5 : ℝ) * massInKilograms setup.ballMass *
          signedAccelerationInMetersPerSecondSquared
            setup.centerOfMassAccelerationAlongRamp :=
    mul_right_cancel₀ radius_ne_zero friction_acceleration_times_radius
  have friction_value :
      signedForceInNewtons setup.tangentialFrictionForce =
        -((2 / 7 : ℝ) * massInKilograms setup.ballMass *
          accelerationMagnitudeInMetersPerSecondSquared
            setup.gravitationalAcceleration *
          Real.sin setup.inclinationBetaRadians) := by
    nlinarith [_laws.tangentialNewtonsSecondLaw]
  have beta_lt_pi : setup.inclinationBetaRadians < Real.pi := by
    nlinarith [_physical.inclinationIsAcute, Real.pi_pos]
  have sin_beta_pos : 0 < Real.sin setup.inclinationBetaRadians :=
    Real.sin_pos_of_pos_of_lt_pi _physical.positiveInclination beta_lt_pi
  have displayed_magnitude_nonnegative :
      0 ≤
        (2 / 7 : ℝ) * massInKilograms setup.ballMass *
          accelerationMagnitudeInMetersPerSecondSquared
            setup.gravitationalAcceleration *
          Real.sin setup.inclinationBetaRadians := by
    exact
      (mul_pos
        (mul_pos
          (mul_pos (by norm_num : (0 : ℝ) < 2 / 7)
            _physical.positiveMass)
          _physical.positiveGravity)
        sin_beta_pos).le
  have friction_nonpositive :
      signedForceInNewtons setup.tangentialFrictionForce ≤ 0 := by
    rw [friction_value]
    exact neg_nonpos.mpr displayed_magnitude_nonnegative
  rw [abs_of_nonpos friction_nonpositive, friction_value]
  ring

end PhyXMiniProblems.ProblemPhyXMini0825
