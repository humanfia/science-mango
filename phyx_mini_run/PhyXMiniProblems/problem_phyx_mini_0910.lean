import Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle
import Physlib.Units.WithDim.Basic

/- USER: The assigned source file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0910

open Dimension

/-!
# Initial angular acceleration of an electric dipole

Two equally massive charged balls are joined by a massless insulating rod and
released in a uniform electric field.  The primary image places the negative
ball at the lower left and the positive ball at the upper right, labels their
center separation by `s = 2.0 cm`, and shows the dipole-moment arrow from the
negative ball to the positive ball at `30 degrees` above the rightward field.

The physical magnitudes below use Physlib's unit-independent `Dimensionful`
quantities.  Real numbers occur only in coherent-SI or named-unit readouts,
angle readouts, and the displayed multiple-choice values.

Assumption/target split:

* governing laws: `F = |q| E`, `p = |q| s`,
  `tau = p E sin(theta)`, the two-endpoint point-mass inertia formula, and
  rotational Newton's second law `tau = I alpha`;
* previous-part results: none;
* figure/data readouts: two `1.0 g` balls, charges `-10 nC` and `+10 nC`,
  separation `2.0 cm`, rightward uniform field `1.0 * 10^4 N/C`, the
  negative-to-positive dipole arrow, and its `30 degree` inclination;
* current target: the initial angular-acceleration magnitude is
  `5 rad/s^2`, which is displayed answer C.
-/

/-! ## Dimensionful physical quantities and coherent-SI readouts -/

/-- The physical dimension `M L T⁻² C⁻¹` of electric-field strength. -/
def electricFieldStrengthDimension : Dimension :=
  M𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹ * C𝓭⁻¹

/-- The physical dimension `M L T⁻²` of force. -/
def forceDimension : Dimension :=
  M𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹

/-- The physical dimension `C L` of electric-dipole moment. -/
def electricDipoleMomentDimension : Dimension :=
  C𝓭 * L𝓭

/-- The physical dimension `M L² T⁻²` of torque. -/
def torqueDimension : Dimension :=
  M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹

/-- The physical dimension `M L²` of a scalar moment of inertia. -/
def momentOfInertiaDimension : Dimension :=
  M𝓭 * L𝓭 * L𝓭

/-- Angular acceleration has dimension `T⁻²`; radians are dimensionless. -/
def angularAccelerationDimension : Dimension :=
  T𝓭⁻¹ * T𝓭⁻¹

/-- A nonnegative, unit-independent physical mass. -/
abbrev MassQuantity : Type :=
  Dimensionful (WithDim M𝓭 NNReal)

/-- A nonnegative, unit-independent physical length. -/
abbrev LengthQuantity : Type :=
  Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative, unit-independent electric-charge magnitude. -/
abbrev ChargeMagnitudeQuantity : Type :=
  Dimensionful (WithDim C𝓭 NNReal)

/-- A nonnegative, unit-independent electric-field-strength magnitude. -/
abbrev ElectricFieldStrengthMagnitude : Type :=
  Dimensionful (WithDim electricFieldStrengthDimension NNReal)

/-- A nonnegative electric-force magnitude. -/
abbrev ForceMagnitudeQuantity : Type :=
  Dimensionful (WithDim forceDimension NNReal)

/-- A nonnegative electric-dipole-moment magnitude. -/
abbrev ElectricDipoleMomentMagnitude : Type :=
  Dimensionful (WithDim electricDipoleMomentDimension NNReal)

/-- A nonnegative torque magnitude about the midpoint of the rod. -/
abbrev TorqueMagnitudeQuantity : Type :=
  Dimensionful (WithDim torqueDimension NNReal)

/-- A nonnegative scalar moment of inertia about the midpoint of the rod. -/
abbrev MomentOfInertiaQuantity : Type :=
  Dimensionful (WithDim momentOfInertiaDimension NNReal)

/-- A nonnegative angular-acceleration magnitude. -/
abbrev AngularAccelerationMagnitude : Type :=
  Dimensionful (WithDim angularAccelerationDimension NNReal)

/-- Read a nonnegative dimensionful quantity in coherent SI base units. -/
def nonnegativeSIReadout {d : Dimension}
    (quantity : Dimensionful (WithDim d NNReal)) : ℝ :=
  ((quantity UnitChoices.SI).val : ℝ)

/-- Read a mass in kilograms. -/
def massInKilograms (mass : MassQuantity) : ℝ :=
  nonnegativeSIReadout mass

/-- Read a mass in grams, the unit printed beside each ball. -/
def massInGrams (mass : MassQuantity) : ℝ :=
  1000 * massInKilograms mass

/-- Read a length in metres. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  nonnegativeSIReadout length

/-- Read a length in centimetres, the unit printed beside `s`. -/
def lengthInCentimeters (length : LengthQuantity) : ℝ :=
  100 * lengthInMeters length

/-- Read a charge magnitude in coulombs. -/
def chargeMagnitudeInCoulombs (charge : ChargeMagnitudeQuantity) : ℝ :=
  nonnegativeSIReadout charge

/-- Read a charge magnitude in nanocoulombs. -/
def chargeMagnitudeInNanocoulombs (charge : ChargeMagnitudeQuantity) : ℝ :=
  (10 : ℝ) ^ 9 * chargeMagnitudeInCoulombs charge

/-- Read electric-field strength in newtons per coulomb. -/
def electricFieldStrengthInNewtonsPerCoulomb
    (fieldStrength : ElectricFieldStrengthMagnitude) : ℝ :=
  nonnegativeSIReadout fieldStrength

/-- Read an electric-force magnitude in newtons. -/
def forceMagnitudeInNewtons (force : ForceMagnitudeQuantity) : ℝ :=
  nonnegativeSIReadout force

/-- Read an electric-dipole moment magnitude in coulomb-metres. -/
def dipoleMomentInCoulombMeters
    (moment : ElectricDipoleMomentMagnitude) : ℝ :=
  nonnegativeSIReadout moment

/-- Read a torque magnitude in newton-metres. -/
def torqueInNewtonMeters (torque : TorqueMagnitudeQuantity) : ℝ :=
  nonnegativeSIReadout torque

/-- Read a moment of inertia in kilogram-metres squared. -/
def momentOfInertiaInKilogramMetersSquared
    (inertia : MomentOfInertiaQuantity) : ℝ :=
  nonnegativeSIReadout inertia

/-- Read angular acceleration in radians per second squared. -/
def angularAccelerationInRadiansPerSecondSquared
    (acceleration : AngularAccelerationMagnitude) : ℝ :=
  nonnegativeSIReadout acceleration

/-- Convert the degree measure used in the image to Mathlib's angle type. -/
def degreesToAngle (value : ℝ) : Real.Angle :=
  ((value * Real.pi / 180 : ℝ) : Real.Angle)

/-! ## Physical labels and primary-image vocabulary -/

/-- The two charged balls, named by the signs printed in the image. -/
inductive BallLabel where
  | negativeBall
  | positiveBall
  deriving DecidableEq, Fintype, Repr

/-- The sign carried by a ball's electric charge. -/
inductive ChargeSign where
  | negative
  | positive
  deriving DecidableEq, Fintype, Repr

/-- Coarse ball locations in the supplied planar drawing. -/
inductive BallPlacement where
  | lowerLeft
  | upperRight
  deriving DecidableEq, Repr

/-- Qualitative directions of arrows in the supplied planar drawing. -/
inductive PlanarDirection where
  | right
  | left
  | upAndRight
  deriving DecidableEq, Repr

/-- The idealized external electric-field models relevant to the problem. -/
inductive ExternalFieldModel where
  | uniform
  | nonuniform
  deriving DecidableEq, Repr

/-- The mass model for the insulating connecting rod. -/
inductive RodMassModel where
  | negligible
  | finite
  deriving DecidableEq, Repr

/-- The model used for rotational inertia when no ball radii are supplied. -/
inductive EndpointMassModel where
  | pointMassesAtBallCenters
  | extendedBalls
  deriving DecidableEq, Repr

/-- How the rod-and-ball assembly begins its motion. -/
inductive ReleaseProtocol where
  | heldAtAngleThenReleasedFromRest
  | externallyDriven
  deriving DecidableEq, Repr

/-- Direction of the force on a signed charge in a rightward electric field. -/
def forceDirectionInRightwardField : ChargeSign → PlanarDirection
  | .negative => .left
  | .positive => .right

/-!
Literal visual information from image `910.png`.  Numerical entries are the
values printed in their displayed units, while the physical quantities remain
separate fields of the setup below.
-/
structure ElectricDipoleFigure where
  showsBall : BallLabel → Bool
  ballPlacement : BallLabel → BallPlacement
  shownChargeSign : BallLabel → ChargeSign
  printedMassInGrams : BallLabel → ℝ
  printedChargeMagnitudeInNanocoulombs : BallLabel → ℝ
  rodShown : Bool
  printedSeparationInCentimeters : ℝ
  electricFieldArrowsShown : Bool
  electricFieldArrowDirection : PlanarDirection
  printedFieldStrengthInNewtonsPerCoulomb : ℝ
  dipoleMomentArrowShown : Bool
  dipoleMomentArrowTail : BallLabel
  dipoleMomentArrowHead : BallLabel
  dipoleMomentArrowDirection : PlanarDirection
  angleMarkerShown : Bool
  printedAngleInDegrees : ℝ

/-! ## Independent setup, problem data, and governing laws -/

/-!
Independent physical quantities for the release configuration.  In
particular, the initial angular acceleration is not defined from any answer
choice; it is related to torque and inertia only by the law structure below.
-/
structure ElectricDipoleReleaseSetup where
  figure : ElectricDipoleFigure
  ballMass : BallLabel → MassQuantity
  chargeSign : BallLabel → ChargeSign
  chargeMagnitude : BallLabel → ChargeMagnitudeQuantity
  rodCenterSeparation : LengthQuantity
  electricFieldStrength : ElectricFieldStrengthMagnitude
  electricFieldDirection : PlanarDirection
  rodAndDipoleDirection : PlanarDirection
  rodFieldAngle : Real.Angle
  electricForceMagnitude : BallLabel → ForceMagnitudeQuantity
  electricForceDirection : BallLabel → PlanarDirection
  dipoleMomentMagnitude : ElectricDipoleMomentMagnitude
  momentOfInertiaAboutMidpoint : MomentOfInertiaQuantity
  initialElectricTorqueMagnitude : TorqueMagnitudeQuantity
  initialAngularAccelerationMagnitude : AngularAccelerationMagnitude
  externalFieldModel : ExternalFieldModel
  rodMassModel : RodMassModel
  endpointMassModel : EndpointMassModel
  releaseProtocol : ReleaseProtocol

/-!
The positions, labels, and arrows read directly from the primary raster.  This
record does not constrain the requested angular acceleration.
-/
structure MatchesPrimaryFigure
    (setup : ElectricDipoleReleaseSetup) : Prop where
  bothBallsShown : ∀ ball, setup.figure.showsBall ball = true
  negativeBallAtLowerLeft :
    setup.figure.ballPlacement .negativeBall = .lowerLeft
  positiveBallAtUpperRight :
    setup.figure.ballPlacement .positiveBall = .upperRight
  negativeSignShown :
    setup.figure.shownChargeSign .negativeBall = .negative
  positiveSignShown :
    setup.figure.shownChargeSign .positiveBall = .positive
  bothMassLabelsReadOneGram :
    ∀ ball, setup.figure.printedMassInGrams ball = 1
  bothChargeMagnitudeLabelsReadTenNanocoulombs :
    ∀ ball,
      setup.figure.printedChargeMagnitudeInNanocoulombs ball = 10
  connectingRodShown : setup.figure.rodShown = true
  separationLabelReadsTwoCentimeters :
    setup.figure.printedSeparationInCentimeters = 2
  fieldArrowsShown : setup.figure.electricFieldArrowsShown = true
  fieldArrowsPointRight :
    setup.figure.electricFieldArrowDirection = .right
  fieldLabelReadsTenThousandNewtonsPerCoulomb :
    setup.figure.printedFieldStrengthInNewtonsPerCoulomb = 10000
  dipoleMomentArrowShown : setup.figure.dipoleMomentArrowShown = true
  dipoleMomentArrowStartsAtNegativeBall :
    setup.figure.dipoleMomentArrowTail = .negativeBall
  dipoleMomentArrowEndsAtPositiveBall :
    setup.figure.dipoleMomentArrowHead = .positiveBall
  dipoleMomentArrowRunsUpAndRight :
    setup.figure.dipoleMomentArrowDirection = .upAndRight
  thirtyDegreeMarkerShown : setup.figure.angleMarkerShown = true
  angleLabelReadsThirtyDegrees :
    setup.figure.printedAngleInDegrees = 30

/-!
Physical numerical readouts and idealizations stated by the problem.  The
point-mass model places each labeled ball mass at its center because the
problem supplies no ball radius and declares the rod mass negligible.
-/
structure MatchesProblemData
    (setup : ElectricDipoleReleaseSetup) : Prop where
  negativeBallHasNegativeCharge :
    setup.chargeSign .negativeBall = .negative
  positiveBallHasPositiveCharge :
    setup.chargeSign .positiveBall = .positive
  equalOneGramBallMasses :
    ∀ ball, massInGrams (setup.ballMass ball) = 1
  equalTenNanocoulombChargeMagnitudes :
    ∀ ball,
      chargeMagnitudeInNanocoulombs (setup.chargeMagnitude ball) = 10
  centerSeparationIsTwoCentimeters :
    lengthInCentimeters setup.rodCenterSeparation = 2
  fieldStrengthIsTenThousandNewtonsPerCoulomb :
    electricFieldStrengthInNewtonsPerCoulomb
        setup.electricFieldStrength = 10000
  fieldIsUniform : setup.externalFieldModel = .uniform
  physicalFieldPointsRight : setup.electricFieldDirection = .right
  physicalDipolePointsUpAndRight :
    setup.rodAndDipoleDirection = .upAndRight
  rodMakesThirtyDegreesWithField :
    setup.rodFieldAngle = degreesToAngle 30
  rodMassIsNegligible : setup.rodMassModel = .negligible
  ballsUseEndpointPointMassModel :
    setup.endpointMassModel = .pointMassesAtBallCenters
  heldThenReleasedFromRest :
    setup.releaseProtocol = .heldAtAngleThenReleasedFromRest

/-!
Electrostatic and rotational laws for the idealized release configuration.
They relate independently stored observables and contain neither the target
value `5` nor any answer-choice label.
-/
structure SatisfiesElectricDipoleRotationalLaws
    (setup : ElectricDipoleReleaseSetup) : Prop where
  electricForceMagnitudeLaw :
    ∀ ball,
      forceMagnitudeInNewtons (setup.electricForceMagnitude ball) =
        chargeMagnitudeInCoulombs (setup.chargeMagnitude ball) *
          electricFieldStrengthInNewtonsPerCoulomb
            setup.electricFieldStrength
  electricForceDirectionLaw :
    ∀ ball,
      setup.electricForceDirection ball =
        forceDirectionInRightwardField (setup.chargeSign ball)
  dipoleMomentDefinition :
    dipoleMomentInCoulombMeters setup.dipoleMomentMagnitude =
      chargeMagnitudeInCoulombs
          (setup.chargeMagnitude .positiveBall) *
        lengthInMeters setup.rodCenterSeparation
  uniformFieldDipoleTorqueLaw :
    torqueInNewtonMeters setup.initialElectricTorqueMagnitude =
      dipoleMomentInCoulombMeters setup.dipoleMomentMagnitude *
        electricFieldStrengthInNewtonsPerCoulomb
          setup.electricFieldStrength *
        Real.Angle.sin setup.rodFieldAngle
  twoEndpointPointMassesMomentOfInertia :
    momentOfInertiaInKilogramMetersSquared
        setup.momentOfInertiaAboutMidpoint =
      massInKilograms (setup.ballMass .negativeBall) *
          (lengthInMeters setup.rodCenterSeparation / 2) ^ 2 +
        massInKilograms (setup.ballMass .positiveBall) *
          (lengthInMeters setup.rodCenterSeparation / 2) ^ 2
  rotationalNewtonsSecondLaw :
    torqueInNewtonMeters setup.initialElectricTorqueMagnitude =
      momentOfInertiaInKilogramMetersSquared
          setup.momentOfInertiaAboutMidpoint *
        angularAccelerationInRadiansPerSecondSquared
          setup.initialAngularAccelerationMagnitude

/-! ## Intermediate physical consequences -/

/-- The applied electric couple initially has magnitude `10⁻⁶ N m`. -/
lemma initialElectricTorqueInNewtonMeters_eq_oneMillionth
    (setup : ElectricDipoleReleaseSetup)
    (hData : MatchesProblemData setup)
    (hLaws : SatisfiesElectricDipoleRotationalLaws setup) :
    torqueInNewtonMeters setup.initialElectricTorqueMagnitude =
      1 / 1000000 := by
  have hChargeLabel :=
    hData.equalTenNanocoulombChargeMagnitudes BallLabel.positiveBall
  have hCharge :
      chargeMagnitudeInCoulombs
          (setup.chargeMagnitude BallLabel.positiveBall) =
        1 / 100000000 := by
    norm_num [chargeMagnitudeInNanocoulombs] at hChargeLabel ⊢
    linarith
  have hLengthLabel := hData.centerSeparationIsTwoCentimeters
  have hLength :
      lengthInMeters setup.rodCenterSeparation = 1 / 50 := by
    norm_num [lengthInCentimeters] at hLengthLabel ⊢
    linarith
  calc
    torqueInNewtonMeters setup.initialElectricTorqueMagnitude =
        dipoleMomentInCoulombMeters setup.dipoleMomentMagnitude *
          electricFieldStrengthInNewtonsPerCoulomb
            setup.electricFieldStrength *
          Real.Angle.sin setup.rodFieldAngle :=
      hLaws.uniformFieldDipoleTorqueLaw
    _ =
        (chargeMagnitudeInCoulombs
              (setup.chargeMagnitude BallLabel.positiveBall) *
            lengthInMeters setup.rodCenterSeparation) *
          electricFieldStrengthInNewtonsPerCoulomb
            setup.electricFieldStrength *
          Real.Angle.sin setup.rodFieldAngle := by
      rw [hLaws.dipoleMomentDefinition]
    _ = 1 / 1000000 := by
      rw [hCharge, hLength,
        hData.fieldStrengthIsTenThousandNewtonsPerCoulomb,
        hData.rodMakesThirtyDegreesWithField]
      rw [degreesToAngle, Real.Angle.sin_coe]
      rw [show (30 : ℝ) * Real.pi / 180 = Real.pi / 6 by ring]
      norm_num

/-- The two `1 g` endpoint masses have axial inertia `2 * 10⁻⁷ kg m²`. -/
lemma momentOfInertiaInKilogramMetersSquared_eq_twoTenthsMillionth
    (setup : ElectricDipoleReleaseSetup)
    (hData : MatchesProblemData setup)
    (hLaws : SatisfiesElectricDipoleRotationalLaws setup) :
    momentOfInertiaInKilogramMetersSquared
        setup.momentOfInertiaAboutMidpoint =
      1 / 5000000 := by
  have hNegativeMassLabel :=
    hData.equalOneGramBallMasses BallLabel.negativeBall
  have hPositiveMassLabel :=
    hData.equalOneGramBallMasses BallLabel.positiveBall
  have hNegativeMass :
      massInKilograms (setup.ballMass BallLabel.negativeBall) =
        1 / 1000 := by
    norm_num [massInGrams] at hNegativeMassLabel ⊢
    linarith
  have hPositiveMass :
      massInKilograms (setup.ballMass BallLabel.positiveBall) =
        1 / 1000 := by
    norm_num [massInGrams] at hPositiveMassLabel ⊢
    linarith
  have hLengthLabel := hData.centerSeparationIsTwoCentimeters
  have hLength :
      lengthInMeters setup.rodCenterSeparation = 1 / 50 := by
    norm_num [lengthInCentimeters] at hLengthLabel ⊢
    linarith
  calc
    momentOfInertiaInKilogramMetersSquared
          setup.momentOfInertiaAboutMidpoint =
        massInKilograms (setup.ballMass BallLabel.negativeBall) *
            (lengthInMeters setup.rodCenterSeparation / 2) ^ 2 +
          massInKilograms (setup.ballMass BallLabel.positiveBall) *
            (lengthInMeters setup.rodCenterSeparation / 2) ^ 2 :=
      hLaws.twoEndpointPointMassesMomentOfInertia
    _ = 1 / 5000000 := by
      rw [hNegativeMass, hPositiveMass, hLength]
      norm_num

/-! ## Displayed answers and current target -/

/-- Labels of the four angular-acceleration choices in the source. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Radian-per-second-squared readout printed beside each choice. -/
def displayedAngularAccelerationInRadiansPerSecondSquared :
    AnswerChoice → ℝ
  | .A => 3
  | .B => 2
  | .C => 5
  | .D => 6

/-- The answer label recorded by the source dataset; it is not a premise. -/
def recordedDatasetAnswer : AnswerChoice := .C

/-- A displayed choice agrees with the independently modeled acceleration. -/
def AnswerMatchesInitialAngularAcceleration
    (setup : ElectricDipoleReleaseSetup) (choice : AnswerChoice) : Prop :=
  angularAccelerationInRadiansPerSecondSquared
      setup.initialAngularAccelerationMagnitude =
    displayedAngularAccelerationInRadiansPerSecondSquared choice

/-!
The initial dipole torque is `10⁻⁶ N m` and the two endpoint masses have
moment of inertia `2 * 10⁻⁷ kg m²`, so `alpha = tau / I = 5 rad/s²`.
This is answer C.

Blueprint: `thm:physics:phyx_mini_0910:target`.
-/
theorem initialAngularAcceleration_eq_fiveRadiansPerSecondSquared
    (setup : ElectricDipoleReleaseSetup)
    (hFigure : MatchesPrimaryFigure setup)
    (hData : MatchesProblemData setup)
    (hLaws : SatisfiesElectricDipoleRotationalLaws setup) :
    angularAccelerationInRadiansPerSecondSquared
        setup.initialAngularAccelerationMagnitude = 5 ∧
      AnswerMatchesInitialAngularAcceleration
        setup recordedDatasetAnswer := by
  have hTorque :=
    initialElectricTorqueInNewtonMeters_eq_oneMillionth setup hData hLaws
  have hInertia :=
    momentOfInertiaInKilogramMetersSquared_eq_twoTenthsMillionth
      setup hData hLaws
  have hAcceleration :
      angularAccelerationInRadiansPerSecondSquared
          setup.initialAngularAccelerationMagnitude = 5 := by
    have hNewton := hLaws.rotationalNewtonsSecondLaw
    rw [hTorque, hInertia] at hNewton
    norm_num at hNewton ⊢
    linarith
  refine ⟨hAcceleration, ?_⟩
  simpa [AnswerMatchesInitialAngularAcceleration, recordedDatasetAnswer,
    displayedAngularAccelerationInRadiansPerSecondSquared] using hAcceleration

end PhyXMiniProblems.ProblemPhyXMini0910
