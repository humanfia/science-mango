import Mathlib
import Physlib.Electromagnetism.Basic
import Physlib.Units.WithDim.Basic

/- USER: The assigned Lean file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0891

open Dimension

/-!
# Electric field holding a charged ball against a spring

The primary raster shows a positively charged ball suspended from a ceiling
pivot by a `60 cm` tether.  The tether is deflected `15°` to the right of the
vertical.  A horizontal plastic spring joins the ball to the left wall and has
spring constant `0.050 N/m`; its relaxed endpoint is the vertical dashed line
through the pivot.  The ball has mass `3.0 g` and charge `20 nC`, and a uniform
electric field points to the right.

The auxiliary caption describes the `60 cm` label as a distance from the wall,
but the primary image places that label along the ceiling tether.  The model
therefore follows the image: the spring extension is the ball's horizontal
displacement `L sin θ` from the dashed vertical.

Mass, charge, length, acceleration, force, spring constant, and electric-field
strength are unit-independent Physlib quantities.  Real numbers occur only at
coherent-SI readout boundaries, as angle readouts, and in literal figure or
answer-choice data.

Assumption/target split:

* governing laws: deflected-tether geometry, Hooke's law, `F_e = q E`,
  `W = m g`, uniform horizontal-field calibration, and the two components of
  static force balance;
* previous-part results: none;
* figure/data readouts: the plastic spring and dashed relaxed reference, the
  `60 cm`, `15°`, `0.050 N/m`, `3.0 g`, and `20 nC` labels, the rightward field
  arrows, and the standard terrestrial readout `g = 9.8 m/s²`;
* current target conclusions: the derived electric-field-strength formula and
  the fact that its value is uniquely closest to displayed answer C,
  `7.5 * 10^5 N/C`.

Neither target conclusion is a field of the setup or of any premise
structure.
-/

/-! ## Dimensionful physical quantities and coherent-SI readouts -/

/-- Dimension of acceleration, `L T⁻²`. -/
def accelerationDimension : Dimension := L𝓭 * T𝓭⁻¹ * T𝓭⁻¹

/-- Dimension of force, `M L T⁻²`. -/
def forceDimension : Dimension := M𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹

/-- Dimension of a linear spring constant, `M T⁻² = N/m`. -/
def springConstantDimension : Dimension := M𝓭 * T𝓭⁻¹ * T𝓭⁻¹

/-- Dimension of electric-field strength, `M L T⁻² C⁻¹ = N/C`. -/
def electricFieldStrengthDimension : Dimension :=
  M𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹ * C𝓭⁻¹

/-- A nonnegative, unit-independent physical mass. -/
abbrev MassQuantity : Type := Dimensionful (WithDim M𝓭 NNReal)

/-- A nonnegative, unit-independent physical length. -/
abbrev LengthQuantity : Type := Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative electric-charge magnitude. -/
abbrev ChargeMagnitudeQuantity : Type :=
  Dimensionful (WithDim C𝓭 NNReal)

/-- A nonnegative acceleration magnitude. -/
abbrev AccelerationMagnitudeQuantity : Type :=
  Dimensionful (WithDim accelerationDimension NNReal)

/-- A nonnegative force magnitude. -/
abbrev ForceMagnitudeQuantity : Type :=
  Dimensionful (WithDim forceDimension NNReal)

/-- A nonnegative linear spring constant. -/
abbrev SpringConstantQuantity : Type :=
  Dimensionful (WithDim springConstantDimension NNReal)

/-- A nonnegative electric-field strength. -/
abbrev ElectricFieldStrengthQuantity : Type :=
  Dimensionful (WithDim electricFieldStrengthDimension NNReal)

/-- Coherent-SI mass readout in kilograms. -/
def massInKilograms (mass : MassQuantity) : ℝ :=
  ((mass UnitChoices.SI).val : ℝ)

/-- Figure-scale mass readout in grams. -/
def massInGrams (mass : MassQuantity) : ℝ :=
  1000 * massInKilograms mass

/-- Coherent-SI length readout in metres. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  ((length UnitChoices.SI).val : ℝ)

/-- Figure-scale length readout in centimetres. -/
def lengthInCentimeters (length : LengthQuantity) : ℝ :=
  100 * lengthInMeters length

/-- Coherent-SI charge-magnitude readout in coulombs. -/
def chargeInCoulombs (charge : ChargeMagnitudeQuantity) : ℝ :=
  ((charge UnitChoices.SI).val : ℝ)

/-- Figure-scale charge-magnitude readout in nanocoulombs. -/
def chargeInNanocoulombs (charge : ChargeMagnitudeQuantity) : ℝ :=
  (10 : ℝ) ^ 9 * chargeInCoulombs charge

/-- Coherent-SI acceleration readout in metres per second squared. -/
def accelerationInMetersPerSecondSquared
    (acceleration : AccelerationMagnitudeQuantity) : ℝ :=
  ((acceleration UnitChoices.SI).val : ℝ)

/-- Coherent-SI force-magnitude readout in newtons. -/
def forceInNewtons (force : ForceMagnitudeQuantity) : ℝ :=
  ((force UnitChoices.SI).val : ℝ)

/-- Coherent-SI spring-constant readout in newtons per metre. -/
def springConstantInNewtonsPerMeter
    (springConstant : SpringConstantQuantity) : ℝ :=
  ((springConstant UnitChoices.SI).val : ℝ)

/-- Coherent-SI electric-field-strength readout in newtons per coulomb. -/
def electricFieldStrengthInNewtonsPerCoulomb
    (strength : ElectricFieldStrengthQuantity) : ℝ :=
  ((strength UnitChoices.SI).val : ℝ)

/-- Convert a literal degree readout into radians. -/
def degreesToRadians (degrees : ℝ) : ℝ := degrees * Real.pi / 180

/-! ## Primary-figure vocabulary and physical setup -/

/-- Constitutive/electrical classification of the spring. -/
inductive SpringMaterial where
  | plasticInsulator
  | electricalConductor
  deriving DecidableEq, Repr

/-- Force roles in the free-body diagram of the suspended ball. -/
inductive BallForceRole where
  | electric
  | spring
  | tetherTension
  | weight
  deriving DecidableEq, Fintype, Repr

/-- Qualitative planar directions needed by the free-body diagram. -/
inductive PlanarDirection where
  | left
  | right
  | down
  | alongTetherTowardPivot
  deriving DecidableEq, Repr

/-!
Literal readouts and visible features of image `891.png`.  The `60 cm` entry is
named as a tether label because that is where it is placed in the raster.
-/
structure ChargedBallSpringFigure where
  ceilingSupportShown : Bool
  leftWallShown : Bool
  ballShown : Bool
  horizontalSpringShown : Bool
  suspensionTetherShown : Bool
  verticalDashedReferenceShown : Bool
  relaxedSpringEndsAtDashedReference : Bool
  electricFieldArrowsShown : Bool
  electricFieldArrowsPointRight : Bool
  tetherLengthLabelCentimeters : ℝ
  deflectionAngleLabelDegrees : ℝ
  springConstantLabelNewtonsPerMeter : ℝ
  ballMassLabelGrams : ℝ
  ballChargeLabelNanocoulombs : ℝ

/-!
Independent physical quantities of the apparatus.  In particular,
`electricFieldStrength` is not defined from an answer choice.  Physlib's full
spacetime electric field is retained in addition to its nonnegative SI
strength readout.
-/
structure ChargedBallSpringSetup where
  figure : ChargedBallSpringFigure
  springMaterial : SpringMaterial
  ballMass : MassQuantity
  ballChargeBeforeSpringContact : ChargeMagnitudeQuantity
  ballChargeMagnitude : ChargeMagnitudeQuantity
  tetherLength : LengthQuantity
  deflectionAngleRadians : ℝ
  bobHorizontalDisplacement : LengthQuantity
  springExtension : LengthQuantity
  springConstant : SpringConstantQuantity
  gravitationalAcceleration : AccelerationMagnitudeQuantity
  weightMagnitude : ForceMagnitudeQuantity
  springForceMagnitude : ForceMagnitudeQuantity
  tetherTensionMagnitude : ForceMagnitudeQuantity
  electricForceMagnitude : ForceMagnitudeQuantity
  electricFieldStrength : ElectricFieldStrengthQuantity
  electricField : Electromagnetism.ElectricField 3
  uniformElectricFieldVector : EuclideanSpace ℝ (Fin 3)
  forceDirection : BallForceRole → PlanarDirection

/-! ## Figure data, scenario, and physical nondegeneracy -/

/-- Visible features and numerical labels transcribed from the primary image. -/
structure MatchesChargedBallSpringFigure
    (setup : ChargedBallSpringSetup) : Prop where
  ceilingSupport : setup.figure.ceilingSupportShown = true
  leftWall : setup.figure.leftWallShown = true
  ball : setup.figure.ballShown = true
  horizontalSpring : setup.figure.horizontalSpringShown = true
  suspensionTether : setup.figure.suspensionTetherShown = true
  dashedVertical : setup.figure.verticalDashedReferenceShown = true
  relaxedSpringReference :
    setup.figure.relaxedSpringEndsAtDashedReference = true
  fieldArrows : setup.figure.electricFieldArrowsShown = true
  fieldArrowsRight : setup.figure.electricFieldArrowsPointRight = true
  tetherLabel : setup.figure.tetherLengthLabelCentimeters = 60
  angleLabel : setup.figure.deflectionAngleLabelDegrees = 15
  springConstantLabel :
    setup.figure.springConstantLabelNewtonsPerMeter = (0.050 : ℝ)
  massLabel : setup.figure.ballMassLabelGrams = 3.0
  chargeLabel : setup.figure.ballChargeLabelNanocoulombs = 20
  tetherReadout :
    lengthInCentimeters setup.tetherLength =
      setup.figure.tetherLengthLabelCentimeters
  angleReadout :
    setup.deflectionAngleRadians =
      degreesToRadians setup.figure.deflectionAngleLabelDegrees
  springConstantReadout :
    springConstantInNewtonsPerMeter setup.springConstant =
      setup.figure.springConstantLabelNewtonsPerMeter
  massReadout :
    massInGrams setup.ballMass = setup.figure.ballMassLabelGrams
  chargeReadout :
    chargeInNanocoulombs setup.ballChargeMagnitude =
      setup.figure.ballChargeLabelNanocoulombs

/-!
The qualitative scenario, including the insulating role of the plastic spring
and the directions of all four forces on the ball.  Charge preservation is a
physical consequence of the stated insulation, not an electric-field answer.
-/
structure MatchesChargedBallSpringScenario
    (setup : ChargedBallSpringSetup) : Prop where
  plasticSpring : setup.springMaterial = .plasticInsulator
  chargePreservedByInsulatingSpring :
    setup.ballChargeMagnitude = setup.ballChargeBeforeSpringContact
  electricForceRight : setup.forceDirection .electric = .right
  springForceLeft : setup.forceDirection .spring = .left
  tetherForceTowardPivot :
    setup.forceDirection .tetherTension = .alongTetherTowardPivot
  weightDown : setup.forceDirection .weight = .down

/-- Standard terrestrial gravitational acceleration used by the calculation. -/
structure UsesStandardTerrestrialGravity
    (setup : ChargedBallSpringSetup) : Prop where
  gravityReadout :
    accelerationInMetersPerSecondSquared setup.gravitationalAcceleration = 9.8

/-- Positivity and the acute-angle regime required by the physical setup. -/
structure HasPhysicalChargedBallSpringParameters
    (setup : ChargedBallSpringSetup) : Prop where
  positiveMass : 0 < massInKilograms setup.ballMass
  positiveCharge : 0 < chargeInCoulombs setup.ballChargeMagnitude
  positiveTetherLength : 0 < lengthInMeters setup.tetherLength
  positiveSpringConstant :
    0 < springConstantInNewtonsPerMeter setup.springConstant
  positiveGravity :
    0 < accelerationInMetersPerSecondSquared setup.gravitationalAcceleration
  positiveTetherTension :
    0 < forceInNewtons setup.tetherTensionMagnitude
  positiveFieldStrength :
    0 < electricFieldStrengthInNewtonsPerCoulomb setup.electricFieldStrength
  angleAcute :
    0 < setup.deflectionAngleRadians ∧
      setup.deflectionAngleRadians < Real.pi / 2

/-! ## Governing geometry and field laws -/

/-!
The dashed line is the zero-extension reference.  Consequently the ball's
horizontal displacement is `L sin θ`, and that displacement is exactly the
extension of the horizontal spring.
-/
structure SatisfiesDeflectedTetherAndSpringGeometry
    (setup : ChargedBallSpringSetup) : Prop where
  horizontalDisplacement :
    lengthInMeters setup.bobHorizontalDisplacement =
      lengthInMeters setup.tetherLength *
        Real.sin setup.deflectionAngleRadians
  springExtensionFromDashedReference :
    lengthInMeters setup.springExtension =
      lengthInMeters setup.bobHorizontalDisplacement

/-!
The spacetime field is uniform and equal to the displayed rightward vector.
Coordinates `0`, `1`, and `2` are respectively rightward horizontal, upward
vertical, and out of the page.
-/
structure SatisfiesUniformHorizontalElectricField
    (setup : ChargedBallSpringSetup) : Prop where
  fieldUniform : ∀ time position,
    setup.electricField time position = setup.uniformElectricFieldVector
  rightwardComponent :
    setup.uniformElectricFieldVector (0 : Fin 3) =
      electricFieldStrengthInNewtonsPerCoulomb setup.electricFieldStrength
  zeroVerticalComponent :
    setup.uniformElectricFieldVector (1 : Fin 3) = 0
  zeroOutOfPageComponent :
    setup.uniformElectricFieldVector (2 : Fin 3) = 0
  strengthMatchesVectorNorm :
    ‖setup.uniformElectricFieldVector‖ =
      electricFieldStrengthInNewtonsPerCoulomb setup.electricFieldStrength

/-!
Hooke's law, electric force, weight, and static force balance, all stated at a
coherent-SI boundary.  The horizontal balance has the rightward electric force
opposed by both the spring and the tether's horizontal component.  No numerical
field strength or answer choice occurs in these laws.
-/
structure SatisfiesChargedBallStaticEquilibrium
    (setup : ChargedBallSpringSetup) : Prop where
  hookeLaw :
    forceInNewtons setup.springForceMagnitude =
      springConstantInNewtonsPerMeter setup.springConstant *
        lengthInMeters setup.springExtension
  electricForceLaw :
    forceInNewtons setup.electricForceMagnitude =
      chargeInCoulombs setup.ballChargeMagnitude *
        electricFieldStrengthInNewtonsPerCoulomb setup.electricFieldStrength
  weightLaw :
    forceInNewtons setup.weightMagnitude =
      massInKilograms setup.ballMass *
        accelerationInMetersPerSecondSquared setup.gravitationalAcceleration
  verticalForceBalance :
    forceInNewtons setup.tetherTensionMagnitude *
        Real.cos setup.deflectionAngleRadians =
      forceInNewtons setup.weightMagnitude
  horizontalForceBalance :
    forceInNewtons setup.electricForceMagnitude =
      forceInNewtons setup.tetherTensionMagnitude *
          Real.sin setup.deflectionAngleRadians +
        forceInNewtons setup.springForceMagnitude

/-! ## Derived field strength and displayed answers -/

/-!
Eliminating tension and the two intermediate force magnitudes gives the exact
static-equilibrium field-strength formula.  It is a conclusion, not a premise
or a definition of `electricFieldStrength`.
-/
theorem electricFieldStrength_closedForm
    (setup : ChargedBallSpringSetup)
    (_figure : MatchesChargedBallSpringFigure setup)
    (_scenario : MatchesChargedBallSpringScenario setup)
    (_gravity : UsesStandardTerrestrialGravity setup)
    (_physical : HasPhysicalChargedBallSpringParameters setup)
    (_geometry : SatisfiesDeflectedTetherAndSpringGeometry setup)
    (_field : SatisfiesUniformHorizontalElectricField setup)
    (_equilibrium : SatisfiesChargedBallStaticEquilibrium setup) :
    electricFieldStrengthInNewtonsPerCoulomb setup.electricFieldStrength =
      (massInKilograms setup.ballMass *
            accelerationInMetersPerSecondSquared
              setup.gravitationalAcceleration *
            Real.tan setup.deflectionAngleRadians +
          springConstantInNewtonsPerMeter setup.springConstant *
            lengthInMeters setup.tetherLength *
            Real.sin setup.deflectionAngleRadians) /
        chargeInCoulombs setup.ballChargeMagnitude := by
  have hcharge :
      chargeInCoulombs setup.ballChargeMagnitude ≠ 0 :=
    ne_of_gt _physical.positiveCharge
  have hweight :
      0 < forceInNewtons setup.weightMagnitude := by
    rw [_equilibrium.weightLaw]
    exact mul_pos _physical.positiveMass _physical.positiveGravity
  have hcos :
      Real.cos setup.deflectionAngleRadians ≠ 0 := by
    intro h
    have hvertical := _equilibrium.verticalForceBalance
    rw [h, mul_zero] at hvertical
    linarith
  have htensionHorizontal :
      forceInNewtons setup.tetherTensionMagnitude *
          Real.sin setup.deflectionAngleRadians =
        forceInNewtons setup.weightMagnitude *
          Real.tan setup.deflectionAngleRadians := by
    rw [Real.tan_eq_sin_div_cos, ← _equilibrium.verticalForceBalance]
    field_simp
  have hspring :
      forceInNewtons setup.springForceMagnitude =
        springConstantInNewtonsPerMeter setup.springConstant *
          lengthInMeters setup.tetherLength *
            Real.sin setup.deflectionAngleRadians := by
    rw [_equilibrium.hookeLaw,
      _geometry.springExtensionFromDashedReference,
      _geometry.horizontalDisplacement]
    ring
  have helectric :
      forceInNewtons setup.electricForceMagnitude =
        massInKilograms setup.ballMass *
              accelerationInMetersPerSecondSquared
                setup.gravitationalAcceleration *
              Real.tan setup.deflectionAngleRadians +
            springConstantInNewtonsPerMeter setup.springConstant *
              lengthInMeters setup.tetherLength *
              Real.sin setup.deflectionAngleRadians := by
    rw [_equilibrium.horizontalForceBalance, htensionHorizontal,
      _equilibrium.weightLaw, hspring]
  apply (eq_div_iff hcharge).2
  rw [mul_comm, ← _equilibrium.electricForceLaw]
  exact helectric

/-- Labels of the four electric-field-strength choices in the source. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Literal field-strength readout, in newtons per coulomb, for each choice. -/
def answerChoiceFieldStrengthInNewtonsPerCoulomb : AnswerChoice → ℝ
  | .A => (1.25 : ℝ) * 10 ^ 3
  | .B => (1.35 : ℝ) * 10 ^ 5
  | .C => (7.5 : ℝ) * 10 ^ 5
  | .D => (5.33 : ℝ) * 10 ^ 5

/-- The answer label recorded by the source dataset. -/
def recordedDatasetAnswer : AnswerChoice := .C

/-- Absolute error of a displayed choice from the modeled physical field. -/
def answerChoiceAbsoluteError
    (setup : ChargedBallSpringSetup) (choice : AnswerChoice) : ℝ :=
  |electricFieldStrengthInNewtonsPerCoulomb setup.electricFieldStrength -
    answerChoiceFieldStrengthInNewtonsPerCoulomb choice|

/-- A selected choice is strictly closer than every other displayed choice. -/
def IsUniqueClosestAnswer
    (setup : ChargedBallSpringSetup) (selected : AnswerChoice) : Prop :=
  ∀ other, other ≠ selected →
    answerChoiceAbsoluteError setup selected <
      answerChoiceAbsoluteError setup other

/-!
For the exact trigonometric model and the printed data, the field is about
`7.8 * 10^5 N/C`; among the coarse displayed choices this uniquely selects
`7.5 * 10^5 N/C`, answer C.  The target selection appears only in this
conclusion.
-/
theorem electricFieldStrength_agreesWithChoiceC
    (setup : ChargedBallSpringSetup)
    (_figure : MatchesChargedBallSpringFigure setup)
    (_scenario : MatchesChargedBallSpringScenario setup)
    (_gravity : UsesStandardTerrestrialGravity setup)
    (_physical : HasPhysicalChargedBallSpringParameters setup)
    (_geometry : SatisfiesDeflectedTetherAndSpringGeometry setup)
    (_field : SatisfiesUniformHorizontalElectricField setup)
    (_equilibrium : SatisfiesChargedBallStaticEquilibrium setup) :
    IsUniqueClosestAnswer setup .C := by
  have hmass :
      massInKilograms setup.ballMass = (3 : ℝ) / 1000 := by
    have h := _figure.massReadout
    rw [_figure.massLabel] at h
    norm_num [massInGrams] at h ⊢
    linarith
  have hcharge :
      chargeInCoulombs setup.ballChargeMagnitude =
        (20 : ℝ) / 10 ^ 9 := by
    have h := _figure.chargeReadout
    rw [_figure.chargeLabel] at h
    norm_num [chargeInNanocoulombs] at h ⊢
    linarith
  have hlength :
      lengthInMeters setup.tetherLength = (60 : ℝ) / 100 := by
    have h := _figure.tetherReadout
    rw [_figure.tetherLabel] at h
    norm_num [lengthInCentimeters] at h ⊢
    linarith
  have hspring :
      springConstantInNewtonsPerMeter setup.springConstant =
        (5 : ℝ) / 100 := by
    calc
      springConstantInNewtonsPerMeter setup.springConstant =
          setup.figure.springConstantLabelNewtonsPerMeter :=
        _figure.springConstantReadout
      _ = (0.050 : ℝ) := _figure.springConstantLabel
      _ = (5 : ℝ) / 100 := by norm_num
  have hgravity :
      accelerationInMetersPerSecondSquared
          setup.gravitationalAcceleration = (98 : ℝ) / 10 := by
    rw [_gravity.gravityReadout]
    norm_num
  have hangle :
      setup.deflectionAngleRadians = Real.pi / 12 := by
    calc
      setup.deflectionAngleRadians =
          degreesToRadians setup.figure.deflectionAngleLabelDegrees :=
        _figure.angleReadout
      _ = degreesToRadians 15 := by rw [_figure.angleLabel]
      _ = Real.pi / 12 := by
        simp only [degreesToRadians]
        ring
  have hsqrtSix :
      Real.sqrt 6 = Real.sqrt 2 * Real.sqrt 3 := by
    rw [show (6 : ℝ) = 2 * 3 by norm_num,
      Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
  have hsin :
      Real.sin (Real.pi / 12) =
        (Real.sqrt 6 - Real.sqrt 2) / 4 := by
    calc
      Real.sin (Real.pi / 12) =
          Real.sin (Real.pi / 4 - Real.pi / 6) := by
        congr 1
        ring
      _ = (Real.sqrt 6 - Real.sqrt 2) / 4 := by
        rw [Real.sin_sub, Real.sin_pi_div_four,
          Real.cos_pi_div_six, Real.cos_pi_div_four,
          Real.sin_pi_div_six, hsqrtSix]
        ring
  have htan :
      Real.tan (Real.pi / 12) = 2 - Real.sqrt 3 := by
    have hsqrtTwo : Real.sqrt 2 ≠ 0 := by positivity
    have hsqrtThreePlusOne : Real.sqrt 3 + 1 ≠ 0 := by positivity
    rw [Real.tan_eq_sin_div_cos]
    rw [show Real.pi / 12 = Real.pi / 4 - Real.pi / 6 by ring,
      Real.sin_sub, Real.cos_sub, Real.sin_pi_div_four,
      Real.cos_pi_div_six, Real.cos_pi_div_four,
      Real.sin_pi_div_six]
    field_simp
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  have hsqrtTwoLower : (141 : ℝ) / 100 < Real.sqrt 2 := by
    rw [Real.lt_sqrt (by norm_num)]
    norm_num
  have hsqrtTwoUpper : Real.sqrt 2 < (142 : ℝ) / 100 := by
    rw [Real.sqrt_lt' (by norm_num)]
    norm_num
  have hsqrtThreeLower : (173 : ℝ) / 100 < Real.sqrt 3 := by
    rw [Real.lt_sqrt (by norm_num)]
    norm_num
  have hsqrtThreeUpper : Real.sqrt 3 < (174 : ℝ) / 100 := by
    rw [Real.sqrt_lt' (by norm_num)]
    norm_num
  have hsqrtSixLower : (244 : ℝ) / 100 < Real.sqrt 6 := by
    rw [Real.lt_sqrt (by norm_num)]
    norm_num
  have hsqrtSixUpper : Real.sqrt 6 < (245 : ℝ) / 100 := by
    rw [Real.sqrt_lt' (by norm_num)]
    norm_num
  have hfield := electricFieldStrength_closedForm setup _figure _scenario
    _gravity _physical _geometry _field _equilibrium
  rw [hmass, hgravity, hangle, htan, hspring, hlength, hsin,
    hcharge] at hfield
  norm_num at hfield
  have hfieldLower :
      (750000 : ℝ) <
        electricFieldStrengthInNewtonsPerCoulomb
          setup.electricFieldStrength := by
    linarith only [hfield, hsqrtThreeUpper, hsqrtSixLower,
      hsqrtTwoUpper]
  have hfieldUpper :
      electricFieldStrengthInNewtonsPerCoulomb
          setup.electricFieldStrength < (800000 : ℝ) := by
    linarith only [hfield, hsqrtThreeLower, hsqrtSixUpper,
      hsqrtTwoLower]
  have hchoiceCPositive :
      0 < electricFieldStrengthInNewtonsPerCoulomb
          setup.electricFieldStrength - 750000 := by
    linarith only [hfieldLower]
  have hchoiceAPositive :
      0 < electricFieldStrengthInNewtonsPerCoulomb
          setup.electricFieldStrength - 1250 := by
    linarith only [hfieldLower]
  have hchoiceBPositive :
      0 < electricFieldStrengthInNewtonsPerCoulomb
          setup.electricFieldStrength - 135000 := by
    linarith only [hfieldLower]
  have hchoiceDPositive :
      0 < electricFieldStrengthInNewtonsPerCoulomb
          setup.electricFieldStrength - 533000 := by
    linarith only [hfieldLower]
  have hanswerA :
      answerChoiceFieldStrengthInNewtonsPerCoulomb .A = 1250 := by
    norm_num [answerChoiceFieldStrengthInNewtonsPerCoulomb]
  have hanswerB :
      answerChoiceFieldStrengthInNewtonsPerCoulomb .B = 135000 := by
    norm_num [answerChoiceFieldStrengthInNewtonsPerCoulomb]
  have hanswerC :
      answerChoiceFieldStrengthInNewtonsPerCoulomb .C = 750000 := by
    norm_num [answerChoiceFieldStrengthInNewtonsPerCoulomb]
  have hanswerD :
      answerChoiceFieldStrengthInNewtonsPerCoulomb .D = 533000 := by
    norm_num [answerChoiceFieldStrengthInNewtonsPerCoulomb]
  intro other hother
  fin_cases other
  · simp only [answerChoiceAbsoluteError, hanswerC, hanswerA]
    rw [abs_of_pos hchoiceCPositive, abs_of_pos hchoiceAPositive]
    linarith only []
  · simp only [answerChoiceAbsoluteError, hanswerC, hanswerB]
    rw [abs_of_pos hchoiceCPositive, abs_of_pos hchoiceBPositive]
    linarith only []
  · exact (hother rfl).elim
  · simp only [answerChoiceAbsoluteError, hanswerC, hanswerD]
    rw [abs_of_pos hchoiceCPositive, abs_of_pos hchoiceDPositive]
    linarith only []

end PhyXMiniProblems.ProblemPhyXMini0891
