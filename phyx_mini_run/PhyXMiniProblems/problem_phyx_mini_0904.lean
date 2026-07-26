import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Physlib.Electromagnetism.Basic
import Physlib.Units.WithDim.Basic

/- USER: The assigned Lean file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0904

open Dimension

/-!
# Charge on a ball suspended in a horizontal electric field

The primary image shows a ball labelled `q` and `5.0 g` hanging from a fixed
support.  Its thread is inclined by `20°` to a dashed vertical reference, and
the ball is displaced to the right.  Parallel arrows labelled `E⃗` point to
the right.  The prose gives the field strength as `100000 N/C`.

Mass, charge, field strength, acceleration, force, and thread length are
unit-independent Physlib `Dimensionful` quantities.  Real numbers occur only
as coherent-SI readouts, explicit gram or microcoulomb readouts, a
dimensionless angle, and displayed answer data.  The setup also retains
Physlib's spacetime-dependent two-dimensional electric field.

Assumption/target split:

* governing laws: `Fₑ = qE`, `W = mg`, and horizontal and vertical static
  force balance for the inclined thread;
* previous-part results: none;
* figure/data readouts: `m = 5.0 g`, `E = 100000 N/C`, `θ = 20°`, a fixed
  upper support, a dashed vertical reference, rightward field arrows, and a
  rightward displacement of the ball;
* current target: the exact charge readout is
  `0.49 * tan (π / 9) μC`, which uniquely rounds to displayed choice C,
  `0.18 μC`.

No premise or setup field fixes the ball's charge to either the exact target
or to a displayed answer value.
-/

/-! ## Dimensionful physical quantities and coherent-SI readouts -/

/-- The dimension `L T⁻²` of acceleration. -/
def accelerationDimension : Dimension :=
  L𝓭 * T𝓭⁻¹ * T𝓭⁻¹

/-- The dimension `M L T⁻²` of force. -/
def forceDimension : Dimension :=
  M𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹

/-- The dimension `M L T⁻² C⁻¹` of electric-field strength. -/
def electricFieldStrengthDimension : Dimension :=
  forceDimension * C𝓭⁻¹

/-- A nonnegative, unit-independent physical mass. -/
abbrev MassQuantity : Type :=
  Dimensionful (WithDim M𝓭 NNReal)

/-- A signed, unit-independent electric charge. -/
abbrev SignedChargeQuantity : Type :=
  Dimensionful (WithDim C𝓭 ℝ)

/-- A nonnegative, unit-independent electric-field magnitude. -/
abbrev ElectricFieldStrengthQuantity : Type :=
  Dimensionful (WithDim electricFieldStrengthDimension NNReal)

/-- A nonnegative, unit-independent acceleration magnitude. -/
abbrev AccelerationQuantity : Type :=
  Dimensionful (WithDim accelerationDimension NNReal)

/-- A nonnegative, unit-independent force magnitude. -/
abbrev ForceMagnitudeQuantity : Type :=
  Dimensionful (WithDim forceDimension NNReal)

/-- A signed component of a unit-independent force. -/
abbrev SignedForceQuantity : Type :=
  Dimensionful (WithDim forceDimension ℝ)

/-- A nonnegative, unit-independent physical length. -/
abbrev LengthQuantity : Type :=
  Dimensionful (WithDim L𝓭 NNReal)

/-- Coherent-SI mass readout, in kilograms. -/
def massInKilograms (mass : MassQuantity) : ℝ :=
  ((mass UnitChoices.SI).val : ℝ)

/-- Gram readout used by the label on the ball. -/
def massInGrams (mass : MassQuantity) : ℝ :=
  1000 * massInKilograms mass

/-- Coherent-SI signed-charge readout, in coulombs. -/
def chargeInCoulombs (charge : SignedChargeQuantity) : ℝ :=
  (charge UnitChoices.SI).val

/-- Microcoulomb readout used by the answer choices. -/
def chargeInMicrocoulombs (charge : SignedChargeQuantity) : ℝ :=
  (10 : ℝ) ^ 6 * chargeInCoulombs charge

/-- Coherent-SI electric-field readout, in newtons per coulomb. -/
def fieldStrengthInNewtonsPerCoulomb
    (fieldStrength : ElectricFieldStrengthQuantity) : ℝ :=
  ((fieldStrength UnitChoices.SI).val : ℝ)

/-- Coherent-SI acceleration readout, in metres per second squared. -/
def accelerationInMetersPerSecondSquared
    (acceleration : AccelerationQuantity) : ℝ :=
  ((acceleration UnitChoices.SI).val : ℝ)

/-- Coherent-SI force-magnitude readout, in newtons. -/
def forceMagnitudeInNewtons (force : ForceMagnitudeQuantity) : ℝ :=
  ((force UnitChoices.SI).val : ℝ)

/-- Coherent-SI signed-force-component readout, in newtons. -/
def signedForceInNewtons (force : SignedForceQuantity) : ℝ :=
  (force UnitChoices.SI).val

/-- Coherent-SI length readout, in metres. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  ((length UnitChoices.SI).val : ℝ)

/-- Conversion of a dimensionless degree readout to radians. -/
def degreesToRadians (degrees : ℝ) : ℝ :=
  degrees * Real.pi / 180

/-! ## Physical setup and labels visible in the primary image -/

/-- The two horizontal directions distinguished by the diagram. -/
inductive HorizontalDirection where
  | left
  | right
  deriving DecidableEq, Repr

/-- The reference line from which the displayed angle is measured. -/
inductive AngleReference where
  | vertical
  | horizontal
  deriving DecidableEq, Repr

/-- The attachment at the upper end of the suspension thread. -/
inductive UpperAttachment where
  | fixedSupport
  | freeSupport
  deriving DecidableEq, Repr

/-!
Literal presentation data from image `904.png`.  These fields record what is
drawn and printed; they do not determine the physical charge.
-/
structure SuspendedChargeFigure where
  chargeLabelQShown : Bool
  printedMassGrams : ℝ
  straightThreadShown : Bool
  upperAttachment : UpperAttachment
  dashedReferenceShown : Bool
  angleReference : AngleReference
  printedAngleDegrees : ℝ
  electricFieldArrowsShown : Bool
  electricFieldVectorLabelShown : Bool
  electricFieldArrowDirection : HorizontalDirection
  ballDisplacementDirection : HorizontalDirection

/-!
Independent physical quantities for the hanging charged ball.  In
particular, `ballCharge` and `horizontalElectricForce` are observables rather
than definitions made from an answer choice.
-/
structure SuspendedChargeSetup where
  figure : SuspendedChargeFigure
  ballMass : MassQuantity
  ballCharge : SignedChargeQuantity
  electricFieldMagnitude : ElectricFieldStrengthQuantity
  electricField : Electromagnetism.ElectricField 2
  gravitationalAcceleration : AccelerationQuantity
  threadLength : LengthQuantity
  threadTension : ForceMagnitudeQuantity
  weight : ForceMagnitudeQuantity
  horizontalElectricForce : SignedForceQuantity
  threadAngleFromVerticalRadians : ℝ

/-! ## Problem data, figure evidence, and governing physics -/

/-!
Numerical data stated in the prose.  The mass and angle are also printed in
the primary image, while the magnitude `100000 N/C` occurs in the text.
-/
structure MatchesProblemStatement (setup : SuspendedChargeSetup) : Prop where
  ballMassIsFiveGrams : massInGrams setup.ballMass = 5
  fieldStrengthIsOneHundredThousand :
    fieldStrengthInNewtonsPerCoulomb setup.electricFieldMagnitude = 100000
  angleIsTwentyDegrees :
    setup.threadAngleFromVerticalRadians = degreesToRadians 20

/-!
Presentation and geometry read directly from the supplied image.  The
rightward displacement and rightward field direction are kept distinct from
the governing force law, so neither one directly assumes the sign or value
of `ballCharge`.
-/
structure MatchesSuppliedFigure (setup : SuspendedChargeSetup) : Prop where
  chargeLabelIsShown : setup.figure.chargeLabelQShown = true
  printedMass : setup.figure.printedMassGrams = 5
  physicalMassMatchesPrintedLabel :
    massInGrams setup.ballMass = setup.figure.printedMassGrams
  threadIsShownStraight : setup.figure.straightThreadShown = true
  threadHasFixedUpperSupport :
    setup.figure.upperAttachment = .fixedSupport
  dashedVerticalReferenceIsShown :
    setup.figure.dashedReferenceShown = true
  angleIsMeasuredFromVertical :
    setup.figure.angleReference = .vertical
  printedAngle : setup.figure.printedAngleDegrees = 20
  physicalAngleMatchesPrintedLabel :
    setup.threadAngleFromVerticalRadians =
      degreesToRadians setup.figure.printedAngleDegrees
  fieldArrowsAreShown : setup.figure.electricFieldArrowsShown = true
  fieldVectorLabelIsShown :
    setup.figure.electricFieldVectorLabelShown = true
  fieldArrowsPointRight :
    setup.figure.electricFieldArrowDirection = .right
  ballIsDisplacedRight :
    setup.figure.ballDisplacementDirection = .right

/-!
The dimensionful field magnitude is the coherent-SI `x` component of
Physlib's two-dimensional electric field, while its `y` component vanishes.
The equality at every spacetime point records the uniform field depicted by
the parallel arrows.
-/
structure RepresentsUniformRightwardElectricField
    (setup : SuspendedChargeSetup) : Prop where
  xComponent : ∀ time position,
    setup.electricField time position 0 =
      fieldStrengthInNewtonsPerCoulomb setup.electricFieldMagnitude
  yComponent : ∀ time position,
    setup.electricField time position 1 = 0

/-- The standard near-Earth gravitational-acceleration calibration used by the calculation. -/
structure UsesStandardNearEarthGravity
    (setup : SuspendedChargeSetup) : Prop where
  gravitationalAccelerationReadout :
    accelerationInMetersPerSecondSquared
      setup.gravitationalAcceleration = 49 / 5

/-!
Positivity and acute-angle conditions selecting the nondegenerate physical
branch shown in the image.  There is deliberately no charge-sign or
charge-value condition here.
-/
structure HasPhysicalSuspendedChargeParameters
    (setup : SuspendedChargeSetup) : Prop where
  massPositive : 0 < massInKilograms setup.ballMass
  fieldStrengthPositive :
    0 < fieldStrengthInNewtonsPerCoulomb setup.electricFieldMagnitude
  gravitationalAccelerationPositive :
    0 < accelerationInMetersPerSecondSquared
      setup.gravitationalAcceleration
  threadLengthPositive : 0 < lengthInMeters setup.threadLength
  threadTensionPositive :
    0 < forceMagnitudeInNewtons setup.threadTension
  anglePositive : 0 < setup.threadAngleFromVerticalRadians
  angleAcute : setup.threadAngleFromVerticalRadians < Real.pi / 2

/-!
The school-level physical laws used for the equilibrium calculation, written
in coherent SI components:

* the horizontal electric force is `q E`;
* the downward weight magnitude is `m g`;
* the horizontal component of tension balances the electric force;
* the vertical component of tension balances the weight.

These are general laws and contain neither `0.18 μC` nor the exact target
charge formula.
-/
structure SatisfiesSuspendedChargeEquilibriumLaws
    (setup : SuspendedChargeSetup) : Prop where
  electricForceLaw :
    signedForceInNewtons setup.horizontalElectricForce =
      chargeInCoulombs setup.ballCharge *
        fieldStrengthInNewtonsPerCoulomb setup.electricFieldMagnitude
  nearEarthWeightLaw :
    forceMagnitudeInNewtons setup.weight =
      massInKilograms setup.ballMass *
        accelerationInMetersPerSecondSquared
          setup.gravitationalAcceleration
  horizontalStaticBalance :
    forceMagnitudeInNewtons setup.threadTension *
        Real.sin setup.threadAngleFromVerticalRadians =
      signedForceInNewtons setup.horizontalElectricForce
  verticalStaticBalance :
    forceMagnitudeInNewtons setup.threadTension *
        Real.cos setup.threadAngleFromVerticalRadians =
      forceMagnitudeInNewtons setup.weight

/-!
Eliminating the tension, electric-force, and weight readouts from the four
governing equations gives the generic equilibrium charge formula.
-/
lemma charge_eq_mass_gravity_tan_div_field
    (setup : SuspendedChargeSetup)
    (_physical : HasPhysicalSuspendedChargeParameters setup)
    (_laws : SatisfiesSuspendedChargeEquilibriumLaws setup) :
    chargeInCoulombs setup.ballCharge =
      massInKilograms setup.ballMass *
          accelerationInMetersPerSecondSquared
            setup.gravitationalAcceleration *
        Real.tan setup.threadAngleFromVerticalRadians /
          fieldStrengthInNewtonsPerCoulomb setup.electricFieldMagnitude := by
  have hcos :
      0 < Real.cos setup.threadAngleFromVerticalRadians :=
    Real.cos_pos_of_mem_Ioo
      ⟨by
        linarith only [_physical.anglePositive, Real.pi_pos],
       _physical.angleAcute⟩
  have hcross :
      chargeInCoulombs setup.ballCharge *
          fieldStrengthInNewtonsPerCoulomb setup.electricFieldMagnitude *
          Real.cos setup.threadAngleFromVerticalRadians =
        massInKilograms setup.ballMass *
          accelerationInMetersPerSecondSquared
            setup.gravitationalAcceleration *
          Real.sin setup.threadAngleFromVerticalRadians := by
    calc
      _ = signedForceInNewtons setup.horizontalElectricForce *
            Real.cos setup.threadAngleFromVerticalRadians := by
              rw [_laws.electricForceLaw]
      _ = (forceMagnitudeInNewtons setup.threadTension *
              Real.sin setup.threadAngleFromVerticalRadians) *
            Real.cos setup.threadAngleFromVerticalRadians := by
              rw [_laws.horizontalStaticBalance]
      _ = (forceMagnitudeInNewtons setup.threadTension *
              Real.cos setup.threadAngleFromVerticalRadians) *
            Real.sin setup.threadAngleFromVerticalRadians := by
              ac_rfl
      _ = forceMagnitudeInNewtons setup.weight *
            Real.sin setup.threadAngleFromVerticalRadians := by
              rw [_laws.verticalStaticBalance]
      _ = (massInKilograms setup.ballMass *
              accelerationInMetersPerSecondSquared
                setup.gravitationalAcceleration) *
            Real.sin setup.threadAngleFromVerticalRadians := by
              rw [_laws.nearEarthWeightLaw]
  rw [Real.tan_eq_sin_div_cos]
  apply (eq_div_iff (ne_of_gt _physical.fieldStrengthPositive)).2
  rw [← mul_div_assoc]
  apply (eq_div_iff (ne_of_gt hcos)).2
  simpa only [mul_assoc] using hcross

/-! ## Displayed answers and final target -/

/-- Labels of the four answer choices displayed with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Charge readout, in microcoulombs, printed beside each answer label. -/
def AnswerChoice.displayedChargeInMicrocoulombs : AnswerChoice → ℝ
  | .A => 0.35
  | .B => 0.55
  | .C => 0.18
  | .D => 0.75

/-- The answer label recorded in the supplied dataset metadata. -/
def recordedDatasetAnswer : AnswerChoice := .C

/-!
A displayed two-decimal answer agrees with the physical charge when their
microcoulomb readouts differ by at most half of `0.01 μC`.
-/
def MatchesDisplayedChargeToNearestHundredth
    (charge : SignedChargeQuantity) (choice : AnswerChoice) : Prop :=
  |chargeInMicrocoulombs charge -
      choice.displayedChargeInMicrocoulombs| ≤ 1 / 200

/-- A displayed answer is the unique choice matching the rounded physical charge. -/
def IsUniqueMatchingDisplayedCharge
    (charge : SignedChargeQuantity) (choice : AnswerChoice) : Prop :=
  MatchesDisplayedChargeToNearestHundredth charge choice ∧
    ∀ other : AnswerChoice, other ≠ choice →
      ¬MatchesDisplayedChargeToNearestHundredth charge other

/-!
For `m = 5.0 g`, `g = 9.8 m/s²`, `E = 100000 N/C`, and `θ = 20° = π/9`,
the charge is exactly `0.49 tan(π/9) μC`, approximately `0.178 μC`.
Consequently it uniquely rounds to `0.18 μC`, answer choice C.

This is the Lean declaration corresponding to blueprint label
`thm:physics:phyx_mini_0904:target`.
-/
theorem problem_phyx_mini_0904
    (setup : SuspendedChargeSetup)
    (_statement : MatchesProblemStatement setup)
    (_figure : MatchesSuppliedFigure setup)
    (_uniformField : RepresentsUniformRightwardElectricField setup)
    (_gravity : UsesStandardNearEarthGravity setup)
    (_physical : HasPhysicalSuspendedChargeParameters setup)
    (_laws : SatisfiesSuspendedChargeEquilibriumLaws setup) :
    chargeInMicrocoulombs setup.ballCharge =
        (49 / 100) * Real.tan (Real.pi / 9) ∧
      IsUniqueMatchingDisplayedCharge setup.ballCharge .C := by
  have hmass :
      massInKilograms setup.ballMass = (1 / 200 : ℝ) := by
    have h := _statement.ballMassIsFiveGrams
    unfold massInGrams at h
    linarith only [h]
  have hangle :
      setup.threadAngleFromVerticalRadians = Real.pi / 9 := by
    rw [_statement.angleIsTwentyDegrees]
    unfold degreesToRadians
    ring
  have hcharge :=
    charge_eq_mass_gravity_tan_div_field setup _physical _laws
  have hchargeMicrocoulombs :
      chargeInMicrocoulombs setup.ballCharge =
        (49 / 100) * Real.tan (Real.pi / 9) := by
    unfold chargeInMicrocoulombs
    rw [hcharge, hmass,
      _gravity.gravitationalAccelerationReadout,
      _statement.fieldStrengthIsOneHundredThousand, hangle]
    norm_num
    ring
  have htanBounds :
      (9 / 25 : ℝ) < Real.tan (Real.pi / 9) ∧
        Real.tan (Real.pi / 9) < (3 / 8 : ℝ) := by
    let x : ℝ := Real.pi / 9
    let t : ℝ := Real.tan x
    let q : ℝ := Real.sqrt 3
    change (9 / 25 : ℝ) < t ∧ t < (3 / 8 : ℝ)
    have hxmem :
        x ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
      dsimp [x]
      constructor <;> nlinarith only [Real.pi_pos]
    have hxpos : 0 < x := by
      dsimp [x]
      positivity
    have hxlt : x < Real.pi / 2 := hxmem.2
    have hcospos : 0 < Real.cos x :=
      Real.cos_pos_of_mem_Ioo hxmem
    have hcosne : Real.cos x ≠ 0 := ne_of_gt hcospos
    have htanCos : t * Real.cos x = Real.sin x := by
      dsimp [t]
      rw [Real.tan_eq_sin_div_cos]
      field_simp
    have hqLower : (17 / 10 : ℝ) < q := by
      dsimp [q]
      rw [Real.lt_sqrt (by norm_num)]
      norm_num
    have hqUpper : q < (7 / 4 : ℝ) := by
      dsimp [q]
      rw [Real.sqrt_lt' (by norm_num)]
      norm_num
    have htrig :
        Real.sin (3 * x) - q * Real.cos (3 * x) = 0 := by
      dsimp [x, q]
      rw [show 3 * (Real.pi / 9) = Real.pi / 3 by ring,
        Real.sin_pi_div_three, Real.cos_pi_div_three]
      ring
    rw [Real.sin_three_mul, Real.cos_three_mul, ← htanCos] at htrig
    have hH :
        3 * t - 4 * t ^ 3 * Real.cos x ^ 2 -
            q * (4 * Real.cos x ^ 2 - 3) = 0 := by
      apply (mul_left_cancel₀ hcosne)
      calc
        Real.cos x *
              (3 * t - 4 * t ^ 3 * Real.cos x ^ 2 -
                q * (4 * Real.cos x ^ 2 - 3)) =
            3 * (t * Real.cos x) -
              4 * (t * Real.cos x) ^ 3 -
              q * (4 * Real.cos x ^ 3 - 3 * Real.cos x) := by
                ring
        _ = 0 := htrig
        _ = Real.cos x * 0 := by ring
    have hunit : Real.cos x ^ 2 * (1 + t ^ 2) = 1 := by
      have hsincos := Real.sin_sq_add_cos_sq x
      rw [← htanCos] at hsincos
      calc
        Real.cos x ^ 2 * (1 + t ^ 2) =
            (t * Real.cos x) ^ 2 + Real.cos x ^ 2 := by ring
        _ = 1 := hsincos
    have hid :
        (3 * t - 4 * t ^ 3 * Real.cos x ^ 2 -
            q * (4 * Real.cos x ^ 2 - 3)) +
          (t ^ 3 - 3 * q * t ^ 2 - 3 * t + q) *
            Real.cos x ^ 2 = 0 := by
      calc
        _ = 3 * (t + q) *
            (1 - Real.cos x ^ 2 * (1 + t ^ 2)) := by ring
        _ = 0 := by
          rw [hunit]
          ring
    have hPc :
        (t ^ 3 - 3 * q * t ^ 2 - 3 * t + q) *
            Real.cos x ^ 2 = 0 := by
      linarith only [hH, hid]
    have hP :
        t ^ 3 - 3 * q * t ^ 2 - 3 * t + q = 0 := by
      rcases mul_eq_zero.mp hPc with hp | hc
      · exact hp
      · exact (pow_ne_zero 2 hcosne hc).elim
    have htpos : 0 < t := by
      dsimp [t]
      exact Real.tan_pos_of_pos_of_lt_pi_div_two hxpos hxlt
    have hxLtSix : x < Real.pi / 6 := by
      dsimp [x]
      nlinarith only [Real.pi_pos]
    have htLtTanSix : t < Real.tan (Real.pi / 6) := by
      dsimp [t]
      exact Real.tan_lt_tan_of_nonneg_of_lt_pi_div_two
        hxpos.le (by nlinarith only [Real.pi_pos]) hxLtSix
    have htLtOne : t < 1 := by
      rw [Real.tan_pi_div_six] at htLtTanSix
      have hqpos : 0 < q := lt_trans (by norm_num) hqLower
      have honeDivQLtOne : (1 : ℝ) / q < 1 := by
        rw [div_lt_one hqpos]
        linarith only [hqLower]
      exact htLtTanSix.trans honeDivQLtOne
    have hqpos : 0 < q := lt_trans (by norm_num) hqLower
    have htSqLt : t ^ 2 < t := by
      simpa [pow_two] using
        mul_lt_mul_of_pos_left htLtOne htpos
    constructor
    · by_contra h
      have htLe : t ≤ 9 / 25 := le_of_not_gt h
      have hsum :
          t ^ 2 + t * (9 / 25) + (9 / 25 : ℝ) ^ 2 < 3 := by
        have h1 : t ^ 2 < 1 := htSqLt.trans htLtOne
        have h2 : t * (9 / 25) < 1 := by
          calc
            t * (9 / 25) < 1 * (9 / 25) :=
              mul_lt_mul_of_pos_right htLtOne (by norm_num)
            _ < 1 := by norm_num
        have h3 : (9 / 25 : ℝ) ^ 2 < 1 := by norm_num
        linarith only [h1, h2, h3]
      have hqterm : 0 ≤ q * (t + 9 / 25) :=
        mul_nonneg hqpos.le
          (add_nonneg htpos.le (by norm_num))
      have hbracket :
          t ^ 2 + t * (9 / 25) + (9 / 25 : ℝ) ^ 2 -
              3 * q * (t + 9 / 25) - 3 < 0 := by
        linarith only [hsum, hqterm]
      have hfactor :
          (t ^ 3 - 3 * q * t ^ 2 - 3 * t + q) -
              ((9 / 25 : ℝ) ^ 3 -
                3 * q * (9 / 25) ^ 2 - 3 * (9 / 25) + q) =
            (t - 9 / 25) *
              (t ^ 2 + t * (9 / 25) + (9 / 25 : ℝ) ^ 2 -
                3 * q * (t + 9 / 25) - 3) := by
        ring
      have hproduct :
          0 ≤ (t - 9 / 25) *
            (t ^ 2 + t * (9 / 25) + (9 / 25 : ℝ) ^ 2 -
              3 * q * (t + 9 / 25) - 3) :=
        mul_nonneg_of_nonpos_of_nonpos
          (sub_nonpos.mpr htLe) hbracket.le
      have hPaPositive :
          0 < (9 / 25 : ℝ) ^ 3 -
              3 * q * (9 / 25) ^ 2 - 3 * (9 / 25) + q := by
        norm_num at hqLower ⊢
        linarith only [hqLower]
      linarith only [hP, hfactor, hproduct, hPaPositive]
    · by_contra h
      have htGe : 3 / 8 ≤ t := le_of_not_gt h
      have hsum :
          t ^ 2 + t * (3 / 8) + (3 / 8 : ℝ) ^ 2 < 3 := by
        have h1 : t ^ 2 < 1 := htSqLt.trans htLtOne
        have h2 : t * (3 / 8) < 1 := by
          calc
            t * (3 / 8) < 1 * (3 / 8) :=
              mul_lt_mul_of_pos_right htLtOne (by norm_num)
            _ < 1 := by norm_num
        have h3 : (3 / 8 : ℝ) ^ 2 < 1 := by norm_num
        linarith only [h1, h2, h3]
      have hqterm : 0 ≤ q * (t + 3 / 8) :=
        mul_nonneg hqpos.le
          (add_nonneg htpos.le (by norm_num))
      have hbracket :
          t ^ 2 + t * (3 / 8) + (3 / 8 : ℝ) ^ 2 -
              3 * q * (t + 3 / 8) - 3 < 0 := by
        linarith only [hsum, hqterm]
      have hfactor :
          (t ^ 3 - 3 * q * t ^ 2 - 3 * t + q) -
              ((3 / 8 : ℝ) ^ 3 -
                3 * q * (3 / 8) ^ 2 - 3 * (3 / 8) + q) =
            (t - 3 / 8) *
              (t ^ 2 + t * (3 / 8) + (3 / 8 : ℝ) ^ 2 -
                3 * q * (t + 3 / 8) - 3) := by
        ring
      have hproduct :
          (t - 3 / 8) *
              (t ^ 2 + t * (3 / 8) + (3 / 8 : ℝ) ^ 2 -
                3 * q * (t + 3 / 8) - 3) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos
          (sub_nonneg.mpr htGe) hbracket.le
      have hPbNegative :
          (3 / 8 : ℝ) ^ 3 -
              3 * q * (3 / 8) ^ 2 - 3 * (3 / 8) + q < 0 := by
        norm_num at hqUpper ⊢
        linarith only [hqUpper]
      linarith only [hP, hfactor, hproduct, hPbNegative]
  refine ⟨hchargeMicrocoulombs, ?_⟩
  constructor
  · unfold MatchesDisplayedChargeToNearestHundredth
    rw [hchargeMicrocoulombs, abs_le]
    norm_num [AnswerChoice.displayedChargeInMicrocoulombs]
    constructor <;> linarith only [htanBounds.1, htanBounds.2]
  · intro other hother
    cases other with
    | A =>
        intro hmatch
        unfold MatchesDisplayedChargeToNearestHundredth at hmatch
        rw [hchargeMicrocoulombs, abs_le] at hmatch
        norm_num [AnswerChoice.displayedChargeInMicrocoulombs] at hmatch
        linarith only [hmatch.1, hmatch.2,
          htanBounds.1, htanBounds.2]
    | B =>
        intro hmatch
        unfold MatchesDisplayedChargeToNearestHundredth at hmatch
        rw [hchargeMicrocoulombs, abs_le] at hmatch
        norm_num [AnswerChoice.displayedChargeInMicrocoulombs] at hmatch
        linarith only [hmatch.1, hmatch.2,
          htanBounds.1, htanBounds.2]
    | C => exact (hother rfl).elim
    | D =>
        intro hmatch
        unfold MatchesDisplayedChargeToNearestHundredth at hmatch
        rw [hchargeMicrocoulombs, abs_le] at hmatch
        norm_num [AnswerChoice.displayedChargeInMicrocoulombs] at hmatch
        linarith only [hmatch.1, hmatch.2,
          htanBounds.1, htanBounds.2]

end PhyXMiniProblems.ProblemPhyXMini0904
