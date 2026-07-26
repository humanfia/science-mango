import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Physlib.Units.WithDim.Basic

/- USER: The assigned source file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0905

open Dimension

/-!
# Deflection of a charged ball in a horizontal electric field

The primary image shows a ball of mass `2.0 g` and positive charge `25 nC`
suspended from a string, together with rightward electric-field arrows.  The
accompanying problem statement gives the uniform field as `200,000 N/C` in the
positive horizontal direction.  The string makes an unknown angle `θ` with
the vertical dashed guide, and static force balance determines that angle.

The source question says "What is the charge on the ball?", but the charge is
already printed in the image and every answer choice is an angle.  The recorded
answer is choice C, `14 degrees`.  The formal target therefore treats the
intended question as asking for the angle.  Since the equilibrium calculation
gives approximately `14.3 degrees`, the conclusion says that the angle rounds
to `14 degrees` and that C is the uniquely closest displayed choice; it does
not assert the physically false exact equality `θ = 14 degrees`.

Physical mass, charge, field, acceleration, and force are unit-independent
Physlib `Dimensionful` quantities.  Real numbers occur only as coherent-SI
readouts, Cartesian components, the dimensionless radian representative of
`θ`, and displayed degree values.

Assumption/target split:

* governing laws: the horizontal and vertical components of static force
  balance, with electric force `q E`, weight `m g`, and string tension;
* previous-part results: none (the arctangent relation below is derived);
* figure/data readouts: the raster gives positive `25 nC`, mass `2.0 g`,
  rightward field arrows, the fixed support, string, vertical guide, angle arc,
  and ball; the source scenario gives the field components
  `(200,000, 0) N/C`; standard terrestrial gravity is an explicit calibration;
* current target: the equilibrium angle is within half a degree of
  `14 degrees`, and answer choice C is uniquely closest.
-/

/-! ## Dimensionful quantities and coherent-SI readouts -/

/-- The physical dimension `L T⁻²` of acceleration. -/
def accelerationDimension : Dimension :=
  L𝓭 * T𝓭⁻¹ * T𝓭⁻¹

/-- The physical dimension `M L T⁻²` of force. -/
def forceDimension : Dimension :=
  M𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹

/-- The physical dimension `M L T⁻² C⁻¹` of electric-field strength. -/
def electricFieldStrengthDimension : Dimension :=
  forceDimension * C𝓭⁻¹

/-- A nonnegative, unit-independent physical mass. -/
abbrev MassQuantity : Type :=
  Dimensionful (WithDim M𝓭 NNReal)

/-- A signed, unit-independent physical electric charge. -/
abbrev SignedChargeQuantity : Type :=
  Dimensionful (WithDim C𝓭 ℝ)

/-- A planar electric-field vector with its physical dimension retained. -/
abbrev PlanarElectricFieldQuantity : Type :=
  Dimensionful
    (WithDim electricFieldStrengthDimension (EuclideanSpace ℝ (Fin 2)))

/-- A planar acceleration vector with its physical dimension retained. -/
abbrev PlanarAccelerationQuantity : Type :=
  Dimensionful
    (WithDim accelerationDimension (EuclideanSpace ℝ (Fin 2)))

/-- A nonnegative magnitude of string tension. -/
abbrev ForceMagnitudeQuantity : Type :=
  Dimensionful (WithDim forceDimension NNReal)

/-- Coordinate `0`, horizontal and positive to the right. -/
def xAxis : Fin 2 := 0

/-- Coordinate `1`, vertical and positive upward. -/
def yAxis : Fin 2 := 1

/-- Read a mass in coherent SI units, kilograms. -/
def massInKilograms (mass : MassQuantity) : ℝ :=
  ((mass UnitChoices.SI).val : ℝ)

/-- Read a signed charge in coherent SI units, coulombs. -/
def chargeInCoulombs (charge : SignedChargeQuantity) : ℝ :=
  (charge UnitChoices.SI).val

/-- Read the planar electric-field vector in newtons per coulomb. -/
def electricFieldInNewtonsPerCoulomb
    (field : PlanarElectricFieldQuantity) : EuclideanSpace ℝ (Fin 2) :=
  (field UnitChoices.SI).val

/-- Read the planar gravitational acceleration in metres per second squared. -/
def accelerationInMetersPerSecondSquared
    (acceleration : PlanarAccelerationQuantity) : EuclideanSpace ℝ (Fin 2) :=
  (acceleration UnitChoices.SI).val

/-- Read a tension magnitude in coherent SI units, newtons. -/
def forceInNewtons (force : ForceMagnitudeQuantity) : ℝ :=
  ((force UnitChoices.SI).val : ℝ)

/-! ## Primary-image vocabulary and physical setup -/

/-- Visible geometric and force-diagram elements in image `905.png`. -/
inductive FigureElement where
  | fixedHorizontalSupport
  | suspensionString
  | dashedVerticalGuide
  | angleArcTheta
  | chargedBall
  | positiveChargeSymbol
  | rightwardElectricFieldArrows
  deriving DecidableEq, Fintype, Repr

/-!
Typed content of the primary raster.  The mass and charge values printed beside
the ball are stated independently in `MatchesPrimaryFigure`.  The field symbol
denotes the applied field, but its magnitude comes from the source scenario.
-/
structure SuspendedChargeFigure where
  showsElement : FigureElement → Bool
  massLabel : MassQuantity
  chargeLabel : SignedChargeQuantity
  electricFieldLabel : PlanarElectricFieldQuantity

/-!
Independent physical quantities in the suspended-ball experiment.  In
particular, the unknown angle is not defined from answer C or from `14`.
-/
structure SuspendedChargeSetup where
  mass : MassQuantity
  charge : SignedChargeQuantity
  electricField : PlanarElectricFieldQuantity
  gravitationalAcceleration : PlanarAccelerationQuantity
  tensionMagnitude : ForceMagnitudeQuantity
  /-- Dimensionless angle from the upward vertical, represented in radians. -/
  angleFromVerticalRadians : ℝ
  figure : SuspendedChargeFigure

/-! ## Figure evidence, calibration, physical branch, and governing laws -/

/--
The visible objects and numerical labels transcribed from the primary image.
The angle arc and field label are only symbolic: no numerical angle or field
magnitude is included here.
-/
structure MatchesPrimaryFigure (setup : SuspendedChargeSetup) : Prop where
  fixedSupportShown :
    setup.figure.showsElement .fixedHorizontalSupport = true
  stringShown :
    setup.figure.showsElement .suspensionString = true
  verticalGuideShown :
    setup.figure.showsElement .dashedVerticalGuide = true
  unknownThetaArcShown :
    setup.figure.showsElement .angleArcTheta = true
  ballShown :
    setup.figure.showsElement .chargedBall = true
  positiveChargeSymbolShown :
    setup.figure.showsElement .positiveChargeSymbol = true
  rightwardFieldArrowsShown :
    setup.figure.showsElement .rightwardElectricFieldArrows = true
  massLabelIdentifiesBall :
    setup.figure.massLabel = setup.mass
  chargeLabelIdentifiesBall :
    setup.figure.chargeLabel = setup.charge
  fieldLabelIdentifiesAppliedField :
    setup.figure.electricFieldLabel = setup.electricField
  massLabelInKilograms :
    massInKilograms setup.figure.massLabel = 2 / 1000
  chargeLabelInCoulombs :
    chargeInCoulombs setup.figure.chargeLabel = 25 / 1000000000

/--
The uniform electric-field components supplied by the accompanying problem
statement rather than by the raster itself.
-/
structure MatchesSourceScenario (setup : SuspendedChargeSetup) : Prop where
  fieldHorizontalComponent :
    electricFieldInNewtonsPerCoulomb setup.electricField xAxis = 200000
  fieldVerticalComponent :
    electricFieldInNewtonsPerCoulomb setup.electricField yAxis = 0

/--
The standard near-Earth gravity calibration used by the numerical textbook
answer.  It is separated from the image evidence because `g` is not printed.
-/
structure HasStandardTerrestrialGravity
    (setup : SuspendedChargeSetup) : Prop where
  horizontalComponentZero :
    accelerationInMetersPerSecondSquared
        setup.gravitationalAcceleration xAxis = 0
  verticalComponent :
    accelerationInMetersPerSecondSquared
        setup.gravitationalAcceleration yAxis = -(98 / 10)

/-- The branch shown in the figure: the string deflects right by an acute angle. -/
structure HasPhysicalDeflectionBranch
    (setup : SuspendedChargeSetup) : Prop where
  anglePositive : 0 < setup.angleFromVerticalRadians
  angleAcute : setup.angleFromVerticalRadians < Real.pi / 2

/-!
Static force balance on the ball.  The tension points up and left along the
string, so its components are `-T sin θ` and `T cos θ`; electric force is
`q E`, and weight is `m g`.  These are governing laws, not the requested
numerical answer.
-/
structure SatisfiesStaticForceBalance
    (setup : SuspendedChargeSetup) : Prop where
  horizontalBalance :
    -(forceInNewtons setup.tensionMagnitude *
        Real.sin setup.angleFromVerticalRadians) +
      chargeInCoulombs setup.charge *
        electricFieldInNewtonsPerCoulomb setup.electricField xAxis +
      massInKilograms setup.mass *
        accelerationInMetersPerSecondSquared
          setup.gravitationalAcceleration xAxis = 0
  verticalBalance :
    forceInNewtons setup.tensionMagnitude *
        Real.cos setup.angleFromVerticalRadians +
      chargeInCoulombs setup.charge *
        electricFieldInNewtonsPerCoulomb setup.electricField yAxis +
      massInKilograms setup.mass *
        accelerationInMetersPerSecondSquared
          setup.gravitationalAcceleration yAxis = 0

/-! ## Derived equilibrium relation and displayed answer choices -/

/--
Resolving the two balance equations and selecting the acute physical branch
gives the usual arctangent expression.  This is derived rather than assumed.
-/
lemma equilibrium_angle_arctan
    (setup : SuspendedChargeSetup)
    (hFigure : MatchesPrimaryFigure setup)
    (hScenario : MatchesSourceScenario setup)
    (hGravity : HasStandardTerrestrialGravity setup)
    (hBranch : HasPhysicalDeflectionBranch setup)
    (hBalance : SatisfiesStaticForceBalance setup) :
    setup.angleFromVerticalRadians =
      Real.arctan
        ((chargeInCoulombs setup.charge *
            electricFieldInNewtonsPerCoulomb setup.electricField xAxis) /
          (massInKilograms setup.mass *
            (-accelerationInMetersPerSecondSquared
              setup.gravitationalAcceleration yAxis))) := by
  have hm :
      massInKilograms setup.mass = 2 / 1000 := by
    rw [← hFigure.massLabelIdentifiesBall]
    exact hFigure.massLabelInKilograms
  have hq :
      chargeInCoulombs setup.charge = 25 / 1000000000 := by
    rw [← hFigure.chargeLabelIdentifiesBall]
    exact hFigure.chargeLabelInCoulombs
  have hcos_pos :
      0 < Real.cos setup.angleFromVerticalRadians := by
    exact Real.cos_pos_of_mem_Ioo
      ⟨by
        have hpi : 0 < Real.pi := Real.pi_pos
        linarith [hBranch.anglePositive],
       hBranch.angleAcute⟩
  have hHorizontal := hBalance.horizontalBalance
  have hVertical := hBalance.verticalBalance
  rw [hScenario.fieldHorizontalComponent,
    hGravity.horizontalComponentZero, hm, hq] at hHorizontal
  rw [hScenario.fieldVerticalComponent,
    hGravity.verticalComponent, hm] at hVertical
  norm_num at hHorizontal hVertical
  have hT_pos :
      0 < forceInNewtons setup.tensionMagnitude := by
    nlinarith
  have hsin_cos :
      Real.sin setup.angleFromVerticalRadians =
        (25 / 98 : ℝ) * Real.cos setup.angleFromVerticalRadians := by
    have hproduct :
        forceInNewtons setup.tensionMagnitude *
          (Real.sin setup.angleFromVerticalRadians -
            (25 / 98 : ℝ) *
              Real.cos setup.angleFromVerticalRadians) = 0 := by
      nlinarith
    rcases mul_eq_zero.mp hproduct with hT | hratio
    · exact (ne_of_gt hT_pos hT).elim
    · nlinarith
  have htan :
      Real.tan setup.angleFromVerticalRadians = 25 / 98 := by
    rw [Real.tan_eq_sin_div_cos, hsin_cos]
    field_simp
  have hreadout :
      ((chargeInCoulombs setup.charge *
          electricFieldInNewtonsPerCoulomb setup.electricField xAxis) /
        (massInKilograms setup.mass *
          (-accelerationInMetersPerSecondSquared
            setup.gravitationalAcceleration yAxis))) =
        (25 / 98 : ℝ) := by
    rw [hq, hScenario.fieldHorizontalComponent, hm,
      hGravity.verticalComponent]
    norm_num
  calc
    setup.angleFromVerticalRadians =
        Real.arctan (Real.tan setup.angleFromVerticalRadians) :=
      (Real.arctan_tan
        (by
          have hpi : 0 < Real.pi := Real.pi_pos
          linarith [hBranch.anglePositive])
        hBranch.angleAcute).symm
    _ = Real.arctan (25 / 98) := by rw [htan]
    _ = Real.arctan
        ((chargeInCoulombs setup.charge *
            electricFieldInNewtonsPerCoulomb setup.electricField xAxis) /
          (massInKilograms setup.mass *
            (-accelerationInMetersPerSecondSquared
              setup.gravitationalAcceleration yAxis))) := by
      rw [hreadout]

/-- Letter labels of the four displayed angle choices. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Degree value printed beside each answer label. -/
def AnswerChoice.degrees : AnswerChoice → ℝ
  | .A => 3
  | .B => 9
  | .C => 14
  | .D => 20

/-- Convert the acute radian representative used by the setup to degrees. -/
def radiansToDegrees (angleRadians : ℝ) : ℝ :=
  angleRadians * 180 / Real.pi

/--
A displayed choice is uniquely closest to the physical angle when its absolute
degree error is strictly smaller than that of every other displayed choice.
-/
def IsUniqueClosestDisplayedAngle
    (angleRadians : ℝ) (choice : AnswerChoice) : Prop :=
  ∀ other : AnswerChoice, other ≠ choice →
    |radiansToDegrees angleRadians - choice.degrees| <
      |radiansToDegrees angleRadians - other.degrees|

/-- The answer label recorded in the dataset metadata. -/
def recordedDatasetAnswer : AnswerChoice := .C

/--
For the primary-image labels, source-scenario field, and standard terrestrial
gravity, the static equilibrium angle is within half a degree of `14 degrees`,
and option C is the unique closest displayed answer.

This formalizes `thm:physics:phyx_mini_0905:target`.
-/
theorem problem_phyx_mini_0905
    (setup : SuspendedChargeSetup)
    (hFigure : MatchesPrimaryFigure setup)
    (hScenario : MatchesSourceScenario setup)
    (hGravity : HasStandardTerrestrialGravity setup)
    (hBranch : HasPhysicalDeflectionBranch setup)
    (hBalance : SatisfiesStaticForceBalance setup) :
    |radiansToDegrees setup.angleFromVerticalRadians -
        AnswerChoice.C.degrees| < 1 / 2 ∧
      IsUniqueClosestDisplayedAngle
        setup.angleFromVerticalRadians AnswerChoice.C := by
  let θ := setup.angleFromVerticalRadians
  have hm :
      massInKilograms setup.mass = 2 / 1000 := by
    rw [← hFigure.massLabelIdentifiesBall]
    exact hFigure.massLabelInKilograms
  have hq :
      chargeInCoulombs setup.charge = 25 / 1000000000 := by
    rw [← hFigure.chargeLabelIdentifiesBall]
    exact hFigure.chargeLabelInCoulombs
  have hθ :
      θ = Real.arctan (25 / 98 : ℝ) := by
    have h := equilibrium_angle_arctan setup hFigure hScenario hGravity
      hBranch hBalance
    rw [hq, hScenario.fieldHorizontalComponent, hm,
      hGravity.verticalComponent] at h
    norm_num at h
    exact h
  have hθ_pos : 0 < θ := by
    exact hBranch.anglePositive
  have hθ_acute : θ < Real.pi / 2 := by
    exact hBranch.angleAcute
  have hcos_pos : 0 < Real.cos θ := by
    exact Real.cos_pos_of_mem_Ioo
      ⟨by
        have hpi : 0 < Real.pi := Real.pi_pos
        linarith,
       hθ_acute⟩
  have htan : Real.tan θ = 25 / 98 := by
    rw [hθ, Real.tan_arctan]
  have hsin_cos :
      Real.sin θ = (25 / 98 : ℝ) * Real.cos θ := by
    rw [Real.tan_eq_sin_div_cos] at htan
    apply (div_eq_iff (ne_of_gt hcos_pos)).mp at htan
    nlinarith

  have htwo :
      2 * θ = Real.arctan (4900 / 8979 : ℝ) := by
    have h := Real.arctan_add
      (x := (25 / 98 : ℝ)) (y := (25 / 98 : ℝ)) (by norm_num)
    rw [hθ]
    norm_num at h ⊢
    linarith
  have hthree :
      3 * θ = Real.arctan (704675 / 757442 : ℝ) := by
    have h := Real.arctan_add
      (x := (4900 / 8979 : ℝ)) (y := (25 / 98 : ℝ)) (by norm_num)
    norm_num at h ⊢
    rw [← htwo, ← hθ] at h
    linarith
  have hfour :
      4 * θ = Real.arctan (87994200 / 56612441 : ℝ) := by
    have h := Real.arctan_add
      (x := (704675 / 757442 : ℝ)) (y := (25 / 98 : ℝ)) (by norm_num)
    norm_num at h ⊢
    rw [← hthree, ← hθ] at h
    linarith
  have hθ_lower_coarse : Real.pi / 16 < θ := by
    have hmono :
        Real.arctan (1 : ℝ) <
          Real.arctan (87994200 / 56612441 : ℝ) :=
      Real.arctan_strictMono (by norm_num)
    rw [Real.arctan_one, ← hfour] at hmono
    linarith
  have hθ_upper_coarse : θ < Real.pi / 12 := by
    have hmono :
        Real.arctan (704675 / 757442 : ℝ) <
          Real.arctan (1 : ℝ) :=
      Real.arctan_strictMono (by norm_num)
    rw [Real.arctan_one, ← hthree] at hmono
    linarith

  have hAngleAdd
      (m n : ℕ) (pm qm pn qn : ℝ)
      (hmul :
        Real.sin ((m : ℝ) * θ) = Real.cos θ ^ m * pm ∧
        Real.cos ((m : ℝ) * θ) = Real.cos θ ^ m * qm)
      (hnul :
        Real.sin ((n : ℝ) * θ) = Real.cos θ ^ n * pn ∧
        Real.cos ((n : ℝ) * θ) = Real.cos θ ^ n * qn) :
      Real.sin (((m + n : ℕ) : ℝ) * θ) =
          Real.cos θ ^ (m + n) * (pm * qn + qm * pn) ∧
        Real.cos (((m + n : ℕ) : ℝ) * θ) =
          Real.cos θ ^ (m + n) * (qm * qn - pm * pn) := by
    rcases hmul with ⟨hms, hmc⟩
    rcases hnul with ⟨hns, hnc⟩
    constructor
    · calc
        Real.sin (((m + n : ℕ) : ℝ) * θ) =
            Real.sin ((m : ℝ) * θ + (n : ℝ) * θ) := by
              congr 1
              push_cast
              ring
        _ = Real.sin ((m : ℝ) * θ) * Real.cos ((n : ℝ) * θ) +
              Real.cos ((m : ℝ) * θ) * Real.sin ((n : ℝ) * θ) := by
                rw [Real.sin_add]
        _ = Real.cos θ ^ (m + n) * (pm * qn + qm * pn) := by
              rw [hms, hmc, hns, hnc, pow_add]
              ring
    · calc
        Real.cos (((m + n : ℕ) : ℝ) * θ) =
            Real.cos ((m : ℝ) * θ + (n : ℝ) * θ) := by
              congr 1
              push_cast
              ring
        _ = Real.cos ((m : ℝ) * θ) * Real.cos ((n : ℝ) * θ) -
              Real.sin ((m : ℝ) * θ) * Real.sin ((n : ℝ) * θ) := by
                rw [Real.cos_add]
        _ = Real.cos θ ^ (m + n) * (qm * qn - pm * pn) := by
              rw [hms, hmc, hns, hnc, pow_add]
              ring

  let p1 : ℝ := 25 / 98
  let q1 : ℝ := 1
  have htrig1 :
      Real.sin (((1 : ℕ) : ℝ) * θ) = Real.cos θ ^ 1 * p1 ∧
      Real.cos (((1 : ℕ) : ℝ) * θ) = Real.cos θ ^ 1 * q1 := by
    dsimp [p1, q1]
    constructor
    · simpa [mul_comm] using hsin_cos
    · simp
  let p2 : ℝ := p1 * q1 + q1 * p1
  let q2 : ℝ := q1 * q1 - p1 * p1
  have htrig2 :
      Real.sin ((2 : ℝ) * θ) = Real.cos θ ^ 2 * p2 ∧
      Real.cos ((2 : ℝ) * θ) = Real.cos θ ^ 2 * q2 := by
    simpa [p2, q2] using hAngleAdd 1 1 p1 q1 p1 q1 htrig1 htrig1
  let p4 : ℝ := p2 * q2 + q2 * p2
  let q4 : ℝ := q2 * q2 - p2 * p2
  have htrig4 :
      Real.sin ((4 : ℝ) * θ) = Real.cos θ ^ 4 * p4 ∧
      Real.cos ((4 : ℝ) * θ) = Real.cos θ ^ 4 * q4 := by
    simpa [p4, q4] using hAngleAdd 2 2 p2 q2 p2 q2 htrig2 htrig2
  let p8 : ℝ := p4 * q4 + q4 * p4
  let q8 : ℝ := q4 * q4 - p4 * p4
  have htrig8 :
      Real.sin ((8 : ℝ) * θ) = Real.cos θ ^ 8 * p8 ∧
      Real.cos ((8 : ℝ) * θ) = Real.cos θ ^ 8 * q8 := by
    simpa [p8, q8] using hAngleAdd 4 4 p4 q4 p4 q4 htrig4 htrig4
  let p12 : ℝ := p8 * q4 + q8 * p4
  let q12 : ℝ := q8 * q4 - p8 * p4
  have htrig12 :
      Real.sin ((12 : ℝ) * θ) = Real.cos θ ^ 12 * p12 ∧
      Real.cos ((12 : ℝ) * θ) = Real.cos θ ^ 12 * q12 := by
    simpa [p12, q12] using
      hAngleAdd 8 4 p8 q8 p4 q4 htrig8 htrig4
  let p13 : ℝ := p12 * q1 + q12 * p1
  let q13 : ℝ := q12 * q1 - p12 * p1
  have htrig13 :
      Real.sin ((13 : ℝ) * θ) = Real.cos θ ^ 13 * p13 ∧
      Real.cos ((13 : ℝ) * θ) = Real.cos θ ^ 13 * q13 := by
    simpa [p13, q13] using
      hAngleAdd 12 1 p12 q12 p1 q1 htrig12 htrig1
  have hp13 : p13 < 0 := by
    norm_num [p13, q12, p12, q8, p8, q4, p4, q2, p2, q1, p1]
  have hsin13 :
      Real.sin ((13 : ℝ) * θ) < 0 := by
    rw [htrig13.1]
    exact mul_neg_of_pos_of_neg (pow_pos hcos_pos 13) hp13

  let p16 : ℝ := p8 * q8 + q8 * p8
  let q16 : ℝ := q8 * q8 - p8 * p8
  have htrig16 :
      Real.sin ((16 : ℝ) * θ) = Real.cos θ ^ 16 * p16 ∧
      Real.cos ((16 : ℝ) * θ) = Real.cos θ ^ 16 * q16 := by
    simpa [p16, q16] using
      hAngleAdd 8 8 p8 q8 p8 q8 htrig8 htrig8
  let p24 : ℝ := p16 * q8 + q16 * p8
  let q24 : ℝ := q16 * q8 - p16 * p8
  have htrig24 :
      Real.sin ((24 : ℝ) * θ) = Real.cos θ ^ 24 * p24 ∧
      Real.cos ((24 : ℝ) * θ) = Real.cos θ ^ 24 * q24 := by
    simpa [p24, q24] using
      hAngleAdd 16 8 p16 q16 p8 q8 htrig16 htrig8
  let p25 : ℝ := p24 * q1 + q24 * p1
  let q25 : ℝ := q24 * q1 - p24 * p1
  have htrig25 :
      Real.sin ((25 : ℝ) * θ) = Real.cos θ ^ 25 * p25 ∧
      Real.cos ((25 : ℝ) * θ) = Real.cos θ ^ 25 * q25 := by
    simpa [p25, q25] using
      hAngleAdd 24 1 p24 q24 p1 q1 htrig24 htrig1
  have hp25 : p25 < 0 := by
    norm_num [p25, q24, p24, q16, p16, q8, p8, q4, p4,
      q2, p2, q1, p1]
  have hsin25 :
      Real.sin ((25 : ℝ) * θ) < 0 := by
    rw [htrig25.1]
    exact mul_neg_of_pos_of_neg (pow_pos hcos_pos 25) hp25

  clear htrig25 htrig24 htrig16 htrig13 htrig12 htrig8 htrig4 htrig2
    htrig1 hAngleAdd
  clear hp25 hp13 q25 p25 q24 p24 q16 p16 q13 p13 q12 p12 q8 p8
    q4 p4 q2 p2 q1 p1

  have hθ_lower : Real.pi / 13 < θ := by
    have hthirteen : Real.pi < 13 * θ := by
      by_contra hnot
      have hnonneg :
          0 ≤ Real.sin ((13 : ℝ) * θ) := by
        apply Real.sin_nonneg_of_nonneg_of_le_pi
        · positivity
        · push_neg at hnot
          exact hnot
      linarith only [hsin13, hnonneg]
    linarith only [hthirteen]
  have hθ_upper : θ < 2 * Real.pi / 25 := by
    have htwentyfive : (25 : ℝ) * θ < 2 * Real.pi := by
      by_contra hnot
      have hnonneg :
          0 ≤ Real.sin ((25 : ℝ) * θ - 2 * Real.pi) := by
        apply Real.sin_nonneg_of_nonneg_of_le_pi
        · push_neg at hnot
          exact sub_nonneg.mpr hnot
        · have hpi : 0 < Real.pi := Real.pi_pos
          linarith only [hθ_upper_coarse, hpi]
      rw [Real.sin_sub_two_pi] at hnonneg
      linarith only [hsin25, hnonneg]
    linarith only [htwentyfive]

  have hdegree_lower :
      (27 / 2 : ℝ) < radiansToDegrees θ := by
    rw [radiansToDegrees, lt_div_iff₀ Real.pi_pos]
    linarith only [hθ_lower, Real.pi_pos]
  have hdegree_upper :
      radiansToDegrees θ < (29 / 2 : ℝ) := by
    rw [radiansToDegrees, div_lt_iff₀ Real.pi_pos]
    linarith only [hθ_upper, Real.pi_pos]
  have herror :
      |radiansToDegrees θ - AnswerChoice.C.degrees| < 1 / 2 := by
    rw [AnswerChoice.degrees, abs_lt]
    constructor
    · linarith only [hdegree_lower]
    · linarith only [hdegree_upper]
  constructor
  · exact herror
  · intro other hother
    cases other with
    | A =>
        simp only [AnswerChoice.degrees]
        calc
          |radiansToDegrees θ - 14| < (1 / 2 : ℝ) := by
            simpa [AnswerChoice.degrees] using herror
          _ < |radiansToDegrees θ - 3| := by
            rw [abs_of_pos (by linarith only [hdegree_lower])]
            linarith only [hdegree_lower]
    | B =>
        simp only [AnswerChoice.degrees]
        calc
          |radiansToDegrees θ - 14| < (1 / 2 : ℝ) := by
            simpa [AnswerChoice.degrees] using herror
          _ < |radiansToDegrees θ - 9| := by
            rw [abs_of_pos (by linarith only [hdegree_lower])]
            linarith only [hdegree_lower]
    | C => exact (hother rfl).elim
    | D =>
        simp only [AnswerChoice.degrees]
        calc
          |radiansToDegrees θ - 14| < (1 / 2 : ℝ) := by
            simpa [AnswerChoice.degrees] using herror
          _ < |radiansToDegrees θ - 20| := by
            rw [abs_of_neg (by linarith only [hdegree_upper])]
            linarith only [hdegree_upper]

end PhyXMiniProblems.ProblemPhyXMini0905
