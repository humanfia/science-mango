import Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle
import Physlib.Units.WithDim.Basic

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0901

open Dimension

/-!
# Equilibrium angle of two charged pendulums

Two identical `5.0 g` point charges, each carrying `+100 nC`, hang from a
common support on `1.0 m` threads. Electrostatic repulsion produces the
mirror-symmetric equilibrium shown in image `901.png`; `theta` is the acute
angle made by either thread with the downward vertical.

Dimensionful physical quantities are represented using Physlib. Real numbers
occur only as coherent-SI readouts, dimensionless trigonometric values, angles
in degrees, and literal data printed in the source.
-/

/-! ## Dimensionful physical quantities and coherent-SI readouts -/

/-- The physical dimension `L T⁻²` of acceleration. -/
def accelerationDimension : Dimension :=
  L𝓭 * T𝓭⁻¹ * T𝓭⁻¹

/-- The physical dimension `M L T⁻²` of force. -/
def forceDimension : Dimension :=
  M𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹

/-- The dimension `force * length² / charge²` of Coulomb's constant. -/
def coulombConstantDimension : Dimension :=
  forceDimension * L𝓭 * L𝓭 * C𝓭⁻¹ * C𝓭⁻¹

/-- A nonnegative mass as a unit-independent physical quantity. -/
abbrev MassQuantity : Type :=
  Dimensionful (WithDim M𝓭 NNReal)

/-- A nonnegative length as a unit-independent physical quantity. -/
abbrev LengthQuantity : Type :=
  Dimensionful (WithDim L𝓭 NNReal)

/-- A signed electric charge as a unit-independent physical quantity. -/
abbrev SignedChargeQuantity : Type :=
  Dimensionful (WithDim C𝓭 ℝ)

/-- A nonnegative acceleration magnitude. -/
abbrev AccelerationMagnitudeQuantity : Type :=
  Dimensionful (WithDim accelerationDimension NNReal)

/-- A nonnegative force magnitude. -/
abbrev ForceMagnitudeQuantity : Type :=
  Dimensionful (WithDim forceDimension NNReal)

/-- A nonnegative physical value of Coulomb's constant. -/
abbrev CoulombConstantQuantity : Type :=
  Dimensionful (WithDim coulombConstantDimension NNReal)

/-- Read a physical mass in kilograms. -/
def massInKilograms (mass : MassQuantity) : ℝ :=
  ((mass UnitChoices.SI).val : ℝ)

/-- Read a physical length in metres. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  ((length UnitChoices.SI).val : ℝ)

/-- Read a signed physical charge in coulombs. -/
def chargeInCoulombs (charge : SignedChargeQuantity) : ℝ :=
  (charge UnitChoices.SI).val

/-- Read an acceleration magnitude in metres per second squared. -/
def accelerationInMetersPerSecondSquared
    (acceleration : AccelerationMagnitudeQuantity) : ℝ :=
  ((acceleration UnitChoices.SI).val : ℝ)

/-- Read a force magnitude in newtons. -/
def forceInNewtons (force : ForceMagnitudeQuantity) : ℝ :=
  ((force UnitChoices.SI).val : ℝ)

/-- Read Coulomb's constant in `N m² / C²`. -/
def coulombConstantInNewtonMetersSquaredPerCoulombSquared
    (constant : CoulombConstantQuantity) : ℝ :=
  ((constant UnitChoices.SI).val : ℝ)

/-- Read the principal representative of an angle in degrees. -/
def angleInDegrees (angle : Real.Angle) : ℝ :=
  angle.toReal * 180 / Real.pi

/-! ## Physical setup and primary-figure vocabulary -/

/-- The left and right suspended charged bodies. -/
inductive Bob where
  | left
  | right
  deriving DecidableEq, Fintype, Repr

/-- Idealization of the two charged bodies used by Coulomb's law. -/
inductive ChargedBodyModel where
  | pointCharge
  | extendedBody
  deriving DecidableEq, Repr

/-- Idealization of each supporting thread. -/
inductive ThreadModel where
  | masslessInextensible
  | massiveOrExtensible
  deriving DecidableEq, Repr

/-- Mechanical state shown after the charges have separated. -/
inductive MechanicalState where
  | staticEquilibrium
  | accelerating
  deriving DecidableEq, Repr

/-- Signs printed inside the two red charge markers. -/
inductive PrintedChargeSign where
  | positive
  | negative
  deriving DecidableEq, Repr

/-- Physical or geometric objects visibly present in the supplied image. -/
inductive FigureObject where
  | overheadSupport
  | commonSuspensionPoint
  | leftThread
  | rightThread
  | leftCharge
  | rightCharge
  | dashedVerticalCenterline
  | angleArc
  deriving DecidableEq, Fintype, Repr

/-- Literal label kinds displayed in image `901.png`. -/
inductive FigureLabel where
  | threadLengthOneMeter
  | massFiveGrams
  | chargeOneHundredNanocoulombs
  | theta
  deriving DecidableEq, Fintype, Repr

/-- Presentation data transcribed from the primary image. -/
structure ChargedPendulumFigure where
  showsObject : FigureObject → Bool
  showsLabel : FigureLabel → Bool
  printedThreadLengthMeters : Bob → Option ℝ
  printedMassGrams : Bob → Option ℝ
  printedChargeNanocoulombs : Bob → Option ℝ
  printedChargeSign : Bob → PrintedChargeSign
  thetaLabelShownOnSide : Bob → Bool
  threadsMeetAtCommonSuspensionPoint : Bool
  centerlineIsVerticalAndDashed : Bool
  threadsAreMirrorSymmetricAboutCenterline : Bool

/-!
Independent physical quantities and observables of the two-pendulum system.
No force, separation, or angle is defined from the recorded answer.
-/
structure ChargedPendulumSetup where
  mass : Bob → MassQuantity
  charge : Bob → SignedChargeQuantity
  threadLength : Bob → LengthQuantity
  centerToCenterSeparation : LengthQuantity
  gravitationalAcceleration : AccelerationMagnitudeQuantity
  coulombConstant : CoulombConstantQuantity
  weightMagnitude : Bob → ForceMagnitudeQuantity
  electrostaticRepulsionMagnitude : ForceMagnitudeQuantity
  threadTensionMagnitude : Bob → ForceMagnitudeQuantity
  thetaFromDownwardVertical : Real.Angle
  chargedBodyModel : ChargedBodyModel
  threadModel : ThreadModel
  mechanicalState : MechanicalState
  figure : ChargedPendulumFigure

/-! ## Scenario, figure, and calibrated data -/

/-- Qualitative assumptions stated or implied by the physical scenario. -/
structure MatchesChargedPendulumScenario
    (setup : ChargedPendulumSetup) : Prop where
  bodiesArePointCharges : setup.chargedBodyModel = .pointCharge
  threadsAreMasslessAndInextensible :
    setup.threadModel = .masslessInextensible
  systemIsInStaticEquilibrium : setup.mechanicalState = .staticEquilibrium

/-- Exact qualitative and literal information visible in image `901.png`. -/
structure MatchesSuppliedFigure (setup : ChargedPendulumSetup) : Prop where
  everyNamedObjectIsShown :
    ∀ object, setup.figure.showsObject object = true
  everyLabelKindIsShown :
    ∀ label, setup.figure.showsLabel label = true
  leftThreadLengthPrinted :
    setup.figure.printedThreadLengthMeters .left = some 1
  rightThreadLengthPrinted :
    setup.figure.printedThreadLengthMeters .right = some 1
  leftMassPrinted : setup.figure.printedMassGrams .left = some 5
  rightMassPrinted : setup.figure.printedMassGrams .right = some 5
  leftChargePrinted :
    setup.figure.printedChargeNanocoulombs .left = some 100
  rightChargePrinted :
    setup.figure.printedChargeNanocoulombs .right = some 100
  bothPrintedSignsArePositive :
    ∀ bob, setup.figure.printedChargeSign bob = .positive
  thetaShownOnBothSides :
    ∀ bob, setup.figure.thetaLabelShownOnSide bob = true
  commonSuspensionPointShown :
    setup.figure.threadsMeetAtCommonSuspensionPoint = true
  verticalDashedCenterlineShown :
    setup.figure.centerlineIsVerticalAndDashed = true
  mirrorSymmetryShown :
    setup.figure.threadsAreMirrorSymmetricAboutCenterline = true

/-!
Dimensionful physical values stated in the problem. The signed charge readout
also records that both charges are positive. No angle or force value occurs
in this interface.
-/
structure HasProblemPhysicalData (setup : ChargedPendulumSetup) : Prop where
  massReadout : ∀ bob,
    massInKilograms (setup.mass bob) = 5 / 1000
  chargeReadout : ∀ bob,
    chargeInCoulombs (setup.charge bob) = 100 / (10 : ℝ) ^ 9
  threadLengthReadout : ∀ bob,
    lengthInMeters (setup.threadLength bob) = 1

/-- Standard textbook calibrations needed for the numerical calculation. -/
structure HasTextbookConstantCalibrations
    (setup : ChargedPendulumSetup) : Prop where
  gravitationalAccelerationSI :
    accelerationInMetersPerSecondSquared
        setup.gravitationalAcceleration = 98 / 10
  coulombConstantSI :
    coulombConstantInNewtonMetersSquaredPerCoulombSquared
        setup.coulombConstant = 8_990_000_000

/-- Positivity and the acute angular branch depicted in the figure. -/
structure HasPhysicalChargedPendulumParameters
    (setup : ChargedPendulumSetup) : Prop where
  positiveMass : ∀ bob, 0 < massInKilograms (setup.mass bob)
  positiveThreadLength :
    ∀ bob, 0 < lengthInMeters (setup.threadLength bob)
  positiveCharge : ∀ bob, 0 < chargeInCoulombs (setup.charge bob)
  positiveSeparation :
    0 < lengthInMeters setup.centerToCenterSeparation
  positiveGravity :
    0 < accelerationInMetersPerSecondSquared
      setup.gravitationalAcceleration
  positiveCoulombConstant :
    0 < coulombConstantInNewtonMetersSquaredPerCoulombSquared
      setup.coulombConstant
  positiveTension :
    ∀ bob, 0 < forceInNewtons (setup.threadTensionMagnitude bob)
  thetaIsPositive : 0 < setup.thetaFromDownwardVertical.toReal
  thetaIsAcute :
    setup.thetaFromDownwardVertical.toReal < Real.pi / 2

/-! ## Governing geometry, electrostatics, gravity, and statics -/

/-!
Mirror-symmetric common-pivot geometry. Each bob's horizontal displacement is
`L sin(theta)`, so the center-to-center separation is `2 L sin(theta)`.
-/
structure SatisfiesSymmetricPendulumGeometry
    (setup : ChargedPendulumSetup) : Prop where
  equalThreadLengths :
    setup.threadLength .left = setup.threadLength .right
  centerSeparation :
    lengthInMeters setup.centerToCenterSeparation =
      2 * lengthInMeters (setup.threadLength .left) *
        Real.Angle.sin setup.thetaFromDownwardVertical

/-!
Coulomb's inverse-square law, weight `m g`, and horizontal and vertical
component force balance. These are coherent-SI readout equations and contain
neither the target angle nor an answer-choice label.
-/
structure SatisfiesChargedPendulumEquilibriumLaws
    (setup : ChargedPendulumSetup) : Prop where
  coulombInverseSquareLaw :
    forceInNewtons setup.electrostaticRepulsionMagnitude =
      coulombConstantInNewtonMetersSquaredPerCoulombSquared
          setup.coulombConstant *
        chargeInCoulombs (setup.charge .left) *
        chargeInCoulombs (setup.charge .right) /
        lengthInMeters setup.centerToCenterSeparation ^ 2
  weightLaw : ∀ bob,
    forceInNewtons (setup.weightMagnitude bob) =
      massInKilograms (setup.mass bob) *
        accelerationInMetersPerSecondSquared
          setup.gravitationalAcceleration
  horizontalForceBalance : ∀ bob,
    forceInNewtons (setup.threadTensionMagnitude bob) *
        Real.Angle.sin setup.thetaFromDownwardVertical =
      forceInNewtons setup.electrostaticRepulsionMagnitude
  verticalForceBalance : ∀ bob,
    forceInNewtons (setup.threadTensionMagnitude bob) *
        Real.Angle.cos setup.thetaFromDownwardVertical =
      forceInNewtons (setup.weightMagnitude bob)

/-! ## Answer choices and requested conclusion -/

/-- Multiple-choice labels in the order displayed by the source. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Numerical angle printed beside an answer choice, in degrees. -/
def AnswerChoice.displayedAngleInDegrees : AnswerChoice → ℝ
  | .A => 3
  | .B => 9
  | .C => 44 / 10
  | .D => 2

/-- Precision of the final printed digit of each displayed choice. -/
def AnswerChoice.unitInLastDisplayedPlaceInDegrees : AnswerChoice → ℝ
  | .A => 1
  | .B => 1
  | .C => 1 / 10
  | .D => 1

/-- An actual angle agrees with a displayed choice under round-to-nearest. -/
def MatchesDisplayedPrecision
    (actualAngleInDegrees : ℝ) (choice : AnswerChoice) : Prop :=
  |actualAngleInDegrees - choice.displayedAngleInDegrees| ≤
    choice.unitInLastDisplayedPlaceInDegrees / 2

/-- A choice matches the independently modeled physical equilibrium angle. -/
def IsMatchingAnswer
    (setup : ChargedPendulumSetup) (choice : AnswerChoice) : Prop :=
  MatchesDisplayedPrecision
    (angleInDegrees setup.thetaFromDownwardVertical) choice

/-- Answer label recorded in the source dataset; metadata only. -/
def recordedDatasetAnswer : AnswerChoice := .C

/-!
For the symmetric charged pendulum satisfying the source data, standard
constants, geometry, Coulomb's law, gravity, and force balance, the acute
equilibrium angle rounds to `4.4°`. Thus choice C, and no other displayed
choice at its printed precision, matches the physical angle.

This declaration formalizes `thm:physics:phyx_mini_0901:target`. The rounded
value and choice selection occur only in this conclusion.
-/
theorem problem_phyx_mini_0901
    (setup : ChargedPendulumSetup)
    (hScenario : MatchesChargedPendulumScenario setup)
    (hFigure : MatchesSuppliedFigure setup)
    (hData : HasProblemPhysicalData setup)
    (hConstants : HasTextbookConstantCalibrations setup)
    (hPhysical : HasPhysicalChargedPendulumParameters setup)
    (hGeometry : SatisfiesSymmetricPendulumGeometry setup)
    (hLaws : SatisfiesChargedPendulumEquilibriumLaws setup) :
    IsMatchingAnswer setup .C ∧
      ∀ choice, IsMatchingAnswer setup choice → choice = .C := by
  let θ : ℝ := setup.thetaFromDownwardVertical.toReal
  let s : ℝ := Real.Angle.sin setup.thetaFromDownwardVertical
  let c : ℝ := Real.Angle.cos setup.thetaFromDownwardVertical
  let r : ℝ := lengthInMeters setup.centerToCenterSeparation
  let electricForce : ℝ :=
    forceInNewtons setup.electrostaticRepulsionMagnitude
  let tension : ℝ :=
    forceInNewtons (setup.threadTensionMagnitude .left)
  let weight : ℝ := forceInNewtons (setup.weightMagnitude .left)

  have hθpos : 0 < θ := hPhysical.thetaIsPositive
  have hθacute : θ < Real.pi / 2 := hPhysical.thetaIsAcute
  have hs_toReal : Real.sin θ = s := by
    exact Real.Angle.sin_toReal setup.thetaFromDownwardVertical
  have hc_toReal : Real.cos θ = c := by
    exact Real.Angle.cos_toReal setup.thetaFromDownwardVertical
  have hspos : 0 < s := by
    rw [← hs_toReal]
    exact Real.sin_pos_of_pos_of_lt_pi hθpos
      (hθacute.trans (by linarith only [Real.pi_pos]))
  have hrpos : 0 < r := hPhysical.positiveSeparation
  have htensionpos : 0 < tension := hPhysical.positiveTension .left

  have hcenter := hGeometry.centerSeparation
  change r = 2 * lengthInMeters (setup.threadLength .left) * s at hcenter
  rw [hData.threadLengthReadout .left] at hcenter
  norm_num at hcenter

  have hcoulomb := hLaws.coulombInverseSquareLaw
  change electricForce =
    coulombConstantInNewtonMetersSquaredPerCoulombSquared
        setup.coulombConstant *
      chargeInCoulombs (setup.charge .left) *
      chargeInCoulombs (setup.charge .right) / r ^ 2 at hcoulomb
  rw [hConstants.coulombConstantSI, hData.chargeReadout .left,
    hData.chargeReadout .right] at hcoulomb
  field_simp [ne_of_gt hrpos] at hcoulomb
  norm_num at hcoulomb

  have hweight := hLaws.weightLaw .left
  change weight =
    massInKilograms (setup.mass .left) *
      accelerationInMetersPerSecondSquared
        setup.gravitationalAcceleration at hweight
  rw [hData.massReadout .left, hConstants.gravitationalAccelerationSI] at hweight
  norm_num at hweight

  have hhorizontal := hLaws.horizontalForceBalance .left
  change tension * s = electricForce at hhorizontal
  have hvertical := hLaws.verticalForceBalance .left
  change tension * c = weight at hvertical

  have hr_sq : r ^ 2 = 4 * s ^ 2 := by
    calc
      r ^ 2 = (2 * s) ^ 2 := congrArg (fun x : ℝ => x ^ 2) hcenter
      _ = 4 * s ^ 2 := by ring
  have hcoulomb' : electricForce * (4 * s ^ 2) = 899 / 10_000_000 := by
    rw [hr_sq] at hcoulomb
    nlinarith only [hcoulomb]
  have htension_cube : tension * (4 * s ^ 3) = 899 / 10_000_000 := by
    calc
      tension * (4 * s ^ 3) = (tension * s) * (4 * s ^ 2) := by ring
      _ = electricForce * (4 * s ^ 2) := by rw [hhorizontal]
      _ = 899 / 10_000_000 := hcoulomb'
  have hweight_value : weight = 49 / 1000 := by
    norm_num at hweight ⊢
    exact hweight
  have htrig : s ^ 3 = (899 / 1_960_000 : ℝ) * c := by
    have h₁ := congrArg (fun x : ℝ => x * c) htension_cube
    have h₂ := congrArg (fun x : ℝ => x * (4 * s ^ 3)) hvertical
    rw [hweight_value] at h₂
    ring_nf at h₁ h₂ ⊢
    linarith only [h₁, h₂]

  have hsqrtTwo_sq : Real.sqrt (2 : ℝ) ^ 2 = 2 :=
    Real.sq_sqrt (by norm_num)
  have hsqrtThree_sq : Real.sqrt (3 : ℝ) ^ 2 = 3 :=
    Real.sq_sqrt (by norm_num)
  have hsqrtTwo_lower :
      (1_414_213 / 1_000_000 : ℝ) < Real.sqrt 2 := by
    rw [Real.lt_sqrt (by norm_num)]
    norm_num
  have hsqrtTwo_upper :
      Real.sqrt 2 < (1_414_214 / 1_000_000 : ℝ) := by
    rw [Real.sqrt_lt' (by norm_num)]
    norm_num
  have hsqrtThree_lower :
      (1_732_050 / 1_000_000 : ℝ) < Real.sqrt 3 := by
    rw [Real.lt_sqrt (by norm_num)]
    norm_num
  have hsqrtThree_upper :
      Real.sqrt 3 < (1_732_051 / 1_000_000 : ℝ) := by
    rw [Real.sqrt_lt' (by norm_num)]
    norm_num
  have hsqrtProduct_lower :
      (1_414_213 / 1_000_000 : ℝ) *
          (1_732_050 / 1_000_000 : ℝ) <
        Real.sqrt 2 * Real.sqrt 3 := by
    exact mul_lt_mul hsqrtTwo_lower hsqrtThree_lower.le (by norm_num)
      (Real.sqrt_nonneg 2)
  have hsqrtProduct_upper :
      Real.sqrt 2 * Real.sqrt 3 <
        (1_414_214 / 1_000_000 : ℝ) *
          (1_732_051 / 1_000_000 : ℝ) := by
    exact mul_lt_mul hsqrtTwo_upper hsqrtThree_upper.le
      (Real.sqrt_pos.2 (by norm_num)) (by norm_num)

  have hcos_pi_div_twelve :
      Real.cos (Real.pi / 12) =
        Real.sqrt 2 / 4 + (Real.sqrt 2 * Real.sqrt 3) / 4 := by
    calc
      Real.cos (Real.pi / 12) =
          Real.cos (Real.pi / 3 - Real.pi / 4) := by congr 1 <;> ring_nf
      _ = Real.cos (Real.pi / 3) * Real.cos (Real.pi / 4) +
          Real.sin (Real.pi / 3) * Real.sin (Real.pi / 4) := by
            rw [Real.cos_sub]
      _ = Real.sqrt 2 / 4 + (Real.sqrt 2 * Real.sqrt 3) / 4 := by
            rw [Real.cos_pi_div_three, Real.cos_pi_div_four,
              Real.sin_pi_div_three, Real.sin_pi_div_four]
            ring_nf
  have hsin_pi_div_twentyfour_sq :
      Real.sin (Real.pi / 24) ^ 2 =
        1 / 2 - Real.cos (Real.pi / 12) / 2 := by
    convert Real.sin_sq_eq_half_sub (Real.pi / 24) using 1 <;> ring_nf
  have hsin_pi_div_twentyfour_pos :
      0 < Real.sin (Real.pi / 24) := by
    exact Real.sin_pos_of_pos_of_lt_pi
      (div_pos Real.pi_pos (by norm_num))
      (by nlinarith only [Real.pi_pos])
  have hsin_pi_div_twentyfour_sq_lower :
      (1305 / 10000 : ℝ) ^ 2 <
        Real.sin (Real.pi / 24) ^ 2 := by
    nlinarith only [hsin_pi_div_twentyfour_sq, hcos_pi_div_twelve,
      hsqrtTwo_upper, hsqrtProduct_upper]
  have hsin_pi_div_twentyfour_sq_upper :
      Real.sin (Real.pi / 24) ^ 2 <
        (1306 / 10000 : ℝ) ^ 2 := by
    nlinarith only [hsin_pi_div_twentyfour_sq, hcos_pi_div_twelve,
      hsqrtTwo_lower, hsqrtProduct_lower]
  have hsin_pi_div_twentyfour_lower :
      (1305 / 10000 : ℝ) < Real.sin (Real.pi / 24) := by
    nlinarith only [hsin_pi_div_twentyfour_sq_lower,
      hsin_pi_div_twentyfour_pos]
  have hsin_pi_div_twentyfour_upper :
      Real.sin (Real.pi / 24) < (1306 / 10000 : ℝ) := by
    nlinarith only [hsin_pi_div_twentyfour_sq_upper,
      hsin_pi_div_twentyfour_pos]

  have hTaylorSix :=
    Real.sin_bound (x := Real.pi / 6) (by
      rw [abs_of_nonneg (by positivity : 0 ≤ Real.pi / 6)]
      nlinarith only [Real.pi_le_four])
  have hTaylorTwentyFour :=
    Real.sin_bound (x := Real.pi / 24) (by
      rw [abs_of_nonneg (by positivity : 0 ≤ Real.pi / 24)]
      nlinarith only [Real.pi_le_four])
  have hTaylorSix_upper :
      Real.sin (Real.pi / 6) ≤
        Real.pi / 6 - (Real.pi / 6) ^ 3 / 6 +
          |Real.pi / 6| ^ 4 * (5 / 96) := by
    linarith only [(abs_le.mp hTaylorSix).2]
  have hTaylorTwentyFour_upper :
      Real.sin (Real.pi / 24) ≤
        Real.pi / 24 - (Real.pi / 24) ^ 3 / 6 +
          |Real.pi / 24| ^ 4 * (5 / 96) := by
    linarith only [(abs_le.mp hTaylorTwentyFour).2]
  have hTaylorTwentyFour_lower :
      Real.pi / 24 - (Real.pi / 24) ^ 3 / 6 -
          |Real.pi / 24| ^ 4 * (5 / 96) ≤
        Real.sin (Real.pi / 24) := by
    linarith only [(abs_le.mp hTaylorTwentyFour).1]

  have hpi_gt_three : (3 : ℝ) < Real.pi := by
    by_contra h
    have hpi_le : Real.pi ≤ 3 := le_of_not_gt h
    have hx_lower : (1 / 3 : ℝ) ≤ Real.pi / 6 := by
      nlinarith only [Real.two_le_pi]
    have hx_upper : Real.pi / 6 ≤ (1 / 2 : ℝ) := by
      nlinarith only [hpi_le]
    have hx_cube : (1 / 3 : ℝ) ^ 3 ≤ (Real.pi / 6) ^ 3 := by
      gcongr
    have hx_fourth : (Real.pi / 6) ^ 4 ≤ (1 / 2 : ℝ) ^ 4 := by
      gcongr
    rw [abs_of_nonneg (by positivity : 0 ≤ Real.pi / 6),
      Real.sin_pi_div_six] at hTaylorSix_upper
    nlinarith only [hTaylorSix_upper, hx_upper, hx_cube, hx_fourth]
  have hpi_gt_three_point_one : (31 / 10 : ℝ) < Real.pi := by
    by_contra h
    have hpi_le : Real.pi ≤ 31 / 10 := le_of_not_gt h
    have hx_lower : (1 / 2 : ℝ) ≤ Real.pi / 6 := by
      nlinarith only [hpi_gt_three]
    have hx_upper : Real.pi / 6 ≤ (31 / 60 : ℝ) := by
      nlinarith only [hpi_le]
    have hx_cube : (1 / 2 : ℝ) ^ 3 ≤ (Real.pi / 6) ^ 3 := by
      gcongr
    have hx_fourth : (Real.pi / 6) ^ 4 ≤ (31 / 60 : ℝ) ^ 4 := by
      gcongr
    rw [abs_of_nonneg (by positivity : 0 ≤ Real.pi / 6),
      Real.sin_pi_div_six] at hTaylorSix_upper
    nlinarith only [hTaylorSix_upper, hx_upper, hx_cube, hx_fourth]
  have hpi_gt_three_point_one_four : (157 / 50 : ℝ) < Real.pi := by
    by_contra h
    have hpi_le : Real.pi ≤ 157 / 50 := le_of_not_gt h
    have hx_lower : (31 / 240 : ℝ) ≤ Real.pi / 24 := by
      nlinarith only [hpi_gt_three_point_one]
    have hx_upper : Real.pi / 24 ≤ (157 / 1200 : ℝ) := by
      nlinarith only [hpi_le]
    have hx_cube : (31 / 240 : ℝ) ^ 3 ≤ (Real.pi / 24) ^ 3 := by
      gcongr
    have hx_fourth :
        (Real.pi / 24) ^ 4 ≤ (157 / 1200 : ℝ) ^ 4 := by
      gcongr
    rw [abs_of_nonneg (by positivity : 0 ≤ Real.pi / 24)] at hTaylorTwentyFour_upper
    nlinarith only [hTaylorTwentyFour_upper, hsin_pi_div_twentyfour_lower,
      hx_upper, hx_cube, hx_fourth]
  have hpi_lt_three_point_two : Real.pi < (16 / 5 : ℝ) := by
    by_contra h
    have hpi_lower : (16 / 5 : ℝ) ≤ Real.pi := le_of_not_gt h
    have hx_lower : (2 / 15 : ℝ) ≤ Real.pi / 24 := by
      nlinarith only [hpi_lower]
    have hx_upper : Real.pi / 24 ≤ (1 / 6 : ℝ) := by
      nlinarith only [Real.pi_le_four]
    have hx_cube : (Real.pi / 24) ^ 3 ≤ (1 / 6 : ℝ) ^ 3 := by
      gcongr
    have hx_fourth : (Real.pi / 24) ^ 4 ≤ (1 / 6 : ℝ) ^ 4 := by
      gcongr
    rw [abs_of_nonneg (by positivity : 0 ≤ Real.pi / 24)] at hTaylorTwentyFour_lower
    nlinarith only [hTaylorTwentyFour_lower, hsin_pi_div_twentyfour_upper,
      hx_lower, hx_cube, hx_fourth]
  have hpi_lt_three_point_one_five : Real.pi < (63 / 20 : ℝ) := by
    by_contra h
    have hpi_lower : (63 / 20 : ℝ) ≤ Real.pi := le_of_not_gt h
    have hx_lower : (21 / 160 : ℝ) ≤ Real.pi / 24 := by
      nlinarith only [hpi_lower]
    have hx_upper : Real.pi / 24 ≤ (2 / 15 : ℝ) := by
      nlinarith only [hpi_lt_three_point_two]
    have hx_cube : (Real.pi / 24) ^ 3 ≤ (2 / 15 : ℝ) ^ 3 := by
      gcongr
    have hx_fourth : (Real.pi / 24) ^ 4 ≤ (2 / 15 : ℝ) ^ 4 := by
      gcongr
    rw [abs_of_nonneg (by positivity : 0 ≤ Real.pi / 24)] at hTaylorTwentyFour_lower
    nlinarith only [hTaylorTwentyFour_lower, hsin_pi_div_twentyfour_upper,
      hx_lower, hx_cube, hx_fourth]

  have hsin_one_lower : (75 / 96 : ℝ) ≤ Real.sin 1 := by
    have h := (abs_le.mp (Real.sin_bound (x := (1 : ℝ)) (by norm_num))).1
    norm_num at h ⊢
    linarith only [h]
  have hθ_lt_one : θ < 1 := by
    by_contra h
    have hθ_ge_one : (1 : ℝ) ≤ θ := le_of_not_gt h
    have hsin_one_le : Real.sin 1 ≤ s := by
      rw [← hs_toReal]
      exact Real.sin_le_sin_of_le_of_le_pi_div_two
        (by nlinarith only [Real.pi_pos]) hθacute.le hθ_ge_one
    have hc_le_one : c ≤ 1 := by
      rw [← hc_toReal]
      exact Real.cos_le_one θ
    have hs_cube_le : s ^ 3 ≤ (899 / 1_960_000 : ℝ) := by
      nlinarith only [htrig, hc_le_one]
    have hs_lower : (75 / 96 : ℝ) ≤ s :=
      hsin_one_lower.trans hsin_one_le
    have hs_cube_lower : (75 / 96 : ℝ) ^ 3 ≤ s ^ 3 := by
      gcongr
    norm_num at hs_cube_lower hs_cube_le
    linarith only [hs_cube_lower, hs_cube_le]
  have hθ_le_one : θ ≤ 1 := hθ_lt_one.le
  have hθ_abs_le_one : |θ| ≤ 1 := by
    rw [abs_of_nonneg hθpos.le]
    exact hθ_le_one

  have hSinTheta := Real.sin_bound hθ_abs_le_one
  have hCosTheta := Real.cos_bound hθ_abs_le_one
  have hsinTheta_upper :
      s ≤ θ - θ ^ 3 / 6 + θ ^ 4 * (5 / 96) := by
    rw [← hs_toReal]
    rw [abs_of_nonneg hθpos.le] at hSinTheta
    linarith only [(abs_le.mp hSinTheta).2]
  have hsinTheta_lower :
      θ - θ ^ 3 / 6 - θ ^ 4 * (5 / 96) ≤ s := by
    rw [← hs_toReal]
    rw [abs_of_nonneg hθpos.le] at hSinTheta
    linarith only [(abs_le.mp hSinTheta).1]
  have hcosTheta_lower :
      1 - θ ^ 2 / 2 - θ ^ 4 * (5 / 96) ≤ c := by
    rw [← hc_toReal]
    rw [abs_of_nonneg hθpos.le] at hCosTheta
    linarith only [(abs_le.mp hCosTheta).1]
  have hc_le_one : c ≤ 1 := by
    rw [← hc_toReal]
    exact Real.cos_le_one θ
  have hs_cube_le : s ^ 3 ≤ (899 / 1_960_000 : ℝ) := by
    nlinarith only [htrig, hc_le_one]

  have hθ_lower : (381 / 5000 : ℝ) < θ := by
    by_contra h
    have hθ_upper : θ ≤ (381 / 5000 : ℝ) := le_of_not_gt h
    have hθ_sq_upper :
        θ ^ 2 ≤ (381 / 5000 : ℝ) ^ 2 := by
      gcongr
    have hθ_fourth_upper :
        θ ^ 4 ≤ (381 / 5000 : ℝ) ^ 4 := by
      gcongr
    have hs_upper :
        s ≤ (381 / 5000 : ℝ) +
          (381 / 5000 : ℝ) ^ 4 * (5 / 96) := by
      nlinarith only [hsinTheta_upper, hθ_upper, hθ_fourth_upper,
        pow_nonneg hθpos.le 3]
    have hs_cube_upper :
        s ^ 3 ≤
          ((381 / 5000 : ℝ) +
            (381 / 5000 : ℝ) ^ 4 * (5 / 96)) ^ 3 := by
      gcongr
    have hc_lower :
        1 - (381 / 5000 : ℝ) ^ 2 / 2 -
            (381 / 5000 : ℝ) ^ 4 * (5 / 96) ≤ c := by
      nlinarith only [hcosTheta_lower, hθ_sq_upper, hθ_fourth_upper]
    nlinarith only [htrig, hs_cube_upper, hc_lower]

  have hθ_lt_one_tenth : θ < (1 / 10 : ℝ) := by
    have hθ_sq_le : θ ^ 2 ≤ θ := by
      nlinarith only [mul_nonneg hθpos.le (sub_nonneg.mpr hθ_le_one)]
    have hθ_cube_le : θ ^ 3 ≤ θ := by
      calc
        θ ^ 3 = θ ^ 2 * θ := by ring
        _ ≤ θ * θ := mul_le_mul_of_nonneg_right hθ_sq_le hθpos.le
        _ ≤ θ := by simpa [pow_two] using hθ_sq_le
    have hθ_fourth_le : θ ^ 4 ≤ θ := by
      calc
        θ ^ 4 = θ ^ 3 * θ := by ring
        _ ≤ θ * θ := mul_le_mul_of_nonneg_right hθ_cube_le hθpos.le
        _ ≤ θ := by simpa [pow_two] using hθ_sq_le
    have hs_linear_lower : (75 / 96 : ℝ) * θ ≤ s := by
      nlinarith only [hsinTheta_lower, hθ_cube_le, hθ_fourth_le]
    by_contra h
    have hθ_ge : (1 / 10 : ℝ) ≤ θ := le_of_not_gt h
    have hs_lower : (5 / 64 : ℝ) ≤ s := by
      nlinarith only [hs_linear_lower, hθ_ge]
    have hs_cube_lower : (5 / 64 : ℝ) ^ 3 ≤ s ^ 3 := by
      gcongr
    norm_num at hs_cube_lower hs_cube_le
    linarith only [hs_cube_lower, hs_cube_le]

  have hθ_upper : θ < (97 / 1250 : ℝ) := by
    by_contra h
    have hθ_ge : (97 / 1250 : ℝ) ≤ θ := le_of_not_gt h
    have hθ_cube_upper : θ ^ 3 ≤ (1 / 10 : ℝ) ^ 3 := by
      gcongr
    have hθ_fourth_upper : θ ^ 4 ≤ (1 / 10 : ℝ) ^ 4 := by
      gcongr
    have hs_lower :
        (97 / 1250 : ℝ) - (1 / 10 : ℝ) ^ 3 / 6 -
            (1 / 10 : ℝ) ^ 4 * (5 / 96) ≤ s := by
      nlinarith only [hsinTheta_lower, hθ_ge, hθ_cube_upper,
        hθ_fourth_upper]
    have hs_cube_lower :
        ((97 / 1250 : ℝ) - (1 / 10 : ℝ) ^ 3 / 6 -
            (1 / 10 : ℝ) ^ 4 * (5 / 96)) ^ 3 ≤ s ^ 3 := by
      gcongr
    norm_num at hs_cube_lower hs_cube_le
    linarith only [hs_cube_lower, hs_cube_le]

  have hAngleDegrees_lower :
      (435 / 100 : ℝ) <
        angleInDegrees setup.thetaFromDownwardVertical := by
    change (435 / 100 : ℝ) < θ * 180 / Real.pi
    rw [lt_div_iff₀ Real.pi_pos]
    nlinarith only [hθ_lower, hpi_lt_three_point_one_five]
  have hAngleDegrees_upper :
      angleInDegrees setup.thetaFromDownwardVertical <
        (445 / 100 : ℝ) := by
    change θ * 180 / Real.pi < (445 / 100 : ℝ)
    rw [div_lt_iff₀ Real.pi_pos]
    nlinarith only [hθ_upper, hpi_gt_three_point_one_four]

  constructor
  · change
      |angleInDegrees setup.thetaFromDownwardVertical - 44 / 10| ≤
        (1 / 10 : ℝ) / 2
    rw [abs_le]
    constructor <;> nlinarith only [hAngleDegrees_lower, hAngleDegrees_upper]
  · intro choice hchoice
    fin_cases choice
    · exfalso
      change
        |angleInDegrees setup.thetaFromDownwardVertical - 3| ≤
          (1 : ℝ) / 2 at hchoice
      rw [abs_le] at hchoice
      nlinarith only [hchoice.2, hAngleDegrees_lower]
    · exfalso
      change
        |angleInDegrees setup.thetaFromDownwardVertical - 9| ≤
          (1 : ℝ) / 2 at hchoice
      rw [abs_le] at hchoice
      nlinarith only [hchoice.1, hAngleDegrees_upper]
    · rfl
    · exfalso
      change
        |angleInDegrees setup.thetaFromDownwardVertical - 2| ≤
          (1 : ℝ) / 2 at hchoice
      rw [abs_le] at hchoice
      nlinarith only [hchoice.2, hAngleDegrees_lower]

end PhyXMiniProblems.ProblemPhyXMini0901
