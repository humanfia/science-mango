import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Physlib.Units.WithDim.Basic

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0839

open Dimension

/-!
# Electric force on a uniformly charged plastic stirrer

A `6.0 cm` plastic stirrer lies radially outward from a long charged wire. Its
near end is `2.0 cm` from the wire, its uniformly distributed charge has
magnitude `10 nC`, and the wire's linear charge density has magnitude
`1.0 * 10^-7 C/m`.

Physical quantities are represented by unit-independent Physlib values. Real
numbers below are explicitly coherent-SI readouts or literal scalar data from
the prose, primary image, and answer choices.

Assumption/target split:

* governing laws: the infinite-line-charge field law
  `E(r) = 2 k lambda / r`, continuous-charge superposition
  `F = integral (dq/dr) E(r) dr`, and repulsion of like charges;
* previous-part results: none;
* figure/data readouts: the `6.0 cm` length, `2.0 cm` near-end distance,
  `10 nC` stirrer charge, `1.0 * 10^-7 C/m` wire density, positive marks on
  the wire, and the relative geometry drawn in image `839.png`;
* current target conclusions: the force has the derived logarithmic closed
  form, points away from the wire, and agrees at the displayed precision with
  choice D, `4.2 * 10^-4 N`.
-/

/-! ## Dimensionful quantities and coherent-SI readouts -/

/-- Dimension of force, `M L T^-2`. -/
def forceDimension : Dimension := M𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹

/-- Dimension of linear charge density, `C L^-1`. -/
def lineChargeDensityDimension : Dimension := C𝓭 * L𝓭⁻¹

/-- Dimension of electric-field magnitude, `N/C`. -/
def electricFieldDimension : Dimension := forceDimension * C𝓭⁻¹

/-- Dimension of Coulomb's constant, `N m^2 / C^2`. -/
def coulombConstantDimension : Dimension :=
  forceDimension * L𝓭 * L𝓭 * C𝓭⁻¹ * C𝓭⁻¹

/-- A nonnegative, unit-independent physical length. -/
abbrev LengthQuantity : Type := Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative, unit-independent electric-charge magnitude. -/
abbrev ChargeMagnitudeQuantity : Type := Dimensionful (WithDim C𝓭 NNReal)

/-- A nonnegative linear-charge-density magnitude. -/
abbrev LineChargeDensityMagnitudeQuantity : Type :=
  Dimensionful (WithDim lineChargeDensityDimension NNReal)

/-- A nonnegative physical force magnitude. -/
abbrev ForceMagnitudeQuantity : Type :=
  Dimensionful (WithDim forceDimension NNReal)

/-- A nonnegative value of Coulomb's constant with its physical dimension. -/
abbrev CoulombConstantQuantity : Type :=
  Dimensionful (WithDim coulombConstantDimension NNReal)

/-- Coherent-SI metre readout of a physical length. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  ((length UnitChoices.SI).val : ℝ)

/-- Coherent-SI coulomb readout of a charge magnitude. -/
def chargeInCoulombs (charge : ChargeMagnitudeQuantity) : ℝ :=
  ((charge UnitChoices.SI).val : ℝ)

/-- Coherent-SI coulomb-per-metre readout of a linear charge density. -/
def lineChargeDensityInCoulombsPerMeter
    (density : LineChargeDensityMagnitudeQuantity) : ℝ :=
  ((density UnitChoices.SI).val : ℝ)

/-- Coherent-SI newton readout of a physical force magnitude. -/
def forceInNewtons (force : ForceMagnitudeQuantity) : ℝ :=
  ((force UnitChoices.SI).val : ℝ)

/-- Coherent-SI readout of Coulomb's constant in `N m^2 / C^2`. -/
def coulombConstantInNewtonMetersSquaredPerCoulombSquared
    (constant : CoulombConstantQuantity) : ℝ :=
  ((constant UnitChoices.SI).val : ℝ)

/-! ## Physical and primary-figure vocabulary -/

/-- The two physical objects shown in the primary image. -/
inductive FigureObject where
  | chargedLongWire
  | plasticStirrer
  deriving DecidableEq, Fintype, Repr

/-- Literal annotations visible in image `839.png`. -/
inductive FigureLabel where
  | wirePositiveChargeMarks
  | lambdaEqualsOneTimesTenToMinusSevenCoulombsPerMeter
  | plasticStirrerText
  | nearEndDistanceTwoCentimeters
  | stirrerLengthSixCentimeters
  deriving DecidableEq, Fintype, Repr

/-- Sign of an object's electric charge. -/
inductive ChargeSign where
  | positive
  | negative
  deriving DecidableEq, Repr

/-- Idealization of the long charged object. -/
inductive WireModel where
  | infiniteStraightLineCharge
  | finiteWire
  deriving DecidableEq, Repr

/-- Distribution of charge along the plastic stirrer. -/
inductive StirrerChargeDistribution where
  | uniformAlongLength
  | nonuniform
  deriving DecidableEq, Repr

/-- Relative orientation of the wire and the stirrer. -/
inductive WireStirrerOrientation where
  | stirrerRadialAndPerpendicularToWire
  | other
  deriving DecidableEq, Repr

/-- Direction of the stirrer's net electric force along its radial axis. -/
inductive RadialForceDirection where
  | towardWire
  | awayFromWire
  deriving DecidableEq, Repr

/-- Method by which the plastic rod is charged in the prose. -/
inductive ChargingMethod where
  | rubbingWithFur
  deriving DecidableEq, Repr

/-- Event at which the requested electric force launches the stirrer. -/
inductive LaunchEvent where
  | releasedFromRestNearWire
  deriving DecidableEq, Repr

/-!
Literal qualitative and scalar information read from the primary bitmap.
There is deliberately no net-force value or answer-choice field here.
-/
structure ChargedStirrerFigure where
  objectShown : FigureObject → Bool
  labelShown : FigureLabel → Bool
  wireIsVertical : Bool
  stirrerIsHorizontal : Bool
  wireIsLeftOfStirrer : Bool
  closestEndGapLabelCentimeters : ℝ
  stirrerLengthLabelCentimeters : ℝ
  wireDensityLabelCoulombsPerMeter : ℝ

/-!
Independent physical quantities in the wire--stirrer system. In particular,
the net force is not defined from the recorded answer, and the electric-field
readout is not defined to be the desired final force formula.
-/
structure ChargedStirrerSetup where
  stirrerLength : LengthQuantity
  closestEndDistanceFromWire : LengthQuantity
  stirrerChargeMagnitude : ChargeMagnitudeQuantity
  wireLinearChargeDensityMagnitude : LineChargeDensityMagnitudeQuantity
  coulombConstant : CoulombConstantQuantity
  /-- Electric-field magnitude in `N/C` at a positive SI radius in metres. -/
  electricFieldMagnitudeInNewtonsPerCoulombAtRadiusMeters : ℝ → ℝ
  netElectricForceMagnitude : ForceMagnitudeQuantity
  netElectricForceDirection : RadialForceDirection
  stirrerChargeSign : ChargeSign
  wireChargeSign : ChargeSign
  wireModel : WireModel
  stirrerChargeDistribution : StirrerChargeDistribution
  orientation : WireStirrerOrientation
  chargingMethod : ChargingMethod
  launchEvent : LaunchEvent
  figure : ChargedStirrerFigure

/-! ## Source data, figure evidence, and governing physics -/

/--
Numerical data stated in the prose, written as exact coherent-SI readouts.
No force value from any answer choice occurs in this premise.
-/
structure HasChargedStirrerProblemData (setup : ChargedStirrerSetup) : Prop where
  stirrerLengthMeters : lengthInMeters setup.stirrerLength = (6 : ℝ) / 100
  closestEndDistanceMeters :
    lengthInMeters setup.closestEndDistanceFromWire = (2 : ℝ) / 100
  stirrerChargeCoulombs :
    chargeInCoulombs setup.stirrerChargeMagnitude =
      (10 : ℝ) * 10 ^ (-9 : ℤ)
  wireLinearDensityCoulombsPerMeter :
    lineChargeDensityInCoulombsPerMeter
        setup.wireLinearChargeDensityMagnitude =
      (1.0 : ℝ) * 10 ^ (-7 : ℤ)

/--
Qualitative modeling assumptions supplied by the prose: a long straight wire,
a uniformly charged rod, like charge signs so release produces repulsion, and
the radial geometry shown in the figure.
-/
structure MatchesChargedStirrerScenario (setup : ChargedStirrerSetup) : Prop where
  wireTreatedAsInfiniteStraightLineCharge :
    setup.wireModel = .infiniteStraightLineCharge
  stirrerChargeIsUniform :
    setup.stirrerChargeDistribution = .uniformAlongLength
  stirrerExtendsRadiallyFromWire :
    setup.orientation = .stirrerRadialAndPerpendicularToWire
  chargesHaveSameSign : setup.stirrerChargeSign = setup.wireChargeSign
  plasticWasChargedByRubbingWithFur :
    setup.chargingMethod = .rubbingWithFur
  forceIsEvaluatedWhenReleased : setup.launchEvent = .releasedFromRestNearWire

/--
Evidence transcribed from the primary image. The three scalar labels are kept
both in their printed units here and related to the setup's SI quantities.
-/
structure MatchesChargedStirrerPrimaryFigure
    (setup : ChargedStirrerSetup) : Prop where
  wireShown : setup.figure.objectShown .chargedLongWire = true
  stirrerShown : setup.figure.objectShown .plasticStirrer = true
  positiveMarksShown :
    setup.figure.labelShown .wirePositiveChargeMarks = true
  lambdaLabelShown :
    setup.figure.labelShown
        .lambdaEqualsOneTimesTenToMinusSevenCoulombsPerMeter = true
  stirrerTextShown : setup.figure.labelShown .plasticStirrerText = true
  twoCentimeterGapLabelShown :
    setup.figure.labelShown .nearEndDistanceTwoCentimeters = true
  sixCentimeterLengthLabelShown :
    setup.figure.labelShown .stirrerLengthSixCentimeters = true
  wireVertical : setup.figure.wireIsVertical = true
  stirrerHorizontal : setup.figure.stirrerIsHorizontal = true
  wireLeftOfStirrer : setup.figure.wireIsLeftOfStirrer = true
  gapLabelCentimeters : setup.figure.closestEndGapLabelCentimeters = 2
  lengthLabelCentimeters : setup.figure.stirrerLengthLabelCentimeters = 6
  densityLabelCoulombsPerMeter :
    setup.figure.wireDensityLabelCoulombsPerMeter =
      (1.0 : ℝ) * 10 ^ (-7 : ℤ)
  gapLabelMatchesPhysicalDistance :
    setup.figure.closestEndGapLabelCentimeters / 100 =
      lengthInMeters setup.closestEndDistanceFromWire
  lengthLabelMatchesPhysicalLength :
    setup.figure.stirrerLengthLabelCentimeters / 100 =
      lengthInMeters setup.stirrerLength
  densityLabelMatchesPhysicalDensity :
    setup.figure.wireDensityLabelCoulombsPerMeter =
      lineChargeDensityInCoulombsPerMeter
        setup.wireLinearChargeDensityMagnitude
  positiveMarksIdentifyWireSign : setup.wireChargeSign = .positive

/-!
The electrostatic laws needed for the computation, stated at coherent-SI
readout level. The first field is the standard value of Coulomb's constant.
The second is the field magnitude of an infinite line charge. The third is
continuous-charge superposition for a uniform radial rod: `dq/dr = Q/L` and
`dF = E dq`. The last field is the general direction law for like charges.

None of these fields states the requested numerical net force.
-/
structure SatisfiesInfiniteLineChargeElectrostatics
    (setup : ChargedStirrerSetup) : Prop where
  coulombConstantSI :
    coulombConstantInNewtonMetersSquaredPerCoulombSquared
        setup.coulombConstant =
      (8.99 : ℝ) * 10 ^ (9 : ℕ)
  infiniteLineElectricFieldLaw :
    ∀ radiusMeters : ℝ,
      0 < radiusMeters →
        setup.electricFieldMagnitudeInNewtonsPerCoulombAtRadiusMeters
            radiusMeters =
          2 *
            coulombConstantInNewtonMetersSquaredPerCoulombSquared
              setup.coulombConstant *
            lineChargeDensityInCoulombsPerMeter
              setup.wireLinearChargeDensityMagnitude /
            radiusMeters
  uniformRodContinuousChargeSuperposition :
    setup.stirrerChargeDistribution = .uniformAlongLength →
      forceInNewtons setup.netElectricForceMagnitude =
        ∫ radiusMeters : ℝ in
          lengthInMeters setup.closestEndDistanceFromWire..
            lengthInMeters setup.closestEndDistanceFromWire +
              lengthInMeters setup.stirrerLength,
          (chargeInCoulombs setup.stirrerChargeMagnitude /
              lengthInMeters setup.stirrerLength) *
            setup.electricFieldMagnitudeInNewtonsPerCoulombAtRadiusMeters
              radiusMeters
  likeChargesRepel :
    setup.stirrerChargeSign = setup.wireChargeSign →
      setup.netElectricForceDirection = .awayFromWire

/-! ## Derived closed form and displayed answer -/

/--
Integration of the inverse-radius line-charge field along the stirrer gives
the logarithmic net-force formula. This is a derived relation, not a field of
the governing-law premise.
-/
theorem netElectricForceMagnitude_closedForm
    (setup : ChargedStirrerSetup)
    (_data : HasChargedStirrerProblemData setup)
    (_scenario : MatchesChargedStirrerScenario setup)
    (_figure : MatchesChargedStirrerPrimaryFigure setup)
    (_laws : SatisfiesInfiniteLineChargeElectrostatics setup) :
    forceInNewtons setup.netElectricForceMagnitude =
      2 *
        coulombConstantInNewtonMetersSquaredPerCoulombSquared
          setup.coulombConstant *
        lineChargeDensityInCoulombsPerMeter
          setup.wireLinearChargeDensityMagnitude *
        (chargeInCoulombs setup.stirrerChargeMagnitude /
          lengthInMeters setup.stirrerLength) *
        Real.log
          ((lengthInMeters setup.closestEndDistanceFromWire +
              lengthInMeters setup.stirrerLength) /
            lengthInMeters setup.closestEndDistanceFromWire) := by
  have hLengthPositive :
      0 < lengthInMeters setup.stirrerLength := by
    rw [_data.stirrerLengthMeters]
    norm_num
  have hNearPositive :
      0 < lengthInMeters setup.closestEndDistanceFromWire := by
    rw [_data.closestEndDistanceMeters]
    norm_num
  have hEndpointsOrdered :
      lengthInMeters setup.closestEndDistanceFromWire ≤
        lengthInMeters setup.closestEndDistanceFromWire +
          lengthInMeters setup.stirrerLength := by
    linarith
  rw [_laws.uniformRodContinuousChargeSuperposition
    _scenario.stirrerChargeIsUniform]
  calc
    (∫ radiusMeters : ℝ in
        lengthInMeters setup.closestEndDistanceFromWire..
          lengthInMeters setup.closestEndDistanceFromWire +
            lengthInMeters setup.stirrerLength,
        (chargeInCoulombs setup.stirrerChargeMagnitude /
            lengthInMeters setup.stirrerLength) *
          setup.electricFieldMagnitudeInNewtonsPerCoulombAtRadiusMeters
            radiusMeters) =
      ∫ radiusMeters : ℝ in
        lengthInMeters setup.closestEndDistanceFromWire..
          lengthInMeters setup.closestEndDistanceFromWire +
            lengthInMeters setup.stirrerLength,
        (chargeInCoulombs setup.stirrerChargeMagnitude /
            lengthInMeters setup.stirrerLength) *
          (2 *
              coulombConstantInNewtonMetersSquaredPerCoulombSquared
                setup.coulombConstant *
              lineChargeDensityInCoulombsPerMeter
                setup.wireLinearChargeDensityMagnitude /
            radiusMeters) := by
      apply intervalIntegral.integral_congr
      intro radiusMeters hRadius
      dsimp only
      rw [_laws.infiniteLineElectricFieldLaw radiusMeters]
      rw [Set.uIcc_of_le hEndpointsOrdered] at hRadius
      exact lt_of_lt_of_le hNearPositive hRadius.1
    _ =
      ∫ radiusMeters : ℝ in
        lengthInMeters setup.closestEndDistanceFromWire..
          lengthInMeters setup.closestEndDistanceFromWire +
            lengthInMeters setup.stirrerLength,
        (2 *
            coulombConstantInNewtonMetersSquaredPerCoulombSquared
              setup.coulombConstant *
            lineChargeDensityInCoulombsPerMeter
              setup.wireLinearChargeDensityMagnitude *
            (chargeInCoulombs setup.stirrerChargeMagnitude /
              lengthInMeters setup.stirrerLength)) *
          (1 / radiusMeters) := by
      apply intervalIntegral.integral_congr
      intro radiusMeters _
      ring
    _ =
      2 *
        coulombConstantInNewtonMetersSquaredPerCoulombSquared
          setup.coulombConstant *
        lineChargeDensityInCoulombsPerMeter
          setup.wireLinearChargeDensityMagnitude *
        (chargeInCoulombs setup.stirrerChargeMagnitude /
          lengthInMeters setup.stirrerLength) *
        Real.log
          ((lengthInMeters setup.closestEndDistanceFromWire +
              lengthInMeters setup.stirrerLength) /
            lengthInMeters setup.closestEndDistanceFromWire) := by
      rw [intervalIntegral.integral_const_mul,
        integral_one_div_of_pos hNearPositive (by linarith)]

/-- The four force magnitudes printed in the multiple-choice list. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Literal answer-choice force readout in newtons. -/
def answerChoiceForceInNewtons : AnswerChoice → ℝ
  | .A => (1.3 : ℝ) * 10 ^ (-5 : ℤ)
  | .B => (5.3 : ℝ) * 10 ^ (-4 : ℤ)
  | .C => (1.0 : ℝ) * 10 ^ (-5 : ℤ)
  | .D => (4.2 : ℝ) * 10 ^ (-4 : ℤ)

/-- Half of the last displayed decimal place in choice D. -/
def choiceDDisplayToleranceInNewtons : ℝ :=
  (0.05 : ℝ) * 10 ^ (-4 : ℤ)

/--
The net force points away from the like-charged wire, and its magnitude agrees
with answer choice D to the precision printed in the source.
-/
theorem netElectricForce_isAwayFromWire_and_agreesWithChoiceD
    (setup : ChargedStirrerSetup)
    (_data : HasChargedStirrerProblemData setup)
    (_scenario : MatchesChargedStirrerScenario setup)
    (_figure : MatchesChargedStirrerPrimaryFigure setup)
    (_laws : SatisfiesInfiniteLineChargeElectrostatics setup) :
    setup.netElectricForceDirection = .awayFromWire ∧
      |forceInNewtons setup.netElectricForceMagnitude -
          answerChoiceForceInNewtons .D| <
        choiceDDisplayToleranceInNewtons := by
  constructor
  · exact _laws.likeChargesRepel _scenario.chargesHaveSameSign
  · rw [netElectricForceMagnitude_closedForm setup _data _scenario _figure
      _laws]
    rw [_laws.coulombConstantSI, _data.wireLinearDensityCoulombsPerMeter,
      _data.stirrerChargeCoulombs, _data.stirrerLengthMeters,
      _data.closestEndDistanceMeters]
    have hLogTwoLower : (693 / 1000 : ℝ) < Real.log 2 := by
      rw [Real.lt_log_iff_exp_lt (by norm_num)]
      have hBound :=
        Real.exp_bound' (x := (693 / 1000 : ℝ))
          (by norm_num) (by norm_num) (n := 10) (by norm_num)
      norm_num [Finset.sum_range_succ, Nat.factorial] at hBound ⊢
      linarith
    have hLogTwoUpper : Real.log 2 < (1387 / 2000 : ℝ) := by
      rw [Real.log_lt_iff_lt_exp (by norm_num)]
      have hBound :=
        Real.sum_le_exp_of_nonneg
          (x := (1387 / 2000 : ℝ)) (by norm_num) 10
      norm_num [Finset.sum_range_succ, Nat.factorial] at hBound ⊢
      linarith
    have hLogFour :
        (1386 / 1000 : ℝ) < Real.log 4 ∧
          Real.log 4 < (1387 / 1000 : ℝ) := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      norm_num
      constructor <;> linarith
    rw [abs_lt]
    constructor <;>
      norm_num [answerChoiceForceInNewtons,
        choiceDDisplayToleranceInNewtons] at hLogFour ⊢ <;>
      nlinarith

end PhyXMiniProblems.ProblemPhyXMini0839
