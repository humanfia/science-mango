import Mathlib
import Physlib.Electromagnetism.Basic
import Physlib.Units.WithDim.Basic

/- USER: The assigned Lean file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0861

open Dimension

/-!
# Charge-magnitude ratio from a one-dimensional electric-field graph

Two point charges `q_a` and `q_b` lie on the `x`-axis at the distinct
coordinates labelled `a` and `b`.  The primary image plots the signed
`x`-component of their resultant electric field.  Its branch is positive
between the charges, negative outside them, and reflection-symmetric about
the midpoint of `a` and `b`.

Charges, source coordinates, and field components are unit-independent
Physlib quantities.  Real numbers below are explicitly coherent-SI readouts:
metres for coordinates, coulombs for charge, and newtons per coulomb for the
field component.  The setup also retains Physlib's spacetime-dependent
one-dimensional electric field.

Assumption/target split:

* governing laws: the one-dimensional point-charge form of Coulomb's law,
  linear superposition, and calibration of the scalar graph readout against
  Physlib's electric field;
* previous-part results: none;
* figure/data readouts: the `x`, `a`, and `b` labels, dashed source lines,
  source order `a < b`, positive interior branch, negative exterior branches,
  and midpoint-reflection symmetry;
* current target conclusions: the signed charge readouts sum to zero, hence
  `|q_a / q_b| = 1`, uniquely matching displayed answer D.

No target charge relation or numerical ratio is a setup field or premise.
-/

/-! ## Dimensionful quantities and coherent-SI readouts -/

/-- The dimension `M L T⁻² C⁻¹` of electric-field strength. -/
def electricFieldStrengthDimension : Dimension :=
  M𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹ * C𝓭⁻¹

/-- A signed, unit-independent coordinate on the physical `x`-axis. -/
abbrev AxisCoordinateQuantity : Type :=
  Dimensionful (WithDim L𝓭 ℝ)

/-- A signed, unit-independent electric charge. -/
abbrev SignedChargeQuantity : Type :=
  Dimensionful (WithDim C𝓭 ℝ)

/-- A signed, unit-independent `x`-component of electric field. -/
abbrev SignedElectricFieldComponentQuantity : Type :=
  Dimensionful (WithDim electricFieldStrengthDimension ℝ)

/-- Coherent-SI coordinate readout, in metres. -/
def axisCoordinateInMeters (coordinate : AxisCoordinateQuantity) : ℝ :=
  (coordinate UnitChoices.SI).val

/-- Coherent-SI signed-charge readout, in coulombs. -/
def chargeInCoulombs (charge : SignedChargeQuantity) : ℝ :=
  (charge UnitChoices.SI).val

/-- Coherent-SI signed field-component readout, in newtons per coulomb. -/
def fieldComponentInNewtonsPerCoulomb
    (component : SignedElectricFieldComponentQuantity) : ℝ :=
  (component UnitChoices.SI).val

/-! ## Named charges, physical setup, and figure content -/

/-- The two source labels printed below the dashed lines in the graph. -/
inductive ChargeLabel where
  | a
  | b
  deriving DecidableEq, Fintype, Repr

/-- A point charge together with its dimensionful `x`-axis coordinate. -/
structure AxisPointCharge where
  position : AxisCoordinateQuantity
  charge : SignedChargeQuantity

/-- The three regions separated by the two vertical source lines. -/
inductive FieldGraphRegion where
  | leftExterior
  | betweenSources
  | rightExterior
  deriving DecidableEq, Fintype, Repr

/-!
Literal presentation features of image `861.png`.  Quantitative
interpretation of the curve is stated separately below.
-/
structure TwoChargeElectricFieldFigure where
  xAxisShown : Bool
  xLabelShown : Bool
  dashedSourceLineShown : ChargeLabel → Bool
  printedLabelAtSourceLine : ChargeLabel → ChargeLabel
  fieldCurveShownIn : FieldGraphRegion → Bool
  fieldCurveAboveXAxisIn : FieldGraphRegion → Bool
  midpointReflectionSymmetryShown : Bool

/-!
Independent physical objects for the electrostatic configuration.  The
requested ratio is not stored here.  The scalar component is a dimensionful
observable indexed by an explicitly metre-valued coordinate, while
`electricField` retains Physlib's full field role.
-/
structure TwoPointChargeAxisSetup where
  source : ChargeLabel → AxisPointCharge
  electromagneticSystem : Electromagnetism.EMSystem
  electricField : Electromagnetism.ElectricField 1
  observationTime : Time
  axisPointAtMeterCoordinate : ℝ → Space 1
  fieldXAtMeterCoordinate : ℝ → SignedElectricFieldComponentQuantity
  figure : TwoChargeElectricFieldFigure

/-- Metre coordinate of a named point charge. -/
def sourcePositionInMeters
    (setup : TwoPointChargeAxisSetup) (source : ChargeLabel) : ℝ :=
  axisCoordinateInMeters (setup.source source).position

/-- Coulomb readout of a named point charge. -/
def sourceChargeInCoulombs
    (setup : TwoPointChargeAxisSetup) (source : ChargeLabel) : ℝ :=
  chargeInCoulombs (setup.source source).charge

/-- Signed graph ordinate `E_x`, in newtons per coulomb. -/
def fieldXInNewtonsPerCoulomb
    (setup : TwoPointChargeAxisSetup) (xInMeters : ℝ) : ℝ :=
  fieldComponentInNewtonsPerCoulomb
    (setup.fieldXAtMeterCoordinate xInMeters)

/-- Reflection of an `x`-coordinate about the midpoint of `a` and `b`. -/
def reflectAboutSourceMidpoint
    (setup : TwoPointChargeAxisSetup) (xInMeters : ℝ) : ℝ :=
  sourcePositionInMeters setup .a + sourcePositionInMeters setup .b -
    xInMeters

/-! ## Figure/data readouts and governing laws -/

/-!
The scalar ordinate used by the graph is the first component of Physlib's
one-dimensional electric field at the corresponding axis point.  Both sides
are coherent-SI readouts.
-/
structure FieldComponentRepresentsPhyslibElectricField
    (setup : TwoPointChargeAxisSetup) : Prop where
  axisPointCoordinate : ∀ xInMeters,
    (setup.axisPointAtMeterCoordinate xInMeters).val 0 = xInMeters
  componentAgreesWithField : ∀ xInMeters,
    fieldXInNewtonsPerCoulomb setup xInMeters =
      setup.electricField setup.observationTime
        (setup.axisPointAtMeterCoordinate xInMeters) 0

/-!
Literal and interpreted evidence from the primary image.  In particular,
`curveMirrorSymmetry` records a visible feature of the supplied graph; it
does not directly assert any relation between the two charges.
-/
structure MatchesSuppliedElectricFieldGraph
    (setup : TwoPointChargeAxisSetup) : Prop where
  xAxisIsShown : setup.figure.xAxisShown = true
  xAxisLabelIsShown : setup.figure.xLabelShown = true
  bothDashedSourceLinesAreShown : ∀ source,
    setup.figure.dashedSourceLineShown source = true
  sourceLabelsAreCorrect : ∀ source,
    setup.figure.printedLabelAtSourceLine source = source
  curveIsShownInEveryRegion : ∀ region,
    setup.figure.fieldCurveShownIn region = true
  interiorCurveIsAboveXAxis :
    setup.figure.fieldCurveAboveXAxisIn .betweenSources = true
  leftExteriorCurveIsBelowXAxis :
    setup.figure.fieldCurveAboveXAxisIn .leftExterior = false
  rightExteriorCurveIsBelowXAxis :
    setup.figure.fieldCurveAboveXAxisIn .rightExterior = false
  reflectionSymmetryIsShown :
    setup.figure.midpointReflectionSymmetryShown = true
  sourceAIsLeftOfSourceB :
    sourcePositionInMeters setup .a < sourcePositionInMeters setup .b
  fieldPositiveBetweenSources : ∀ xInMeters,
    sourcePositionInMeters setup .a < xInMeters →
    xInMeters < sourcePositionInMeters setup .b →
    0 < fieldXInNewtonsPerCoulomb setup xInMeters
  fieldNegativeLeftOfBothSources : ∀ xInMeters,
    xInMeters < sourcePositionInMeters setup .a →
    fieldXInNewtonsPerCoulomb setup xInMeters < 0
  fieldNegativeRightOfBothSources : ∀ xInMeters,
    sourcePositionInMeters setup .b < xInMeters →
    fieldXInNewtonsPerCoulomb setup xInMeters < 0
  curveMirrorSymmetry : ∀ xInMeters,
    xInMeters ≠ sourcePositionInMeters setup .a →
    xInMeters ≠ sourcePositionInMeters setup .b →
    fieldXInNewtonsPerCoulomb setup
        (reflectAboutSourceMidpoint setup xInMeters) =
      fieldXInNewtonsPerCoulomb setup xInMeters

/-- Nondegeneracy and positivity conditions for two genuine point charges. -/
structure HasPhysicalTwoPointChargeParameters
    (setup : TwoPointChargeAxisSetup) : Prop where
  eachChargeIsNonzero : ∀ source,
    sourceChargeInCoulombs setup source ≠ 0
  coulombConstantIsPositive :
    0 < setup.electromagneticSystem.coulombConstant

/-!
The one-dimensional point-charge law and linear superposition.  Away from
both source positions, each term is `k q r / |r|³`; their sum is the measured
resultant `x`-component.  This all-regular-points law contains no requested
charge ratio.
-/
structure SatisfiesTwoPointChargeCoulombLaw
    (setup : TwoPointChargeAxisSetup) : Prop where
  fieldAtRegularCoordinate : ∀ xInMeters,
    xInMeters ≠ sourcePositionInMeters setup .a →
    xInMeters ≠ sourcePositionInMeters setup .b →
    fieldXInNewtonsPerCoulomb setup xInMeters =
      setup.electromagneticSystem.coulombConstant *
        (sourceChargeInCoulombs setup .a *
            (xInMeters - sourcePositionInMeters setup .a) /
              |xInMeters - sourcePositionInMeters setup .a| ^ 3 +
          sourceChargeInCoulombs setup .b *
            (xInMeters - sourcePositionInMeters setup .b) /
              |xInMeters - sourcePositionInMeters setup .b| ^ 3)

/-! ## Derived charge relation and multiple-choice target -/

/-- The dimensionless magnitude ratio asked for in the problem. -/
def absoluteChargeRatio (setup : TwoPointChargeAxisSetup) : ℝ :=
  |sourceChargeInCoulombs setup .a /
    sourceChargeInCoulombs setup .b|

/-- The four answer labels supplied with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Exact real value printed by each displayed answer choice. -/
def AnswerChoice.displayedChargeMagnitudeRatio : AnswerChoice → ℝ
  | .A => 6 / 5
  | .B => 7 / 5
  | .C => 2
  | .D => 1

/-- The answer label recorded in the supplied dataset metadata. -/
def recordedDatasetAnswer : AnswerChoice := .D

/-- A displayed choice is the unique one whose value equals a given ratio. -/
def IsUniqueMatchingDisplayedRatio
    (actual : ℝ) (choice : AnswerChoice) : Prop :=
  choice.displayedChargeMagnitudeRatio = actual ∧
    ∀ other : AnswerChoice, other ≠ choice →
      other.displayedChargeMagnitudeRatio ≠ actual

/-!
Midpoint-reflection symmetry of the Coulomb field forces the signed source
charges to be opposites.  This is a derived lemma, not a premise.
-/
lemma sourceChargeReadouts_sum_eq_zero
    (setup : TwoPointChargeAxisSetup)
    (_figure : MatchesSuppliedElectricFieldGraph setup)
    (_physical : HasPhysicalTwoPointChargeParameters setup)
    (_coulomb : SatisfiesTwoPointChargeCoulombLaw setup) :
    sourceChargeInCoulombs setup .a +
        sourceChargeInCoulombs setup .b = 0 := by
  let aPos : ℝ := sourcePositionInMeters setup .a
  let bPos : ℝ := sourcePositionInMeters setup .b
  let qA : ℝ := sourceChargeInCoulombs setup .a
  let qB : ℝ := sourceChargeInCoulombs setup .b
  let k : ℝ := setup.electromagneticSystem.coulombConstant
  let xLeft : ℝ := 2 * aPos - bPos
  let xRight : ℝ := 2 * bPos - aPos
  have hab : aPos < bPos := _figure.sourceAIsLeftOfSourceB
  have hd : 0 < bPos - aPos := sub_pos.mpr hab
  have h2d : 0 < 2 * (bPos - aPos) := mul_pos (by norm_num) hd
  have hxLeftA : xLeft ≠ aPos := by
    dsimp [xLeft]
    linarith
  have hxLeftB : xLeft ≠ bPos := by
    dsimp [xLeft]
    linarith
  have hxRightA : xRight ≠ aPos := by
    dsimp [xRight]
    linarith
  have hxRightB : xRight ≠ bPos := by
    dsimp [xRight]
    linarith
  have hreflect :
      reflectAboutSourceMidpoint setup xLeft = xRight := by
    dsimp [reflectAboutSourceMidpoint, xLeft, xRight, aPos, bPos]
    ring
  have hsymmetry :=
    _figure.curveMirrorSymmetry xLeft hxLeftA hxLeftB
  rw [hreflect] at hsymmetry
  have hleft :=
    _coulomb.fieldAtRegularCoordinate xLeft hxLeftA hxLeftB
  have hright :=
    _coulomb.fieldAtRegularCoordinate xRight hxRightA hxRightB
  change fieldXInNewtonsPerCoulomb setup xLeft =
      k * (qA * (xLeft - aPos) / |xLeft - aPos| ^ 3 +
        qB * (xLeft - bPos) / |xLeft - bPos| ^ 3) at hleft
  change fieldXInNewtonsPerCoulomb setup xRight =
      k * (qA * (xRight - aPos) / |xRight - aPos| ^ 3 +
        qB * (xRight - bPos) / |xRight - bPos| ^ 3) at hright
  rw [hright, hleft] at hsymmetry
  have hxRightADistance :
      xRight - aPos = 2 * (bPos - aPos) := by
    dsimp [xRight]
    ring
  have hxRightBDistance :
      xRight - bPos = bPos - aPos := by
    dsimp [xRight]
    ring
  have hxLeftADistance :
      xLeft - aPos = -(bPos - aPos) := by
    dsimp [xLeft]
    ring
  have hxLeftBDistance :
      xLeft - bPos = -(2 * (bPos - aPos)) := by
    dsimp [xLeft]
    ring
  rw [hxRightADistance, hxRightBDistance,
    hxLeftADistance, hxLeftBDistance] at hsymmetry
  simp only [abs_neg, abs_of_pos hd, abs_of_pos h2d] at hsymmetry
  field_simp [ne_of_gt hd] at hsymmetry
  ring_nf at hsymmetry
  have hk : k ≠ 0 := ne_of_gt _physical.coulombConstantIsPositive
  have hfactor : k * (qA + qB) = 0 := by
    nlinarith [hsymmetry]
  exact (mul_eq_zero.mp hfactor).resolve_left hk

/-!
The symmetric field graph and Coulomb's law imply equal and opposite source
charges.  Their magnitude ratio is therefore `1`, uniquely selecting answer
D.

This is the Lean declaration corresponding to
`thm:physics:phyx_mini_0861:target`.
-/
theorem problem_phyx_mini_0861
    (setup : TwoPointChargeAxisSetup)
    (_fieldRepresentation :
      FieldComponentRepresentsPhyslibElectricField setup)
    (_figure : MatchesSuppliedElectricFieldGraph setup)
    (_physical : HasPhysicalTwoPointChargeParameters setup)
    (_coulomb : SatisfiesTwoPointChargeCoulombLaw setup) :
    absoluteChargeRatio setup = 1 ∧
      IsUniqueMatchingDisplayedRatio
        (absoluteChargeRatio setup) recordedDatasetAnswer := by
  have hsum :=
    sourceChargeReadouts_sum_eq_zero setup _figure _physical _coulomb
  have hchargeB :
      sourceChargeInCoulombs setup .b ≠ 0 :=
    _physical.eachChargeIsNonzero .b
  have hchargeA :
      sourceChargeInCoulombs setup .a =
        -sourceChargeInCoulombs setup .b := by
    linarith
  have hratio : absoluteChargeRatio setup = 1 := by
    unfold absoluteChargeRatio
    rw [hchargeA, neg_div, div_self hchargeB]
    norm_num
  constructor
  · exact hratio
  · unfold IsUniqueMatchingDisplayedRatio
    constructor
    · simp [recordedDatasetAnswer,
        AnswerChoice.displayedChargeMagnitudeRatio, hratio]
    · intro other hother
      rw [hratio]
      cases other with
      | A =>
          norm_num [AnswerChoice.displayedChargeMagnitudeRatio]
      | B =>
          norm_num [AnswerChoice.displayedChargeMagnitudeRatio]
      | C =>
          norm_num [AnswerChoice.displayedChargeMagnitudeRatio]
      | D =>
          exact (hother rfl).elim

end PhyXMiniProblems.ProblemPhyXMini0861
