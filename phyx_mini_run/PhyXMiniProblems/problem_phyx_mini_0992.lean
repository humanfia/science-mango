import Mathlib
import Physlib.Electromagnetism.Basic
import Physlib.Units.WithDim.Basic

/- USER: The assigned Lean file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0992

open Dimension

/-!
# Coulomb-force magnitude between two point charges

The primary image shows a red positive sphere labelled `q₁` on the left and a
blue negative sphere labelled `q₂` on the right.  A horizontal double-headed
arrow labelled `r` joins the two sphere centers.  The accompanying text gives
`q₁ = +25 nC`, `q₂ = -75 nC`, and `r = 3.0 cm`, and asks for the magnitude of
the force exerted by `q₁` on `q₂`.

Charges, separation, and force magnitude below are unit-independent Physlib
quantities.  Real numbers occur only as explicitly named unit readouts and as
the scalar coherent-SI value of Physlib's Coulomb constant.

Assumption/target split:

* governing law: the point-charge Coulomb magnitude law
  `F = k |q₁ q₂| / r²`;
* previous-part results: none;
* figure/data readouts: the two labelled and signed colored spheres, their
  left/right order, the double-headed arrow labelled `r`, the two signed
  nanocoulomb values, the `3.0 cm` separation, and the rounded school value of
  Coulomb's constant;
* current target conclusions: the independently stored force magnitude rounds
  to `0.0187 N` at four decimal places, and answer B is its uniquely closest
  displayed choice.

No target force value or answer choice occurs in the setup or in a premise
structure.
-/

/-! ## Dimensionful physical quantities and unit readouts -/

/-- The physical dimension `M L T⁻²` of force. -/
def forceDimension : Dimension :=
  M𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹

/-- A signed, unit-independent physical electric charge. -/
abbrev SignedChargeQuantity : Type :=
  Dimensionful (WithDim C𝓭 ℝ)

/-- A nonnegative, unit-independent physical separation. -/
abbrev LengthQuantity : Type :=
  Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative, unit-independent physical force magnitude. -/
abbrev ForceMagnitudeQuantity : Type :=
  Dimensionful (WithDim forceDimension NNReal)

/-- Coherent-SI readout of a signed charge, in coulombs. -/
def chargeInCoulombs (charge : SignedChargeQuantity) : ℝ :=
  (charge UnitChoices.SI).val

/-- Nanocoulomb readout used by the numerical problem statement. -/
def chargeInNanocoulombs (charge : SignedChargeQuantity) : ℝ :=
  (10 : ℝ) ^ 9 * chargeInCoulombs charge

/-- Coherent-SI readout of a separation, in metres. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  ((length UnitChoices.SI).val : ℝ)

/-- Centimetre readout used by the numerical problem statement. -/
def lengthInCentimeters (length : LengthQuantity) : ℝ :=
  100 * lengthInMeters length

/-- Coherent-SI readout of a force magnitude, in newtons. -/
def forceMagnitudeInNewtons (force : ForceMagnitudeQuantity) : ℝ :=
  ((force UnitChoices.SI).val : ℝ)

/-! ## Primary-image vocabulary and independent physical setup -/

/-- The two charges named in image `992.png` and in the problem text. -/
inductive ChargeLabel where
  | q1
  | q2
  deriving DecidableEq, Fintype, Repr

/-- Horizontal location of a charge marker in the supplied image. -/
inductive HorizontalSide where
  | left
  | right
  deriving DecidableEq, Repr

/-- Fill color of a charge sphere in the primary image. -/
inductive ChargeSphereColor where
  | red
  | blue
  deriving DecidableEq, Repr

/-- Sign glyph drawn inside a charge sphere. -/
inductive ChargeSignGlyph where
  | plus
  | minus
  deriving DecidableEq, Repr

/-- Idealization of each charged body used in the governing law. -/
inductive ChargedBodyModel where
  | pointCharge
  | extendedBody
  deriving DecidableEq, Repr

/-- Expected typographic label beside each charge sphere. -/
def expectedChargeName : ChargeLabel → String
  | .q1 => "q₁"
  | .q2 => "q₂"

/-- Expected left/right placement of the two charge spheres. -/
def expectedHorizontalSide : ChargeLabel → HorizontalSide
  | .q1 => .left
  | .q2 => .right

/-- Expected sphere color at each labelled charge. -/
def expectedSphereColor : ChargeLabel → ChargeSphereColor
  | .q1 => .red
  | .q2 => .blue

/-- Expected sign glyph at each labelled charge. -/
def expectedChargeSign : ChargeLabel → ChargeSignGlyph
  | .q1 => .plus
  | .q2 => .minus

/-!
Literal presentation data transcribed from image `992.png`.  It contains no
force value and no answer-choice label.
-/
structure TwoPointChargeFigure where
  sphereShown : ChargeLabel → Bool
  printedChargeName : ChargeLabel → String
  horizontalSide : ChargeLabel → HorizontalSide
  sphereColor : ChargeLabel → ChargeSphereColor
  chargeSign : ChargeLabel → ChargeSignGlyph
  doubleHeadedSeparationArrowShown : Bool
  separationArrowTouchesSphere : ChargeLabel → Bool
  printedSeparationName : String

/-!
Independent physical quantities in the two-charge setup.  In particular, the
force exerted by `q₁` on `q₂` is stored independently rather than defined from
Coulomb's formula or from the recorded answer.
-/
structure TwoPointChargeForceSetup where
  figure : TwoPointChargeFigure
  bodyModel : ChargeLabel → ChargedBodyModel
  charge : ChargeLabel → SignedChargeQuantity
  centerSeparation : LengthQuantity
  forceOnQ2FromQ1Magnitude : ForceMagnitudeQuantity
  electromagneticSystem : Electromagnetism.EMSystem

/-! ## Figure evidence, stated data, and governing electrostatics -/

/-- Exact qualitative evidence read from the supplied primary image. -/
structure MatchesSuppliedTwoPointChargeFigure
    (setup : TwoPointChargeForceSetup) : Prop where
  bothSpheresShown : ∀ label, setup.figure.sphereShown label = true
  printedChargeNames : ∀ label,
    setup.figure.printedChargeName label = expectedChargeName label
  leftRightPlacement : ∀ label,
    setup.figure.horizontalSide label = expectedHorizontalSide label
  sphereColors : ∀ label,
    setup.figure.sphereColor label = expectedSphereColor label
  signGlyphs : ∀ label,
    setup.figure.chargeSign label = expectedChargeSign label
  separationArrowShown :
    setup.figure.doubleHeadedSeparationArrowShown = true
  separationArrowJoinsSpheres : ∀ label,
    setup.figure.separationArrowTouchesSphere label = true
  separationLabel : setup.figure.printedSeparationName = "r"

/-!
The numerical values and point-charge idealization stated in the prose.  These
are calibrated readouts of dimensionful quantities, not scalar replacements
for charge or length.
-/
structure MatchesStatedPointChargeData
    (setup : TwoPointChargeForceSetup) : Prop where
  bothBodiesArePointCharges : ∀ label,
    setup.bodyModel label = .pointCharge
  q1ChargeNanocoulombs :
    chargeInNanocoulombs (setup.charge .q1) = 25
  q2ChargeNanocoulombs :
    chargeInNanocoulombs (setup.charge .q2) = -75
  separationCentimeters :
    lengthInCentimeters setup.centerSeparation = 3

/-!
The rounded textbook calibration `8.99 × 10⁹ N m²/C²`.  Physlib represents
`Electromagnetism.EMSystem.coulombConstant` as the coherent-SI scalar
`1 / (4 π ε₀)`; this premise supplies the precision used by the answer list.
-/
structure UsesRoundedCoulombConstant
    (setup : TwoPointChargeForceSetup) : Prop where
  coulombConstantCalibration :
    setup.electromagneticSystem.coulombConstant =
      (8.99 : ℝ) * 10 ^ (9 : ℕ)

/-- Positivity and separation conditions selecting the physical branch. -/
structure HasPhysicalPointChargeParameters
    (setup : TwoPointChargeForceSetup) : Prop where
  chargesAreSeparated : 0 < lengthInMeters setup.centerSeparation
  coulombConstantPositive :
    0 < setup.electromagneticSystem.coulombConstant

/-!
Coulomb's inverse-square law for the magnitude of the force exerted by `q₁`
on `q₂`.  Absolute value retains the signed charge data while producing a
nonnegative magnitude.  This general law contains no numerical target value.
-/
structure SatisfiesPointChargeCoulombMagnitudeLaw
    (setup : TwoPointChargeForceSetup) : Prop where
  forceMagnitudeRelation :
    lengthInMeters setup.centerSeparation ≠ 0 →
      forceMagnitudeInNewtons setup.forceOnQ2FromQ1Magnitude =
        setup.electromagneticSystem.coulombConstant *
          |chargeInCoulombs (setup.charge .q1) *
            chargeInCoulombs (setup.charge .q2)| /
          lengthInMeters setup.centerSeparation ^ 2

/-! ## Derived SI relation and multiple-choice target -/

/-- The four force magnitudes printed in the source's answer list. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Literal newton value printed beside an answer choice. -/
def AnswerChoice.forceInNewtons : AnswerChoice → ℝ
  | .A => 63 / 100
  | .B => 187 / 10000
  | .C => 19 / 1000
  | .D => 28 / 1000

/-- The answer label recorded in the supplied dataset metadata. -/
def recordedDatasetAnswer : AnswerChoice := .B

/-!
The strict half-unit criterion for displaying an actual newton value to four
places after the decimal point.  The strict inequality excludes tie cases.
-/
def RoundsToFourDecimalPlaces (actual displayed : ℝ) : Prop :=
  |actual - displayed| < 1 / (2 * (10 : ℝ) ^ 4)

/-- A displayed answer is uniquely closest to the actual force magnitude. -/
def IsStrictlyClosestAnswerChoice
    (actual : ℝ) (choice : AnswerChoice) : Prop :=
  ∀ alternative, alternative ≠ choice →
    |actual - choice.forceInNewtons| <
      |actual - alternative.forceInNewtons|

/-!
Specializing the governing magnitude law gives the exact coherent-SI Coulomb
expression before any decimal rounding.
-/
lemma forceOnQ2FromQ1_eq_coulombExpression
    (setup : TwoPointChargeForceSetup)
    (_physical : HasPhysicalPointChargeParameters setup)
    (_law : SatisfiesPointChargeCoulombMagnitudeLaw setup) :
    forceMagnitudeInNewtons setup.forceOnQ2FromQ1Magnitude =
      setup.electromagneticSystem.coulombConstant *
        |chargeInCoulombs (setup.charge .q1) *
          chargeInCoulombs (setup.charge .q2)| /
        lengthInMeters setup.centerSeparation ^ 2 := by
  exact _law.forceMagnitudeRelation (ne_of_gt _physical.chargesAreSeparated)

/-!
The stated nanocoulomb and centimetre values have these coherent-SI readouts.
This helper records unit conversion only; it does not mention the force.
-/
lemma statedDataInCoherentSI
    (setup : TwoPointChargeForceSetup)
    (_data : MatchesStatedPointChargeData setup) :
    chargeInCoulombs (setup.charge .q1) = 25 * (10 : ℝ) ^ (-9 : ℤ) ∧
      chargeInCoulombs (setup.charge .q2) = -75 * (10 : ℝ) ^ (-9 : ℤ) ∧
      lengthInMeters setup.centerSeparation = 3 * (10 : ℝ) ^ (-2 : ℤ) := by
  have hq1 := _data.q1ChargeNanocoulombs
  have hq2 := _data.q2ChargeNanocoulombs
  have hr := _data.separationCentimeters
  norm_num [chargeInNanocoulombs] at hq1 hq2
  norm_num [lengthInCentimeters] at hr
  norm_num at ⊢
  constructor
  · linarith
  constructor
  · linarith
  · linarith

/-!
For `q₁ = +25 nC`, `q₂ = -75 nC`, `r = 3.0 cm`, and
`k = 8.99 × 10⁹ N m²/C²`, Coulomb's law gives approximately
`0.018729... N`.  It therefore displays as `0.0187 N` at four decimal places
and is uniquely closest to answer B.

This is the Lean declaration corresponding to
`thm:physics:phyx_mini_0992:target`.
-/
theorem problem_phyx_mini_0992
    (setup : TwoPointChargeForceSetup)
    (_figure : MatchesSuppliedTwoPointChargeFigure setup)
    (_data : MatchesStatedPointChargeData setup)
    (_constant : UsesRoundedCoulombConstant setup)
    (_physical : HasPhysicalPointChargeParameters setup)
    (_law : SatisfiesPointChargeCoulombMagnitudeLaw setup) :
    RoundsToFourDecimalPlaces
        (forceMagnitudeInNewtons setup.forceOnQ2FromQ1Magnitude)
        (187 / 10000) ∧
      IsStrictlyClosestAnswerChoice
        (forceMagnitudeInNewtons setup.forceOnQ2FromQ1Magnitude)
        recordedDatasetAnswer := by
  have hforce :=
    forceOnQ2FromQ1_eq_coulombExpression setup _physical _law
  obtain ⟨hq1, hq2, hr⟩ := statedDataInCoherentSI setup _data
  rw [_constant.coulombConstantCalibration, hq1, hq2, hr] at hforce
  norm_num [abs_of_nonpos] at hforce
  rw [hforce]
  constructor
  · norm_num [RoundsToFourDecimalPlaces, abs_of_nonneg, abs_of_nonpos]
  · intro alternative hne
    cases alternative
    · norm_num [recordedDatasetAnswer, AnswerChoice.forceInNewtons,
        abs_of_nonneg, abs_of_nonpos]
    · exact (hne rfl).elim
    · norm_num [recordedDatasetAnswer, AnswerChoice.forceInNewtons,
        abs_of_nonneg, abs_of_nonpos]
    · norm_num [recordedDatasetAnswer, AnswerChoice.forceInNewtons,
        abs_of_nonneg, abs_of_nonpos]

end PhyXMiniProblems.ProblemPhyXMini0992
