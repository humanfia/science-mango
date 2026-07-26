import Mathlib
import Physlib.Electromagnetism.Basic
import Physlib.Units.WithDim.Basic

/- USER: The assigned Lean file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0900

open Dimension

/-!
# Unknown charge in a collinear three-charge equilibrium

The primary image places the charge `q₁` on the left, a positive `5.0 nC`
charge in the middle, and the charge `q₂` on the right.  The two adjacent
separations are both labelled `10 cm`.  The problem states that `q₂` is in
static equilibrium and asks for `q₁`.

Charge, axial position, separation, and axial force are represented by
Physlib's unit-independent `Dimensionful` quantities.  Real numbers below are
only explicit readouts in coulombs, nanocoulombs, metres, centimetres, or
newtons.

Assumption/target split:

* governing laws: the signed one-dimensional point-charge form of Coulomb's
  force law, superposition of the forces on `q₂`, and the zero-net-force
  criterion for static equilibrium;
* previous-part results: none;
* figure/data readouts: the left-to-right order `q₁`, `5.0 nC`, `q₂`, the plus
  glyph on the middle charge, and the two `10 cm` gaps;
* current target conclusion: the nanocoulomb readout of `q₁` is `-20`, answer
  choice C.

No premise or setup field assigns a numerical value to `q₁`.
-/

/-! ## Dimensionful physical quantities and named-unit readouts -/

/-- The physical dimension `M L T⁻²` of a force component. -/
def forceDimension : Dimension :=
  M𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹

/-- A signed, unit-independent physical electric charge. -/
abbrev SignedChargeQuantity : Type :=
  Dimensionful (WithDim C𝓭 ℝ)

/-- A signed, unit-independent position coordinate on the horizontal axis. -/
abbrev AxialPositionQuantity : Type :=
  Dimensionful (WithDim L𝓭 ℝ)

/-- A nonnegative, unit-independent physical separation. -/
abbrev LengthQuantity : Type :=
  Dimensionful (WithDim L𝓭 NNReal)

/-- A signed, unit-independent horizontal force component. -/
abbrev AxialForceComponentQuantity : Type :=
  Dimensionful (WithDim forceDimension ℝ)

/-- Read a physical charge in a selected Physlib charge unit. -/
def chargeReadout
    (unit : ChargeUnit) (charge : SignedChargeQuantity) : ℝ :=
  (charge {UnitChoices.SI with charge := unit}).val

/-- The charge unit `10⁻⁹ C` used by the middle label and answer choices. -/
def nanocoulombUnit : ChargeUnit :=
  ChargeUnit.scale ((1 / 10 : ℝ) ^ 9) ChargeUnit.coulombs

/-- Coherent-SI coulomb readout of a signed charge. -/
def chargeInCoulombs (charge : SignedChargeQuantity) : ℝ :=
  chargeReadout ChargeUnit.coulombs charge

/-- Nanocoulomb readout used by the printed charge label. -/
def chargeInNanocoulombs (charge : SignedChargeQuantity) : ℝ :=
  chargeReadout nanocoulombUnit charge

/-- Read a nonnegative physical separation in a selected length unit. -/
def lengthReadout (unit : LengthUnit) (length : LengthQuantity) : ℝ :=
  ((length {UnitChoices.SI with length := unit}).val : ℝ)

/-- Coherent-SI metre readout of a separation. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.meters length

/-- Centimetre readout used by the two dimension arrows. -/
def lengthInCentimeters (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.centimeters length

/-- Coherent-SI metre readout of a signed axial position. -/
def positionInMeters (position : AxialPositionQuantity) : ℝ :=
  (position UnitChoices.SI).val

/-- Coherent-SI newton readout of a signed axial force component. -/
def forceComponentInNewtons
    (force : AxialForceComponentQuantity) : ℝ :=
  (force UnitChoices.SI).val

/-!
The Physlib named units make these scale conversions consequences rather than
extra physical hypotheses.  They are recorded as helper lemmas for the later
algebraic proof.
-/
lemma chargeInNanocoulombs_eq_scaled_chargeInCoulombs
    (charge : SignedChargeQuantity) :
    chargeInNanocoulombs charge =
      (10 : ℝ) ^ 9 * chargeInCoulombs charge := by
  unfold chargeInNanocoulombs chargeInCoulombs chargeReadout
  rw [charge.2 UnitChoices.SI]
  change
    (↑(UnitChoices.SI.dimScale
        {UnitChoices.SI with charge := nanocoulombUnit} C𝓭) : ℝ) *
        (charge UnitChoices.SI).val =
      (10 : ℝ) ^ 9 * (charge UnitChoices.SI).val
  congr 1
  rw [UnitChoices.dimScale_apply]
  simp only [C𝓭, LengthUnit.div_self, TimeUnit.div_self, MassUnit.div_self,
    TemperatureUnit.div_self, Rat.cast_zero, NNReal.one_rpow, one_mul,
    Rat.cast_one, NNReal.rpow_one]
  norm_num [nanocoulombUnit]
  rfl

lemma lengthInCentimeters_eq_scaled_lengthInMeters
    (length : LengthQuantity) :
    lengthInCentimeters length = 100 * lengthInMeters length := by
  unfold lengthInCentimeters lengthInMeters lengthReadout
  rw [length.2 UnitChoices.SI]
  change
    (↑(UnitChoices.SI.dimScale
        {UnitChoices.SI with length := LengthUnit.centimeters} L𝓭) : ℝ) *
        ((length UnitChoices.SI).val : ℝ) =
      100 * ((length UnitChoices.SI).val : ℝ)
  congr 1
  rw [UnitChoices.dimScale_apply]
  simp only [L𝓭, Rat.cast_one, NNReal.rpow_one, TimeUnit.div_self,
    MassUnit.div_self, ChargeUnit.div_self, TemperatureUnit.div_self,
    Rat.cast_zero, NNReal.one_rpow, mul_one]
  norm_num [LengthUnit.centimeters]
  rfl

/-! ## Primary-image labels and independent physical setup -/

/-- The three circular charges, named by their left-to-right figure roles. -/
inductive ChargeSite where
  | q1
  | middleFive
  | q2
  deriving DecidableEq, Fintype, Repr

/-- The two labelled adjacent gaps in the image. -/
inductive AdjacentGap where
  | q1ToMiddle
  | middleToQ2
  deriving DecidableEq, Fintype, Repr

/-- Fill colours visibly distinguishing the three charge circles. -/
inductive FigureChargeColor where
  | lightTeal
  | red
  | lightRed
  deriving DecidableEq, Repr

/-- The only sign glyph visible inside a charge circle is a plus. -/
inductive FigureSignGlyph where
  | plus
  deriving DecidableEq, Repr

/-- Literal charge text expected above each of the three circles. -/
def expectedChargeText : ChargeSite → String
  | .q1 => "q₁"
  | .middleFive => "5.0 nC"
  | .q2 => "q₂"

/-- Literal circle colour expected for each charge site. -/
def expectedChargeColor : ChargeSite → FigureChargeColor
  | .q1 => .lightTeal
  | .middleFive => .red
  | .q2 => .lightRed

/-- Sign glyph expected inside each circle. -/
def expectedSignGlyph : ChargeSite → Option FigureSignGlyph
  | .q1 => none
  | .middleFive => some .plus
  | .q2 => none

/-- Optional numerical nanocoulomb label attached to each charge site. -/
def expectedPrintedChargeNanocoulombs : ChargeSite → Option ℝ
  | .q1 => none
  | .middleFive => some 5
  | .q2 => none

/-- Literal presentation data transcribed from primary image `900.png`. -/
structure CollinearThreeChargeFigure where
  circleShown : ChargeSite → Bool
  printedChargeText : ChargeSite → String
  circleColor : ChargeSite → FigureChargeColor
  signGlyph : ChargeSite → Option FigureSignGlyph
  printedChargeNanocoulombs : ChargeSite → Option ℝ
  horizontalOrder : List ChargeSite
  horizontalBaselineShown : Bool
  doubleHeadedDistanceArrowShown : AdjacentGap → Bool
  printedDistanceCentimeters : AdjacentGap → ℝ

/-!
Independent physical quantities for the three point charges.  In particular,
`charge .q1` is not defined from an answer choice or from the requested value.
-/
structure CollinearThreeChargeEquilibriumSetup where
  figure : CollinearThreeChargeFigure
  electromagneticSystem : Electromagnetism.EMSystem
  charge : ChargeSite → SignedChargeQuantity
  position : ChargeSite → AxialPositionQuantity
  adjacentSeparation : AdjacentGap → LengthQuantity
  sourceIsPointCharge : ChargeSite → Bool
  forceOnQ2From : ChargeSite → AxialForceComponentQuantity
  netForceOnQ2 : AxialForceComponentQuantity
  q2InStaticEquilibrium : Bool

/-- Metre displacement from a source charge to the target charge `q₂`. -/
def displacementFromSourceToQ2InMeters
    (setup : CollinearThreeChargeEquilibriumSetup)
    (source : ChargeSite) : ℝ :=
  positionInMeters (setup.position .q2) -
    positionInMeters (setup.position source)

/-! ## Scenario, primary-image evidence, and physical nondegeneracy -/

/-- The problem treats all three labelled circles as point charges and `q₂`
as the charge in static equilibrium. -/
structure MatchesThreePointChargeEquilibriumScenario
    (setup : CollinearThreeChargeEquilibriumSetup) : Prop where
  allSourcesArePointCharges :
    ∀ site, setup.sourceIsPointCharge site = true
  q2EquilibriumIsGiven : setup.q2InStaticEquilibrium = true

/-!
All literal labels and geometric relations read from the primary raster.  The
coordinate origin is chosen at `q₁`; this convention does not constrain its
charge.  The only numerical charge premise is the middle `+5.0 nC` readout.
-/
structure MatchesSuppliedCollinearChargeFigure
    (setup : CollinearThreeChargeEquilibriumSetup) : Prop where
  allCirclesShown : ∀ site, setup.figure.circleShown site = true
  chargeTexts : ∀ site,
    setup.figure.printedChargeText site = expectedChargeText site
  chargeColors : ∀ site,
    setup.figure.circleColor site = expectedChargeColor site
  signGlyphs : ∀ site,
    setup.figure.signGlyph site = expectedSignGlyph site
  numericalChargeLabels : ∀ site,
    setup.figure.printedChargeNanocoulombs site =
      expectedPrintedChargeNanocoulombs site
  middlePhysicalChargeMatchesLabel :
    chargeInNanocoulombs (setup.charge .middleFive) = 5
  leftToRightOrder :
    setup.figure.horizontalOrder = [.q1, .middleFive, .q2]
  baselineIsShown : setup.figure.horizontalBaselineShown = true
  bothDistanceArrowsAreShown : ∀ gap,
    setup.figure.doubleHeadedDistanceArrowShown gap = true
  bothPrintedDistancesAreTenCentimeters : ∀ gap,
    setup.figure.printedDistanceCentimeters gap = 10
  physicalGapsMatchPrintedDistances : ∀ gap,
    lengthInCentimeters (setup.adjacentSeparation gap) =
      setup.figure.printedDistanceCentimeters gap
  q1ChosenAsCoordinateOrigin :
    positionInMeters (setup.position .q1) = 0
  middleCoordinateFollowsLeftGap :
    positionInMeters (setup.position .middleFive) =
      positionInMeters (setup.position .q1) +
        lengthInMeters (setup.adjacentSeparation .q1ToMiddle)
  q2CoordinateFollowsRightGap :
    positionInMeters (setup.position .q2) =
      positionInMeters (setup.position .middleFive) +
        lengthInMeters (setup.adjacentSeparation .middleToQ2)

/-- Nondegeneracy conditions implicit in a three-charge equilibrium problem. -/
structure HasPhysicalThreeChargeParameters
    (setup : CollinearThreeChargeEquilibriumSetup) : Prop where
  bothAdjacentGapsPositive : ∀ gap,
    0 < lengthInMeters (setup.adjacentSeparation gap)
  q2ChargeNonzero : chargeInCoulombs (setup.charge .q2) ≠ 0
  coulombConstantPositive :
    0 < setup.electromagneticSystem.coulombConstant

/-! ## Governing electrostatic and equilibrium laws -/

/-!
For either other source, the signed force on `q₂` is

`k q₂ q_source (x₂ - x_source) / |x₂ - x_source|³`.

This is the one-dimensional vector form of Coulomb's law, stated only away
from self-interaction.  It contains no numerical conclusion for `q₁`.
-/
structure SatisfiesAxialPointChargeCoulombForceLaw
    (setup : CollinearThreeChargeEquilibriumSetup) : Prop where
  forceFromEachOtherSource : ∀ source,
    source ≠ .q2 →
      displacementFromSourceToQ2InMeters setup source ≠ 0 →
        forceComponentInNewtons (setup.forceOnQ2From source) =
          setup.electromagneticSystem.coulombConstant *
            chargeInCoulombs (setup.charge .q2) *
            chargeInCoulombs (setup.charge source) *
            displacementFromSourceToQ2InMeters setup source /
            |displacementFromSourceToQ2InMeters setup source| ^ 3

/-- The total horizontal force on `q₂` is the sum of the two other charges'
electrostatic forces. -/
structure SatisfiesForceSuperpositionOnQ2
    (setup : CollinearThreeChargeEquilibriumSetup) : Prop where
  netForceIsSourceSum :
    forceComponentInNewtons setup.netForceOnQ2 =
      forceComponentInNewtons (setup.forceOnQ2From .q1) +
        forceComponentInNewtons (setup.forceOnQ2From .middleFive)

/-- Static equilibrium entails a vanishing net horizontal force. -/
structure SatisfiesStaticEquilibriumForceBalance
    (setup : CollinearThreeChargeEquilibriumSetup) : Prop where
  equilibriumImpliesZeroNetForce :
    setup.q2InStaticEquilibrium = true →
      forceComponentInNewtons setup.netForceOnQ2 = 0

/-! ## Derived force balance and multiple-choice target -/

/-!
The scenario and the two general force-combination laws first give a zero sum
of the left-source and middle-source force components.  This is a derived
relation, not a premise about `q₁`.
-/
lemma sourceForcesOnQ2_sum_to_zero
    (setup : CollinearThreeChargeEquilibriumSetup)
    (_scenario : MatchesThreePointChargeEquilibriumScenario setup)
    (_superposition : SatisfiesForceSuperpositionOnQ2 setup)
    (_equilibrium : SatisfiesStaticEquilibriumForceBalance setup) :
    forceComponentInNewtons (setup.forceOnQ2From .q1) +
      forceComponentInNewtons (setup.forceOnQ2From .middleFive) = 0 := by
  rw [← _superposition.netForceIsSourceSum]
  exact _equilibrium.equilibriumImpliesZeroNetForce
    _scenario.q2EquilibriumIsGiven

/-- Labels attached to the four displayed charge choices. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Nanocoulomb value printed next to each answer label. -/
def AnswerChoice.chargeInNanocoulombs : AnswerChoice → ℝ
  | .A => -12
  | .B => 20
  | .C => -20
  | .D => 5

/-- The answer label recorded in the supplied dataset metadata. -/
def recordedDatasetAnswer : AnswerChoice := .C

/-!
**Blueprint target** `thm:physics:phyx_mini_0900:target`.

The equal adjacent gaps put `q₁` twice as far from `q₂` as the positive middle
charge.  Coulomb's inverse-square law and zero net force therefore require
`q₁ = -4(5 nC) = -20 nC`, the value displayed by answer C.
-/
theorem problem_phyx_mini_0900
    (setup : CollinearThreeChargeEquilibriumSetup)
    (_scenario : MatchesThreePointChargeEquilibriumScenario setup)
    (_figure : MatchesSuppliedCollinearChargeFigure setup)
    (_physical : HasPhysicalThreeChargeParameters setup)
    (_coulomb : SatisfiesAxialPointChargeCoulombForceLaw setup)
    (_superposition : SatisfiesForceSuperpositionOnQ2 setup)
    (_equilibrium : SatisfiesStaticEquilibriumForceBalance setup) :
    chargeInNanocoulombs (setup.charge .q1) = -20 := by
  have gapInMeters (gap : AdjacentGap) :
      lengthInMeters (setup.adjacentSeparation gap) = (1 / 10 : ℝ) := by
    have hreadout := _figure.physicalGapsMatchPrintedDistances gap
    rw [_figure.bothPrintedDistancesAreTenCentimeters gap] at hreadout
    have hscale :=
      lengthInCentimeters_eq_scaled_lengthInMeters
        (setup.adjacentSeparation gap)
    linarith
  have hq1Position := _figure.q1ChosenAsCoordinateOrigin
  have hmiddlePosition := _figure.middleCoordinateFollowsLeftGap
  have hq2Position := _figure.q2CoordinateFollowsRightGap
  rw [gapInMeters .q1ToMiddle] at hmiddlePosition
  rw [gapInMeters .middleToQ2] at hq2Position
  have hq1Displacement :
      displacementFromSourceToQ2InMeters setup .q1 = (1 / 5 : ℝ) := by
    unfold displacementFromSourceToQ2InMeters
    linarith
  have hmiddleDisplacement :
      displacementFromSourceToQ2InMeters setup .middleFive =
        (1 / 10 : ℝ) := by
    unfold displacementFromSourceToQ2InMeters
    linarith
  have hforceFromQ1 :=
    _coulomb.forceFromEachOtherSource .q1 (by decide) (by
      rw [hq1Displacement]
      norm_num)
  have hforceFromMiddle :=
    _coulomb.forceFromEachOtherSource .middleFive (by decide) (by
      rw [hmiddleDisplacement]
      norm_num)
  rw [hq1Displacement] at hforceFromQ1
  rw [hmiddleDisplacement] at hforceFromMiddle
  norm_num [abs_of_nonneg] at hforceFromQ1 hforceFromMiddle
  have hforceBalance :=
    sourceForcesOnQ2_sum_to_zero setup _scenario _superposition _equilibrium
  rw [hforceFromQ1, hforceFromMiddle] at hforceBalance
  have hcommonFactor :
      setup.electromagneticSystem.coulombConstant *
          chargeInCoulombs (setup.charge .q2) ≠ 0 :=
    mul_ne_zero (ne_of_gt _physical.coulombConstantPositive)
      _physical.q2ChargeNonzero
  have hcoulombChargeRelation :
      chargeInCoulombs (setup.charge .q1) =
        -4 * chargeInCoulombs (setup.charge .middleFive) := by
    apply mul_left_cancel₀ hcommonFactor
    linear_combination hforceBalance / 25
  rw [chargeInNanocoulombs_eq_scaled_chargeInCoulombs,
    hcoulombChargeRelation]
  have hmiddleReadout :=
    chargeInNanocoulombs_eq_scaled_chargeInCoulombs
      (setup.charge .middleFive)
  rw [_figure.middlePhysicalChargeMatchesLabel] at hmiddleReadout
  linarith

end PhyXMiniProblems.ProblemPhyXMini0900
