import Mathlib
import Physlib.Electromagnetism.Basic
import Physlib.Units.WithDim.Basic

/- USER: The assigned Lean file did not exist when this autoformalization task began.
The primary image shows the `4.0 cm` arrow from the baseline to `q`, so the
separation between `q` and the `1.0 nC` charge is `2.0 cm`, not `4.0 cm`. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0899

open Dimension
open scoped BigOperators

/-!
# Charge required for electrostatic equilibrium in a four-charge diagram

The primary image contains four point charges.  The lower charges are at
`(-3, 0) cm` and `(3, 0) cm`, the `1.0 nC` test charge is at `(0, 2) cm`, and
the unknown charge `q` is at `(0, 4) cm`.  The two lower charges are each
`+2.0 nC`.  The net force on the test charge is stated to vanish.

Charge, Cartesian coordinates, and force components are represented by
Physlib's unit-independent `Dimensionful` quantities.  Real numbers occur
only as readouts in explicitly named units.

Assumption/target split:

* governing laws: the vector form of Coulomb's point-charge force law and
  linear superposition of the three forces acting on each charge;
* previous-part results: none;
* figure/data readouts: the four labels, the three visible plus signs, the
  `3.0 cm`, `3.0 cm`, `2.0 cm`, and `4.0 cm` arrows, the corresponding planar
  coordinates, the three known charge values, and zero net force on the
  `1.0 nC` test charge;
* current target: the unknown charge is exactly
  `32 / (13 * sqrt 13) nC`, and recorded choice C (`0.68 nC`) is the unique
  closest displayed decimal choice.

No setup field or premise gives the value or sign of the unknown charge.
-/

/-! ## Dimensionful physical quantities and unit readouts -/

/-- The physical dimension `M L T⁻²` of a force component. -/
def forceDimension : Dimension :=
  M𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹

/-- A signed, unit-independent electric charge. -/
abbrev SignedChargeQuantity : Type :=
  Dimensionful (WithDim C𝓭 ℝ)

/-- A signed, unit-independent Cartesian coordinate. -/
abbrev CartesianCoordinateQuantity : Type :=
  Dimensionful (WithDim L𝓭 ℝ)

/-- A signed, unit-independent Cartesian force component. -/
abbrev ForceComponentQuantity : Type :=
  Dimensionful (WithDim forceDimension ℝ)

/-- Read a signed physical charge in coherent-SI coulombs. -/
def chargeInCoulombs (charge : SignedChargeQuantity) : ℝ :=
  (charge UnitChoices.SI).val

/-- Read a signed physical charge in nanocoulombs. -/
def chargeInNanocoulombs (charge : SignedChargeQuantity) : ℝ :=
  (10 : ℝ) ^ 9 * chargeInCoulombs charge

/-- Read a signed Cartesian coordinate in coherent-SI metres. -/
def coordinateInMeters (coordinate : CartesianCoordinateQuantity) : ℝ :=
  (coordinate UnitChoices.SI).val

/-- Read a signed Cartesian coordinate in centimetres. -/
def coordinateInCentimeters
    (coordinate : CartesianCoordinateQuantity) : ℝ :=
  100 * coordinateInMeters coordinate

/-- Read a signed Cartesian force component in newtons. -/
def forceComponentInNewtons (component : ForceComponentQuantity) : ℝ :=
  (component UnitChoices.SI).val

/-- A planar physical force, retaining independent dimensionful components. -/
structure PlanarForce where
  x : ForceComponentQuantity
  y : ForceComponentQuantity

/-! ## Figure labels and independent physical setup -/

/-- The four charge sites visible in the supplied image. -/
inductive ChargeSite where
  | lowerLeft
  | test
  | lowerRight
  | top
  deriving DecidableEq, Fintype, Repr

/-- Text printed beside each of the four charge circles. -/
def expectedChargeLabel : ChargeSite → String
  | .lowerLeft => "2.0 nC"
  | .test => "1.0 nC"
  | .lowerRight => "2.0 nC"
  | .top => "q"

/-- The explicit sign glyph that may be drawn inside a charge circle. -/
inductive ChargeSignGlyph where
  | plus
  | minus
  deriving DecidableEq, Repr

/-- The two horizontal dimension arrows along the baseline. -/
inductive HorizontalSpan where
  | leftToCenter
  | centerToRight
  deriving DecidableEq, Fintype, Repr

/-- The two vertical dimension arrows in the primary image. -/
inductive VerticalSpan where
  | baselineToTest
  | baselineToTop
  deriving DecidableEq, Fintype, Repr

/-- Literal presentation data transcribed from image `899.png`. -/
structure FourChargeEquilibriumFigure where
  chargeCircleShown : ChargeSite → Bool
  printedChargeLabel : ChargeSite → String
  signGlyph : ChargeSite → Option ChargeSignGlyph
  horizontalArrowShown : HorizontalSpan → Bool
  horizontalLengthLabelCentimeters : HorizontalSpan → ℝ
  verticalArrowShown : VerticalSpan → Bool
  verticalLengthLabelCentimeters : VerticalSpan → ℝ
  testAndTopAppearOnPerpendicularBisector : Bool

/-!
Independent physical charges, positions, pairwise forces, and net forces.
The charge at `.top` is an unconstrained observable here, rather than being
defined from the requested answer.
-/
structure FourChargeEquilibriumSetup where
  figure : FourChargeEquilibriumFigure
  electromagneticSystem : Electromagnetism.EMSystem
  charge : ChargeSite → SignedChargeQuantity
  xCoordinate : ChargeSite → CartesianCoordinateQuantity
  yCoordinate : ChargeSite → CartesianCoordinateQuantity
  isPointCharge : ChargeSite → Bool
  pairwiseForceOn : ChargeSite → ChargeSite → PlanarForce
  netForceOn : ChargeSite → PlanarForce

/-- Horizontal displacement, in metres, from a source to a target charge. -/
def horizontalDisplacementInMeters
    (setup : FourChargeEquilibriumSetup)
    (target source : ChargeSite) : ℝ :=
  coordinateInMeters (setup.xCoordinate target) -
    coordinateInMeters (setup.xCoordinate source)

/-- Vertical displacement, in metres, from a source to a target charge. -/
def verticalDisplacementInMeters
    (setup : FourChargeEquilibriumSetup)
    (target source : ChargeSite) : ℝ :=
  coordinateInMeters (setup.yCoordinate target) -
    coordinateInMeters (setup.yCoordinate source)

/-- Euclidean separation, in metres, between two charge sites. -/
def separationInMeters
    (setup : FourChargeEquilibriumSetup)
    (target source : ChargeSite) : ℝ :=
  Real.sqrt
    (horizontalDisplacementInMeters setup target source ^ 2 +
      verticalDisplacementInMeters setup target source ^ 2)

/-! ## Primary-image evidence and physical parameters -/

/-!
The literal labels and arrows visible in the supplied image, together with
their calibration against the independent physical charges and coordinates.
The top circle has no sign glyph or numerical charge label, so this premise
places no restriction on the value or sign of `setup.charge .top`.
-/
structure MatchesSuppliedFourChargeFigure
    (setup : FourChargeEquilibriumSetup) : Prop where
  allFourChargeCirclesShown :
    ∀ site, setup.figure.chargeCircleShown site = true
  printedChargeLabels :
    ∀ site, setup.figure.printedChargeLabel site = expectedChargeLabel site
  lowerLeftPlusSign :
    setup.figure.signGlyph .lowerLeft = some .plus
  testPlusSign :
    setup.figure.signGlyph .test = some .plus
  lowerRightPlusSign :
    setup.figure.signGlyph .lowerRight = some .plus
  topHasNoPrintedSign :
    setup.figure.signGlyph .top = none
  bothHorizontalArrowsShown :
    ∀ span, setup.figure.horizontalArrowShown span = true
  leftHorizontalLabel :
    setup.figure.horizontalLengthLabelCentimeters .leftToCenter = 3
  rightHorizontalLabel :
    setup.figure.horizontalLengthLabelCentimeters .centerToRight = 3
  bothVerticalArrowsShown :
    ∀ span, setup.figure.verticalArrowShown span = true
  testHeightLabel :
    setup.figure.verticalLengthLabelCentimeters .baselineToTest = 2
  topHeightLabel :
    setup.figure.verticalLengthLabelCentimeters .baselineToTop = 4
  displayedPerpendicularBisectorAlignment :
    setup.figure.testAndTopAppearOnPerpendicularBisector = true
  lowerLeftChargeReadout :
    chargeInNanocoulombs (setup.charge .lowerLeft) = 2
  testChargeReadout :
    chargeInNanocoulombs (setup.charge .test) = 1
  lowerRightChargeReadout :
    chargeInNanocoulombs (setup.charge .lowerRight) = 2
  lowerLeftCoordinates :
    coordinateInCentimeters (setup.xCoordinate .lowerLeft) = -3 ∧
      coordinateInCentimeters (setup.yCoordinate .lowerLeft) = 0
  testCoordinates :
    coordinateInCentimeters (setup.xCoordinate .test) = 0 ∧
      coordinateInCentimeters (setup.yCoordinate .test) = 2
  lowerRightCoordinates :
    coordinateInCentimeters (setup.xCoordinate .lowerRight) = 3 ∧
      coordinateInCentimeters (setup.yCoordinate .lowerRight) = 0
  topCoordinates :
    coordinateInCentimeters (setup.xCoordinate .top) = 0 ∧
      coordinateInCentimeters (setup.yCoordinate .top) = 4

/-- Point-charge roles, noncollision, and positivity of Coulomb's constant. -/
structure HasPhysicalFourChargeParameters
    (setup : FourChargeEquilibriumSetup) : Prop where
  allSitesArePointCharges : ∀ site, setup.isPointCharge site = true
  pairwiseSeparationPositive : ∀ target source,
    target ≠ source → 0 < separationInMeters setup target source
  coulombConstantPositive :
    0 < setup.electromagneticSystem.coulombConstant

/-! ## Governing electrostatic laws and equilibrium datum -/

/-!
For distinct point charges, the force on `target` due to `source` is

`k q_target q_source (r_target - r_source) / |r_target - r_source|^3`.

The two fields below state its Cartesian components for every distinct pair.
They contain no numerical conclusion about the top charge.
-/
structure SatisfiesPlanarPointChargeCoulombLaw
    (setup : FourChargeEquilibriumSetup) : Prop where
  pairwiseForceX : ∀ target source,
    target ≠ source →
      forceComponentInNewtons (setup.pairwiseForceOn target source).x =
        setup.electromagneticSystem.coulombConstant *
          chargeInCoulombs (setup.charge target) *
          chargeInCoulombs (setup.charge source) *
          horizontalDisplacementInMeters setup target source /
          separationInMeters setup target source ^ 3
  pairwiseForceY : ∀ target source,
    target ≠ source →
      forceComponentInNewtons (setup.pairwiseForceOn target source).y =
        setup.electromagneticSystem.coulombConstant *
          chargeInCoulombs (setup.charge target) *
          chargeInCoulombs (setup.charge source) *
          verticalDisplacementInMeters setup target source /
          separationInMeters setup target source ^ 3

/-- The net force is the componentwise sum of all nonselfforce terms. -/
structure SatisfiesElectrostaticForceSuperposition
    (setup : FourChargeEquilibriumSetup) : Prop where
  netForceX : ∀ target,
    forceComponentInNewtons (setup.netForceOn target).x =
      ∑ source ∈ Finset.univ.erase target,
        forceComponentInNewtons (setup.pairwiseForceOn target source).x
  netForceY : ∀ target,
    forceComponentInNewtons (setup.netForceOn target).y =
      ∑ source ∈ Finset.univ.erase target,
        forceComponentInNewtons (setup.pairwiseForceOn target source).y

/-- The written scenario's datum that the force on the `1.0 nC` charge is zero. -/
structure HasZeroNetForceOnTestCharge
    (setup : FourChargeEquilibriumSetup) : Prop where
  zeroHorizontalComponent :
    forceComponentInNewtons (setup.netForceOn .test).x = 0
  zeroVerticalComponent :
    forceComponentInNewtons (setup.netForceOn .test).y = 0

/-! ## Derived geometry and multiple-choice target -/

/-- The two lower charges are each `sqrt 13 cm` from the test charge. -/
lemma test_to_lower_charge_separations
    (setup : FourChargeEquilibriumSetup)
    (_figure : MatchesSuppliedFourChargeFigure setup) :
    separationInMeters setup .test .lowerLeft = Real.sqrt 13 / 100 ∧
      separationInMeters setup .test .lowerRight = Real.sqrt 13 / 100 := by
  rcases _figure.testCoordinates with ⟨htx, hty⟩
  rcases _figure.lowerLeftCoordinates with ⟨hllx, hlly⟩
  rcases _figure.lowerRightCoordinates with ⟨hlrx, hlry⟩
  have htxm : coordinateInMeters (setup.xCoordinate .test) = 0 := by
    rw [coordinateInCentimeters] at htx
    linarith only [htx]
  have htym : coordinateInMeters (setup.yCoordinate .test) = 1 / 50 := by
    rw [coordinateInCentimeters] at hty
    linarith only [hty]
  have hllxm :
      coordinateInMeters (setup.xCoordinate .lowerLeft) = -3 / 100 := by
    rw [coordinateInCentimeters] at hllx
    linarith only [hllx]
  have hllym : coordinateInMeters (setup.yCoordinate .lowerLeft) = 0 := by
    rw [coordinateInCentimeters] at hlly
    linarith only [hlly]
  have hlrxm :
      coordinateInMeters (setup.xCoordinate .lowerRight) = 3 / 100 := by
    rw [coordinateInCentimeters] at hlrx
    linarith only [hlrx]
  have hlrym : coordinateInMeters (setup.yCoordinate .lowerRight) = 0 := by
    rw [coordinateInCentimeters] at hlry
    linarith only [hlry]
  have hsqrt :
      Real.sqrt (13 / 10000 : ℝ) = Real.sqrt 13 / 100 := by
    calc
      Real.sqrt (13 / 10000 : ℝ) =
          Real.sqrt 13 / Real.sqrt 10000 :=
        Real.sqrt_div (by norm_num) 10000
      _ = Real.sqrt 13 / 100 := by norm_num
  constructor
  · rw [separationInMeters, horizontalDisplacementInMeters,
      verticalDisplacementInMeters, htxm, hllxm, htym, hllym]
    norm_num [hsqrt]
  · rw [separationInMeters, horizontalDisplacementInMeters,
      verticalDisplacementInMeters, htxm, hlrxm, htym, hlrym]
    norm_num [hsqrt]

/-- The top charge is `2 cm` above the test charge in the primary image. -/
lemma test_to_top_charge_separation
    (setup : FourChargeEquilibriumSetup)
    (_figure : MatchesSuppliedFourChargeFigure setup) :
    separationInMeters setup .test .top = 1 / 50 := by
  rcases _figure.testCoordinates with ⟨htx, hty⟩
  rcases _figure.topCoordinates with ⟨htopx, htopy⟩
  have htxm : coordinateInMeters (setup.xCoordinate .test) = 0 := by
    rw [coordinateInCentimeters] at htx
    linarith only [htx]
  have htym : coordinateInMeters (setup.yCoordinate .test) = 1 / 50 := by
    rw [coordinateInCentimeters] at hty
    linarith only [hty]
  have htopxm : coordinateInMeters (setup.xCoordinate .top) = 0 := by
    rw [coordinateInCentimeters] at htopx
    linarith only [htopx]
  have htopym : coordinateInMeters (setup.yCoordinate .top) = 1 / 25 := by
    rw [coordinateInCentimeters] at htopy
    linarith only [htopy]
  rw [separationInMeters, horizontalDisplacementInMeters,
    verticalDisplacementInMeters, htxm, htym, htopxm, htopym]
  norm_num

/-- Labels attached to the four displayed charge choices. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Charge value, in nanocoulombs, printed beside a displayed choice. -/
def AnswerChoice.chargeInNanocoulombs : AnswerChoice → ℝ
  | .A => 69 / 100
  | .B => 48 / 100
  | .C => 68 / 100
  | .D => 65 / 100

/-- The answer label recorded in the supplied dataset metadata. -/
def recordedDatasetAnswer : AnswerChoice := .C

/-!
**Blueprint target** `thm:physics:phyx_mini_0899:target`.

Balancing the upward vertical components from the two lower charges against
the downward force from the top charge gives

`q = 32 / (13 * sqrt 13) nC ≈ 0.6827 nC`.

Consequently `0.68 nC`, recorded choice C, is the unique closest displayed
decimal value.  The exact physical result and the multiple-choice selection
are both conclusions, not assumptions.
-/
theorem problem_phyx_mini_0899
    (setup : FourChargeEquilibriumSetup)
    (_figure : MatchesSuppliedFourChargeFigure setup)
    (_physical : HasPhysicalFourChargeParameters setup)
    (_coulomb : SatisfiesPlanarPointChargeCoulombLaw setup)
    (_superposition : SatisfiesElectrostaticForceSuperposition setup)
    (_equilibrium : HasZeroNetForceOnTestCharge setup) :
    chargeInNanocoulombs (setup.charge .top) =
        32 / (13 * Real.sqrt 13) ∧
      ∀ choice, choice ≠ recordedDatasetAnswer →
        |chargeInNanocoulombs (setup.charge .top) -
            recordedDatasetAnswer.chargeInNanocoulombs| <
          |chargeInNanocoulombs (setup.charge .top) -
            choice.chargeInNanocoulombs| := by
  rcases test_to_lower_charge_separations setup _figure with
    ⟨hLowerLeftSeparation, hLowerRightSeparation⟩
  have hTopSeparation := test_to_top_charge_separation setup _figure
  rcases _figure.testCoordinates with ⟨_, hTestY⟩
  rcases _figure.lowerLeftCoordinates with ⟨_, hLowerLeftY⟩
  rcases _figure.lowerRightCoordinates with ⟨_, hLowerRightY⟩
  rcases _figure.topCoordinates with ⟨_, hTopY⟩
  have hTestYMeters :
      coordinateInMeters (setup.yCoordinate .test) = 1 / 50 := by
    rw [coordinateInCentimeters] at hTestY
    linarith only [hTestY]
  have hLowerLeftYMeters :
      coordinateInMeters (setup.yCoordinate .lowerLeft) = 0 := by
    rw [coordinateInCentimeters] at hLowerLeftY
    linarith only [hLowerLeftY]
  have hLowerRightYMeters :
      coordinateInMeters (setup.yCoordinate .lowerRight) = 0 := by
    rw [coordinateInCentimeters] at hLowerRightY
    linarith only [hLowerRightY]
  have hTopYMeters :
      coordinateInMeters (setup.yCoordinate .top) = 1 / 25 := by
    rw [coordinateInCentimeters] at hTopY
    linarith only [hTopY]
  have hLowerLeftVertical :
      verticalDisplacementInMeters setup .test .lowerLeft = 1 / 50 := by
    rw [verticalDisplacementInMeters, hTestYMeters, hLowerLeftYMeters]
    norm_num
  have hLowerRightVertical :
      verticalDisplacementInMeters setup .test .lowerRight = 1 / 50 := by
    rw [verticalDisplacementInMeters, hTestYMeters, hLowerRightYMeters]
    norm_num
  have hTopVertical :
      verticalDisplacementInMeters setup .test .top = -1 / 50 := by
    rw [verticalDisplacementInMeters, hTestYMeters, hTopYMeters]
    norm_num
  have hTestCharge :
      chargeInCoulombs (setup.charge .test) = 1 / 10 ^ 9 := by
    have hReadout := _figure.testChargeReadout
    rw [chargeInNanocoulombs] at hReadout
    norm_num at hReadout ⊢
    linarith only [hReadout]
  have hLowerLeftCharge :
      chargeInCoulombs (setup.charge .lowerLeft) = 2 / 10 ^ 9 := by
    have hReadout := _figure.lowerLeftChargeReadout
    rw [chargeInNanocoulombs] at hReadout
    norm_num at hReadout ⊢
    linarith only [hReadout]
  have hLowerRightCharge :
      chargeInCoulombs (setup.charge .lowerRight) = 2 / 10 ^ 9 := by
    have hReadout := _figure.lowerRightChargeReadout
    rw [chargeInNanocoulombs] at hReadout
    norm_num at hReadout ⊢
    linarith only [hReadout]
  have hSources :
      Finset.univ.erase (.test : ChargeSite) =
        {.lowerLeft, .lowerRight, .top} := by
    decide
  have forceSumIsZero :
      ∑ source ∈ Finset.univ.erase (.test : ChargeSite),
          forceComponentInNewtons
            (setup.pairwiseForceOn .test source).y = 0 := by
    rw [← _superposition.netForceY .test]
    exact _equilibrium.zeroVerticalComponent
  rw [hSources] at forceSumIsZero
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton] at forceSumIsZero
  have hLowerLeftForce :=
    _coulomb.pairwiseForceY .test .lowerLeft (by decide)
  rw [hLowerLeftSeparation, hLowerLeftVertical, hTestCharge,
    hLowerLeftCharge] at hLowerLeftForce
  have hLowerRightForce :=
    _coulomb.pairwiseForceY .test .lowerRight (by decide)
  rw [hLowerRightSeparation, hLowerRightVertical, hTestCharge,
    hLowerRightCharge] at hLowerRightForce
  have hTopForce :=
    _coulomb.pairwiseForceY .test .top (by decide)
  rw [hTopSeparation, hTopVertical, hTestCharge] at hTopForce
  rw [hLowerLeftForce, hLowerRightForce, hTopForce] at forceSumIsZero
  have hSqrtPositive : 0 < Real.sqrt (13 : ℝ) :=
    Real.sqrt_pos.2 (by norm_num)
  have hSqrtNonzero : Real.sqrt (13 : ℝ) ≠ 0 :=
    ne_of_gt hSqrtPositive
  have hSqrtSquared : Real.sqrt (13 : ℝ) ^ 2 = 13 :=
    Real.sq_sqrt (by norm_num)
  have hCommonFactorNonzero :
      setup.electromagneticSystem.coulombConstant *
          chargeInCoulombs (setup.charge .test) ≠ 0 :=
    mul_ne_zero (ne_of_gt _physical.coulombConstantPositive) (by
      rw [hTestCharge]
      norm_num)
  have hSqrtCubed :
      Real.sqrt (13 : ℝ) ^ 3 = 13 * Real.sqrt 13 := by
    calc
      Real.sqrt (13 : ℝ) ^ 3 =
          Real.sqrt 13 * Real.sqrt 13 ^ 2 := by ring
      _ = Real.sqrt 13 * 13 := by rw [hSqrtSquared]
      _ = 13 * Real.sqrt 13 := by ring
  have hLowerDenominator :
      (Real.sqrt 13 / 100 : ℝ) ^ 3 =
        (13 * Real.sqrt 13) / 1000000 := by
    rw [div_pow, hSqrtCubed]
    norm_num
  have hTopDenominator : ((1 / 50 : ℝ) ^ 3) = 1 / 125000 := by
    norm_num
  have hFactoredEquilibrium :
      (setup.electromagneticSystem.coulombConstant * (1 / 10 ^ 9)) *
          ((2 / 10 ^ 9) * (1 / 50) /
              (Real.sqrt 13 / 100) ^ 3 +
            (2 / 10 ^ 9) * (1 / 50) /
              (Real.sqrt 13 / 100) ^ 3 +
            chargeInCoulombs (setup.charge .top) * (-1 / 50) /
              (1 / 50) ^ 3) = 0 := by
    calc
      _ =
          setup.electromagneticSystem.coulombConstant * (1 / 10 ^ 9) *
                (2 / 10 ^ 9) * (1 / 50) /
              (Real.sqrt 13 / 100) ^ 3 +
            (setup.electromagneticSystem.coulombConstant * (1 / 10 ^ 9) *
                  (2 / 10 ^ 9) * (1 / 50) /
                (Real.sqrt 13 / 100) ^ 3 +
              setup.electromagneticSystem.coulombConstant * (1 / 10 ^ 9) *
                  chargeInCoulombs (setup.charge .top) * (-1 / 50) /
                (1 / 50) ^ 3) := by ring
      _ = 0 := forceSumIsZero
  have hNumericCommonFactorNonzero :
      setup.electromagneticSystem.coulombConstant * (1 / 10 ^ 9) ≠ 0 := by
    rw [hTestCharge] at hCommonFactorNonzero
    exact hCommonFactorNonzero
  have hScalarEquilibrium :=
    (mul_eq_zero.mp hFactoredEquilibrium).resolve_left
      hNumericCommonFactorNonzero
  rw [hLowerDenominator, hTopDenominator] at hScalarEquilibrium
  norm_num at hScalarEquilibrium
  field_simp [hSqrtNonzero] at hScalarEquilibrium
  have hChargeEquation :
      (10 : ℝ) ^ 9 * chargeInCoulombs (setup.charge .top) *
          (13 * Real.sqrt 13) = 32 := by
    nlinarith only [hScalarEquilibrium]
  have hExactCharge :
      chargeInNanocoulombs (setup.charge .top) =
        32 / (13 * Real.sqrt 13) := by
    rw [chargeInNanocoulombs]
    apply (eq_div_iff (mul_ne_zero (by norm_num) hSqrtNonzero)).2
    exact hChargeEquation
  have hExactLowerBound :
      (17 / 25 : ℝ) < 32 / (13 * Real.sqrt 13) := by
    have hSqrtUpperBound : Real.sqrt (13 : ℝ) < 361 / 100 :=
      (Real.sqrt_lt (by norm_num) (by norm_num)).2 (by norm_num)
    apply
      (lt_div_iff₀ (mul_pos (by norm_num) hSqrtPositive)).2
    nlinarith only [hSqrtUpperBound]
  have hExactUpperBound :
      32 / (13 * Real.sqrt 13) < (137 / 200 : ℝ) := by
    have hSqrtLowerBound : (18 / 5 : ℝ) < Real.sqrt 13 := by
      nlinarith only [hSqrtSquared, hSqrtPositive]
    apply
      (div_lt_iff₀ (mul_pos (by norm_num) hSqrtPositive)).2
    nlinarith only [hSqrtLowerBound]
  constructor
  · exact hExactCharge
  · intro choice hChoice
    rw [hExactCharge]
    cases choice with
    | A =>
        rw [abs_of_nonneg (by
              norm_num [recordedDatasetAnswer,
                AnswerChoice.chargeInNanocoulombs]
              linarith only [hExactLowerBound]),
          abs_of_nonpos (by
              norm_num [recordedDatasetAnswer,
                AnswerChoice.chargeInNanocoulombs]
              linarith only [hExactUpperBound])]
        norm_num [recordedDatasetAnswer, AnswerChoice.chargeInNanocoulombs]
        linarith only [hExactLowerBound, hExactUpperBound]
    | B =>
        rw [abs_of_nonneg (by
              norm_num [recordedDatasetAnswer,
                AnswerChoice.chargeInNanocoulombs]
              linarith only [hExactLowerBound]),
          abs_of_nonneg (by
              norm_num [recordedDatasetAnswer,
                AnswerChoice.chargeInNanocoulombs]
              linarith only [hExactLowerBound])]
        norm_num [recordedDatasetAnswer, AnswerChoice.chargeInNanocoulombs]
    | C =>
        simp [recordedDatasetAnswer] at hChoice
    | D =>
        rw [abs_of_nonneg (by
              norm_num [recordedDatasetAnswer,
                AnswerChoice.chargeInNanocoulombs]
              linarith only [hExactLowerBound]),
          abs_of_nonneg (by
              norm_num [recordedDatasetAnswer,
                AnswerChoice.chargeInNanocoulombs]
              linarith only [hExactLowerBound])]
        norm_num [recordedDatasetAnswer, AnswerChoice.chargeInNanocoulombs]

end PhyXMiniProblems.ProblemPhyXMini0899
