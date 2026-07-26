import Mathlib
import Physlib.Electromagnetism.Basic
import Physlib.Units.WithDim.Basic

/- USER: The assigned Lean file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0892

open Dimension
open scoped BigOperators

/-!
# Net electric force on charge A in a collinear three-charge arrangement

The primary image shows three point charges in the left-to-right order
`A`, `B`, `C`.  Their displayed charges are respectively `+1 nC`, `-1 nC`,
and `+4 nC`; both adjacent gaps are `1 cm`.  All forces are therefore along
one axis, so a signed axial force component completely represents the force.

Assumption/target split:

* governing laws: the signed one-dimensional point-charge form of Coulomb's
  force law and linear superposition of the forces on `A`;
* previous-part results: none;
* figure/data readouts: the three labels, colors, charge-sign glyphs, charge
  values, left-to-right order, and the two adjacent `1 cm` distance arrows;
* current target conclusion: the signed net-force component on `A` is
  `0 N`, corresponding to answer C.

The net-force observable is an independent field of the setup.  Neither it
nor either source force is defined to equal the requested answer.
-/

/-! ## Dimensionful quantities and coherent-SI readouts -/

/-- The physical dimension `M L T⁻²` of force. -/
def forceDimension : Dimension :=
  M𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹

/-- A signed, unit-independent electric charge. -/
abbrev SignedChargeQuantity : Type :=
  Dimensionful (WithDim C𝓭 ℝ)

/-- A signed position coordinate on the line containing the charges. -/
abbrev AxialPositionQuantity : Type :=
  Dimensionful (WithDim L𝓭 ℝ)

/-- A nonnegative, unit-independent physical separation. -/
abbrev LengthQuantity : Type :=
  Dimensionful (WithDim L𝓭 NNReal)

/-- A signed axial component of a physical force. -/
abbrev AxialForceComponentQuantity : Type :=
  Dimensionful (WithDim forceDimension ℝ)

/-- Read a signed physical charge in coherent-SI coulombs. -/
def chargeInCoulombs (charge : SignedChargeQuantity) : ℝ :=
  (charge UnitChoices.SI).val

/-- Read a charge in the nanocoulombs used by the figure labels. -/
def chargeInNanocoulombs (charge : SignedChargeQuantity) : ℝ :=
  (10 : ℝ) ^ 9 * chargeInCoulombs charge

/-- Read an axial position in coherent-SI metres. -/
def positionInMeters (position : AxialPositionQuantity) : ℝ :=
  (position UnitChoices.SI).val

/-- Read a nonnegative physical length in coherent-SI metres. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  ((length UnitChoices.SI).val : ℝ)

/-- Read a length in the centimetres used by the distance arrows. -/
def lengthInCentimeters (length : LengthQuantity) : ℝ :=
  100 * lengthInMeters length

/-- Read a signed axial force component in coherent-SI newtons. -/
def forceComponentInNewtons (force : AxialForceComponentQuantity) : ℝ :=
  (force UnitChoices.SI).val

/-! ## Figure labels and the independent physical setup -/

/-- The three charged objects, named exactly as in image `892.png`. -/
inductive ChargeSite where
  | A
  | B
  | C
  deriving DecidableEq, Fintype, Repr

/-- The two charges other than `A` which exert force on `A`. -/
inductive SourceForA where
  | B
  | C
  deriving DecidableEq, Fintype, Repr

/-- Regard a source of force on `A` as one of the three labelled sites. -/
def SourceForA.toChargeSite : SourceForA → ChargeSite
  | .B => .B
  | .C => .C

/-- The two adjacent gaps whose arrows are printed in the image. -/
inductive AdjacentGap where
  | AB
  | BC
  deriving DecidableEq, Fintype, Repr

/-- Left endpoint of a displayed adjacent gap. -/
def AdjacentGap.leftEndpoint : AdjacentGap → ChargeSite
  | .AB => .A
  | .BC => .B

/-- Right endpoint of a displayed adjacent gap. -/
def AdjacentGap.rightEndpoint : AdjacentGap → ChargeSite
  | .AB => .B
  | .BC => .C

/-- The sign glyph drawn inside a charge circle. -/
inductive FigureChargeSign where
  | plus
  | minus
  deriving DecidableEq, Repr

/-- The two circle colors visibly used to distinguish the charges. -/
inductive FigureChargeColor where
  | red
  | teal
  deriving DecidableEq, Repr

/-- The literal label expected beside each charged object. -/
def expectedSiteLabel : ChargeSite → String
  | .A => "A"
  | .B => "B"
  | .C => "C"

/-- Charge signs transcribed from the primary image. -/
def expectedChargeSign : ChargeSite → FigureChargeSign
  | .A => .plus
  | .B => .minus
  | .C => .plus

/-- Circle colors transcribed from the primary image. -/
def expectedChargeColor : ChargeSite → FigureChargeColor
  | .A => .red
  | .B => .teal
  | .C => .red

/-- Nanocoulomb values printed above the three charge circles. -/
def expectedChargeLabelNanocoulombs : ChargeSite → ℝ
  | .A => 1
  | .B => -1
  | .C => 4

/-- Literal presentation data transcribed from image `892.png`. -/
structure ThreeChargeLineFigure where
  siteShown : ChargeSite → Bool
  printedSiteLabel : ChargeSite → String
  chargeSignGlyph : ChargeSite → FigureChargeSign
  chargeCircleColor : ChargeSite → FigureChargeColor
  printedChargeNanocoulombs : ChargeSite → ℝ
  arrangedOnStraightLine : Bool
  leftToRightOrder : List ChargeSite
  distanceArrowShown : AdjacentGap → Bool
  printedGapCentimeters : AdjacentGap → ℝ

/-!
The physical charges, positions, separations, and force observables associated
with the diagram.  The force from each other charge and the net force on `A`
are primitive observables here; the governing laws below relate their SI
readouts without defining them from the requested zero value.
-/
structure ThreePointChargeLineSetup where
  figure : ThreeChargeLineFigure
  electromagneticSystem : Electromagnetism.EMSystem
  charge : ChargeSite → SignedChargeQuantity
  position : ChargeSite → AxialPositionQuantity
  adjacentSeparation : AdjacentGap → LengthQuantity
  modeledAsPointCharge : ChargeSite → Bool
  forceOnAFrom : SourceForA → AxialForceComponentQuantity
  netForceOnA : AxialForceComponentQuantity

/-- Axial displacement from a source charge to charge `A`, in metres. -/
def displacementFromSourceToAInMeters
    (setup : ThreePointChargeLineSetup) (source : SourceForA) : ℝ :=
  positionInMeters (setup.position .A) -
    positionInMeters (setup.position source.toChargeSite)

/-! ## Scenario, primary-image evidence, and physical geometry -/

/-- All three pictured objects are modelled as point charges. -/
structure MatchesThreePointChargeScenario
    (setup : ThreePointChargeLineSetup) : Prop where
  allSitesArePointCharges :
    ∀ site, setup.modeledAsPointCharge site = true

/-!
The literal image features and their calibration to the independent physical
charges and separations.  These premises contain no force value.
-/
structure MatchesSuppliedThreeChargeFigure
    (setup : ThreePointChargeLineSetup) : Prop where
  allSitesShown : ∀ site, setup.figure.siteShown site = true
  printedSiteLabels : ∀ site,
    setup.figure.printedSiteLabel site = expectedSiteLabel site
  signGlyphs : ∀ site,
    setup.figure.chargeSignGlyph site = expectedChargeSign site
  circleColors : ∀ site,
    setup.figure.chargeCircleColor site = expectedChargeColor site
  printedChargeLabels : ∀ site,
    setup.figure.printedChargeNanocoulombs site =
      expectedChargeLabelNanocoulombs site
  physicalChargesMatchLabels : ∀ site,
    chargeInNanocoulombs (setup.charge site) =
      setup.figure.printedChargeNanocoulombs site
  straightLineShown : setup.figure.arrangedOnStraightLine = true
  displayedLeftToRightOrder :
    setup.figure.leftToRightOrder = [.A, .B, .C]
  bothDistanceArrowsShown : ∀ gap,
    setup.figure.distanceArrowShown gap = true
  bothPrintedGapLabelsAreOneCentimeter : ∀ gap,
    setup.figure.printedGapCentimeters gap = 1
  physicalSeparationsMatchLabels : ∀ gap,
    lengthInCentimeters (setup.adjacentSeparation gap) =
      setup.figure.printedGapCentimeters gap

/-!
The signed position coordinates realize the printed `A`--`B`--`C` order and
the two positive physical separations.
-/
structure HasCollinearAdjacentGapGeometry
    (setup : ThreePointChargeLineSetup) : Prop where
  aIsLeftOfB :
    positionInMeters (setup.position .A) <
      positionInMeters (setup.position .B)
  bIsLeftOfC :
    positionInMeters (setup.position .B) <
      positionInMeters (setup.position .C)
  adjacentSeparationsPositive : ∀ gap,
    0 < lengthInMeters (setup.adjacentSeparation gap)
  adjacentCoordinateDifferences : ∀ gap,
    positionInMeters (setup.position gap.rightEndpoint) -
        positionInMeters (setup.position gap.leftEndpoint) =
      lengthInMeters (setup.adjacentSeparation gap)

/-- Basic nondegeneracy and positivity conditions for the electrostatic model. -/
structure HasPhysicalElectrostaticParameters
    (setup : ThreePointChargeLineSetup) : Prop where
  chargeANonzero : chargeInCoulombs (setup.charge .A) ≠ 0
  chargeBNonzero : chargeInCoulombs (setup.charge .B) ≠ 0
  chargeCNonzero : chargeInCoulombs (setup.charge .C) ≠ 0
  coulombConstantPositive :
    0 < setup.electromagneticSystem.coulombConstant

/-! ## Governing electrostatic laws -/

/-!
For each source `S ∈ {B,C}`, the signed one-dimensional force on `A` is

`k q_A q_S (x_A - x_S) / |x_A - x_S|^3`.

This is Coulomb's inverse-square law with the displacement factor retaining
the force direction.  It is a general governing law, not the target value.
-/
structure SatisfiesAxialPointChargeForceLaw
    (setup : ThreePointChargeLineSetup) : Prop where
  forceFromEachSource : ∀ source,
    positionInMeters (setup.position .A) ≠
        positionInMeters (setup.position source.toChargeSite) →
      forceComponentInNewtons (setup.forceOnAFrom source) =
        setup.electromagneticSystem.coulombConstant *
          chargeInCoulombs (setup.charge .A) *
          chargeInCoulombs (setup.charge source.toChargeSite) *
          displacementFromSourceToAInMeters setup source /
          |displacementFromSourceToAInMeters setup source| ^ 3

/-- The signed net force on `A` is the sum of the forces due to `B` and `C`. -/
structure SatisfiesAxialForceSuperposition
    (setup : ThreePointChargeLineSetup) : Prop where
  netForceIsSourceSum :
    forceComponentInNewtons setup.netForceOnA =
      ∑ source : SourceForA,
        forceComponentInNewtons (setup.forceOnAFrom source)

/-! ## Cancellation and multiple-choice target -/

/-!
The `-1 nC` charge at `1 cm` attracts `A` to the right, while the `+4 nC`
charge at `2 cm` repels `A` to the left.  Coulomb's inverse-square scaling
makes the two signed source-force components cancel.
-/
lemma source_force_components_cancel
    (setup : ThreePointChargeLineSetup)
    (_figure : MatchesSuppliedThreeChargeFigure setup)
    (_geometry : HasCollinearAdjacentGapGeometry setup)
    (_physical : HasPhysicalElectrostaticParameters setup)
    (_coulomb : SatisfiesAxialPointChargeForceLaw setup) :
    forceComponentInNewtons (setup.forceOnAFrom .B) +
        forceComponentInNewtons (setup.forceOnAFrom .C) = 0 := by
  have hqA := _figure.physicalChargesMatchLabels ChargeSite.A
  have hqB := _figure.physicalChargesMatchLabels ChargeSite.B
  have hqC := _figure.physicalChargesMatchLabels ChargeSite.C
  rw [_figure.printedChargeLabels ChargeSite.A] at hqA
  rw [_figure.printedChargeLabels ChargeSite.B] at hqB
  rw [_figure.printedChargeLabels ChargeSite.C] at hqC
  norm_num [chargeInNanocoulombs, expectedChargeLabelNanocoulombs] at hqA hqB hqC
  have hqA' :
      chargeInCoulombs (setup.charge ChargeSite.A) = (1 : ℝ) / 1000000000 := by
    linarith
  have hqB' :
      chargeInCoulombs (setup.charge ChargeSite.B) = -(1 : ℝ) / 1000000000 := by
    linarith
  have hqC' :
      chargeInCoulombs (setup.charge ChargeSite.C) = (4 : ℝ) / 1000000000 := by
    linarith
  have hAB := _figure.physicalSeparationsMatchLabels AdjacentGap.AB
  have hBC := _figure.physicalSeparationsMatchLabels AdjacentGap.BC
  rw [_figure.bothPrintedGapLabelsAreOneCentimeter AdjacentGap.AB] at hAB
  rw [_figure.bothPrintedGapLabelsAreOneCentimeter AdjacentGap.BC] at hBC
  norm_num [lengthInCentimeters] at hAB hBC
  have hABpos := _geometry.adjacentCoordinateDifferences AdjacentGap.AB
  have hBCpos := _geometry.adjacentCoordinateDifferences AdjacentGap.BC
  simp only [AdjacentGap.rightEndpoint, AdjacentGap.leftEndpoint] at hABpos hBCpos
  have hABdiff :
      positionInMeters (setup.position ChargeSite.B) -
          positionInMeters (setup.position ChargeSite.A) = (1 : ℝ) / 100 := by
    linarith
  have hBCdiff :
      positionInMeters (setup.position ChargeSite.C) -
          positionInMeters (setup.position ChargeSite.B) = (1 : ℝ) / 100 := by
    linarith
  have hBA_displacement :
      positionInMeters (setup.position ChargeSite.A) -
          positionInMeters (setup.position ChargeSite.B) = -(1 : ℝ) / 100 := by
    linarith
  have hCA_displacement :
      positionInMeters (setup.position ChargeSite.A) -
          positionInMeters (setup.position ChargeSite.C) = -(1 : ℝ) / 50 := by
    linarith
  have hAC :
      positionInMeters (setup.position ChargeSite.A) <
        positionInMeters (setup.position ChargeSite.C) :=
    lt_trans _geometry.aIsLeftOfB _geometry.bIsLeftOfC
  have hforceB := _coulomb.forceFromEachSource SourceForA.B
    (ne_of_lt _geometry.aIsLeftOfB)
  have hforceC := _coulomb.forceFromEachSource SourceForA.C
    (ne_of_lt hAC)
  simp only [displacementFromSourceToAInMeters, SourceForA.toChargeSite] at hforceB hforceC
  rw [hqA', hqB', hBA_displacement] at hforceB
  rw [hqA', hqC', hCA_displacement] at hforceC
  norm_num at hforceB hforceC
  linarith

/-- Labels attached to the four force choices in the problem source. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Force magnitude in newtons printed beside each displayed answer label. -/
def AnswerChoice.forceInNewtons : AnswerChoice → ℝ
  | .A => 1.25
  | .B => 1.35
  | .C => 0
  | .D => 5.33

/-- The answer label recorded by the supplied dataset. -/
def recordedDatasetAnswer : AnswerChoice := .C

/-!
**Blueprint target** `thm:physics:phyx_mini_0892:target`.

Under the figure calibration, collinear geometry, Coulomb force law, and
superposition, the net electric force on charge `A` has zero signed axial
component in newtons.  Since every force is axial, this states that the force
vector itself is zero, selecting answer C.
-/
theorem problem_phyx_mini_0892
    (setup : ThreePointChargeLineSetup)
    (_scenario : MatchesThreePointChargeScenario setup)
    (_figure : MatchesSuppliedThreeChargeFigure setup)
    (_geometry : HasCollinearAdjacentGapGeometry setup)
    (_physical : HasPhysicalElectrostaticParameters setup)
    (_coulomb : SatisfiesAxialPointChargeForceLaw setup)
    (_superposition : SatisfiesAxialForceSuperposition setup) :
    forceComponentInNewtons setup.netForceOnA = 0 := by
  classical
  rw [_superposition.netForceIsSourceSum]
  rw [show (Finset.univ : Finset SourceForA) = {.B, .C} by
    ext source
    cases source <;> simp]
  simpa using
    source_force_components_cancel setup _figure _geometry _physical _coulomb

end PhyXMiniProblems.ProblemPhyXMini0892
