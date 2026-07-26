import Mathlib
import Physlib.Electromagnetism.Basic
import Physlib.Units.WithDim.Basic

/- USER: The assigned Lean file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0911

open Dimension

/-!
# Force exerted by a sodium ion on a water dipole

The primary image places a positive sodium ion to the left of a water
molecule.  The water molecule's negative end faces the ion, its positive end
is farther away, and the displayed separation is `10 nm`.  The ion therefore
exerts an attractive, leftward force on the water molecule.

Assumption/target split:

* governing laws: the axial aligned ion--dipole leading term
  `F₀ = 2 k |q| p / r^3`, an explicit signed approximation remainder bounded
  by one percent of `F₀`, with the sign determined by the pictured
  orientation, and Newton's third-law relation between the two force arrows;
* previous-part results: none;
* figure/data readouts: the `Na⁺ ion` and `Water molecule` labels, their
  left-to-right order, the negative and positive ends of the water molecule,
  both labelled force arrows, the attraction arc, the `10 nm` separation, and
  the stated permanent dipole moment `6.2 * 10⁻³⁰ C m`;
* current target conclusions: the ion-on-dipole force is directed toward the
  ion and its magnitude agrees, at the displayed precision, with answer C,
  `1.8 * 10⁻¹⁴ N`.

The two force components in the setup are independent dimensionful physical
observables.  The approximation remainder is likewise an independent
dimensionful quantity.  None is defined from the requested answer choice.
-/

/-! ## Dimensionful physical quantities and coherent-SI readouts -/

/-- The physical dimension `M L T⁻²` of force. -/
def forceDimension : Dimension :=
  M𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹

/-- The physical dimension `C L` of electric dipole moment. -/
def electricDipoleMomentDimension : Dimension :=
  C𝓭 * L𝓭

/-- A signed, unit-independent electric charge. -/
abbrev SignedChargeQuantity : Type :=
  Dimensionful (WithDim C𝓭 ℝ)

/-- A nonnegative, unit-independent electric dipole-moment magnitude. -/
abbrev DipoleMomentMagnitudeQuantity : Type :=
  Dimensionful (WithDim electricDipoleMomentDimension NNReal)

/-- A signed axial position. -/
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

/-- Read a dipole-moment magnitude in coherent-SI coulomb-metres. -/
def dipoleMomentInCoulombMeters
    (moment : DipoleMomentMagnitudeQuantity) : ℝ :=
  ((moment UnitChoices.SI).val : ℝ)

/-- Read an axial position in coherent-SI metres. -/
def positionInMeters (position : AxialPositionQuantity) : ℝ :=
  (position UnitChoices.SI).val

/-- Read a nonnegative physical length in coherent-SI metres. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  ((length UnitChoices.SI).val : ℝ)

/-- Read a physical length in nanometres, the unit printed in the image. -/
def lengthInNanometers (length : LengthQuantity) : ℝ :=
  (10 : ℝ) ^ (9 : ℕ) * lengthInMeters length

/-- Read a signed axial force component in coherent-SI newtons. -/
def forceComponentInNewtons (force : AxialForceComponentQuantity) : ℝ :=
  (force UnitChoices.SI).val

/-! ## Primary-image labels and physical setup -/

/-- The two physical objects named in image `911.png`. -/
inductive FigureObject where
  | sodiumIon
  | waterMolecule
  deriving DecidableEq, Fintype, Repr

/-- The two ends of the pictured water-dipole representation. -/
inductive WaterMoleculeEnd where
  | ionFacing
  | farFromIon
  deriving DecidableEq, Fintype, Repr

/-- The partial-charge sign drawn at an end of the water molecule. -/
inductive PartialChargeSign where
  | negative
  | positive
  deriving DecidableEq, Repr

/-- The two force arrows explicitly labelled in the primary image. -/
inductive ForceArrow where
  | dipoleOnIon
  | ionOnDipole
  deriving DecidableEq, Fintype, Repr

/-- Direction on the image's horizontal axis, with positive coordinate rightward. -/
inductive AxialDirection where
  | left
  | right
  deriving DecidableEq, Repr

/-- The material environment stated in the prose. -/
inductive InteractionMedium where
  | saltwaterSolution
  deriving DecidableEq, Repr

/-- Idealization used for the sodium ion in the textbook computation. -/
inductive IonModel where
  | pointIon
  deriving DecidableEq, Repr

/-- Orientation of the permanent water dipole relative to the positive ion. -/
inductive DipoleOrientation where
  | negativeEndTowardIon
  deriving DecidableEq, Repr

/-!
The recorded numerical answer uses the unscreened textbook ion--dipole law;
this constructor makes that approximation explicit despite the stated
saltwater environment.
-/
inductive ElectrostaticApproximation where
  | unscreenedPointIonDipole
  deriving DecidableEq, Repr

/-- Literal object labels visible below the two drawings. -/
def expectedObjectLabel : FigureObject → String
  | .sodiumIon => "Na+ ion"
  | .waterMolecule => "Water molecule"

/-- Partial-charge signs read from the two ends of the water molecule. -/
def expectedWaterEndSign : WaterMoleculeEnd → PartialChargeSign
  | .ionFacing => .negative
  | .farFromIon => .positive

/-- Literal names of the force arrows in the figure. -/
def expectedForceArrowLabel : ForceArrow → String
  | .dipoleOnIon => "F_dipole on ion"
  | .ionOnDipole => "F_ion on dipole"

/-- The image shows both interaction forces pointing toward the other object. -/
def expectedForceArrowDirection : ForceArrow → AxialDirection
  | .dipoleOnIon => .right
  | .ionOnDipole => .left

/-!
Presentation data transcribed from the primary bitmap.  In particular, this
structure contains no numerical physical-force value.
-/
structure SodiumIonWaterFigure where
  objectShown : FigureObject → Bool
  printedObjectLabel : FigureObject → String
  sodiumPositiveChargeGlyphShown : Bool
  waterEndSign : WaterMoleculeEnd → PartialChargeSign
  forceArrowShown : ForceArrow → Bool
  printedForceArrowLabel : ForceArrow → String
  forceArrowDirection : ForceArrow → AxialDirection
  dashedInteractionArcShown : Bool
  separationArrowShown : Bool
  printedSeparationNanometers : ℝ

/-!
Independent physical quantities associated with the prose and diagram.  The
two force fields are observables, and the remainder is an independent model
discrepancy; none is a definition of the requested answer.
-/
structure SodiumIonWaterDipoleSetup where
  figure : SodiumIonWaterFigure
  electromagneticSystem : Electromagnetism.EMSystem
  medium : InteractionMedium
  ionModel : IonModel
  dipoleOrientation : DipoleOrientation
  approximation : ElectrostaticApproximation
  sodiumIonCharge : SignedChargeQuantity
  waterDipoleMomentMagnitude : DipoleMomentMagnitudeQuantity
  sodiumIonPosition : AxialPositionQuantity
  waterMoleculePosition : AxialPositionQuantity
  separation : LengthQuantity
  forceIonOnDipole : AxialForceComponentQuantity
  forceDipoleOnIon : AxialForceComponentQuantity
  alignedPointDipoleRemainder : AxialForceComponentQuantity

/-- Magnitude of the requested force, obtained from its signed axial component. -/
def ionOnDipoleForceMagnitudeInNewtons
    (setup : SodiumIonWaterDipoleSetup) : ℝ :=
  |forceComponentInNewtons setup.forceIonOnDipole|

/-! ## Scenario, data calibration, and primary-image evidence -/

/-- Qualitative physical modeling assumptions stated or implied by the scenario. -/
structure MatchesSodiumIonWaterScenario
    (setup : SodiumIonWaterDipoleSetup) : Prop where
  mediumIsSaltwater : setup.medium = .saltwaterSolution
  sodiumTreatedAsPointIon : setup.ionModel = .pointIon
  sodiumIonIsPositive : 0 < chargeInCoulombs setup.sodiumIonCharge
  waterDipoleIsOrientedAsShown :
    setup.dipoleOrientation = .negativeEndTowardIon
  usesUnscreenedPointDipoleModel :
    setup.approximation = .unscreenedPointIonDipole

/-!
Numerical physical data from the prose together with the standard elementary
charge and Coulomb-constant values needed by the textbook model.  No force
value from an answer choice appears here.
-/
structure HasIonDipolePhysicalData
    (setup : SodiumIonWaterDipoleSetup) : Prop where
  waterPermanentDipoleMoment :
    dipoleMomentInCoulombMeters setup.waterDipoleMomentMagnitude =
      (6.2 : ℝ) * 10 ^ (-30 : ℤ)
  singlyChargedSodiumIonCharge :
    chargeInCoulombs setup.sodiumIonCharge =
      (1.60 : ℝ) * 10 ^ (-19 : ℤ)
  standardCoulombConstant :
    setup.electromagneticSystem.coulombConstant =
      (8.99 : ℝ) * 10 ^ (9 : ℕ)

/-!
All qualitative and scalar evidence read from image `911.png`, including the
calibration between the printed distance and the physical separation.
-/
structure MatchesSuppliedIonDipoleFigure
    (setup : SodiumIonWaterDipoleSetup) : Prop where
  bothObjectsShown : ∀ object, setup.figure.objectShown object = true
  objectLabels : ∀ object,
    setup.figure.printedObjectLabel object = expectedObjectLabel object
  sodiumPositiveGlyph : setup.figure.sodiumPositiveChargeGlyphShown = true
  waterEndSigns : ∀ waterEnd,
    setup.figure.waterEndSign waterEnd = expectedWaterEndSign waterEnd
  bothForceArrowsShown : ∀ arrow,
    setup.figure.forceArrowShown arrow = true
  forceArrowLabels : ∀ arrow,
    setup.figure.printedForceArrowLabel arrow = expectedForceArrowLabel arrow
  forceArrowDirections : ∀ arrow,
    setup.figure.forceArrowDirection arrow =
      expectedForceArrowDirection arrow
  interactionArc : setup.figure.dashedInteractionArcShown = true
  separationArrow : setup.figure.separationArrowShown = true
  displayedSeparation : setup.figure.printedSeparationNanometers = 10
  physicalSeparationMatchesDisplay :
    lengthInNanometers setup.separation =
      setup.figure.printedSeparationNanometers

/-!
The signed coordinates realize the left-to-right ion--water order and the
positive separation shown by the double-headed arrow.
-/
structure HasIonWaterAxialGeometry
    (setup : SodiumIonWaterDipoleSetup) : Prop where
  ionIsLeftOfWater :
    positionInMeters setup.sodiumIonPosition <
      positionInMeters setup.waterMoleculePosition
  coordinateDifferenceIsSeparation :
    positionInMeters setup.waterMoleculePosition -
        positionInMeters setup.sodiumIonPosition =
      lengthInMeters setup.separation
  separationIsPositive : 0 < lengthInMeters setup.separation

/-! ## Governing ion--dipole laws -/

/-!
For a point ion and an aligned permanent dipole on the same axis, the leading
force magnitude is `2 k |q| p / r^3`.  With positive coordinate rightward and
the positive ion on the left, the negative sign states that the leading force
on the water dipole is attractive.

The water molecule is not literally a mathematical point dipole, and the
scenario says that the interaction occurs in saltwater.  Consequently the
textbook formula is not asserted as an exact physical identity.  The first
field exposes a signed force remainder, and the second imposes the explicit
one-percent relative-error contract needed when using the unscreened aligned
point-dipole model for this numerical answer.  Neither field contains an
answer choice or its force value.
-/
structure SatisfiesAlignedIonDipoleForceLaw
    (setup : SodiumIonWaterDipoleSetup) : Prop where
  forceLawWithRemainder :
    setup.ionModel = .pointIon →
    setup.dipoleOrientation = .negativeEndTowardIon →
    setup.approximation = .unscreenedPointIonDipole →
      forceComponentInNewtons setup.forceIonOnDipole =
        -(2 * setup.electromagneticSystem.coulombConstant *
          |chargeInCoulombs setup.sodiumIonCharge| *
          dipoleMomentInCoulombMeters setup.waterDipoleMomentMagnitude /
          lengthInMeters setup.separation ^ 3) +
        forceComponentInNewtons setup.alignedPointDipoleRemainder
  controlledApproximationRemainder :
    |forceComponentInNewtons setup.alignedPointDipoleRemainder| ≤
      (1 / 100 : ℝ) *
        |2 * setup.electromagneticSystem.coulombConstant *
          |chargeInCoulombs setup.sodiumIonCharge| *
          dipoleMomentInCoulombMeters setup.waterDipoleMomentMagnitude /
          lengthInMeters setup.separation ^ 3|

/-- Newton's third law relates the two force arrows shown in the image. -/
structure SatisfiesIonDipoleActionReaction
    (setup : SodiumIonWaterDipoleSetup) : Prop where
  equalAndOppositeForces :
    forceComponentInNewtons setup.forceDipoleOnIon =
      -forceComponentInNewtons setup.forceIonOnDipole

/-! ## Multiple-choice force and blueprint target -/

/-- Labels of the four force magnitudes printed in the problem source. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Force magnitude in newtons printed beside each answer label. -/
def AnswerChoice.forceInNewtons : AnswerChoice → ℝ
  | .A => (1.3 : ℝ) * 10 ^ (-14 : ℤ)
  | .B => (5.3 : ℝ) * 10 ^ (-14 : ℤ)
  | .C => (1.8 : ℝ) * 10 ^ (-14 : ℤ)
  | .D => (3.5 : ℝ) * 10 ^ (-14 : ℤ)

/-- Half of the last displayed decimal place in answer choice C. -/
def choiceCDisplayToleranceInNewtons : ℝ :=
  (0.05 : ℝ) * 10 ^ (-14 : ℤ)

/-- The answer label recorded by the supplied dataset. -/
def recordedDatasetAnswer : AnswerChoice := .C

/-!
**Blueprint target** `thm:physics:phyx_mini_0911:target`.

The force exerted by the positive sodium ion on the pictured water dipole is
leftward (toward the ion), and its magnitude agrees at the displayed precision
with choice C, `1.8 * 10⁻¹⁴ N`.
-/
theorem problem_phyx_mini_0911
    (setup : SodiumIonWaterDipoleSetup)
    (_scenario : MatchesSodiumIonWaterScenario setup)
    (_data : HasIonDipolePhysicalData setup)
    (_figure : MatchesSuppliedIonDipoleFigure setup)
    (_geometry : HasIonWaterAxialGeometry setup)
    (_forceLaw : SatisfiesAlignedIonDipoleForceLaw setup)
    (_actionReaction : SatisfiesIonDipoleActionReaction setup) :
    forceComponentInNewtons setup.forceIonOnDipole < 0 ∧
      |ionOnDipoleForceMagnitudeInNewtons setup -
          AnswerChoice.forceInNewtons .C| <
        choiceCDisplayToleranceInNewtons := by
  have hsepNm : lengthInNanometers setup.separation = 10 := by
    calc
      lengthInNanometers setup.separation =
          setup.figure.printedSeparationNanometers :=
        _figure.physicalSeparationMatchesDisplay
      _ = 10 := _figure.displayedSeparation
  have hsep : lengthInMeters setup.separation = (1 / 100000000 : ℝ) := by
    rw [lengthInNanometers] at hsepNm
    norm_num at hsepNm ⊢
    linarith
  have hforce := _forceLaw.forceLawWithRemainder
    _scenario.sodiumTreatedAsPointIon
    _scenario.waterDipoleIsOrientedAsShown
    _scenario.usesUnscreenedPointDipoleModel
  have hrem := _forceLaw.controlledApproximationRemainder
  rw [_data.waterPermanentDipoleMoment,
    _data.singlyChargedSodiumIonCharge,
    _data.standardCoulombConstant, hsep] at hforce hrem
  norm_num at hforce hrem
  rcases abs_le.mp hrem with ⟨hremLower, hremUpper⟩
  have hforceNeg :
      forceComponentInNewtons setup.forceIonOnDipole < 0 := by
    linarith
  constructor
  · exact hforceNeg
  · rw [ionOnDipoleForceMagnitudeInNewtons, abs_of_neg hforceNeg]
    norm_num [AnswerChoice.forceInNewtons,
      choiceCDisplayToleranceInNewtons]
    rw [abs_lt]
    constructor <;> linarith

end PhyXMiniProblems.ProblemPhyXMini0911
