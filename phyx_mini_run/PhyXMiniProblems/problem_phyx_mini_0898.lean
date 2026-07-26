import Mathlib
import Physlib.Electromagnetism.Basic
import Physlib.Units.WithDim.Basic

/- USER: The assigned source file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0898

open Dimension
open scoped BigOperators

/-!
# Force on the lower-left charge in a three-charge rectangle

The primary image shows a dashed `3.0 cm` by `4.0 cm` rectangle.  A positive
`5.0 nC` target charge is at the lower-left corner, a positive `10 nC` source
is directly above it, and a negative `10 nC` source is at the upper-right
corner.  The lower-right corner is empty.  In particular, the diagonal from
the target to the negative source is not itself drawn, although it is the
displacement used in the Coulomb-force calculation.

Lengths, signed charges, planar positions, and planar forces are represented
by unit-independent Physlib quantities.  Real vectors and scalars below are
explicit coherent-SI readouts in metres and newtons.

Assumption/target split:

* governing laws: vector Coulomb force for each source and linear
  superposition of the two pair forces;
* previous-part results: none;
* figure/data readouts: the three corner assignments, charge signs and
  nanocoulomb labels, the four dashed rectangle edges, absence of a diagonal,
  the `3.0 cm` horizontal label, the `4.0 cm` vertical label, and a rounded
  free-space Coulomb constant;
* current target conclusions: the resultant force magnitude lies between
  `1.74e-4 N` and `1.75e-4 N`, rounds to the displayed `1.7e-4 N`, and makes
  answer C the unique nearest displayed choice.

No target force magnitude or answer label occurs in a setup field or physics
premise.
-/

/-! ## Dimensionful physical quantities and coherent-SI readouts -/

/-- A Cartesian vector in the plane of the supplied figure. -/
abbrev PlanarVector : Type :=
  EuclideanSpace ℝ (Fin 2)

/-- The physical dimension `M L T⁻²` of force. -/
def forceDimension : Dimension :=
  M𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹

/-- A nonnegative, unit-independent physical length. -/
abbrev LengthQuantity : Type :=
  Dimensionful (WithDim L𝓭 NNReal)

/-- A signed, unit-independent electric charge. -/
abbrev SignedChargeQuantity : Type :=
  Dimensionful (WithDim C𝓭 ℝ)

/-- A unit-independent physical position in the plane. -/
abbrev PlanarPositionQuantity : Type :=
  Dimensionful (WithDim L𝓭 PlanarVector)

/-- A unit-independent physical force vector in the plane. -/
abbrev PlanarForceQuantity : Type :=
  Dimensionful (WithDim forceDimension PlanarVector)

/-- Coherent-SI metre readout of a nonnegative physical length. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  ((length UnitChoices.SI).val : ℝ)

/-- Centimetre readout used by the two dimension labels in the figure. -/
def lengthInCentimeters (length : LengthQuantity) : ℝ :=
  100 * lengthInMeters length

/-- Coherent-SI coulomb readout of a signed physical charge. -/
def chargeInCoulombs (charge : SignedChargeQuantity) : ℝ :=
  (charge UnitChoices.SI).val

/-- Nanocoulomb readout used by the three printed charge labels. -/
def chargeInNanocoulombs (charge : SignedChargeQuantity) : ℝ :=
  (10 : ℝ) ^ 9 * chargeInCoulombs charge

/-- Cartesian metre readout of a physical planar position. -/
def positionVectorInMeters (position : PlanarPositionQuantity) : PlanarVector :=
  (position UnitChoices.SI).val

/-- Cartesian newton readout of a physical planar force. -/
def forceVectorInNewtons (force : PlanarForceQuantity) : PlanarVector :=
  (force UnitChoices.SI).val

/-- Euclidean magnitude, in newtons, of a physical planar force. -/
def forceMagnitudeInNewtons (force : PlanarForceQuantity) : ℝ :=
  ‖forceVectorInNewtons force‖

/-! ## Named figure objects and independent physical setup -/

/-- The four corners of the dashed rectangle in image `898.png`. -/
inductive RectangleCorner where
  | upperLeft
  | upperRight
  | lowerRight
  | lowerLeft
  deriving DecidableEq, Fintype, Repr

/-- The three physical charges, named by value and role in the figure. -/
inductive ChargeLabel where
  | targetFiveNanocoulombs
  | upperLeftTenNanocoulombs
  | upperRightMinusTenNanocoulombs
  deriving DecidableEq, Fintype, Repr

/-- The two charges exerting force on the lower-left target charge. -/
inductive SourceCharge where
  | upperLeft
  | upperRight
  deriving DecidableEq, Fintype, Repr

/-- Charge label associated with each source role. -/
def sourceChargeLabel : SourceCharge → ChargeLabel
  | .upperLeft => .upperLeftTenNanocoulombs
  | .upperRight => .upperRightMinusTenNanocoulombs

/-- The charge whose force is requested. -/
def targetChargeLabel : ChargeLabel :=
  .targetFiveNanocoulombs

/-- Corner occupied by each charge in the primary image. -/
def expectedChargeCorner : ChargeLabel → RectangleCorner
  | .targetFiveNanocoulombs => .lowerLeft
  | .upperLeftTenNanocoulombs => .upperLeft
  | .upperRightMinusTenNanocoulombs => .upperRight

/-- Sign glyph drawn inside a charge circle. -/
inductive FigureChargeSign where
  | plus
  | minus
  deriving DecidableEq, Repr

/-- Fill colour used to distinguish positive and negative charges. -/
inductive FigureChargeColor where
  | lightRed
  | lightTeal
  deriving DecidableEq, Repr

/-- Sign glyph expected for each of the three charges. -/
def expectedChargeSign : ChargeLabel → FigureChargeSign
  | .targetFiveNanocoulombs => .plus
  | .upperLeftTenNanocoulombs => .plus
  | .upperRightMinusTenNanocoulombs => .minus

/-- Circle colour expected for each of the three charges. -/
def expectedChargeColor : ChargeLabel → FigureChargeColor
  | .targetFiveNanocoulombs => .lightRed
  | .upperLeftTenNanocoulombs => .lightRed
  | .upperRightMinusTenNanocoulombs => .lightTeal

/-- Signed nanocoulomb number printed beside each charge. -/
def expectedChargeInNanocoulombs : ChargeLabel → ℝ
  | .targetFiveNanocoulombs => 5
  | .upperLeftTenNanocoulombs => 10
  | .upperRightMinusTenNanocoulombs => -10

/-- The four dashed sides of the rectangle. -/
inductive RectangleEdge where
  | top
  | right
  | bottom
  | left
  deriving DecidableEq, Fintype, Repr

/-- The two sides carrying numerical dimension labels. -/
inductive DimensionLabelSide where
  | topHorizontal
  | leftVertical
  deriving DecidableEq, Fintype, Repr

/-!
Literal presentation data transcribed from the primary bitmap.  It contains
no force readout and no answer-choice label.
-/
structure ThreeChargeRectangleFigure where
  chargeCircleShown : ChargeLabel → Bool
  extraChargeAtLowerRightShown : Bool
  chargeCorner : ChargeLabel → RectangleCorner
  chargeSign : ChargeLabel → FigureChargeSign
  chargeColor : ChargeLabel → FigureChargeColor
  printedChargeNanocoulombs : ChargeLabel → ℝ
  dashedEdgeShown : RectangleEdge → Bool
  diagonalFromLowerLeftToUpperRightShown : Bool
  dimensionLabelCentimeters : DimensionLabelSide → ℝ

/-!
Independent physical quantities and force observables.  The resultant force
is not defined from the recorded answer; the governing-law premises below
relate it to the two independent pair forces.
-/
structure ThreePointChargeForceSetup where
  figure : ThreeChargeRectangleFigure
  horizontalSeparation : LengthQuantity
  verticalSeparation : LengthQuantity
  cornerPosition : RectangleCorner → PlanarPositionQuantity
  charge : ChargeLabel → SignedChargeQuantity
  electromagneticSystem : Electromagnetism.EMSystem
  pairForceOnTarget : SourceCharge → PlanarForceQuantity
  resultantForceOnTarget : PlanarForceQuantity

/-- Position of a named charge in coherent-SI metres. -/
def chargePositionInMeters
    (setup : ThreePointChargeForceSetup) (charge : ChargeLabel) : PlanarVector :=
  positionVectorInMeters
    (setup.cornerPosition (setup.figure.chargeCorner charge))

/-- Position of a named source charge in coherent-SI metres. -/
def sourcePositionInMeters
    (setup : ThreePointChargeForceSetup) (source : SourceCharge) : PlanarVector :=
  chargePositionInMeters setup (sourceChargeLabel source)

/-- Position of the lower-left target charge in coherent-SI metres. -/
def targetPositionInMeters (setup : ThreePointChargeForceSetup) : PlanarVector :=
  chargePositionInMeters setup targetChargeLabel

/-!
Displacement from a source to the target.  This orientation makes
`k q_target q_source r / ‖r‖³` point away for like charges and toward for
unlike charges.
-/
def sourceToTargetDisplacementInMeters
    (setup : ThreePointChargeForceSetup) (source : SourceCharge) : PlanarVector :=
  targetPositionInMeters setup - sourcePositionInMeters setup source

/-! ## Figure/data readouts and governing electrostatics -/

/-!
Facts read from image `898.png`, together with their association to the
dimensionful charges, lengths, and positions.  No resultant-force value
appears here.
-/
structure MatchesSuppliedThreeChargeFigure
    (setup : ThreePointChargeForceSetup) : Prop where
  allChargeCirclesShown : ∀ charge,
    setup.figure.chargeCircleShown charge = true
  lowerRightCornerIsEmpty :
    setup.figure.extraChargeAtLowerRightShown = false
  chargeLocations : ∀ charge,
    setup.figure.chargeCorner charge = expectedChargeCorner charge
  chargeSignGlyphs : ∀ charge,
    setup.figure.chargeSign charge = expectedChargeSign charge
  chargeCircleColors : ∀ charge,
    setup.figure.chargeColor charge = expectedChargeColor charge
  printedChargeLabels : ∀ charge,
    setup.figure.printedChargeNanocoulombs charge =
      expectedChargeInNanocoulombs charge
  physicalChargesMatchLabels : ∀ charge,
    chargeInNanocoulombs (setup.charge charge) =
      setup.figure.printedChargeNanocoulombs charge
  allRectangleEdgesDashed : ∀ edge,
    setup.figure.dashedEdgeShown edge = true
  noDrawnDiagonal :
    setup.figure.diagonalFromLowerLeftToUpperRightShown = false
  topDimensionLabel :
    setup.figure.dimensionLabelCentimeters .topHorizontal = 3
  leftDimensionLabel :
    setup.figure.dimensionLabelCentimeters .leftVertical = 4
  horizontalLengthMatchesLabel :
    lengthInCentimeters setup.horizontalSeparation =
      setup.figure.dimensionLabelCentimeters .topHorizontal
  verticalLengthMatchesLabel :
    lengthInCentimeters setup.verticalSeparation =
      setup.figure.dimensionLabelCentimeters .leftVertical
  lowerLeftAtOrigin :
    positionVectorInMeters (setup.cornerPosition .lowerLeft) = !₂[0, 0]
  upperLeftCoordinates :
    positionVectorInMeters (setup.cornerPosition .upperLeft) =
      !₂[0, lengthInMeters setup.verticalSeparation]
  upperRightCoordinates :
    positionVectorInMeters (setup.cornerPosition .upperRight) =
      !₂[lengthInMeters setup.horizontalSeparation,
        lengthInMeters setup.verticalSeparation]
  lowerRightCoordinates :
    positionVectorInMeters (setup.cornerPosition .lowerRight) =
      !₂[lengthInMeters setup.horizontalSeparation, 0]

/-!
Rounded free-space calibration used in the textbook multiple-choice
calculation.  Physlib's scalar has coherent-SI units `N m² / C²` here.
-/
structure UsesSchoolCoulombConstant
    (setup : ThreePointChargeForceSetup) : Prop where
  coulombConstantCalibration :
    setup.electromagneticSystem.coulombConstant = 9 * (10 : ℝ) ^ 9

/-- Nondegeneracy and positivity conditions selecting the physical branch. -/
structure HasPhysicalThreeChargeParameters
    (setup : ThreePointChargeForceSetup) : Prop where
  horizontalSeparationPositive :
    0 < lengthInMeters setup.horizontalSeparation
  verticalSeparationPositive :
    0 < lengthInMeters setup.verticalSeparation
  eachChargeNonzero : ∀ charge,
    chargeInCoulombs (setup.charge charge) ≠ 0
  coulombConstantPositive :
    0 < setup.electromagneticSystem.coulombConstant
  eachSourceSeparatedFromTarget : ∀ source,
    0 < ‖sourceToTargetDisplacementInMeters setup source‖

/-!
Vector Coulomb law for the force of each source on the target.  For
displacement `r` from source to target, this is
`F = k q_target q_source r / ‖r‖³`.  It is a governing law and contains no
requested numerical magnitude.
-/
structure SatisfiesPairwiseCoulombForceLaw
    (setup : ThreePointChargeForceSetup) : Prop where
  forceFromEachSource : ∀ source,
    forceVectorInNewtons (setup.pairForceOnTarget source) =
      (setup.electromagneticSystem.coulombConstant *
          chargeInCoulombs (setup.charge targetChargeLabel) *
          chargeInCoulombs (setup.charge (sourceChargeLabel source)) /
        ‖sourceToTargetDisplacementInMeters setup source‖ ^ 3) •
          sourceToTargetDisplacementInMeters setup source

/-- The resultant force on the target is the vector sum of both pair forces. -/
structure SatisfiesElectrostaticForceSuperposition
    (setup : ThreePointChargeForceSetup) : Prop where
  resultantIsPairForceSum :
    forceVectorInNewtons setup.resultantForceOnTarget =
      ∑ source : SourceCharge,
        forceVectorInNewtons (setup.pairForceOnTarget source)

/-! ## Derived force and displayed-answer target -/

/-- Labels attached to the four multiple-choice answers. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Force magnitude in newtons printed beside each answer label. -/
def AnswerChoice.forceMagnitudeInNewtons : AnswerChoice → ℝ
  | .A => 725 / 1000000
  | .B => 635 / 1000000
  | .C => 17 / 100000
  | .D => 133 / 1000000

/-- Answer label recorded by the supplied dataset metadata. -/
def recordedDatasetAnswer : AnswerChoice := .C

/-!
A magnitude rounds to a displayed reading at the nearest `10⁻⁵ N`; the
half-step tolerance is `5 * 10⁻⁶ N`.
-/
def RoundsToNearestTenMicroNewtons (actual displayed : ℝ) : Prop :=
  |actual - displayed| < 1 / 200000

/-- A displayed force is strictly nearer than every alternative. -/
def IsUniqueNearestDisplayedForce
    (actual : ℝ) (choice : AnswerChoice) : Prop :=
  ∀ other : AnswerChoice, other ≠ choice →
    |actual - choice.forceMagnitudeInNewtons| <
      |actual - other.forceMagnitudeInNewtons|

/-!
The primary-image coordinates give the vertical `4 cm` displacement to the
positive source and the `3-4-5` diagonal displacement to the negative source.
-/
lemma sourceToTargetDisplacements_from_figure
    (setup : ThreePointChargeForceSetup)
    (_figure : MatchesSuppliedThreeChargeFigure setup) :
    sourceToTargetDisplacementInMeters setup .upperLeft =
        !₂[0, -(4 / 100 : ℝ)] ∧
      sourceToTargetDisplacementInMeters setup .upperRight =
        !₂[-(3 / 100 : ℝ), -(4 / 100 : ℝ)] := by
  have hhorizontal :
      lengthInMeters setup.horizontalSeparation = (3 : ℝ) / 100 := by
    have h := _figure.horizontalLengthMatchesLabel
    rw [_figure.topDimensionLabel] at h
    simp only [lengthInCentimeters] at h
    linarith
  have hvertical :
      lengthInMeters setup.verticalSeparation = (4 : ℝ) / 100 := by
    have h := _figure.verticalLengthMatchesLabel
    rw [_figure.leftDimensionLabel] at h
    simp only [lengthInCentimeters] at h
    linarith
  constructor
  · simp [sourceToTargetDisplacementInMeters, targetPositionInMeters,
      sourcePositionInMeters, chargePositionInMeters, targetChargeLabel,
      sourceChargeLabel, _figure.chargeLocations, expectedChargeCorner,
      _figure.lowerLeftAtOrigin, _figure.upperLeftCoordinates, hvertical]
    ext i
    fin_cases i <;> norm_num
  · simp [sourceToTargetDisplacementInMeters, targetPositionInMeters,
      sourcePositionInMeters, chargePositionInMeters, targetChargeLabel,
      sourceChargeLabel, _figure.chargeLocations, expectedChargeCorner,
      _figure.lowerLeftAtOrigin, _figure.upperRightCoordinates,
      hhorizontal, hvertical]
    ext i
    fin_cases i <;> norm_num

/-!
Coulomb's law and superposition express the resultant in terms of only the
independent source data and the governing electromagnetic constant.
-/
lemma resultantForceOnTarget_eq_coulombSum
    (setup : ThreePointChargeForceSetup)
    (_physical : HasPhysicalThreeChargeParameters setup)
    (_coulomb : SatisfiesPairwiseCoulombForceLaw setup)
    (_superposition : SatisfiesElectrostaticForceSuperposition setup) :
    forceVectorInNewtons setup.resultantForceOnTarget =
      ∑ source : SourceCharge,
        (setup.electromagneticSystem.coulombConstant *
            chargeInCoulombs (setup.charge targetChargeLabel) *
            chargeInCoulombs (setup.charge (sourceChargeLabel source)) /
          ‖sourceToTargetDisplacementInMeters setup source‖ ^ 3) •
            sourceToTargetDisplacementInMeters setup source := by
  simpa only [_coulomb.forceFromEachSource] using
    _superposition.resultantIsPairForceSum

/-!
For the three charge labels and rectangle dimensions in the image, the
resultant magnitude is approximately `1.7465e-4 N`.
-/
lemma resultantForceMagnitude_numericalBounds
    (setup : ThreePointChargeForceSetup)
    (_figure : MatchesSuppliedThreeChargeFigure setup)
    (_constant : UsesSchoolCoulombConstant setup)
    (_physical : HasPhysicalThreeChargeParameters setup)
    (_coulomb : SatisfiesPairwiseCoulombForceLaw setup)
    (_superposition : SatisfiesElectrostaticForceSuperposition setup) :
    (174 : ℝ) / 1000000 <
        forceMagnitudeInNewtons setup.resultantForceOnTarget ∧
      forceMagnitudeInNewtons setup.resultantForceOnTarget <
        (175 : ℝ) / 1000000 := by
  have hq_target :
      chargeInCoulombs (setup.charge targetChargeLabel) = (5 : ℝ) / 10 ^ 9 := by
    have h := (_figure.physicalChargesMatchLabels targetChargeLabel).trans
      (_figure.printedChargeLabels targetChargeLabel)
    norm_num [chargeInNanocoulombs, targetChargeLabel,
      expectedChargeInNanocoulombs] at h ⊢
    linarith
  have hq_left :
      chargeInCoulombs (setup.charge (sourceChargeLabel .upperLeft)) =
        (10 : ℝ) / 10 ^ 9 := by
    have h := (_figure.physicalChargesMatchLabels
      (sourceChargeLabel .upperLeft)).trans
      (_figure.printedChargeLabels (sourceChargeLabel .upperLeft))
    norm_num [chargeInNanocoulombs, sourceChargeLabel,
      expectedChargeInNanocoulombs] at h ⊢
    linarith
  have hq_right :
      chargeInCoulombs (setup.charge (sourceChargeLabel .upperRight)) =
        (-10 : ℝ) / 10 ^ 9 := by
    have h := (_figure.physicalChargesMatchLabels
      (sourceChargeLabel .upperRight)).trans
      (_figure.printedChargeLabels (sourceChargeLabel .upperRight))
    norm_num [chargeInNanocoulombs, sourceChargeLabel,
      expectedChargeInNanocoulombs] at h ⊢
    linarith
  have hdisp := sourceToTargetDisplacements_from_figure setup _figure
  have hnorm_left :
      ‖(!₂[0, -(4 / 100 : ℝ)] : PlanarVector)‖ = (4 : ℝ) / 100 := by
    rw [EuclideanSpace.norm_eq]
    norm_num [Fin.sum_univ_two]
  have hnorm_right :
      ‖(!₂[-(3 / 100 : ℝ), -(4 / 100 : ℝ)] : PlanarVector)‖ =
        (5 : ℝ) / 100 := by
    rw [EuclideanSpace.norm_eq]
    norm_num [Fin.sum_univ_two]
  have hsum (f : SourceCharge → PlanarVector) :
      ∑ source, f source = f .upperLeft + f .upperRight := by
    rw [show (Finset.univ : Finset SourceCharge) =
        {.upperLeft, .upperRight} by
      ext source
      fin_cases source <;> simp]
    simp
  have hresult :=
    resultantForceOnTarget_eq_coulombSum setup _physical _coulomb
      _superposition
  rw [hsum, hq_target, hq_left, hq_right,
    _constant.coulombConstantCalibration, hdisp.1, hdisp.2,
    hnorm_left, hnorm_right] at hresult
  have hforce :
      forceVectorInNewtons setup.resultantForceOnTarget =
        !₂[(108 : ℝ) / 1000000, -(549 : ℝ) / 4000000] := by
    rw [hresult]
    ext i
    fin_cases i <;> norm_num
  unfold forceMagnitudeInNewtons
  rw [hforce]
  have hsquare := EuclideanSpace.norm_sq_eq
    (!₂[(108 : ℝ) / 1000000, -(549 : ℝ) / 4000000] : PlanarVector)
  norm_num [Fin.sum_univ_two] at hsquare
  have hnonnegative :
      0 ≤ ‖(!₂[(108 : ℝ) / 1000000,
        -(549 : ℝ) / 4000000] : PlanarVector)‖ := norm_nonneg _
  constructor <;> nlinarith

/-!
The force on the `+5.0 nC` lower-left charge has magnitude between
`1.74e-4 N` and `1.75e-4 N`.  It therefore rounds to the displayed
`1.7e-4 N`, uniquely selecting answer C.

This is the Lean declaration corresponding to
`thm:physics:phyx_mini_0898:target`.
-/
theorem problem_phyx_mini_0898
    (setup : ThreePointChargeForceSetup)
    (_figure : MatchesSuppliedThreeChargeFigure setup)
    (_constant : UsesSchoolCoulombConstant setup)
    (_physical : HasPhysicalThreeChargeParameters setup)
    (_coulomb : SatisfiesPairwiseCoulombForceLaw setup)
    (_superposition : SatisfiesElectrostaticForceSuperposition setup) :
    (174 : ℝ) / 1000000 <
        forceMagnitudeInNewtons setup.resultantForceOnTarget ∧
      forceMagnitudeInNewtons setup.resultantForceOnTarget <
        (175 : ℝ) / 1000000 ∧
      RoundsToNearestTenMicroNewtons
        (forceMagnitudeInNewtons setup.resultantForceOnTarget)
        recordedDatasetAnswer.forceMagnitudeInNewtons ∧
      IsUniqueNearestDisplayedForce
        (forceMagnitudeInNewtons setup.resultantForceOnTarget)
        recordedDatasetAnswer := by
  have hbounds :=
    resultantForceMagnitude_numericalBounds setup _figure _constant
      _physical _coulomb _superposition
  refine ⟨hbounds.1, hbounds.2, ?_, ?_⟩
  · unfold RoundsToNearestTenMicroNewtons
    norm_num [recordedDatasetAnswer, AnswerChoice.forceMagnitudeInNewtons]
      at hbounds ⊢
    rw [abs_of_pos]
    · linarith
    · linarith
  · unfold IsUniqueNearestDisplayedForce
    intro other hother
    fin_cases other
    · norm_num [recordedDatasetAnswer, AnswerChoice.forceMagnitudeInNewtons]
        at hbounds ⊢
      rw [abs_of_pos, abs_of_neg] <;> linarith
    · norm_num [recordedDatasetAnswer, AnswerChoice.forceMagnitudeInNewtons]
        at hbounds ⊢
      rw [abs_of_pos, abs_of_neg] <;> linarith
    · simp [recordedDatasetAnswer] at hother
    · norm_num [recordedDatasetAnswer, AnswerChoice.forceMagnitudeInNewtons]
        at hbounds ⊢
      rw [abs_of_pos, abs_of_pos] <;> linarith

end PhyXMiniProblems.ProblemPhyXMini0898
