import Mathlib
import Physlib.Electromagnetism.Basic
import Physlib.Units.WithDim.Basic

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0832

open Dimension
open scoped BigOperators

/-!
# Electric field at the unoccupied corner of a charged rectangle

The primary image shows three point charges at the top-left, top-right, and
bottom-left corners of a rectangle.  A black observation dot occupies the
bottom-right corner.  The horizontal and vertical side lengths are `2.0 cm`
and `4.0 cm`; the three signed charge labels are `-5.0 nC`, `+10 nC`, and
`+5.0 nC`.

Charge, length, and electric-field strength are represented by Physlib
dimensionful quantities.  The real numbers below occur only as calibrated SI
readouts or as coordinates in a metre-calibrated chart on `Space 2`.
Physlib's `Electromagnetism.ElectricField 2` retains the vector-field role of
each source contribution and of their resultant.

Assumption/target split:

* governing laws: the signed vector form of Coulomb's point-charge field law,
  vector superposition, and the norm relation between the resultant vector
  field and its dimensionful strength;
* previous-part results: none;
* figure/data readouts: charge labels, rectangle side lengths, corner
  coordinates, dashed rectangle edges, the observation dot, and the standard
  SI calibration of Coulomb's constant;
* current conclusions: a tight enclosure for the resultant magnitude and the
  fact that displayed answer D, `1.1 * 10^5 N/C`, is closest to it.
-/

/-! ## Dimensionful quantities and calibrated readouts -/

/-- A nonnegative physical length. -/
abbrev LengthQuantity : Type :=
  Dimensionful (WithDim L𝓭 NNReal)

/-- A signed electric charge, rather than a bare scalar charge alias. -/
abbrev SignedChargeQuantity : Type :=
  Dimensionful (WithDim C𝓭 ℝ)

/-- The dimension `M L T⁻² C⁻¹` of electric-field strength. -/
def electricFieldStrengthDimension : Dimension :=
  M𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹ * C𝓭⁻¹

/-- A nonnegative physical magnitude of electric-field strength. -/
abbrev ElectricFieldStrengthQuantity : Type :=
  Dimensionful (WithDim electricFieldStrengthDimension NNReal)

/-- Read a physical length in a selected unit. -/
def lengthReadout (unit : LengthUnit) (length : LengthQuantity) : ℝ :=
  ((length {UnitChoices.SI with length := unit}).val : ℝ)

/-- SI readout of a signed charge, in coulombs. -/
def signedChargeInCoulombs (charge : SignedChargeQuantity) : ℝ :=
  (charge UnitChoices.SI).val

/-- SI readout of electric-field strength, in newtons per coulomb. -/
def electricFieldStrengthInNewtonsPerCoulomb
    (strength : ElectricFieldStrengthQuantity) : ℝ :=
  ((strength UnitChoices.SI).val : ℝ)

/-! ## Named charges, figure corners, and physical setup -/

/-- The three charged corners visible in the image. -/
inductive SourceCharge where
  | topLeft
  | topRight
  | bottomLeft
  deriving DecidableEq, Fintype, Repr

/-- The four corners of the dashed rectangle. -/
inductive FigureCorner where
  | topLeft
  | topRight
  | bottomLeft
  | bottomRight
  deriving DecidableEq, Fintype, Repr

/-- The figure corner occupied by each named source charge. -/
def sourceCorner : SourceCharge → FigureCorner
  | .topLeft => .topLeft
  | .topRight => .topRight
  | .bottomLeft => .bottomLeft

/-!
Typed content of the primary raster.  Its length and charge labels are
physical quantities; their numerical readouts are imposed separately by
`MatchesPrimaryFigure832`.
-/
structure RectangularPointChargeFigure where
  sourceCorner : SourceCharge → FigureCorner
  signedChargeLabel : SourceCharge → SignedChargeQuantity
  horizontalSeparationLabel : LengthQuantity
  verticalSeparationLabel : LengthQuantity
  observationDotCorner : FigureCorner
  dashedRectangleEdgesShown : Bool

/-!
The electrostatic system and its independent observable.  In particular,
`resultantFieldStrengthAtDot` is not defined from answer D or from any
displayed numerical choice.
-/
structure RectangularPointChargeSetup where
  sourceCharge : SourceCharge → SignedChargeQuantity
  sourcePosition : SourceCharge → Space 2
  observationPosition : Space 2
  rectangleWidth : LengthQuantity
  rectangleHeight : LengthQuantity
  electromagneticSystem : Electromagnetism.EMSystem
  contributionField : SourceCharge → Electromagnetism.ElectricField 2
  resultantField : Electromagnetism.ElectricField 2
  resultantFieldStrengthAtDot : ElectricFieldStrengthQuantity
  figure : RectangularPointChargeFigure

/-! ## Metre-coordinate chart and field readouts -/

/-- Horizontal coordinate in the metre-calibrated chart used for the figure. -/
def xCoordinateInMeters (position : Space 2) : ℝ := position 0

/-- Vertical coordinate in the metre-calibrated chart used for the figure. -/
def yCoordinateInMeters (position : Space 2) : ℝ := position 1

/-- Magnitude of the resultant vector-field readout at a spacetime point. -/
def resultantMagnitudeInNewtonsPerCoulombAt
    (setup : RectangularPointChargeSetup)
    (time : Time) (position : Space 2) : ℝ :=
  ‖setup.resultantField time position‖

/-!
The signed Coulomb-law vector produced by one source at a proposed position.
Coordinates are metre readouts, charge is read in coulombs, and Physlib's
Coulomb constant is read in the corresponding coherent SI units.
-/
def coulombFieldVectorAt
    (setup : RectangularPointChargeSetup)
    (source : SourceCharge) (position : Space 2) :
    EuclideanSpace ℝ (Fin 2) :=
  let displacement := position -ᵥ setup.sourcePosition source
  (setup.electromagneticSystem.coulombConstant *
      signedChargeInCoulombs (setup.sourceCharge source) /
      ‖displacement‖ ^ 3) • displacement

/-! ## Figure evidence, reference data, and governing laws -/

/-!
Literal charge, distance, corner, and presentation readouts from image 832.
The bottom-left corner is chosen as the coordinate origin.  No resultant
field strength or answer choice occurs in this figure predicate.
-/
structure MatchesPrimaryFigure832
    (setup : RectangularPointChargeSetup) : Prop where
  figureSourceCorners :
    ∀ source, setup.figure.sourceCorner source = sourceCorner source
  figureChargeLabelsArePhysical :
    ∀ source, setup.figure.signedChargeLabel source = setup.sourceCharge source
  horizontalLabelIsPhysicalWidth :
    setup.figure.horizontalSeparationLabel = setup.rectangleWidth
  verticalLabelIsPhysicalHeight :
    setup.figure.verticalSeparationLabel = setup.rectangleHeight
  dotIsAtBottomRight : setup.figure.observationDotCorner = .bottomRight
  dashedRectangleEdges : setup.figure.dashedRectangleEdgesShown = true
  topLeftChargeNanocoulombs :
    signedChargeInCoulombs (setup.sourceCharge .topLeft) = -5e-9
  topRightChargeNanocoulombs :
    signedChargeInCoulombs (setup.sourceCharge .topRight) = 10e-9
  bottomLeftChargeNanocoulombs :
    signedChargeInCoulombs (setup.sourceCharge .bottomLeft) = 5e-9
  horizontalSeparationCentimeters :
    lengthReadout LengthUnit.centimeters setup.rectangleWidth = 2
  verticalSeparationCentimeters :
    lengthReadout LengthUnit.centimeters setup.rectangleHeight = 4
  horizontalSeparationMeters :
    lengthReadout LengthUnit.meters setup.rectangleWidth = 2 / 100
  verticalSeparationMeters :
    lengthReadout LengthUnit.meters setup.rectangleHeight = 4 / 100
  bottomLeftCoordinates :
    xCoordinateInMeters (setup.sourcePosition .bottomLeft) = 0 ∧
      yCoordinateInMeters (setup.sourcePosition .bottomLeft) = 0
  bottomRightDotCoordinates :
    xCoordinateInMeters setup.observationPosition = 2 / 100 ∧
      yCoordinateInMeters setup.observationPosition = 0
  topLeftCoordinates :
    xCoordinateInMeters (setup.sourcePosition .topLeft) = 0 ∧
      yCoordinateInMeters (setup.sourcePosition .topLeft) = 4 / 100
  topRightCoordinates :
    xCoordinateInMeters (setup.sourcePosition .topRight) = 2 / 100 ∧
      yCoordinateInMeters (setup.sourcePosition .topRight) = 4 / 100

/-- Standard electrostatic reference data used for the numerical comparison. -/
structure UsesStandardCoulombConstant
    (setup : RectangularPointChargeSetup) : Prop where
  coulombConstantCalibration :
    setup.electromagneticSystem.coulombConstant = 8.9875517923e9

/-- Positivity and noncoincidence conditions for the physical configuration. -/
structure HasPhysicalRectangularChargeParameters
    (setup : RectangularPointChargeSetup) : Prop where
  positiveWidth : 0 < lengthReadout LengthUnit.meters setup.rectangleWidth
  positiveHeight : 0 < lengthReadout LengthUnit.meters setup.rectangleHeight
  positiveCoulombConstant :
    0 < setup.electromagneticSystem.coulombConstant
  observationAwayFromSources :
    ∀ source, setup.observationPosition ≠ setup.sourcePosition source

/-!
Coulomb's point-charge field law and vector superposition.  The first law is
stated at every nonsource point and every time, not only at the target dot.
The last field connects the independent dimensionful strength observable to
the norm of the resultant vector field; it does not prescribe a number.
-/
structure SatisfiesCoulombFieldAndSuperpositionLaws
    (setup : RectangularPointChargeSetup) : Prop where
  pointChargeCoulombField : ∀ source time position,
    position ≠ setup.sourcePosition source →
      setup.contributionField source time position =
        coulombFieldVectorAt setup source position
  vectorSuperposition : ∀ time position,
    setup.resultantField time position =
      ∑ source : SourceCharge, setup.contributionField source time position
  resultantStrengthIsNormAtDot : ∀ time,
    electricFieldStrengthInNewtonsPerCoulomb
        setup.resultantFieldStrengthAtDot =
      resultantMagnitudeInNewtonsPerCoulombAt
        setup time setup.observationPosition

/-! ## Displayed choices and current target -/

/-- Labels attached to the four displayed electric-field choices. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Electric-field strength in `N/C` printed beside each answer label. -/
def displayedFieldStrengthInNewtonsPerCoulomb : AnswerChoice → ℝ
  | .A => 1.3 * 10 ^ 5
  | .B => 5.3 * 10 ^ 5
  | .C => 1.0 * 10 ^ 5
  | .D => 1.1 * 10 ^ 5

/-!
A displayed choice is closest when its printed magnitude is at least as close
to the physical resultant strength as every alternative.  This models the
resolution of the multiple-choice question without defining the physical
field strength from the recorded answer.
-/
def IsClosestDisplayedFieldStrength
    (strength : ElectricFieldStrengthQuantity)
    (choice : AnswerChoice) : Prop :=
  ∀ alternative,
    |electricFieldStrengthInNewtonsPerCoulomb strength -
        displayedFieldStrengthInNewtonsPerCoulomb choice| ≤
      |electricFieldStrengthInNewtonsPerCoulomb strength -
        displayedFieldStrengthInNewtonsPerCoulomb alternative|

/-!
The three Coulomb contributions give a resultant magnitude between
`1.08 * 10^5 N/C` and `1.09 * 10^5 N/C` before rounding.
-/
lemma resultant_field_magnitude_bounds
    (setup : RectangularPointChargeSetup)
    (hFigure : MatchesPrimaryFigure832 setup)
    (hReference : UsesStandardCoulombConstant setup)
    (hPhysical : HasPhysicalRectangularChargeParameters setup)
    (hLaws : SatisfiesCoulombFieldAndSuperpositionLaws setup) :
    108000 < electricFieldStrengthInNewtonsPerCoulomb
        setup.resultantFieldStrengthAtDot ∧
      electricFieldStrengthInNewtonsPerCoulomb
          setup.resultantFieldStrengthAtDot < 109000 := by
  have hField :
      setup.resultantField (0 : Time) setup.observationPosition =
        ∑ source : SourceCharge,
          coulombFieldVectorAt setup source setup.observationPosition := by
    rw [hLaws.vectorSuperposition]
    apply Finset.sum_congr rfl
    intro source _
    exact hLaws.pointChargeCoulombField source 0 setup.observationPosition
      (hPhysical.observationAwayFromSources source)
  rw [hLaws.resultantStrengthIsNormAtDot 0]
  rw [resultantMagnitudeInNewtonsPerCoulombAt, hField]
  let v :=
    ∑ source : SourceCharge,
      coulombFieldVectorAt setup source setup.observationPosition
  change 108000 < ‖v‖ ∧ ‖v‖ < 109000
  have hObsX : setup.observationPosition 0 = 2 / 100 := by
    simpa [xCoordinateInMeters] using hFigure.bottomRightDotCoordinates.1
  have hObsY : setup.observationPosition 1 = 0 := by
    simpa [yCoordinateInMeters] using hFigure.bottomRightDotCoordinates.2
  have hBLX : setup.sourcePosition .bottomLeft 0 = 0 := by
    simpa [xCoordinateInMeters] using hFigure.bottomLeftCoordinates.1
  have hBLY : setup.sourcePosition .bottomLeft 1 = 0 := by
    simpa [yCoordinateInMeters] using hFigure.bottomLeftCoordinates.2
  have hTLX : setup.sourcePosition .topLeft 0 = 0 := by
    simpa [xCoordinateInMeters] using hFigure.topLeftCoordinates.1
  have hTLY : setup.sourcePosition .topLeft 1 = 4 / 100 := by
    simpa [yCoordinateInMeters] using hFigure.topLeftCoordinates.2
  have hTRX : setup.sourcePosition .topRight 0 = 2 / 100 := by
    simpa [xCoordinateInMeters] using hFigure.topRightCoordinates.1
  have hTRY : setup.sourcePosition .topRight 1 = 4 / 100 := by
    simpa [yCoordinateInMeters] using hFigure.topRightCoordinates.2
  have hNormBL :
      ‖setup.observationPosition -ᵥ setup.sourcePosition .bottomLeft‖ =
        (1 : ℝ) / 50 := by
    have hsq :
        ‖setup.observationPosition -ᵥ setup.sourcePosition .bottomLeft‖ ^ 2 =
          (1 : ℝ) / 2500 := by
      rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_two]
      simp [Space.vsub_apply, hObsX, hObsY, hBLX, hBLY]
      norm_num
    nlinarith [norm_nonneg
      (setup.observationPosition -ᵥ setup.sourcePosition .bottomLeft)]
  have hNormTR :
      ‖setup.observationPosition -ᵥ setup.sourcePosition .topRight‖ =
        (1 : ℝ) / 25 := by
    have hsq :
        ‖setup.observationPosition -ᵥ setup.sourcePosition .topRight‖ ^ 2 =
          (1 : ℝ) / 625 := by
      rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_two]
      simp [Space.vsub_apply, hObsX, hObsY, hTRX, hTRY]
      norm_num
    nlinarith [norm_nonneg
      (setup.observationPosition -ᵥ setup.sourcePosition .topRight)]
  let r :=
    ‖setup.observationPosition -ᵥ setup.sourcePosition .topLeft‖
  have hrSq : r ^ 2 = (1 : ℝ) / 500 := by
    dsimp [r]
    rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_two]
    simp [Space.vsub_apply, hObsX, hObsY, hTLX, hTLY]
    norm_num
  have hrNonneg : 0 ≤ r := norm_nonneg _
  have hrPos : 0 < r := by
    nlinarith only [hrSq, hrNonneg]
  have hvX :
      v 0 =
        (11234439740375 : ℝ) / 100000000 -
          ((89875517923 : ℝ) / 100000000000) * (1 / r ^ 3) := by
    dsimp [v]
    rw [show (Finset.univ : Finset SourceCharge) =
      {.topLeft, .topRight, .bottomLeft} by decide]
    simp [coulombFieldVectorAt, hReference.coulombConstantCalibration,
      hFigure.topLeftChargeNanocoulombs,
      hFigure.topRightChargeNanocoulombs,
      hFigure.bottomLeftChargeNanocoulombs, Space.vsub_apply,
      hObsX, hBLX, hTLX, hTRX, hNormBL, hNormTR, r]
    ring
  have hvY :
      v 1 =
        -(56172198701875 : ℝ) / 1000000000 +
          ((179751035846 : ℝ) / 100000000000) * (1 / r ^ 3) := by
    dsimp [v]
    rw [show (Finset.univ : Finset SourceCharge) =
      {.topLeft, .topRight, .bottomLeft} by decide]
    simp [coulombFieldVectorAt, hReference.coulombConstantCalibration,
      hFigure.topLeftChargeNanocoulombs,
      hFigure.topRightChargeNanocoulombs,
      hFigure.bottomLeftChargeNanocoulombs, Space.vsub_apply,
      hObsY, hBLY, hTLY, hTRY, hNormBL, hNormTR, r]
    ring
  have hrLower : (4472 : ℝ) / 100000 < r := by
    nlinarith only [hrSq, hrNonneg]
  have hrUpper : r < (4473 : ℝ) / 100000 := by
    nlinarith only [hrSq, hrNonneg]
  have hrCubeLower :
      ((4472 : ℝ) / 100000) ^ 3 < r ^ 3 :=
    pow_lt_pow_left₀ hrLower (by norm_num) (by norm_num)
  have hrCubeUpper :
      r ^ 3 < ((4473 : ℝ) / 100000) ^ 3 :=
    pow_lt_pow_left₀ hrUpper hrNonneg (by norm_num)
  have hInvLower : (11173 : ℝ) < 1 / r ^ 3 := by
    have hReciprocal :
        1 / (((4473 : ℝ) / 100000) ^ 3) < 1 / r ^ 3 :=
      one_div_lt_one_div_of_lt (by positivity) hrCubeUpper
    have hNumeric :
        (11173 : ℝ) < 1 / (((4473 : ℝ) / 100000) ^ 3) := by
      norm_num
    linarith
  have hInvUpper : 1 / r ^ 3 < (11182 : ℝ) := by
    have hReciprocal :
        1 / r ^ 3 < 1 / (((4472 : ℝ) / 100000) ^ 3) :=
      one_div_lt_one_div_of_lt (by positivity) hrCubeLower
    have hNumeric :
        1 / (((4472 : ℝ) / 100000) ^ 3) < (11182 : ℝ) := by
      norm_num
    linarith
  have hvXLower : (102294 : ℝ) < v 0 := by
    rw [hvX]
    linarith only [hInvUpper]
  have hvXUpper : v 0 < (102303 : ℝ) := by
    rw [hvX]
    linarith only [hInvLower]
  have hvYLower : (-36089 : ℝ) < v 1 := by
    rw [hvY]
    linarith only [hInvLower]
  have hvYUpper : v 1 < (-36072 : ℝ) := by
    rw [hvY]
    linarith only [hInvUpper]
  have hvNormSq :
      ‖v‖ ^ 2 = (v 0) ^ 2 + (v 1) ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_two]
    simp [Real.norm_eq_abs, sq_abs]
  have hvXSqLower : (102294 : ℝ) ^ 2 < (v 0) ^ 2 := by
    nlinarith only [hvXLower, sq_nonneg (v 0 - 102294)]
  have hvXSqUpper : (v 0) ^ 2 < (102303 : ℝ) ^ 2 := by
    nlinarith only [hvXLower, hvXUpper, sq_nonneg (v 0 - 102303)]
  have hvYSqLower : (36072 : ℝ) ^ 2 < (v 1) ^ 2 := by
    nlinarith only [hvYUpper, sq_nonneg (v 1 + 36072)]
  have hvYSqUpper : (v 1) ^ 2 < (36089 : ℝ) ^ 2 := by
    nlinarith only [hvYLower, hvYUpper, sq_nonneg (v 1 + 36089)]
  have hvNonneg : 0 ≤ ‖v‖ := norm_nonneg _
  constructor
  · nlinarith only [hvNormSq, hvXSqLower, hvYSqLower, hvNonneg]
  · nlinarith only [hvNormSq, hvXSqUpper, hvYSqUpper, hvNonneg]

/-!
Therefore the closest displayed magnitude is answer D,
`1.1 * 10^5 N/C`.
-/
theorem electric_field_magnitude_at_dot_selects_D
    (setup : RectangularPointChargeSetup)
    (hFigure : MatchesPrimaryFigure832 setup)
    (hReference : UsesStandardCoulombConstant setup)
    (hPhysical : HasPhysicalRectangularChargeParameters setup)
    (hLaws : SatisfiesCoulombFieldAndSuperpositionLaws setup) :
    IsClosestDisplayedFieldStrength setup.resultantFieldStrengthAtDot .D := by
  obtain ⟨hLower, hUpper⟩ :=
    resultant_field_magnitude_bounds setup hFigure hReference hPhysical hLaws
  unfold IsClosestDisplayedFieldStrength
  intro alternative
  cases alternative with
  | A =>
      norm_num [displayedFieldStrengthInNewtonsPerCoulomb]
      rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
      linarith
  | B =>
      norm_num [displayedFieldStrengthInNewtonsPerCoulomb]
      rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
      linarith
  | C =>
      norm_num [displayedFieldStrengthInNewtonsPerCoulomb]
      rw [abs_of_nonpos (by linarith), abs_of_nonneg (by linarith)]
      linarith
  | D =>
      exact le_rfl

end PhyXMiniProblems.ProblemPhyXMini0832
