import Mathlib
import Physlib.Electromagnetism.Basic
import Physlib.Units.WithDim.Basic

/- USER: The assigned source file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0834

open Dimension
open scoped BigOperators

/-!
# Electric-field magnitude at the empty corner of a charged rectangle

The primary image is a `5.0 cm` by `3.0 cm` rectangle.  It places a `-10 nC`
charge at the top-left corner, a `+10 nC` charge at the top-right corner, a
`-5.0 nC` charge at the bottom-right corner, and the observation dot at the
uncharged bottom-left corner.

Signed charges, side lengths, and the resultant field magnitude are
unit-independent Physlib quantities.  The planar coordinates below are
explicit metre readouts.  The component values of Physlib's
`Electromagnetism.ElectricField 2` are interpreted as coherent-SI electric
field readouts, in newtons per coulomb (equivalently volts per metre).

Assumption/target split:

* governing laws: the vector point-charge form of Coulomb's law, linear
  superposition, and the relation between the dimensionful magnitude and the
  norm of the resultant field vector;
* previous-part results: none;
* figure/data readouts: all four corner roles, the three charge signs and
  nanocoulomb labels, the `5.0 cm` and `3.0 cm` side labels, and the rectangle
  coordinates;
* target conclusions: the resultant magnitude rounds to
  `8.6 * 10^4 N/C` and answer D is the unique nearest displayed choice.

No target magnitude or answer label occurs in a setup field or theorem
premise.
-/

/-! ## Dimensionful quantities and coherent-SI readouts -/

/-- A nonnegative, unit-independent physical length. -/
abbrev LengthQuantity : Type :=
  Dimensionful (WithDim L𝓭 NNReal)

/-- A signed, unit-independent physical electric charge. -/
abbrev SignedChargeQuantity : Type :=
  Dimensionful (WithDim C𝓭 ℝ)

/-- The physical dimension `M L T⁻² C⁻¹` of electric-field strength. -/
def electricFieldStrengthDimension : Dimension :=
  M𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹ * C𝓭⁻¹

/-- A nonnegative physical electric-field magnitude. -/
abbrev ElectricFieldMagnitudeQuantity : Type :=
  Dimensionful (WithDim electricFieldStrengthDimension NNReal)

/-- Coherent-SI metre readout of a physical length. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  ((length UnitChoices.SI).val : ℝ)

/-- Centimetre readout used by the two dimension labels in the image. -/
def lengthInCentimeters (length : LengthQuantity) : ℝ :=
  100 * lengthInMeters length

/-- Coherent-SI coulomb readout of a signed physical charge. -/
def chargeInCoulombs (charge : SignedChargeQuantity) : ℝ :=
  (charge UnitChoices.SI).val

/-- Nanocoulomb readout used by the three printed charge labels. -/
def chargeInNanocoulombs (charge : SignedChargeQuantity) : ℝ :=
  (10 : ℝ) ^ 9 * chargeInCoulombs charge

/-- Coherent-SI readout of a field magnitude in newtons per coulomb. -/
def fieldMagnitudeInNewtonsPerCoulomb
    (magnitude : ElectricFieldMagnitudeQuantity) : ℝ :=
  ((magnitude UnitChoices.SI).val : ℝ)

/-! ## Figure labels and physical setup -/

/-- The four corners of the dashed rectangle in the supplied figure. -/
inductive RectangleCorner where
  | topLeft
  | topRight
  | bottomRight
  | bottomLeft
  deriving DecidableEq, Fintype, Repr

/-- The three point charges, distinguished by their image locations. -/
inductive SourceCharge where
  | topLeftCharge
  | topRightCharge
  | bottomRightCharge
  deriving DecidableEq, Fintype, Repr

/-- The corner at which each named source appears in the primary image. -/
def expectedSourceCorner : SourceCharge → RectangleCorner
  | .topLeftCharge => .topLeft
  | .topRightCharge => .topRight
  | .bottomRightCharge => .bottomRight

/-- The teal and red fill colours used to distinguish charge signs. -/
inductive FigureChargeColor where
  | lightTeal
  | lightRed
  deriving DecidableEq, Repr

/-- The sign glyph drawn inside a charge circle. -/
inductive FigureChargeSign where
  | minus
  | plus
  deriving DecidableEq, Repr

/-- Colour of each source circle in the supplied raster. -/
def expectedSourceColor : SourceCharge → FigureChargeColor
  | .topLeftCharge => .lightTeal
  | .topRightCharge => .lightRed
  | .bottomRightCharge => .lightTeal

/-- Sign glyph of each source circle in the supplied raster. -/
def expectedSourceSign : SourceCharge → FigureChargeSign
  | .topLeftCharge => .minus
  | .topRightCharge => .plus
  | .bottomRightCharge => .minus

/-- Signed nanocoulomb value printed beside each source. -/
def expectedChargeInNanocoulombs : SourceCharge → ℝ
  | .topLeftCharge => -10
  | .topRightCharge => 10
  | .bottomRightCharge => -5

/-- The two sides carrying numerical dimension labels. -/
inductive FigureDimensionSide where
  | topHorizontal
  | leftVertical
  deriving DecidableEq, Fintype, Repr

/-- Literal presentation data transcribed from image `834.png`. -/
structure RectangularChargeFigure where
  sourceCorner : SourceCharge → RectangleCorner
  sourceColor : SourceCharge → FigureChargeColor
  sourceSign : SourceCharge → FigureChargeSign
  printedChargeNanocoulombs : SourceCharge → ℝ
  blackDotCorner : RectangleCorner
  blackDotShown : Bool
  blackDotHasChargeLabel : Bool
  dashedHorizontalSidesShown : Bool
  dashedVerticalSidesShown : Bool
  dimensionLabelCentimeters : FigureDimensionSide → ℝ

/-- Turn a planar `Space 2` point into its explicitly metre-valued vector. -/
def positionVectorInMeters (point : Space 2) : EuclideanSpace ℝ (Fin 2) :=
  !₂[point.val 0, point.val 1]

/--
Independent physical quantities and fields in the electrostatic setup.

The resultant magnitude is an unknown physical observable.  It is not defined
from a displayed answer; a separate premise below relates it to the norm of
the independently modeled resultant vector field.
-/
structure RectangularPointChargeSetup where
  figure : RectangularChargeFigure
  rectangleWidth : LengthQuantity
  rectangleHeight : LengthQuantity
  cornerPosition : RectangleCorner → Space 2
  charge : SourceCharge → SignedChargeQuantity
  electromagneticSystem : Electromagnetism.EMSystem
  sourceElectricField : SourceCharge → Electromagnetism.ElectricField 2
  resultantElectricField : Electromagnetism.ElectricField 2
  observationTime : Time
  resultantMagnitude : ElectricFieldMagnitudeQuantity

/-- Spatial position of a named source charge. -/
def sourcePosition
    (setup : RectangularPointChargeSetup) (source : SourceCharge) : Space 2 :=
  setup.cornerPosition (setup.figure.sourceCorner source)

/-- Spatial position marked by the black observation dot. -/
def observationPosition (setup : RectangularPointChargeSetup) : Space 2 :=
  setup.cornerPosition setup.figure.blackDotCorner

/-- Displacement from a named charge to an arbitrary field point, in metres. -/
def displacementFromSourceInMeters
    (setup : RectangularPointChargeSetup)
    (source : SourceCharge) (point : Space 2) :
    EuclideanSpace ℝ (Fin 2) :=
  positionVectorInMeters point -
    positionVectorInMeters (sourcePosition setup source)

/-- Resultant field vector at the black dot, in newtons per coulomb. -/
def resultantFieldAtDotInNewtonsPerCoulomb
    (setup : RectangularPointChargeSetup) :
    EuclideanSpace ℝ (Fin 2) :=
  setup.resultantElectricField setup.observationTime
    (observationPosition setup)

/-- Norm of the resultant vector field at the dot, in newtons per coulomb. -/
def resultantFieldNormAtDotInNewtonsPerCoulomb
    (setup : RectangularPointChargeSetup) : ℝ :=
  ‖resultantFieldAtDotInNewtonsPerCoulomb setup‖

/-! ## Problem data and primary-image evidence -/

/--
Literal image evidence, numerical labels, and their association with the
physical charges and rectangle dimensions.  No resultant field value appears
here.
-/
structure MatchesSuppliedChargeRectangleFigure
    (setup : RectangularPointChargeSetup) : Prop where
  sourceLocations : ∀ source,
    setup.figure.sourceCorner source = expectedSourceCorner source
  sourceColors : ∀ source,
    setup.figure.sourceColor source = expectedSourceColor source
  sourceSignGlyphs : ∀ source,
    setup.figure.sourceSign source = expectedSourceSign source
  printedChargeLabels : ∀ source,
    setup.figure.printedChargeNanocoulombs source =
      expectedChargeInNanocoulombs source
  physicalChargesMatchPrintedLabels : ∀ source,
    chargeInNanocoulombs (setup.charge source) =
      setup.figure.printedChargeNanocoulombs source
  observationDotAtBottomLeft :
    setup.figure.blackDotCorner = .bottomLeft
  observationDotIsShown : setup.figure.blackDotShown = true
  observationDotIsUnlabelled :
    setup.figure.blackDotHasChargeLabel = false
  noSourceOccupiesObservationCorner : ∀ source,
    setup.figure.sourceCorner source ≠ setup.figure.blackDotCorner
  horizontalDashedSidesShown :
    setup.figure.dashedHorizontalSidesShown = true
  verticalDashedSidesShown :
    setup.figure.dashedVerticalSidesShown = true
  topSideLabel :
    setup.figure.dimensionLabelCentimeters .topHorizontal = 5
  leftSideLabel :
    setup.figure.dimensionLabelCentimeters .leftVertical = 3
  widthMatchesTopLabel :
    lengthInCentimeters setup.rectangleWidth =
      setup.figure.dimensionLabelCentimeters .topHorizontal
  heightMatchesLeftLabel :
    lengthInCentimeters setup.rectangleHeight =
      setup.figure.dimensionLabelCentimeters .leftVertical
  bottomLeftAtOrigin :
    positionVectorInMeters (setup.cornerPosition .bottomLeft) = !₂[0, 0]
  topLeftCoordinates :
    positionVectorInMeters (setup.cornerPosition .topLeft) =
      !₂[0, lengthInMeters setup.rectangleHeight]
  topRightCoordinates :
    positionVectorInMeters (setup.cornerPosition .topRight) =
      !₂[lengthInMeters setup.rectangleWidth,
        lengthInMeters setup.rectangleHeight]
  bottomRightCoordinates :
    positionVectorInMeters (setup.cornerPosition .bottomRight) =
      !₂[lengthInMeters setup.rectangleWidth, 0]

/--
Independent free-space calibration of Physlib's electromagnetic system.  The
scalar has coherent-SI units `N m²/C²` in the Coulomb formula below.
-/
structure UsesVacuumCoulombConstant
    (setup : RectangularPointChargeSetup) : Prop where
  coulombConstantCalibration :
    setup.electromagneticSystem.coulombConstant = 8.9875517923e9

/-- Positivity and separation conditions selecting the physical branch. -/
structure HasPhysicalRectangleParameters
    (setup : RectangularPointChargeSetup) : Prop where
  widthPositive : 0 < lengthInMeters setup.rectangleWidth
  heightPositive : 0 < lengthInMeters setup.rectangleHeight
  coulombConstantPositive :
    0 < setup.electromagneticSystem.coulombConstant
  sourcesSeparatedFromObservation : ∀ source,
    0 < ‖displacementFromSourceInMeters setup source
      (observationPosition setup)‖

/-! ## Governing electrostatic laws -/

/-!
For a source charge `q` and displacement vector `r` from the source to the
field point, the electric field is `k q r / ‖r‖³`.  This all-points law is
stated only away from the point source and contains no requested result.
-/
structure SatisfiesPointChargeCoulombFieldLaw
    (setup : RectangularPointChargeSetup) : Prop where
  fieldOfEachSource : ∀ source time point,
    point ≠ sourcePosition setup source →
      setup.sourceElectricField source time point =
        (setup.electromagneticSystem.coulombConstant *
            chargeInCoulombs (setup.charge source) /
          ‖displacementFromSourceInMeters setup source point‖ ^ 3) •
            displacementFromSourceInMeters setup source point

/-- The total electric field is the vector sum of all three source fields. -/
structure SatisfiesElectricFieldSuperposition
    (setup : RectangularPointChargeSetup) : Prop where
  resultantIsSourceSum : ∀ time point,
    setup.resultantElectricField time point =
      ∑ source : SourceCharge, setup.sourceElectricField source time point

/-!
The dimensionful scalar observable is the Euclidean magnitude of the modeled
resultant vector at the black dot.  This states a measurement relation, not a
numerical answer.
-/
structure ResultantMagnitudeRepresentsFieldAtDot
    (setup : RectangularPointChargeSetup) : Prop where
  magnitudeReadoutAgreesWithVectorNorm :
    fieldMagnitudeInNewtonsPerCoulomb setup.resultantMagnitude =
      resultantFieldNormAtDotInNewtonsPerCoulomb setup

/-! ## Derived field and displayed-answer target -/

/-- Labels attached to the four multiple-choice answers. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Electric-field magnitude in newtons per coulomb printed by each choice. -/
def AnswerChoice.fieldMagnitudeInNewtonsPerCoulomb : AnswerChoice → ℝ
  | .A => 13 * (10 : ℝ) ^ 4
  | .B => 53 * (10 : ℝ) ^ 3
  | .C => 10 * (10 : ℝ) ^ 4
  | .D => 86 * (10 : ℝ) ^ 3

/-- The answer label recorded by the supplied dataset metadata. -/
def recordedDatasetAnswer : AnswerChoice := .D

/-- A value rounds to a displayed reading at the nearest `10³ N/C`. -/
def RoundsToNearestThousand
    (actual displayed : ℝ) : Prop :=
  |actual - displayed| < 500

/-- A displayed choice is strictly nearer than every alternative. -/
def IsUniqueNearestDisplayedFieldMagnitude
    (actual : ℝ) (choice : AnswerChoice) : Prop :=
  ∀ other : AnswerChoice, other ≠ choice →
    |actual - choice.fieldMagnitudeInNewtonsPerCoulomb| <
      |actual - other.fieldMagnitudeInNewtonsPerCoulomb|

/-!
Coulomb's vector law and superposition give the source-by-source expression
for the field at the observation dot.  The expression contains only the
independent source data and governing constant.
-/
lemma resultantFieldAtDot_eq_coulombSum
    (setup : RectangularPointChargeSetup)
    (_physical : HasPhysicalRectangleParameters setup)
    (_coulomb : SatisfiesPointChargeCoulombFieldLaw setup)
    (_superposition : SatisfiesElectricFieldSuperposition setup) :
    resultantFieldAtDotInNewtonsPerCoulomb setup =
      ∑ source : SourceCharge,
        (setup.electromagneticSystem.coulombConstant *
            chargeInCoulombs (setup.charge source) /
          ‖displacementFromSourceInMeters setup source
              (observationPosition setup)‖ ^ 3) •
            displacementFromSourceInMeters setup source
              (observationPosition setup) := by
  rw [resultantFieldAtDotInNewtonsPerCoulomb,
    _superposition.resultantIsSourceSum]
  apply Finset.sum_congr rfl
  intro source _
  apply _coulomb.fieldOfEachSource
  intro h
  have hSeparated :=
    _physical.sourcesSeparatedFromObservation source
  simp [displacementFromSourceInMeters, h] at hSeparated

/-!
With the three image charges and rectangle dimensions, the resultant magnitude
lies between `85.5 kN/C` and `86.5 kN/C`.  In particular it rounds to the
displayed `8.6 * 10^4 N/C` value.
-/
lemma resultantFieldNormAtDot_numericalBounds
    (setup : RectangularPointChargeSetup)
    (_figure : MatchesSuppliedChargeRectangleFigure setup)
    (_constant : UsesVacuumCoulombConstant setup)
    (_physical : HasPhysicalRectangleParameters setup)
    (_coulomb : SatisfiesPointChargeCoulombFieldLaw setup)
    (_superposition : SatisfiesElectricFieldSuperposition setup) :
    (85500 : ℝ) < resultantFieldNormAtDotInNewtonsPerCoulomb setup ∧
      resultantFieldNormAtDotInNewtonsPerCoulomb setup < 86500 := by
  have hWidth : lengthInMeters setup.rectangleWidth = (1 : ℝ) / 20 := by
    have h := _figure.widthMatchesTopLabel
    rw [_figure.topSideLabel] at h
    simp only [lengthInCentimeters] at h
    linarith
  have hHeight : lengthInMeters setup.rectangleHeight = (3 : ℝ) / 100 := by
    have h := _figure.heightMatchesLeftLabel
    rw [_figure.leftSideLabel] at h
    simp only [lengthInCentimeters] at h
    linarith
  have hChargeTopLeft :
      chargeInCoulombs (setup.charge .topLeftCharge) =
        -(1 : ℝ) / 100000000 := by
    have h := _figure.physicalChargesMatchPrintedLabels .topLeftCharge
    rw [_figure.printedChargeLabels] at h
    norm_num [chargeInNanocoulombs,
      expectedChargeInNanocoulombs] at h ⊢
    linarith
  have hChargeTopRight :
      chargeInCoulombs (setup.charge .topRightCharge) =
        (1 : ℝ) / 100000000 := by
    have h := _figure.physicalChargesMatchPrintedLabels .topRightCharge
    rw [_figure.printedChargeLabels] at h
    norm_num [chargeInNanocoulombs,
      expectedChargeInNanocoulombs] at h ⊢
    linarith
  have hChargeBottomRight :
      chargeInCoulombs (setup.charge .bottomRightCharge) =
        -(1 : ℝ) / 200000000 := by
    have h := _figure.physicalChargesMatchPrintedLabels .bottomRightCharge
    rw [_figure.printedChargeLabels] at h
    norm_num [chargeInNanocoulombs,
      expectedChargeInNanocoulombs] at h ⊢
    linarith
  have hDisplacementTopLeft :
      displacementFromSourceInMeters setup .topLeftCharge
          (observationPosition setup) =
        !₂[(0 : ℝ), -(3 : ℝ) / 100] := by
    rw [displacementFromSourceInMeters, observationPosition, sourcePosition,
      _figure.observationDotAtBottomLeft,
      _figure.sourceLocations, expectedSourceCorner,
      _figure.bottomLeftAtOrigin, _figure.topLeftCoordinates, hHeight]
    ext i
    fin_cases i <;> norm_num
  have hDisplacementTopRight :
      displacementFromSourceInMeters setup .topRightCharge
          (observationPosition setup) =
        !₂[-(1 : ℝ) / 20, -(3 : ℝ) / 100] := by
    rw [displacementFromSourceInMeters, observationPosition, sourcePosition,
      _figure.observationDotAtBottomLeft,
      _figure.sourceLocations, expectedSourceCorner,
      _figure.bottomLeftAtOrigin, _figure.topRightCoordinates, hWidth, hHeight]
    ext i
    fin_cases i <;> norm_num
  have hDisplacementBottomRight :
      displacementFromSourceInMeters setup .bottomRightCharge
          (observationPosition setup) =
        !₂[-(1 : ℝ) / 20, (0 : ℝ)] := by
    rw [displacementFromSourceInMeters, observationPosition, sourcePosition,
      _figure.observationDotAtBottomLeft,
      _figure.sourceLocations, expectedSourceCorner,
      _figure.bottomLeftAtOrigin, _figure.bottomRightCoordinates, hWidth]
    ext i
    fin_cases i <;> norm_num
  have hNormTopLeft :
      ‖(!₂[(0 : ℝ), -(3 : ℝ) / 100] :
          EuclideanSpace ℝ (Fin 2))‖ = 3 / 100 := by
    rw [EuclideanSpace.norm_eq]
    norm_num [Real.norm_eq_abs, Fin.sum_univ_two]
  have hNormTopRight :
      ‖(!₂[-(1 : ℝ) / 20, -(3 : ℝ) / 100] :
          EuclideanSpace ℝ (Fin 2))‖ =
        Real.sqrt 34 / 100 := by
    have hsq :
        ‖(!₂[-(1 : ℝ) / 20, -(3 : ℝ) / 100] :
            EuclideanSpace ℝ (Fin 2))‖ ^ 2 =
          (34 : ℝ) / 10000 := by
      rw [EuclideanSpace.norm_sq_eq]
      norm_num [Real.norm_eq_abs, Fin.sum_univ_two]
    have hsqrt : (Real.sqrt (34 : ℝ)) ^ 2 = 34 :=
      Real.sq_sqrt (by norm_num)
    have hnorm_nonneg :
        0 ≤ ‖(!₂[-(1 : ℝ) / 20, -(3 : ℝ) / 100] :
          EuclideanSpace ℝ (Fin 2))‖ := norm_nonneg _
    have hsqrt_nonneg : 0 ≤ Real.sqrt (34 : ℝ) :=
      Real.sqrt_nonneg _
    nlinarith
  have hNormBottomRight :
      ‖(!₂[-(1 : ℝ) / 20, (0 : ℝ)] :
          EuclideanSpace ℝ (Fin 2))‖ = 1 / 20 := by
    rw [EuclideanSpace.norm_eq]
    norm_num [Real.norm_eq_abs, Fin.sum_univ_two]
  have hSourceSum
      (f : SourceCharge → EuclideanSpace ℝ (Fin 2)) :
      ∑ source : SourceCharge, f source =
        f .topLeftCharge + f .topRightCharge + f .bottomRightCharge := by
    rw [show (Finset.univ : Finset SourceCharge) =
      {.topLeftCharge, .topRightCharge, .bottomRightCharge} by decide]
    simp
    abel
  have hField := resultantFieldAtDot_eq_coulombSum
    setup _physical _coulomb _superposition
  rw [hSourceSum, _constant.coulombConstantCalibration,
    hChargeTopLeft, hChargeTopRight, hChargeBottomRight,
    hDisplacementTopLeft, hDisplacementTopRight,
    hDisplacementBottomRight, hNormTopLeft, hNormTopRight,
    hNormBottomRight] at hField
  have hsqrt_sq : (Real.sqrt (34 : ℝ)) ^ 2 = 34 :=
    Real.sq_sqrt (by norm_num)
  have hsqrt_pos : 0 < Real.sqrt (34 : ℝ) :=
    Real.sqrt_pos.2 (by norm_num)
  have hFieldComponents :
      resultantFieldAtDotInNewtonsPerCoulomb setup =
        !₂[
          89875517923 / 5000000 -
            89875517923 * Real.sqrt 34 / 23120000,
          89875517923 / 900000 -
            269626553769 * Real.sqrt 34 / 115600000] := by
    rw [hField]
    ext i
    fin_cases i <;> simp <;> field_simp <;> nlinarith
  have hNormSq :
      resultantFieldNormAtDotInNewtonsPerCoulomb setup ^ 2 =
        (89875517923 / 5000000 -
            89875517923 * Real.sqrt 34 / 23120000) ^ 2 +
          (89875517923 / 900000 -
            269626553769 * Real.sqrt 34 / 115600000) ^ 2 := by
    rw [resultantFieldNormAtDotInNewtonsPerCoulomb,
      hFieldComponents, EuclideanSpace.norm_sq_eq]
    simp [Real.norm_eq_abs, Fin.sum_univ_two, sq_abs]
  have hSqrtLower :
      (58309 : ℝ) / 10000 < Real.sqrt 34 := by
    rw [Real.lt_sqrt (by norm_num)]
    norm_num
  have hSqrtUpper :
      Real.sqrt 34 < (5831 : ℝ) / 1000 := by
    rw [Real.sqrt_lt (by norm_num) (by norm_num)]
    norm_num
  have hNormSqLower :
      (85500 : ℝ) ^ 2 <
        resultantFieldNormAtDotInNewtonsPerCoulomb setup ^ 2 := by
    rw [hNormSq]
    nlinarith [hsqrt_sq]
  have hNormSqUpper :
      resultantFieldNormAtDotInNewtonsPerCoulomb setup ^ 2 <
        (86500 : ℝ) ^ 2 := by
    rw [hNormSq]
    nlinarith [hsqrt_sq]
  have hNormNonnegative :
      0 ≤ resultantFieldNormAtDotInNewtonsPerCoulomb setup :=
    norm_nonneg _
  constructor <;> nlinarith

/-!
The three Coulomb fields add to a magnitude of approximately
`8.64 * 10^4 N/C`.  Thus the value rounds to `8.6 * 10^4 N/C`, and D is the
unique nearest displayed answer.

This is the Lean declaration corresponding to
`thm:physics:phyx_mini_0834:target`.
-/
theorem problem_phyx_mini_0834
    (setup : RectangularPointChargeSetup)
    (hFigure : MatchesSuppliedChargeRectangleFigure setup)
    (hConstant : UsesVacuumCoulombConstant setup)
    (hPhysical : HasPhysicalRectangleParameters setup)
    (hCoulomb : SatisfiesPointChargeCoulombFieldLaw setup)
    (hSuperposition : SatisfiesElectricFieldSuperposition setup)
    (hMagnitude : ResultantMagnitudeRepresentsFieldAtDot setup) :
    (85500 : ℝ) <
        fieldMagnitudeInNewtonsPerCoulomb setup.resultantMagnitude ∧
      fieldMagnitudeInNewtonsPerCoulomb setup.resultantMagnitude < 86500 ∧
      RoundsToNearestThousand
        (fieldMagnitudeInNewtonsPerCoulomb setup.resultantMagnitude)
        recordedDatasetAnswer.fieldMagnitudeInNewtonsPerCoulomb ∧
      IsUniqueNearestDisplayedFieldMagnitude
        (fieldMagnitudeInNewtonsPerCoulomb setup.resultantMagnitude)
        recordedDatasetAnswer := by
  have hBounds := resultantFieldNormAtDot_numericalBounds
    setup hFigure hConstant hPhysical hCoulomb hSuperposition
  have hLower :
      (85500 : ℝ) <
        fieldMagnitudeInNewtonsPerCoulomb setup.resultantMagnitude := by
    rw [hMagnitude.magnitudeReadoutAgreesWithVectorNorm]
    exact hBounds.1
  have hUpper :
      fieldMagnitudeInNewtonsPerCoulomb setup.resultantMagnitude <
        (86500 : ℝ) := by
    rw [hMagnitude.magnitudeReadoutAgreesWithVectorNorm]
    exact hBounds.2
  have hRounded :
      |fieldMagnitudeInNewtonsPerCoulomb setup.resultantMagnitude -
        86000| < (500 : ℝ) := by
    rw [abs_lt]
    constructor <;> linarith
  refine ⟨hLower, hUpper, ?_, ?_⟩
  · norm_num [RoundsToNearestThousand, recordedDatasetAnswer,
      AnswerChoice.fieldMagnitudeInNewtonsPerCoulomb]
    exact hRounded
  · intro other hOther
    fin_cases other
    · have hDistance :
          |fieldMagnitudeInNewtonsPerCoulomb setup.resultantMagnitude -
            130000| =
              130000 -
                fieldMagnitudeInNewtonsPerCoulomb
                  setup.resultantMagnitude := by
        rw [abs_of_neg (by linarith)]
        ring
      norm_num [recordedDatasetAnswer,
        AnswerChoice.fieldMagnitudeInNewtonsPerCoulomb]
      rw [hDistance]
      exact lt_trans hRounded (by linarith)
    · have hDistance :
          |fieldMagnitudeInNewtonsPerCoulomb setup.resultantMagnitude -
            53000| =
              fieldMagnitudeInNewtonsPerCoulomb
                setup.resultantMagnitude - 53000 := by
        rw [abs_of_pos (by linarith)]
      norm_num [recordedDatasetAnswer,
        AnswerChoice.fieldMagnitudeInNewtonsPerCoulomb]
      rw [hDistance]
      exact lt_trans hRounded (by linarith)
    · have hDistance :
          |fieldMagnitudeInNewtonsPerCoulomb setup.resultantMagnitude -
            100000| =
              100000 -
                fieldMagnitudeInNewtonsPerCoulomb
                  setup.resultantMagnitude := by
        rw [abs_of_neg (by linarith)]
        ring
      norm_num [recordedDatasetAnswer,
        AnswerChoice.fieldMagnitudeInNewtonsPerCoulomb]
      rw [hDistance]
      exact lt_trans hRounded (by linarith)
    · exact (hOther rfl).elim

end PhyXMiniProblems.ProblemPhyXMini0834
