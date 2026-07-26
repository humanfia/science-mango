import Mathlib
import Physlib.Electromagnetism.Basic
import Physlib.Units.WithDim.Basic

/- USER: The assigned source file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0913

open Dimension
open scoped BigOperators

/-!
# Electric-field strength beside two equal positive point charges

The primary image places a black observation dot `5.0 cm` to the left of the
midpoint of two red positive charges.  The upper charge is `5.0 cm` above the
midpoint, the lower charge is `5.0 cm` below it, and both charges are labelled
`3.0 nC`.

Signed charge, length, and field-strength magnitude are represented by Physlib
dimensionful quantities.  Coordinates are coherent-SI metre readouts, while
the components of `Electromagnetism.ElectricField 2` are coherent-SI field
readouts in newtons per coulomb.

Assumption/target split:

* governing laws: the vector point-charge form of Coulomb's law, electric-field
  superposition, and the measurement relation between the physical magnitude
  and the norm of the resultant field vector;
* previous-part results: none;
* figure/data readouts: two red `+3.0 nC` charges, the black observation dot,
  the three `5.0 cm` dimension arrows, and their planar geometry;
* target conclusions: the resultant strength is between `7550 N/C` and
  `7650 N/C`, hence rounds to `7.6 * 10^3 N/C`, making answer C uniquely
  nearest among the displayed choices.

No numerical resultant-field value is a setup field or theorem premise.
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

/-- A nonnegative, unit-independent electric-field magnitude. -/
abbrev ElectricFieldMagnitudeQuantity : Type :=
  Dimensionful (WithDim electricFieldStrengthDimension NNReal)

/-- Coherent-SI metre readout of a physical length. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  ((length UnitChoices.SI).val : ℝ)

/-- Centimetre readout used by the dimension labels in the image. -/
def lengthInCentimeters (length : LengthQuantity) : ℝ :=
  100 * lengthInMeters length

/-- Coherent-SI coulomb readout of a signed physical charge. -/
def chargeInCoulombs (charge : SignedChargeQuantity) : ℝ :=
  (charge UnitChoices.SI).val

/-- Nanocoulomb readout used by the two printed charge labels. -/
def chargeInNanocoulombs (charge : SignedChargeQuantity) : ℝ :=
  (10 : ℝ) ^ 9 * chargeInCoulombs charge

/-- Coherent-SI readout of a field magnitude in newtons per coulomb. -/
def fieldMagnitudeInNewtonsPerCoulomb
    (magnitude : ElectricFieldMagnitudeQuantity) : ℝ :=
  ((magnitude UnitChoices.SI).val : ℝ)

/-! ## Figure labels and physical setup -/

/-- The two equal point charges, named by their locations in the image. -/
inductive SourceCharge where
  | upper
  | lower
  deriving DecidableEq, Fintype, Repr

/-- The four geometrically distinguished points in the supplied image. -/
inductive FigurePoint where
  | upperChargeCenter
  | midpoint
  | lowerChargeCenter
  | observationDot
  deriving DecidableEq, Fintype, Repr

/-- The center occupied by each named source. -/
def expectedSourceCenter : SourceCharge → FigurePoint
  | .upper => .upperChargeCenter
  | .lower => .lowerChargeCenter

/-- Colours of the charge circles and observation dot in the raster. -/
inductive FigureMarkColor where
  | red
  | black
  deriving DecidableEq, Repr

/-- The sign glyph drawn in each charge circle. -/
inductive FigureChargeSign where
  | plus
  | minus
  deriving DecidableEq, Repr

/-- The three dimension-arrow segments, all labelled `5.0 cm`. -/
inductive FigureDimensionSegment where
  | dotToMidpoint
  | midpointToUpperCharge
  | midpointToLowerCharge
  deriving DecidableEq, Fintype, Repr

/-- Literal presentation data transcribed from image `913.png`. -/
structure TwoChargeFieldFigure where
  sourceCenter : SourceCharge → FigurePoint
  sourceColor : SourceCharge → FigureMarkColor
  sourceSign : SourceCharge → FigureChargeSign
  printedChargeNanocoulombs : SourceCharge → ℝ
  blackDotPoint : FigurePoint
  blackDotColor : FigureMarkColor
  blackDotShown : Bool
  dimensionArrowShown : FigureDimensionSegment → Bool
  dimensionLabelCentimeters : FigureDimensionSegment → ℝ

/-- Turn a planar point into its explicitly metre-valued position vector. -/
def positionVectorInMeters (point : Space 2) :
    EuclideanSpace ℝ (Fin 2) :=
  !₂[point.val 0, point.val 1]

/--
Independent physical quantities and fields in the electrostatic setup.

The resultant magnitude is an unknown observable.  It is related to the norm
of the independently modeled resultant vector field only by a separate
measurement premise below.
-/
structure SymmetricTwoChargeSetup where
  figure : TwoChargeFieldFigure
  horizontalOffset : LengthQuantity
  upperVerticalOffset : LengthQuantity
  lowerVerticalOffset : LengthQuantity
  pointPosition : FigurePoint → Space 2
  charge : SourceCharge → SignedChargeQuantity
  electromagneticSystem : Electromagnetism.EMSystem
  sourceElectricField : SourceCharge → Electromagnetism.ElectricField 2
  resultantElectricField : Electromagnetism.ElectricField 2
  observationTime : Time
  resultantMagnitude : ElectricFieldMagnitudeQuantity

/-- Spatial position of a named point charge. -/
def sourcePosition
    (setup : SymmetricTwoChargeSetup) (source : SourceCharge) : Space 2 :=
  setup.pointPosition (setup.figure.sourceCenter source)

/-- Spatial position marked by the black dot. -/
def observationPosition (setup : SymmetricTwoChargeSetup) : Space 2 :=
  setup.pointPosition setup.figure.blackDotPoint

/-- Displacement from a source to a field point, in metres. -/
def displacementFromSourceInMeters
    (setup : SymmetricTwoChargeSetup)
    (source : SourceCharge) (point : Space 2) :
    EuclideanSpace ℝ (Fin 2) :=
  positionVectorInMeters point -
    positionVectorInMeters (sourcePosition setup source)

/-- Resultant field vector at the observation dot, in newtons per coulomb. -/
def resultantFieldAtDotInNewtonsPerCoulomb
    (setup : SymmetricTwoChargeSetup) :
    EuclideanSpace ℝ (Fin 2) :=
  setup.resultantElectricField setup.observationTime
    (observationPosition setup)

/-- Norm of the resultant field vector at the dot, in newtons per coulomb. -/
def resultantFieldNormAtDotInNewtonsPerCoulomb
    (setup : SymmetricTwoChargeSetup) : ℝ :=
  ‖resultantFieldAtDotInNewtonsPerCoulomb setup‖

/-! ## Primary-image evidence and physical parameters -/

/--
Literal image evidence and its association with the physical quantities and
planar coordinates.  No resultant field value occurs in this predicate.
-/
structure MatchesSuppliedSymmetricChargeFigure
    (setup : SymmetricTwoChargeSetup) : Prop where
  sourceCenters : ∀ source,
    setup.figure.sourceCenter source = expectedSourceCenter source
  sourceCirclesAreRed : ∀ source,
    setup.figure.sourceColor source = .red
  sourceGlyphsArePlus : ∀ source,
    setup.figure.sourceSign source = .plus
  printedChargeLabels : ∀ source,
    setup.figure.printedChargeNanocoulombs source = 3
  physicalChargesMatchPrintedLabels : ∀ source,
    chargeInNanocoulombs (setup.charge source) =
      setup.figure.printedChargeNanocoulombs source
  blackDotAtObservationPoint :
    setup.figure.blackDotPoint = .observationDot
  observationDotIsBlack : setup.figure.blackDotColor = .black
  observationDotIsShown : setup.figure.blackDotShown = true
  allDimensionArrowsShown : ∀ segment,
    setup.figure.dimensionArrowShown segment = true
  allDimensionLabelsAreFiveCentimeters : ∀ segment,
    setup.figure.dimensionLabelCentimeters segment = 5
  horizontalOffsetMatchesLabel :
    lengthInCentimeters setup.horizontalOffset =
      setup.figure.dimensionLabelCentimeters .dotToMidpoint
  upperOffsetMatchesLabel :
    lengthInCentimeters setup.upperVerticalOffset =
      setup.figure.dimensionLabelCentimeters .midpointToUpperCharge
  lowerOffsetMatchesLabel :
    lengthInCentimeters setup.lowerVerticalOffset =
      setup.figure.dimensionLabelCentimeters .midpointToLowerCharge
  midpointCoordinates :
    positionVectorInMeters (setup.pointPosition .midpoint) = !₂[0, 0]
  observationDotCoordinates :
    positionVectorInMeters (setup.pointPosition .observationDot) =
      !₂[-lengthInMeters setup.horizontalOffset, 0]
  upperChargeCoordinates :
    positionVectorInMeters (setup.pointPosition .upperChargeCenter) =
      !₂[0, lengthInMeters setup.upperVerticalOffset]
  lowerChargeCoordinates :
    positionVectorInMeters (setup.pointPosition .lowerChargeCenter) =
      !₂[0, -lengthInMeters setup.lowerVerticalOffset]
  noSourceOccupiesObservationDot : ∀ source,
    setup.figure.sourceCenter source ≠ setup.figure.blackDotPoint

/--
Coherent-SI calibration of Physlib's Coulomb constant.  The scalar has units
`N m²/C²` in the field law below.
-/
structure UsesVacuumCoulombConstant
    (setup : SymmetricTwoChargeSetup) : Prop where
  coulombConstantCalibration :
    setup.electromagneticSystem.coulombConstant = 8.9875517923e9

/-- Positivity and source-observation separation conditions. -/
structure HasPhysicalTwoChargeParameters
    (setup : SymmetricTwoChargeSetup) : Prop where
  horizontalOffsetPositive : 0 < lengthInMeters setup.horizontalOffset
  upperVerticalOffsetPositive :
    0 < lengthInMeters setup.upperVerticalOffset
  lowerVerticalOffsetPositive :
    0 < lengthInMeters setup.lowerVerticalOffset
  coulombConstantPositive :
    0 < setup.electromagneticSystem.coulombConstant
  sourcesSeparatedFromObservation : ∀ source,
    0 < ‖displacementFromSourceInMeters setup source
      (observationPosition setup)‖

/-! ## Governing electrostatic laws -/

/-!
For charge `q` and displacement `r` from the source to a field point, the
electric field is `k q r / ‖r‖³`.  This law is quantified over every point away
from each source and contains no requested numerical result.
-/
structure SatisfiesPointChargeCoulombFieldLaw
    (setup : SymmetricTwoChargeSetup) : Prop where
  fieldOfEachSource : ∀ source time point,
    point ≠ sourcePosition setup source →
      setup.sourceElectricField source time point =
        (setup.electromagneticSystem.coulombConstant *
            chargeInCoulombs (setup.charge source) /
          ‖displacementFromSourceInMeters setup source point‖ ^ 3) •
            displacementFromSourceInMeters setup source point

/-- The resultant field is the vector sum of the two source fields. -/
structure SatisfiesElectricFieldSuperposition
    (setup : SymmetricTwoChargeSetup) : Prop where
  resultantIsSourceSum : ∀ time point,
    setup.resultantElectricField time point =
      ∑ source : SourceCharge, setup.sourceElectricField source time point

/-!
The dimensionful scalar observable is the Euclidean magnitude of the modeled
resultant vector at the black dot.  This is a general measurement relation,
not a numerical answer.
-/
structure ResultantMagnitudeRepresentsFieldAtDot
    (setup : SymmetricTwoChargeSetup) : Prop where
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

/-- Field strength in newtons per coulomb printed by each answer choice. -/
def AnswerChoice.fieldStrengthInNewtonsPerCoulomb : AnswerChoice → ℝ
  | .A => 13 * (10 : ℝ) ^ 2
  | .B => 53 * (10 : ℝ) ^ 2
  | .C => 76 * (10 : ℝ) ^ 2
  | .D => 35 * (10 : ℝ) ^ 2

/-- The answer label recorded by the supplied dataset metadata. -/
def recordedDatasetAnswer : AnswerChoice := .C

/-- A value rounds to a displayed reading at the nearest `100 N/C`. -/
def RoundsToNearestHundred (actual displayed : ℝ) : Prop :=
  |actual - displayed| < 50

/-- A displayed choice is strictly nearer than every alternative. -/
def IsUniqueNearestDisplayedFieldStrength
    (actual : ℝ) (choice : AnswerChoice) : Prop :=
  ∀ other : AnswerChoice, other ≠ choice →
    |actual - choice.fieldStrengthInNewtonsPerCoulomb| <
      |actual - other.fieldStrengthInNewtonsPerCoulomb|

/-!
Coulomb's vector law and superposition give the source-by-source expression at
the observation dot.  It contains only source data and the governing constant.
-/
lemma resultantFieldAtDot_eq_coulombSum
    (setup : SymmetricTwoChargeSetup)
    (_physical : HasPhysicalTwoChargeParameters setup)
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
  intro hEq
  have hPositive := _physical.sourcesSeparatedFromObservation source
  rw [hEq] at hPositive
  simp [displacementFromSourceInMeters] at hPositive

/-!
By the reflection symmetry of the two equal charges, the vertical components
of their fields cancel at the observation dot.
-/
lemma resultantFieldAtDot_verticalComponent_eq_zero
    (setup : SymmetricTwoChargeSetup)
    (_figure : MatchesSuppliedSymmetricChargeFigure setup)
    (_physical : HasPhysicalTwoChargeParameters setup)
    (_coulomb : SatisfiesPointChargeCoulombFieldLaw setup)
    (_superposition : SatisfiesElectricFieldSuperposition setup) :
    resultantFieldAtDotInNewtonsPerCoulomb setup 1 = 0 := by
  have hHorizontal :
      lengthInMeters setup.horizontalOffset = (1 : ℝ) / 20 := by
    have h := _figure.horizontalOffsetMatchesLabel
    rw [_figure.allDimensionLabelsAreFiveCentimeters] at h
    norm_num [lengthInCentimeters] at h ⊢
    linarith
  have hUpper :
      lengthInMeters setup.upperVerticalOffset = (1 : ℝ) / 20 := by
    have h := _figure.upperOffsetMatchesLabel
    rw [_figure.allDimensionLabelsAreFiveCentimeters] at h
    norm_num [lengthInCentimeters] at h ⊢
    linarith
  have hLower :
      lengthInMeters setup.lowerVerticalOffset = (1 : ℝ) / 20 := by
    have h := _figure.lowerOffsetMatchesLabel
    rw [_figure.allDimensionLabelsAreFiveCentimeters] at h
    norm_num [lengthInCentimeters] at h ⊢
    linarith
  have hChargeUpper :
      chargeInCoulombs (setup.charge .upper) =
        (3 : ℝ) / 1000000000 := by
    have h := _figure.physicalChargesMatchPrintedLabels .upper
    rw [_figure.printedChargeLabels] at h
    norm_num [chargeInNanocoulombs] at h ⊢
    linarith
  have hChargeLower :
      chargeInCoulombs (setup.charge .lower) =
        (3 : ℝ) / 1000000000 := by
    have h := _figure.physicalChargesMatchPrintedLabels .lower
    rw [_figure.printedChargeLabels] at h
    norm_num [chargeInNanocoulombs] at h ⊢
    linarith
  have hDisplacementUpper :
      displacementFromSourceInMeters setup .upper
          (observationPosition setup) =
        !₂[-(1 : ℝ) / 20, -(1 : ℝ) / 20] := by
    rw [displacementFromSourceInMeters, observationPosition, sourcePosition,
      _figure.blackDotAtObservationPoint, _figure.sourceCenters,
      expectedSourceCenter, _figure.observationDotCoordinates,
      _figure.upperChargeCoordinates, hHorizontal, hUpper]
    ext i
    fin_cases i <;> norm_num
  have hDisplacementLower :
      displacementFromSourceInMeters setup .lower
          (observationPosition setup) =
        !₂[-(1 : ℝ) / 20, (1 : ℝ) / 20] := by
    rw [displacementFromSourceInMeters, observationPosition, sourcePosition,
      _figure.blackDotAtObservationPoint, _figure.sourceCenters,
      expectedSourceCenter, _figure.observationDotCoordinates,
      _figure.lowerChargeCoordinates, hHorizontal, hLower]
    ext i
    fin_cases i <;> norm_num
  have hNormsEqual :
      ‖displacementFromSourceInMeters setup .upper
          (observationPosition setup)‖ =
        ‖displacementFromSourceInMeters setup .lower
          (observationPosition setup)‖ := by
    rw [hDisplacementUpper, hDisplacementLower]
    have hUpperSq :
        ‖(!₂[-(1 : ℝ) / 20, -(1 : ℝ) / 20] :
            EuclideanSpace ℝ (Fin 2))‖ ^ 2 = 1 / 200 := by
      rw [EuclideanSpace.norm_sq_eq]
      norm_num [Real.norm_eq_abs, Fin.sum_univ_two]
    have hLowerSq :
        ‖(!₂[-(1 : ℝ) / 20, (1 : ℝ) / 20] :
            EuclideanSpace ℝ (Fin 2))‖ ^ 2 = 1 / 200 := by
      rw [EuclideanSpace.norm_sq_eq]
      norm_num [Real.norm_eq_abs, Fin.sum_univ_two]
    have hUpperNonnegative :
        0 ≤ ‖(!₂[-(1 : ℝ) / 20, -(1 : ℝ) / 20] :
          EuclideanSpace ℝ (Fin 2))‖ := norm_nonneg _
    have hLowerNonnegative :
        0 ≤ ‖(!₂[-(1 : ℝ) / 20, (1 : ℝ) / 20] :
          EuclideanSpace ℝ (Fin 2))‖ := norm_nonneg _
    nlinarith
  have hSourceSum
      (f : SourceCharge → EuclideanSpace ℝ (Fin 2)) :
      ∑ source : SourceCharge, f source = f .upper + f .lower := by
    rw [show (Finset.univ : Finset SourceCharge) =
      {.upper, .lower} by decide]
    simp
  have hField := resultantFieldAtDot_eq_coulombSum
    setup _physical _coulomb _superposition
  rw [hSourceSum, hChargeUpper, hChargeLower, hNormsEqual,
    hDisplacementUpper, hDisplacementLower] at hField
  rw [hField]
  simp
  ring

/-!
The two Coulomb contributions yield an unrounded magnitude of approximately
`7.63 * 10^3 N/C`, which lies in the nearest-hundred rounding interval for
`7.6 * 10^3 N/C`.
-/
lemma resultantFieldNormAtDot_numericalBounds
    (setup : SymmetricTwoChargeSetup)
    (_figure : MatchesSuppliedSymmetricChargeFigure setup)
    (_constant : UsesVacuumCoulombConstant setup)
    (_physical : HasPhysicalTwoChargeParameters setup)
    (_coulomb : SatisfiesPointChargeCoulombFieldLaw setup)
    (_superposition : SatisfiesElectricFieldSuperposition setup) :
    (7550 : ℝ) < resultantFieldNormAtDotInNewtonsPerCoulomb setup ∧
      resultantFieldNormAtDotInNewtonsPerCoulomb setup < 7650 := by
  have hHorizontal :
      lengthInMeters setup.horizontalOffset = (1 : ℝ) / 20 := by
    have h := _figure.horizontalOffsetMatchesLabel
    rw [_figure.allDimensionLabelsAreFiveCentimeters] at h
    norm_num [lengthInCentimeters] at h ⊢
    linarith
  have hUpper :
      lengthInMeters setup.upperVerticalOffset = (1 : ℝ) / 20 := by
    have h := _figure.upperOffsetMatchesLabel
    rw [_figure.allDimensionLabelsAreFiveCentimeters] at h
    norm_num [lengthInCentimeters] at h ⊢
    linarith
  have hLower :
      lengthInMeters setup.lowerVerticalOffset = (1 : ℝ) / 20 := by
    have h := _figure.lowerOffsetMatchesLabel
    rw [_figure.allDimensionLabelsAreFiveCentimeters] at h
    norm_num [lengthInCentimeters] at h ⊢
    linarith
  have hChargeUpper :
      chargeInCoulombs (setup.charge .upper) =
        (3 : ℝ) / 1000000000 := by
    have h := _figure.physicalChargesMatchPrintedLabels .upper
    rw [_figure.printedChargeLabels] at h
    norm_num [chargeInNanocoulombs] at h ⊢
    linarith
  have hChargeLower :
      chargeInCoulombs (setup.charge .lower) =
        (3 : ℝ) / 1000000000 := by
    have h := _figure.physicalChargesMatchPrintedLabels .lower
    rw [_figure.printedChargeLabels] at h
    norm_num [chargeInNanocoulombs] at h ⊢
    linarith
  have hDisplacementUpper :
      displacementFromSourceInMeters setup .upper
          (observationPosition setup) =
        !₂[-(1 : ℝ) / 20, -(1 : ℝ) / 20] := by
    rw [displacementFromSourceInMeters, observationPosition, sourcePosition,
      _figure.blackDotAtObservationPoint, _figure.sourceCenters,
      expectedSourceCenter, _figure.observationDotCoordinates,
      _figure.upperChargeCoordinates, hHorizontal, hUpper]
    ext i
    fin_cases i <;> norm_num
  have hDisplacementLower :
      displacementFromSourceInMeters setup .lower
          (observationPosition setup) =
        !₂[-(1 : ℝ) / 20, (1 : ℝ) / 20] := by
    rw [displacementFromSourceInMeters, observationPosition, sourcePosition,
      _figure.blackDotAtObservationPoint, _figure.sourceCenters,
      expectedSourceCenter, _figure.observationDotCoordinates,
      _figure.lowerChargeCoordinates, hHorizontal, hLower]
    ext i
    fin_cases i <;> norm_num
  have hNormUpperSq :
      ‖displacementFromSourceInMeters setup .upper
          (observationPosition setup)‖ ^ 2 = 1 / 200 := by
    rw [hDisplacementUpper, EuclideanSpace.norm_sq_eq]
    norm_num [Real.norm_eq_abs, Fin.sum_univ_two]
  have hNormLowerSq :
      ‖displacementFromSourceInMeters setup .lower
          (observationPosition setup)‖ ^ 2 = 1 / 200 := by
    rw [hDisplacementLower, EuclideanSpace.norm_sq_eq]
    norm_num [Real.norm_eq_abs, Fin.sum_univ_two]
  have hNormsEqual :
      ‖displacementFromSourceInMeters setup .upper
          (observationPosition setup)‖ =
        ‖displacementFromSourceInMeters setup .lower
          (observationPosition setup)‖ := by
    have hUpperNonnegative :
        0 ≤ ‖displacementFromSourceInMeters setup .upper
          (observationPosition setup)‖ := norm_nonneg _
    have hLowerNonnegative :
        0 ≤ ‖displacementFromSourceInMeters setup .lower
          (observationPosition setup)‖ := norm_nonneg _
    nlinarith
  have hRadiusSq :
      ‖(!₂[-(1 : ℝ) / 20, (1 : ℝ) / 20] :
          EuclideanSpace ℝ (Fin 2))‖ ^ 2 = 1 / 200 := by
    rw [EuclideanSpace.norm_sq_eq]
    norm_num [Real.norm_eq_abs, Fin.sum_univ_two]
  have hRadiusSixth :
      ‖(!₂[-(1 : ℝ) / 20, (1 : ℝ) / 20] :
          EuclideanSpace ℝ (Fin 2))‖ ^ 6 = 1 / 8000000 := by
    calc
      ‖(!₂[-(1 : ℝ) / 20, (1 : ℝ) / 20] :
          EuclideanSpace ℝ (Fin 2))‖ ^ 6 =
          (‖(!₂[-(1 : ℝ) / 20, (1 : ℝ) / 20] :
            EuclideanSpace ℝ (Fin 2))‖ ^ 2) ^ 3 := by ring
      _ = (1 / 200 : ℝ) ^ 3 := by rw [hRadiusSq]
      _ = 1 / 8000000 := by norm_num
  have hSourceSum
      (f : SourceCharge → EuclideanSpace ℝ (Fin 2)) :
      ∑ source : SourceCharge, f source = f .upper + f .lower := by
    rw [show (Finset.univ : Finset SourceCharge) =
      {.upper, .lower} by decide]
    simp
  have hField := resultantFieldAtDot_eq_coulombSum
    setup _physical _coulomb _superposition
  rw [hSourceSum, _constant.coulombConstantCalibration,
    hChargeUpper, hChargeLower, hNormsEqual,
    hDisplacementUpper, hDisplacementLower] at hField
  have hFieldComponents :
      resultantFieldAtDotInNewtonsPerCoulomb setup =
        !₂[-((269626553769 : ℝ) / 100000000000 /
          ‖(!₂[-(1 : ℝ) / 20, (1 : ℝ) / 20] :
            EuclideanSpace ℝ (Fin 2))‖ ^ 3), 0] := by
    rw [hField]
    ext i
    fin_cases i <;> simp <;> ring
  have hNormSq :
      resultantFieldNormAtDotInNewtonsPerCoulomb setup ^ 2 =
        ((269626553769 : ℝ) / 100000000000 /
          ‖(!₂[-(1 : ℝ) / 20, (1 : ℝ) / 20] :
            EuclideanSpace ℝ (Fin 2))‖ ^ 3) ^ 2 := by
    rw [resultantFieldNormAtDotInNewtonsPerCoulomb,
      hFieldComponents, EuclideanSpace.norm_sq_eq]
    simp [Real.norm_eq_abs, Fin.sum_univ_two, sq_abs]
  have hNormSqNumerical :
      resultantFieldNormAtDotInNewtonsPerCoulomb setup ^ 2 =
        ((269626553769 : ℝ) / 100000000000) ^ 2 * 8000000 := by
    rw [hNormSq, div_pow]
    rw [show
      (‖(!₂[-(1 : ℝ) / 20, (1 : ℝ) / 20] :
          EuclideanSpace ℝ (Fin 2))‖ ^ 3) ^ 2 =
        ‖(!₂[-(1 : ℝ) / 20, (1 : ℝ) / 20] :
          EuclideanSpace ℝ (Fin 2))‖ ^ 6 by ring,
      hRadiusSixth]
    ring
  have hNormNonnegative :
      0 ≤ resultantFieldNormAtDotInNewtonsPerCoulomb setup :=
    norm_nonneg _
  have hLowerSq :
      (7550 : ℝ) ^ 2 <
        resultantFieldNormAtDotInNewtonsPerCoulomb setup ^ 2 := by
    rw [hNormSqNumerical]
    norm_num
  have hUpperSq :
      resultantFieldNormAtDotInNewtonsPerCoulomb setup ^ 2 <
        (7650 : ℝ) ^ 2 := by
    rw [hNormSqNumerical]
    norm_num
  constructor <;> nlinarith

/-!
The strength at the black dot rounds to `7.6 * 10^3 N/C`; among the four
displayed choices, C is uniquely nearest.

This is the Lean declaration corresponding to
`thm:physics:phyx_mini_0913:target`.
-/
theorem problem_phyx_mini_0913
    (setup : SymmetricTwoChargeSetup)
    (hFigure : MatchesSuppliedSymmetricChargeFigure setup)
    (hConstant : UsesVacuumCoulombConstant setup)
    (hPhysical : HasPhysicalTwoChargeParameters setup)
    (hCoulomb : SatisfiesPointChargeCoulombFieldLaw setup)
    (hSuperposition : SatisfiesElectricFieldSuperposition setup)
    (hMagnitude : ResultantMagnitudeRepresentsFieldAtDot setup) :
    (7550 : ℝ) <
        fieldMagnitudeInNewtonsPerCoulomb setup.resultantMagnitude ∧
      fieldMagnitudeInNewtonsPerCoulomb setup.resultantMagnitude < 7650 ∧
      RoundsToNearestHundred
        (fieldMagnitudeInNewtonsPerCoulomb setup.resultantMagnitude)
        recordedDatasetAnswer.fieldStrengthInNewtonsPerCoulomb ∧
      IsUniqueNearestDisplayedFieldStrength
        (fieldMagnitudeInNewtonsPerCoulomb setup.resultantMagnitude)
        recordedDatasetAnswer := by
  have hBounds := resultantFieldNormAtDot_numericalBounds
    setup hFigure hConstant hPhysical hCoulomb hSuperposition
  rw [← hMagnitude.magnitudeReadoutAgreesWithVectorNorm] at hBounds
  rcases hBounds with ⟨hLower, hUpper⟩
  have hNear :
      |fieldMagnitudeInNewtonsPerCoulomb setup.resultantMagnitude -
          recordedDatasetAnswer.fieldStrengthInNewtonsPerCoulomb| < 50 := by
    rw [abs_lt]
    norm_num [recordedDatasetAnswer,
      AnswerChoice.fieldStrengthInNewtonsPerCoulomb]
    constructor <;> linarith
  refine ⟨hLower, hUpper, hNear, ?_⟩
  intro other hOther
  fin_cases other
  · norm_num [recordedDatasetAnswer,
      AnswerChoice.fieldStrengthInNewtonsPerCoulomb] at hNear ⊢
    have hFar :
        50 <
          |fieldMagnitudeInNewtonsPerCoulomb setup.resultantMagnitude -
            1300| := by
      rw [abs_of_pos (by linarith)]
      linarith
    exact hNear.trans hFar
  · norm_num [recordedDatasetAnswer,
      AnswerChoice.fieldStrengthInNewtonsPerCoulomb] at hNear ⊢
    have hFar :
        50 <
          |fieldMagnitudeInNewtonsPerCoulomb setup.resultantMagnitude -
            5300| := by
      rw [abs_of_pos (by linarith)]
      linarith
    exact hNear.trans hFar
  · simp [recordedDatasetAnswer] at hOther
  · norm_num [recordedDatasetAnswer,
      AnswerChoice.fieldStrengthInNewtonsPerCoulomb] at hNear ⊢
    have hFar :
        50 <
          |fieldMagnitudeInNewtonsPerCoulomb setup.resultantMagnitude -
            3500| := by
      rw [abs_of_pos (by linarith)]
      linarith
    exact hNear.trans hFar

end PhyXMiniProblems.ProblemPhyXMini0913
