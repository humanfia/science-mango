import Mathlib
import Physlib.Electromagnetism.Basic
import Physlib.Units.WithDim.Basic

/- USER: The assigned Lean file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0914

open Dimension

/-!
# Electric-field strength due to two positive point charges

The primary image `914.png` shows two identical positive charges, each labelled
`3.0 nC`.  The lower charge is `10 cm` vertically below the upper charge, and
the black observation dot is `5.0 cm` horizontally to the right of the upper
charge.  The requested quantity is the magnitude of the vector sum of the two
point-charge electric fields at the dot.

Dimensionful charge, length, and electric-field-strength quantities use
Physlib's unit-independent `Dimensionful` representation.  The planar
coordinates below are explicitly coherent-SI coordinate readouts in metres,
and the vector fields use Physlib's `Electromagnetism.ElectricField 2`.

Assumption/target split:

* governing laws: the vector inverse-square point-charge field law, linear
  superposition, and calibration of field strength by the norm of the total
  vector field;
* previous-part results: none;
* figure/data readouts: two positive `3.0 nC` point charges, their vertical
  alignment and `10 cm` separation, and a dot `5.0 cm` horizontally to the
  right of the upper charge;
* current target conclusion: the field-strength readout at the dot rounds to
  the physically supported value `1.2 * 10^4 N/C` (to two significant
  figures).

The total field, its two source contributions, and its magnitude are
independent fields of the setup.  None is defined from the target value.  The
dataset's recorded answer C, `1.2 * 10^3 N/C`, is retained below only as
metadata because it is a factor of ten smaller than the value implied by the
pictured charges and distances.
-/

/-! ## Dimensionful quantities and coherent-SI readouts -/

/-- The physical dimension `M L T⁻² C⁻¹` of electric-field strength. -/
def electricFieldStrengthDimension : Dimension :=
  M𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹ * C𝓭⁻¹

/-- A signed, unit-independent electric charge. -/
abbrev SignedChargeQuantity : Type :=
  Dimensionful (WithDim C𝓭 ℝ)

/-- A nonnegative, unit-independent physical length. -/
abbrev LengthQuantity : Type :=
  Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative, unit-independent electric-field strength. -/
abbrev ElectricFieldStrengthQuantity : Type :=
  Dimensionful (WithDim electricFieldStrengthDimension NNReal)

/-- Read a signed physical charge in coherent-SI coulombs. -/
def chargeInCoulombs (charge : SignedChargeQuantity) : ℝ :=
  (charge UnitChoices.SI).val

/-- Read a charge in the nanocoulombs printed in the figure. -/
def chargeInNanocoulombs (charge : SignedChargeQuantity) : ℝ :=
  (10 : ℝ) ^ 9 * chargeInCoulombs charge

/-- Read a nonnegative physical length in coherent-SI metres. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  ((length UnitChoices.SI).val : ℝ)

/-- Read a physical length in the centimetres used by the two arrows. -/
def lengthInCentimeters (length : LengthQuantity) : ℝ :=
  100 * lengthInMeters length

/-- Read a field strength in coherent-SI newtons per coulomb. -/
def electricFieldStrengthInNewtonsPerCoulomb
    (strength : ElectricFieldStrengthQuantity) : ℝ :=
  ((strength UnitChoices.SI).val : ℝ)

/-! ## Figure labels and independent physical setup -/

/-- The two identical source charges visible in the primary image. -/
inductive SourceCharge where
  | upper
  | lower
  deriving DecidableEq, Fintype, Repr

/-- The two source locations and the black observation dot. -/
inductive DiagramSite where
  | upperCharge
  | lowerCharge
  | fieldPoint
  deriving DecidableEq, Fintype, Repr

/-- Regard a source charge as its corresponding geometric site. -/
def SourceCharge.toDiagramSite : SourceCharge → DiagramSite
  | .upper => .upperCharge
  | .lower => .lowerCharge

/-- The sign glyph drawn inside each red charge marker. -/
inductive FigureChargeSign where
  | plus
  | minus
  deriving DecidableEq, Repr

/-- Literal presentation data transcribed from image `914.png`. -/
structure TwoChargeFieldFigure where
  chargeCircleShown : SourceCharge → Bool
  chargeCircleIsRed : SourceCharge → Bool
  chargeSignGlyph : SourceCharge → FigureChargeSign
  printedChargeNanocoulombs : SourceCharge → ℝ
  observationDotShown : Bool
  chargesVerticallyAligned : Bool
  observationDotRightOfUpperCharge : Bool
  horizontalDistanceArrowShown : Bool
  horizontalDistanceArrowStartsAtUpperCharge : Bool
  horizontalDistanceArrowEndsAtDot : Bool
  printedHorizontalDistanceCentimeters : ℝ
  verticalDistanceArrowShown : Bool
  verticalDistanceArrowConnectsCharges : Bool
  printedVerticalSeparationCentimeters : ℝ

/-!
Independent physical quantities and observables for the two-charge system.
The planar coordinates are measured in metres in an arbitrary orthonormal
frame whose rightward and upward directions are also recorded explicitly.
-/
structure TwoPointChargeFieldSetup where
  figure : TwoChargeFieldFigure
  electromagneticSystem : Electromagnetism.EMSystem
  charge : SourceCharge → SignedChargeQuantity
  horizontalOffset : LengthQuantity
  verticalSeparation : LengthQuantity
  coordinateInMeters : DiagramSite → EuclideanSpace ℝ (Fin 2)
  rightwardUnit : EuclideanSpace ℝ (Fin 2)
  upwardUnit : EuclideanSpace ℝ (Fin 2)
  modeledAsPointCharge : SourceCharge → Bool
  sourcesAreStationary : Bool
  spatialOrigin : Space 2
  observationTime : Time
  sourceElectricField : SourceCharge → Electromagnetism.ElectricField 2
  totalElectricField : Electromagnetism.ElectricField 2
  fieldStrengthAtDot : ElectricFieldStrengthQuantity

/-- Displacement in metres from a source charge to the observation dot. -/
def displacementFromSourceToDotInMeters
    (setup : TwoPointChargeFieldSetup) (source : SourceCharge) :
    EuclideanSpace ℝ (Fin 2) :=
  setup.coordinateInMeters .fieldPoint -
    setup.coordinateInMeters source.toDiagramSite

/-- The source contribution evaluated at the marked dot and observation time. -/
def sourceFieldVectorAtDot
    (setup : TwoPointChargeFieldSetup) (source : SourceCharge) :
    EuclideanSpace ℝ (Fin 2) :=
  setup.sourceElectricField source setup.observationTime
    (setup.coordinateInMeters .fieldPoint +ᵥ setup.spatialOrigin)

/-- The total electric-field vector evaluated at the marked dot. -/
def totalFieldVectorAtDot
    (setup : TwoPointChargeFieldSetup) : EuclideanSpace ℝ (Fin 2) :=
  setup.totalElectricField setup.observationTime
    (setup.coordinateInMeters .fieldPoint +ᵥ setup.spatialOrigin)

/-! ## Scenario and primary-image evidence -/

/-- The two pictured sources are stationary point charges. -/
structure MatchesTwoStationaryPointChargeScenario
    (setup : TwoPointChargeFieldSetup) : Prop where
  bothSourcesArePointCharges :
    ∀ source, setup.modeledAsPointCharge source = true
  bothSourcesAreStationary : setup.sourcesAreStationary = true

/-!
Every qualitative feature and numerical label read directly from the primary
image, together with the calibration of those labels to physical quantities.
No electric-field value occurs in this predicate.
-/
structure MatchesSuppliedTwoChargeFieldFigure
    (setup : TwoPointChargeFieldSetup) : Prop where
  bothChargeCirclesShown :
    ∀ source, setup.figure.chargeCircleShown source = true
  bothChargeCirclesRed :
    ∀ source, setup.figure.chargeCircleIsRed source = true
  bothChargeSignsPositive :
    ∀ source, setup.figure.chargeSignGlyph source = .plus
  bothPrintedChargeLabelsAreThreeNanocoulombs :
    ∀ source, setup.figure.printedChargeNanocoulombs source = 3
  physicalChargesMatchLabels : ∀ source,
    chargeInNanocoulombs (setup.charge source) =
      setup.figure.printedChargeNanocoulombs source
  blackObservationDotShown : setup.figure.observationDotShown = true
  verticalAlignmentShown : setup.figure.chargesVerticallyAligned = true
  dotShownRightOfUpperCharge :
    setup.figure.observationDotRightOfUpperCharge = true
  horizontalArrowShown : setup.figure.horizontalDistanceArrowShown = true
  horizontalArrowStartsAtUpperCharge :
    setup.figure.horizontalDistanceArrowStartsAtUpperCharge = true
  horizontalArrowEndsAtDot :
    setup.figure.horizontalDistanceArrowEndsAtDot = true
  printedHorizontalDistanceIsFiveCentimeters :
    setup.figure.printedHorizontalDistanceCentimeters = 5
  physicalHorizontalOffsetMatchesLabel :
    lengthInCentimeters setup.horizontalOffset =
      setup.figure.printedHorizontalDistanceCentimeters
  verticalArrowShown : setup.figure.verticalDistanceArrowShown = true
  verticalArrowConnectsTheCharges :
    setup.figure.verticalDistanceArrowConnectsCharges = true
  printedVerticalSeparationIsTenCentimeters :
    setup.figure.printedVerticalSeparationCentimeters = 10
  physicalVerticalSeparationMatchesLabel :
    lengthInCentimeters setup.verticalSeparation =
      setup.figure.printedVerticalSeparationCentimeters

/-!
The metric geometry depicted by the image.  The observation dot is displaced
rightward from the upper charge, and the upper charge is displaced upward from
the lower charge.  The two indicated directions form an orthonormal frame.
-/
structure SatisfiesTwoChargeFigureGeometry
    (setup : TwoPointChargeFieldSetup) : Prop where
  rightwardDirectionIsUnit : ‖setup.rightwardUnit‖ = 1
  upwardDirectionIsUnit : ‖setup.upwardUnit‖ = 1
  displayedDirectionsArePerpendicular :
    inner ℝ setup.rightwardUnit setup.upwardUnit = 0
  dotRelativeToUpperCharge :
    setup.coordinateInMeters .fieldPoint -
        setup.coordinateInMeters .upperCharge =
      lengthInMeters setup.horizontalOffset • setup.rightwardUnit
  upperRelativeToLowerCharge :
    setup.coordinateInMeters .upperCharge -
        setup.coordinateInMeters .lowerCharge =
      lengthInMeters setup.verticalSeparation • setup.upwardUnit

/-- Positivity and nondegeneracy conditions for the electrostatic model. -/
structure HasPhysicalTwoChargeFieldParameters
    (setup : TwoPointChargeFieldSetup) : Prop where
  bothChargesPositive :
    ∀ source, 0 < chargeInCoulombs (setup.charge source)
  horizontalOffsetPositive : 0 < lengthInMeters setup.horizontalOffset
  verticalSeparationPositive : 0 < lengthInMeters setup.verticalSeparation
  bothSourcesSeparatedFromDot :
    ∀ source, displacementFromSourceToDotInMeters setup source ≠ 0
  coulombConstantPositive :
    0 < setup.electromagneticSystem.coulombConstant

/-!
The rounded value of Coulomb's constant customarily used for this textbook
multiple-choice calculation.  It is a background constant, not a field-value
answer.
-/
structure UsesTextbookCoulombConstant
    (setup : TwoPointChargeFieldSetup) : Prop where
  coulombConstantCalibration :
    setup.electromagneticSystem.coulombConstant = 9 * (10 : ℝ) ^ 9

/-! ## Governing point-charge and superposition laws -/

/-!
For a source charge `q` and source-to-dot displacement `r`, the contribution
at the dot is `k q r / ‖r‖³`.  This vector equation combines the inverse-square
magnitude with the radial direction and contains no answer-choice value.
-/
structure SatisfiesPointChargeElectricFieldLaw
    (setup : TwoPointChargeFieldSetup) : Prop where
  fieldFromEachSource : ∀ source,
    displacementFromSourceToDotInMeters setup source ≠ 0 →
      sourceFieldVectorAtDot setup source =
        (setup.electromagneticSystem.coulombConstant *
            chargeInCoulombs (setup.charge source) /
              ‖displacementFromSourceToDotInMeters setup source‖ ^ 3) •
          displacementFromSourceToDotInMeters setup source

/-- The total field at the dot is the vector sum of the two source fields. -/
structure SatisfiesElectricFieldSuperposition
    (setup : TwoPointChargeFieldSetup) : Prop where
  totalFieldIsSourceSum :
    totalFieldVectorAtDot setup =
      sourceFieldVectorAtDot setup .upper +
        sourceFieldVectorAtDot setup .lower

/-!
The dimensionful scalar observable is calibrated to the Euclidean norm of the
total Physlib electric-field vector at the dot.
-/
structure CalibratesElectricFieldStrengthAtDot
    (setup : TwoPointChargeFieldSetup) : Prop where
  strengthIsTotalFieldNorm :
    electricFieldStrengthInNewtonsPerCoulomb setup.fieldStrengthAtDot =
      ‖totalFieldVectorAtDot setup‖

/-! ## Geometry consequences, displayed metadata, and physical answer -/

/-- The upper source is the displayed `5.0 cm` from the dot. -/
lemma upperSourceDistanceInMeters
    (setup : TwoPointChargeFieldSetup)
    (_figure : MatchesSuppliedTwoChargeFieldFigure setup)
    (_geometry : SatisfiesTwoChargeFigureGeometry setup) :
    ‖displacementFromSourceToDotInMeters setup .upper‖ = 5 / 100 := by
  have horizontalOffsetInMeters :
      lengthInMeters setup.horizontalOffset = 5 / 100 := by
    have h :
        100 * lengthInMeters setup.horizontalOffset = 5 := by
      calc
        100 * lengthInMeters setup.horizontalOffset =
            lengthInCentimeters setup.horizontalOffset := rfl
        _ = setup.figure.printedHorizontalDistanceCentimeters :=
          _figure.physicalHorizontalOffsetMatchesLabel
        _ = 5 := _figure.printedHorizontalDistanceIsFiveCentimeters
    linarith only [h]
  rw [displacementFromSourceToDotInMeters, SourceCharge.toDiagramSite,
    _geometry.dotRelativeToUpperCharge, norm_smul,
    _geometry.rightwardDirectionIsUnit, mul_one, horizontalOffsetInMeters]
  norm_num

/-!
The lower-source displacement is the sum of the displayed rightward `5.0 cm`
offset and upward `10 cm` separation.
-/
lemma lowerSourceDisplacementInMeters
    (setup : TwoPointChargeFieldSetup)
    (_geometry : SatisfiesTwoChargeFigureGeometry setup) :
    displacementFromSourceToDotInMeters setup .lower =
      lengthInMeters setup.horizontalOffset • setup.rightwardUnit +
        lengthInMeters setup.verticalSeparation • setup.upwardUnit := by
  rw [displacementFromSourceToDotInMeters, SourceCharge.toDiagramSite]
  calc
    setup.coordinateInMeters .fieldPoint -
          setup.coordinateInMeters .lowerCharge =
        (setup.coordinateInMeters .fieldPoint -
            setup.coordinateInMeters .upperCharge) +
          (setup.coordinateInMeters .upperCharge -
            setup.coordinateInMeters .lowerCharge) := by
      abel
    _ = lengthInMeters setup.horizontalOffset • setup.rightwardUnit +
          lengthInMeters setup.verticalSeparation • setup.upwardUnit := by
      rw [_geometry.dotRelativeToUpperCharge,
        _geometry.upperRelativeToLowerCharge]

/-- Labels attached to the four displayed field-strength choices. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Field strength in newtons per coulomb printed beside each answer label. -/
def AnswerChoice.fieldStrengthInNewtonsPerCoulomb : AnswerChoice → ℝ
  | .A => 1300
  | .B => 5300
  | .C => 1200
  | .D => 3500

/-- The answer label recorded by the supplied dataset metadata. -/
def recordedDatasetAnswer : AnswerChoice := .C

/-!
`value` rounds to `rounded` to the nearest thousand.  Dividing by `1000` and
using Mathlib's `round` makes the intended two-significant-figure convention
for a value near `1.2 * 10^4` explicit.
-/
def RoundsToNearestThousand (value rounded : ℝ) : Prop :=
  (1000 : ℝ) * (round (value / 1000) : ℝ) = rounded

/-!
**Blueprint target** `thm:physics:phyx_mini_0914:target`.

Under the primary-image calibration, planar geometry, vector point-charge law,
field superposition, and magnitude calibration, the electric-field strength
at the black dot rounds to `1.2 * 10^4 N/C` to two significant figures.

Indeed, the upper source contributes `10800 N/C` rightward.  The lower source
is at distance `sqrt (0.05^2 + 0.10^2)` metres and contributes a vector of
magnitude `2160 N/C`, giving a total magnitude about `11923.54 N/C`.  Thus the
physical result rounds to `12000 N/C`.  The recorded dataset value `1200 N/C`
does not occur in the conclusion or in any premise.
-/
theorem problem_phyx_mini_0914
    (setup : TwoPointChargeFieldSetup)
    (_scenario : MatchesTwoStationaryPointChargeScenario setup)
    (_figure : MatchesSuppliedTwoChargeFieldFigure setup)
    (_geometry : SatisfiesTwoChargeFigureGeometry setup)
    (_physical : HasPhysicalTwoChargeFieldParameters setup)
    (_constant : UsesTextbookCoulombConstant setup)
    (_coulomb : SatisfiesPointChargeElectricFieldLaw setup)
    (_superposition : SatisfiesElectricFieldSuperposition setup)
    (_magnitude : CalibratesElectricFieldStrengthAtDot setup) :
    RoundsToNearestThousand
      (electricFieldStrengthInNewtonsPerCoulomb setup.fieldStrengthAtDot)
      (12 * (10 : ℝ) ^ 3) := by
  have horizontalOffsetInMeters :
      lengthInMeters setup.horizontalOffset = 5 / 100 := by
    have h :
        100 * lengthInMeters setup.horizontalOffset = 5 := by
      calc
        100 * lengthInMeters setup.horizontalOffset =
            lengthInCentimeters setup.horizontalOffset := rfl
        _ = setup.figure.printedHorizontalDistanceCentimeters :=
          _figure.physicalHorizontalOffsetMatchesLabel
        _ = 5 := _figure.printedHorizontalDistanceIsFiveCentimeters
    linarith only [h]
  have verticalSeparationInMeters :
      lengthInMeters setup.verticalSeparation = 10 / 100 := by
    have h :
        100 * lengthInMeters setup.verticalSeparation = 10 := by
      calc
        100 * lengthInMeters setup.verticalSeparation =
            lengthInCentimeters setup.verticalSeparation := rfl
        _ = setup.figure.printedVerticalSeparationCentimeters :=
          _figure.physicalVerticalSeparationMatchesLabel
        _ = 10 := _figure.printedVerticalSeparationIsTenCentimeters
    linarith only [h]
  have chargeInCoulombsIsThreeNanocoulombs (source : SourceCharge) :
      chargeInCoulombs (setup.charge source) = 3 / (10 : ℝ) ^ 9 := by
    have h := _figure.physicalChargesMatchLabels source
    rw [_figure.bothPrintedChargeLabelsAreThreeNanocoulombs source] at h
    norm_num [chargeInNanocoulombs] at h ⊢
    linarith only [h]
  have upperDisplacement :
      displacementFromSourceToDotInMeters setup .upper =
        (5 / 100 : ℝ) • setup.rightwardUnit := by
    rw [displacementFromSourceToDotInMeters, SourceCharge.toDiagramSite,
      _geometry.dotRelativeToUpperCharge, horizontalOffsetInMeters]
  have lowerDisplacement :
      displacementFromSourceToDotInMeters setup .lower =
        (5 / 100 : ℝ) • setup.rightwardUnit +
          (10 / 100 : ℝ) • setup.upwardUnit := by
    rw [lowerSourceDisplacementInMeters setup _geometry,
      horizontalOffsetInMeters, verticalSeparationInMeters]
  have upperDistance :
      ‖displacementFromSourceToDotInMeters setup .upper‖ = 5 / 100 :=
    upperSourceDistanceInMeters setup _figure _geometry
  have lowerDistanceSquared :
      ‖displacementFromSourceToDotInMeters setup .lower‖ ^ 2 =
        (1 / 80 : ℝ) := by
    rw [lowerDisplacement, norm_add_sq_real, norm_smul, norm_smul,
      _geometry.rightwardDirectionIsUnit, _geometry.upwardDirectionIsUnit,
      real_inner_smul_left, real_inner_smul_right,
      _geometry.displayedDirectionsArePerpendicular]
    norm_num [Real.norm_eq_abs]
  set d : ℝ :=
    ‖displacementFromSourceToDotInMeters setup .lower‖ with d_eq
  clear_value d
  have dSquared : d ^ 2 = (1 / 80 : ℝ) := by
    exact lowerDistanceSquared
  have dPositive : 0 < d := by
    rw [d_eq]
    exact norm_pos_iff.mpr (_physical.bothSourcesSeparatedFromDot .lower)
  have dLowerBound : (1 / 10 : ℝ) < d := by
    apply (sq_lt_sq₀ (by norm_num) dPositive.le).mp
    rw [dSquared]
    norm_num
  have dUpperBound : d < (1 / 8 : ℝ) := by
    apply (sq_lt_sq₀ dPositive.le (by norm_num)).mp
    rw [dSquared]
    norm_num
  have upperField :
      sourceFieldVectorAtDot setup .upper =
        (10800 : ℝ) • setup.rightwardUnit := by
    rw [_coulomb.fieldFromEachSource .upper
        (_physical.bothSourcesSeparatedFromDot .upper),
      _constant.coulombConstantCalibration,
      chargeInCoulombsIsThreeNanocoulombs, upperDistance,
      upperDisplacement]
    norm_num [smul_smul]
  set c : ℝ := 27 / d ^ 3 with c_eq
  clear_value c
  have cPositive : 0 < c := by
    rw [c_eq]
    exact div_pos (by norm_num) (pow_pos dPositive 3)
  have lowerField :
      sourceFieldVectorAtDot setup .lower =
        c • displacementFromSourceToDotInMeters setup .lower := by
    rw [_coulomb.fieldFromEachSource .lower
        (_physical.bothSourcesSeparatedFromDot .lower),
      _constant.coulombConstantCalibration,
      chargeInCoulombsIsThreeNanocoulombs, ← d_eq, c_eq]
    norm_num
  have cTimesDistance : c * d = 2160 := by
    calc
      c * d = (27 / d ^ 3) * d := by rw [c_eq]
      _ = 27 / d ^ 2 := by
        field_simp [ne_of_gt dPositive]
      _ = 2160 := by
        rw [dSquared]
        norm_num
  have upperFieldNorm :
      ‖sourceFieldVectorAtDot setup .upper‖ = 10800 := by
    rw [upperField, norm_smul, _geometry.rightwardDirectionIsUnit]
    norm_num [Real.norm_eq_abs]
  have lowerFieldNorm :
      ‖sourceFieldVectorAtDot setup .lower‖ = 2160 := by
    rw [lowerField, norm_smul, Real.norm_eq_abs,
      abs_of_pos cPositive, ← d_eq, cTimesDistance]
  have rightwardInnerLowerDisplacement :
      inner ℝ setup.rightwardUnit
          (displacementFromSourceToDotInMeters setup .lower) =
        1 / 20 := by
    rw [lowerDisplacement, inner_add_right, real_inner_smul_right,
      real_inner_smul_right, real_inner_self_eq_norm_sq,
      _geometry.rightwardDirectionIsUnit,
      _geometry.displayedDirectionsArePerpendicular]
    norm_num
  have innerOfSourceFields :
      inner ℝ (sourceFieldVectorAtDot setup .upper)
          (sourceFieldVectorAtDot setup .lower) =
        540 * c := by
    rw [upperField, lowerField, real_inner_smul_left,
      real_inner_smul_right, rightwardInnerLowerDisplacement]
    ring
  have cLowerBound : 17280 < c := by
    have hproduct :=
      mul_lt_mul_of_pos_left dUpperBound cPositive
    rw [cTimesDistance] at hproduct
    norm_num at hproduct ⊢
    linarith only [hproduct]
  have cUpperBound : c < 21600 := by
    have hproduct :=
      mul_lt_mul_of_pos_left dLowerBound cPositive
    rw [cTimesDistance] at hproduct
    norm_num at hproduct ⊢
    linarith only [hproduct]
  have innerLowerBound :
      9331200 <
        inner ℝ (sourceFieldVectorAtDot setup .upper)
          (sourceFieldVectorAtDot setup .lower) := by
    rw [innerOfSourceFields]
    linarith only [cLowerBound]
  have innerUpperBound :
      inner ℝ (sourceFieldVectorAtDot setup .upper)
          (sourceFieldVectorAtDot setup .lower) <
        11664000 := by
    rw [innerOfSourceFields]
    linarith only [cUpperBound]
  have totalFieldNormSquared :
      ‖totalFieldVectorAtDot setup‖ ^ 2 =
        10800 ^ 2 +
          2 * inner ℝ (sourceFieldVectorAtDot setup .upper)
            (sourceFieldVectorAtDot setup .lower) +
          2160 ^ 2 := by
    rw [_superposition.totalFieldIsSourceSum, norm_add_sq_real,
      upperFieldNorm, lowerFieldNorm]
  have totalFieldNormLowerBound :
      11500 < ‖totalFieldVectorAtDot setup‖ := by
    apply (sq_lt_sq₀ (by norm_num)
      (norm_nonneg (totalFieldVectorAtDot setup))).mp
    linarith only [totalFieldNormSquared, innerLowerBound]
  have totalFieldNormUpperBound :
      ‖totalFieldVectorAtDot setup‖ < 12500 := by
    apply (sq_lt_sq₀ (norm_nonneg (totalFieldVectorAtDot setup))
      (by norm_num)).mp
    linarith only [totalFieldNormSquared, innerUpperBound]
  have roundedTotalField :
      round
          (electricFieldStrengthInNewtonsPerCoulomb
              setup.fieldStrengthAtDot / 1000) =
        12 := by
    rw [_magnitude.strengthIsTotalFieldNorm]
    apply (round_eq_iff).2
    constructor
    · norm_num
      linarith only [totalFieldNormLowerBound]
    · norm_num
      linarith only [totalFieldNormUpperBound]
  unfold RoundsToNearestThousand
  rw [roundedTotalField]
  norm_num

end PhyXMiniProblems.ProblemPhyXMini0914
