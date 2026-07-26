import Mathlib
import Physlib.Electromagnetism.Basic
import Physlib.Units.WithDim.Basic

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0860

open Dimension
open scoped BigOperators

/-!
# Charge inferred from the electric potential at a rectangular corner

The supplied image places an unknown positive point charge `q` at the
top-left corner of a `2.0 cm` by `4.0 cm` rectangle, a `-5.0 nC` charge at the
top-right corner, a `+5.0 nC` charge at the bottom-left corner, and a black
observation dot at the bottom-right corner.  The potential reported at the dot
is `3140 V`.

Charges, side lengths, and electric potentials are represented by Physlib's
unit-independent `Dimensionful` quantities.  Real numbers below are only
coordinate or named-unit readouts.  The planar coordinates describe the plane
in three-dimensional space containing all three sources and the observation
point; the usual three-dimensional point-charge potential still depends only
on their Euclidean separation.

The printed potential and the textbook value `k = 9 * 10^9 N m^2/C^2` are
given to the displayed precision.  `RoundsToNearestTenVolts` records that
precision rather than imposing an inconsistent exact equation: with the
figure data, `q = 10 nC` gives approximately `3137.46 V`, which is printed as
`3140 V`.

Assumption/target split:

* governing laws: the scalar point-charge potential law with zero reference
  at infinity, and linear superposition of the three source potentials;
* previous-part results: none;
* figure/data readouts: charge signs and fixed `5.0 nC` labels, `2.0 cm` and
  `4.0 cm` rectangle labels and coordinates, the `3140 V` rounded readout, the
  introductory-physics Coulomb-constant calibration, and the four displayed
  charge choices;
* target conclusions: the unknown charge has the `10 nC` readout associated
  with recorded answer D, and no other displayed choice has that readout.

Neither the `10 nC` conclusion nor answer D occurs in a premise selecting the
unknown charge.  The multiple-choice premise says only that the charge equals
one of all four displayed candidates.
-/

/-! ## Dimensionful quantities and calibrated unit readouts -/

/-- A nonnegative, unit-independent physical length. -/
abbrev LengthQuantity : Type :=
  Dimensionful (WithDim L𝓭 NNReal)

/-- A signed, unit-independent physical electric charge. -/
abbrev SignedChargeQuantity : Type :=
  Dimensionful (WithDim C𝓭 ℝ)

/-- The dimension `M L² T⁻² C⁻¹` of electrostatic potential. -/
def electricPotentialDimension : Dimension :=
  M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹ * C𝓭⁻¹

/-- A signed, unit-independent electrostatic potential. -/
abbrev ElectricPotentialQuantity : Type :=
  Dimensionful (WithDim electricPotentialDimension ℝ)

/-- Read a physical length in a selected Physlib length unit. -/
def lengthReadout (unit : LengthUnit) (length : LengthQuantity) : ℝ :=
  ((length {UnitChoices.SI with length := unit}).val : ℝ)

/-- Coherent-SI metre readout of a physical length. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.meters length

/-- Centimetre readout used by the two dimension labels in the image. -/
def lengthInCentimeters (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.centimeters length

/-- Read a signed physical charge in a selected Physlib charge unit. -/
def chargeReadout (unit : ChargeUnit) (charge : SignedChargeQuantity) : ℝ :=
  (charge {UnitChoices.SI with charge := unit}).val

/-- The charge unit `10⁻⁹ C` used by the three charge labels and choices. -/
def nanocoulombUnit : ChargeUnit :=
  ChargeUnit.scale ((1 / 10 : ℝ) ^ 9) ChargeUnit.coulombs

/-- Coherent-SI coulomb readout of a signed physical charge. -/
def chargeInCoulombs (charge : SignedChargeQuantity) : ℝ :=
  chargeReadout ChargeUnit.coulombs charge

/-- Nanocoulomb readout used by the printed source labels and answer choices. -/
def chargeInNanocoulombs (charge : SignedChargeQuantity) : ℝ :=
  chargeReadout nanocoulombUnit charge

/-- Coherent-SI readout of an electrostatic potential in volts. -/
def potentialInVolts (potential : ElectricPotentialQuantity) : ℝ :=
  (potential UnitChoices.SI).val

/-! ## Figure labels and the physical setup -/

/-- The four geometrical roles visible in the supplied rectangular diagram. -/
inductive FigurePoint where
  | topLeft
  | topRight
  | bottomLeft
  | observationDot
  deriving DecidableEq, Fintype, Repr

/-- The three point charges, named by their role in the image. -/
inductive SourceCharge where
  | unknownQ
  | negativeFive
  | positiveFive
  deriving DecidableEq, Fintype, Repr

/-- The corner occupied by each of the three source charges. -/
def expectedSourcePoint : SourceCharge → FigurePoint
  | .unknownQ => .topLeft
  | .negativeFive => .topRight
  | .positiveFive => .bottomLeft

/-- The plus or minus glyph drawn inside a source circle. -/
inductive FigureChargeSign where
  | positive
  | negative
  deriving DecidableEq, Repr

/-- The sign glyph associated with each source in the primary image. -/
def expectedSourceSign : SourceCharge → FigureChargeSign
  | .unknownQ => .positive
  | .negativeFive => .negative
  | .positiveFive => .positive

/-- Literal text printed next to each source circle. -/
def expectedPrintedChargeText : SourceCharge → String
  | .unknownQ => "q"
  | .negativeFive => "-5.0 nC"
  | .positiveFive => "5.0 nC"

/-- Literal presentation data transcribed from image `860.png`. -/
structure RectangularPotentialFigure where
  sourcePoint : SourceCharge → FigurePoint
  sourceSign : SourceCharge → FigureChargeSign
  printedChargeText : SourceCharge → String
  blackDotPoint : FigurePoint
  blackDotShown : Bool
  blackDotHasChargeLabel : Bool
  horizontalDashedSegmentShown : Bool
  verticalDashedSegmentShown : Bool
  horizontalLabelCentimeters : ℝ
  verticalLabelCentimeters : ℝ

/-!
The independent physical quantities and potential fields in the problem.
`charge .unknownQ` is an unknown dimensionful charge, and is not defined from
the recorded answer or from a displayed choice.
-/
structure RectangularPointChargePotentialSetup where
  figure : RectangularPotentialFigure
  rectangleWidth : LengthQuantity
  rectangleHeight : LengthQuantity
  pointPosition : FigurePoint → Space 2
  charge : SourceCharge → SignedChargeQuantity
  electromagneticSystem : Electromagnetism.EMSystem
  sourcePotential : SourceCharge → Space 2 → ElectricPotentialQuantity
  totalPotential : Space 2 → ElectricPotentialQuantity
  reportedPotentialVolts : ℝ

/-- Position in the charge plane of a named source. -/
def sourcePosition
    (setup : RectangularPointChargePotentialSetup)
    (source : SourceCharge) : Space 2 :=
  setup.pointPosition (setup.figure.sourcePoint source)

/-- Position marked by the black observation dot. -/
def observationPosition
    (setup : RectangularPointChargePotentialSetup) : Space 2 :=
  setup.pointPosition setup.figure.blackDotPoint

/-- Explicitly metre-valued coordinate vector associated with a planar point. -/
def positionVectorInMeters (point : Space 2) : EuclideanSpace ℝ (Fin 2) :=
  !₂[point.val 0, point.val 1]

/-- Displacement from a named source to an arbitrary planar point, in metres. -/
def displacementFromSourceInMeters
    (setup : RectangularPointChargePotentialSetup)
    (source : SourceCharge) (point : Space 2) :
    EuclideanSpace ℝ (Fin 2) :=
  positionVectorInMeters point -
    positionVectorInMeters (sourcePosition setup source)

/-- Euclidean source-to-point separation in metres. -/
def sourceDistanceInMeters
    (setup : RectangularPointChargePotentialSetup)
    (source : SourceCharge) (point : Space 2) : ℝ :=
  ‖displacementFromSourceInMeters setup source point‖

/-! ## Multiple-choice data and displayed precision -/

/-- Labels attached to the four displayed charge choices. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Nanocoulomb value printed by each answer choice. -/
def AnswerChoice.chargeInNanocoulombs : AnswerChoice → ℝ
  | .A => 12
  | .B => 14
  | .C => 20
  | .D => 10

/-- Answer label recorded in the supplied dataset metadata. -/
def recordedDatasetAnswer : AnswerChoice := .D

/-- Agreement with a voltage printed to the nearest ten volts. -/
def RoundsToNearestTenVolts (actual displayed : ℝ) : Prop :=
  |actual - displayed| < 5

/-! ## Problem data and primary-image evidence -/

/-!
The literal figure features, their dimensional readouts, the reported
potential, and their association with the physical sources.  This contains no
numerical value for the unknown charge.
-/
structure MatchesSuppliedPotentialFigure
    (setup : RectangularPointChargePotentialSetup) : Prop where
  sourceLocations : ∀ source,
    setup.figure.sourcePoint source = expectedSourcePoint source
  sourceSignGlyphs : ∀ source,
    setup.figure.sourceSign source = expectedSourceSign source
  sourceTexts : ∀ source,
    setup.figure.printedChargeText source = expectedPrintedChargeText source
  negativeFiveChargeLabel :
    chargeInNanocoulombs (setup.charge .negativeFive) = -5
  positiveFiveChargeLabel :
    chargeInNanocoulombs (setup.charge .positiveFive) = 5
  unknownChargeIsPositive :
    0 < chargeInCoulombs (setup.charge .unknownQ)
  observationDotLocation :
    setup.figure.blackDotPoint = .observationDot
  observationDotIsShown : setup.figure.blackDotShown = true
  observationDotIsUnlabelled :
    setup.figure.blackDotHasChargeLabel = false
  noSourceAtObservationDot : ∀ source,
    setup.figure.sourcePoint source ≠ setup.figure.blackDotPoint
  horizontalDashedSegment :
    setup.figure.horizontalDashedSegmentShown = true
  verticalDashedSegment : setup.figure.verticalDashedSegmentShown = true
  horizontalPrintedLabel : setup.figure.horizontalLabelCentimeters = 2
  verticalPrintedLabel : setup.figure.verticalLabelCentimeters = 4
  widthMatchesHorizontalLabel :
    lengthInCentimeters setup.rectangleWidth =
      setup.figure.horizontalLabelCentimeters
  heightMatchesVerticalLabel :
    lengthInCentimeters setup.rectangleHeight =
      setup.figure.verticalLabelCentimeters
  widthInMeters : lengthInMeters setup.rectangleWidth = 2 / 100
  heightInMeters : lengthInMeters setup.rectangleHeight = 4 / 100
  bottomLeftAtOrigin :
    positionVectorInMeters (setup.pointPosition .bottomLeft) = !₂[0, 0]
  topLeftCoordinates :
    positionVectorInMeters (setup.pointPosition .topLeft) =
      !₂[0, lengthInMeters setup.rectangleHeight]
  topRightCoordinates :
    positionVectorInMeters (setup.pointPosition .topRight) =
      !₂[lengthInMeters setup.rectangleWidth,
        lengthInMeters setup.rectangleHeight]
  observationCoordinates :
    positionVectorInMeters (setup.pointPosition .observationDot) =
      !₂[lengthInMeters setup.rectangleWidth, 0]
  reportedPotential : setup.reportedPotentialVolts = 3140
  potentialReportedToDisplayedPrecision :
    RoundsToNearestTenVolts
      (potentialInVolts
        (setup.totalPotential (observationPosition setup)))
      setup.reportedPotentialVolts

/-!
The multiple-choice convention restricts the unknown to one of all four
displayed values.  It does not select D or assert the requested `10 nC`
conclusion.
-/
structure UnknownChargeIsOneOfDisplayedChoices
    (setup : RectangularPointChargePotentialSetup) : Prop where
  isDisplayedChoice : ∃ choice : AnswerChoice,
    chargeInNanocoulombs (setup.charge .unknownQ) =
      choice.chargeInNanocoulombs

/-!
The school-physics approximation to Coulomb's constant used with the displayed
three-significant-figure potential.  The scalar is the coherent-SI readout in
`N m²/C²`.
-/
structure UsesIntroductoryCoulombConstant
    (setup : RectangularPointChargePotentialSetup) : Prop where
  coulombConstantCalibration :
    setup.electromagneticSystem.coulombConstant = 9 * 10 ^ 9

/-- Positivity and separation conditions selecting the physical branch. -/
structure HasPhysicalPointChargeParameters
    (setup : RectangularPointChargePotentialSetup) : Prop where
  widthPositive : 0 < lengthInMeters setup.rectangleWidth
  heightPositive : 0 < lengthInMeters setup.rectangleHeight
  coulombConstantPositive :
    0 < setup.electromagneticSystem.coulombConstant
  sourcesSeparatedFromObservation : ∀ source,
    0 < sourceDistanceInMeters setup source (observationPosition setup)

/-! ## Governing electrostatic laws -/

/-!
With electric potential zero at infinity, a point charge `Q` at distance `r`
contributes `k Q / r`.  This all-points law is stated away from each source and
contains no requested value of `q`.
-/
structure SatisfiesPointChargePotentialLaw
    (setup : RectangularPointChargePotentialSetup) : Prop where
  potentialOfEachSource : ∀ source point,
    point ≠ sourcePosition setup source →
      potentialInVolts (setup.sourcePotential source point) =
        setup.electromagneticSystem.coulombConstant *
          chargeInCoulombs (setup.charge source) /
            sourceDistanceInMeters setup source point

/-- The total scalar potential is the sum of all three source potentials. -/
structure SatisfiesElectricPotentialSuperposition
    (setup : RectangularPointChargePotentialSetup) : Prop where
  totalPotentialIsSourceSum : ∀ point,
    potentialInVolts (setup.totalPotential point) =
      ∑ source : SourceCharge,
        potentialInVolts (setup.sourcePotential source point)

/-! ## Geometry and potential consequences -/

/-!
The rectangle coordinates imply source-to-dot distances `2√5 cm`, `4 cm`,
and `2 cm` for the unknown, negative, and positive sources respectively.
-/
lemma sourceDistancesAtObservation
    (setup : RectangularPointChargePotentialSetup)
    (_figure : MatchesSuppliedPotentialFigure setup) :
    sourceDistanceInMeters setup .unknownQ (observationPosition setup) =
        Real.sqrt 20 / 100 ∧
      sourceDistanceInMeters setup .negativeFive (observationPosition setup) =
        4 / 100 ∧
      sourceDistanceInMeters setup .positiveFive (observationPosition setup) =
        2 / 100 := by
  constructor
  · simp [sourceDistanceInMeters, displacementFromSourceInMeters,
      sourcePosition, observationPosition, _figure.sourceLocations,
      expectedSourcePoint, _figure.observationDotLocation,
      _figure.observationCoordinates, _figure.topLeftCoordinates,
      _figure.widthInMeters, _figure.heightInMeters,
      EuclideanSpace.norm_eq, Fin.sum_univ_two]
    rw [show (2 / 100 : ℝ) ^ 2 + (4 / 100 : ℝ) ^ 2 =
      20 / 10000 by norm_num]
    rw [Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 20)]
    norm_num
  · constructor
    · simp [sourceDistanceInMeters, displacementFromSourceInMeters,
        sourcePosition, observationPosition, _figure.sourceLocations,
        expectedSourcePoint, _figure.observationDotLocation,
        _figure.observationCoordinates, _figure.topRightCoordinates,
        _figure.widthInMeters, _figure.heightInMeters,
        EuclideanSpace.norm_eq, Fin.sum_univ_two,
        Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 4 / 100)]
    · simp [sourceDistanceInMeters, displacementFromSourceInMeters,
        sourcePosition, observationPosition, _figure.sourceLocations,
        expectedSourcePoint, _figure.observationDotLocation,
        _figure.observationCoordinates, _figure.bottomLeftAtOrigin,
        _figure.widthInMeters, EuclideanSpace.norm_eq, Fin.sum_univ_two,
        Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2 / 100)]

/-!
Point-charge potential and superposition give the source-by-source expression
for the potential at the observation dot.  Its right-hand side contains only
independent source data, geometry, and the governing Coulomb constant.
-/
lemma totalPotentialAtObservation_eq_coulombSum
    (setup : RectangularPointChargePotentialSetup)
    (_physical : HasPhysicalPointChargeParameters setup)
    (_pointCharge : SatisfiesPointChargePotentialLaw setup)
    (_superposition : SatisfiesElectricPotentialSuperposition setup) :
    potentialInVolts
        (setup.totalPotential (observationPosition setup)) =
      ∑ source : SourceCharge,
        setup.electromagneticSystem.coulombConstant *
          chargeInCoulombs (setup.charge source) /
            sourceDistanceInMeters setup source (observationPosition setup) := by
  rw [_superposition.totalPotentialIsSourceSum]
  apply Finset.sum_congr rfl
  intro source _
  rw [_pointCharge.potentialOfEachSource]
  intro hEq
  have hdist := _physical.sourcesSeparatedFromObservation source
  rw [hEq] at hdist
  simp [sourceDistanceInMeters, displacementFromSourceInMeters] at hdist

/-!
The rounded `3140 V` readout, Coulomb's potential law, and the three-source
geometry select the `10 nC` candidate.  Hence answer D is the unique displayed
charge choice matching the unknown physical charge.

This declaration corresponds to
`thm:physics:phyx_mini_0860:target`.
-/
theorem problem_phyx_mini_0860
    (setup : RectangularPointChargePotentialSetup)
    (hFigure : MatchesSuppliedPotentialFigure setup)
    (hChoices : UnknownChargeIsOneOfDisplayedChoices setup)
    (hConstant : UsesIntroductoryCoulombConstant setup)
    (hPhysical : HasPhysicalPointChargeParameters setup)
    (hPointCharge : SatisfiesPointChargePotentialLaw setup)
    (hSuperposition : SatisfiesElectricPotentialSuperposition setup) :
    chargeInNanocoulombs (setup.charge .unknownQ) =
        recordedDatasetAnswer.chargeInNanocoulombs ∧
      ∀ other : AnswerChoice, other ≠ recordedDatasetAnswer →
        chargeInNanocoulombs (setup.charge .unknownQ) ≠
          other.chargeInNanocoulombs := by
  have charge_coulombs_eq (q : SignedChargeQuantity) :
      chargeInCoulombs q = chargeInNanocoulombs q / 10 ^ 9 := by
    have hscale := congrArg WithDim.val
      (q.2 UnitChoices.SI
        {UnitChoices.SI with charge := nanocoulombUnit})
    change chargeInNanocoulombs q =
      (↑(UnitChoices.SI.dimScale
        {UnitChoices.SI with charge := nanocoulombUnit} C𝓭) : ℝ) *
        chargeInCoulombs q at hscale
    have hfactor :
        (↑(UnitChoices.SI.dimScale
          {UnitChoices.SI with charge := nanocoulombUnit} C𝓭) : ℝ) =
        1000000000 := by
      norm_num [UnitChoices.dimScale, C𝓭, nanocoulombUnit,
        ChargeUnit.scale, ChargeUnit.coulombs, ChargeUnit.div_eq_val]
      rfl
    rw [hfactor] at hscale
    norm_num at hscale ⊢
    linarith
  obtain ⟨hUnknownDistance, hNegativeDistance, hPositiveDistance⟩ :=
    sourceDistancesAtObservation setup hFigure
  have hPotential := totalPotentialAtObservation_eq_coulombSum
    setup hPhysical hPointCharge hSuperposition
  have hSourceSum (f : SourceCharge → ℝ) :
      ∑ source : SourceCharge, f source =
        f .unknownQ + f .negativeFive + f .positiveFive := by
    rw [show (Finset.univ : Finset SourceCharge) =
      {.unknownQ, .negativeFive, .positiveFive} by
        ext source
        fin_cases source <;> simp]
    simp
    ring
  have hsqrt_pos : 0 < Real.sqrt 20 :=
    Real.sqrt_pos.2 (by norm_num)
  have hsqrt_sq : (Real.sqrt 20) ^ 2 = 20 :=
    Real.sq_sqrt (by norm_num)
  have hPotentialFormula :
      potentialInVolts
          (setup.totalPotential (observationPosition setup)) =
        1125 + 45 * Real.sqrt 20 *
          chargeInNanocoulombs (setup.charge .unknownQ) := by
    rw [hPotential, hSourceSum, hConstant.coulombConstantCalibration,
      charge_coulombs_eq, charge_coulombs_eq, charge_coulombs_eq,
      hFigure.negativeFiveChargeLabel, hFigure.positiveFiveChargeLabel,
      hUnknownDistance, hNegativeDistance, hPositiveDistance]
    field_simp
    ring_nf
    rw [hsqrt_sq]
    ring
  have hPotentialUpper :
      potentialInVolts
          (setup.totalPotential (observationPosition setup)) < 3145 := by
    have hRounded := hFigure.potentialReportedToDisplayedPrecision
    rw [RoundsToNearestTenVolts, hFigure.reportedPotential, abs_lt] at hRounded
    linarith
  have hsqrt_gt_four : 4 < Real.sqrt 20 := by
    rw [Real.lt_sqrt (by norm_num)]
    norm_num
  obtain ⟨choice, hChoice⟩ := hChoices.isDisplayedChoice
  fin_cases choice
  · norm_num [AnswerChoice.chargeInNanocoulombs] at hChoice
    rw [hChoice] at hPotentialFormula
    linarith
  · norm_num [AnswerChoice.chargeInNanocoulombs] at hChoice
    rw [hChoice] at hPotentialFormula
    linarith
  · norm_num [AnswerChoice.chargeInNanocoulombs] at hChoice
    rw [hChoice] at hPotentialFormula
    linarith
  · norm_num [AnswerChoice.chargeInNanocoulombs] at hChoice
    rw [hChoice]
    constructor
    · rfl
    · intro other hOther
      fin_cases other
      · norm_num [recordedDatasetAnswer,
          AnswerChoice.chargeInNanocoulombs]
      · norm_num [recordedDatasetAnswer,
          AnswerChoice.chargeInNanocoulombs]
      · norm_num [recordedDatasetAnswer,
          AnswerChoice.chargeInNanocoulombs]
      · exact (hOther rfl).elim

end PhyXMiniProblems.ProblemPhyXMini0860
