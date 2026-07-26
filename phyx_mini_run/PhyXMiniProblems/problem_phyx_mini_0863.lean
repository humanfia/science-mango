import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Physlib.Electromagnetism.Basic
import Physlib.Units.WithDim.Basic

/- USER: The assigned Lean file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0863

open Dimension

/-!
# Potential above the midpoint of an oppositely charged split rod

The primary image shows a horizontal rod of total length `L`, divided at its
midpoint.  The left half carries uniformly distributed total charge `+Q` and
the right half carries uniformly distributed total charge `-Q`.  The
observation dot is a perpendicular distance `d` above the division point.

The two source points at axial coordinates `-x` and `x` are equidistant from
the dot and carry opposite line-charge densities.  Coulomb superposition
therefore makes their scalar-potential contributions cancel.

All basic physical quantities below are unit-independent Physlib quantities.
Real numbers are used only for coherent-SI readouts, the figure's coordinate
chart, and the numerical volt values printed in the answer choices.

Assumption/target split:

* governing laws: uniform equal-and-opposite half-rod charge densities,
  total-charge accounting, and scalar Coulomb-potential superposition with
  zero potential at spatial infinity;
* previous-part results: none;
* figure/data readouts: a horizontal rod of length `L`, its central division,
  positive marks on the left, negative marks on the right, and a dot directly
  above the division by the distance `d`;
* target conclusions: the electric potential at the dot is exactly `0 V`, and
  this uniquely selects displayed answer D.
-/

/-! ## Dimensionful physical quantities and coherent-SI readouts -/

/-- The dimension `C L⁻¹` of linear electric-charge density. -/
def linearChargeDensityDimension : Dimension := C𝓭 * L𝓭⁻¹

/-- The dimension `M L² T⁻² C⁻¹` of electric potential. -/
def electricPotentialDimension : Dimension :=
  M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹ * C𝓭⁻¹

/-- A nonnegative, unit-independent physical length. -/
abbrev LengthQuantity : Type :=
  Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative, unit-independent magnitude of electric charge. -/
abbrev ChargeMagnitudeQuantity : Type :=
  Dimensionful (WithDim C𝓭 NNReal)

/-- A signed, unit-independent physical linear charge density. -/
abbrev LinearChargeDensityQuantity : Type :=
  Dimensionful (WithDim linearChargeDensityDimension ℝ)

/-- A signed, unit-independent physical electric potential. -/
abbrev ElectricPotentialQuantity : Type :=
  Dimensionful (WithDim electricPotentialDimension ℝ)

/-- Read a physical length in coherent-SI metres. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  ((length UnitChoices.SI).val : ℝ)

/-- Read a physical charge magnitude in coherent-SI coulombs. -/
def chargeMagnitudeInCoulombs (charge : ChargeMagnitudeQuantity) : ℝ :=
  ((charge UnitChoices.SI).val : ℝ)

/-- Read a signed line-charge density in coherent-SI coulombs per metre. -/
def linearChargeDensityInCoulombsPerMeter
    (density : LinearChargeDensityQuantity) : ℝ :=
  (density UnitChoices.SI).val

/-- Read a signed electric potential in coherent-SI volts. -/
def electricPotentialInVolts (potential : ElectricPotentialQuantity) : ℝ :=
  (potential UnitChoices.SI).val

/-! ## Charged rod, observation point, and primary-image vocabulary -/

/--
The split rod and its independent charge observables.  The argument of
`linearChargeDensityAt` is an axial coordinate read in SI metres.
-/
structure UniformOppositelyChargedRod where
  totalLength : LengthQuantity
  halfChargeMagnitude : ChargeMagnitudeQuantity
  linearChargeDensityAt : ℝ → LinearChargeDensityQuantity

/-- Distinguished points shown in, or determined by, the primary image. -/
inductive FigurePoint where
  | leftEndpoint
  | divisionPoint
  | rightEndpoint
  | observationDot
  deriving DecidableEq, Fintype, Repr

/-- Qualitative features visible in the supplied bitmap `863.png`. -/
inductive FigureFeature where
  | horizontalRectangularRod
  | centralDivision
  | positiveMarksOnLeftHalf
  | negativeMarksOnRightHalf
  | observationDot
  | verticalDistanceArrow
  | distanceLabelD
  | horizontalLengthArrow
  | lengthLabelL
  deriving DecidableEq, Fintype, Repr

/--
The figure is represented in an SI-metre coordinate chart.  Its physical
labels `L` and `d` remain dimensionful quantities rather than scalar aliases.
-/
structure SplitChargedRodFigure where
  shows : FigureFeature → Bool
  horizontalCoordinateInMeters : FigurePoint → ℝ
  verticalCoordinateInMeters : FigurePoint → ℝ
  lengthArrowStart : FigurePoint
  lengthArrowEnd : FigurePoint
  distanceArrowStart : FigurePoint
  distanceArrowEnd : FigurePoint
  lengthLabelQuantity : LengthQuantity
  distanceLabelQuantity : LengthQuantity

/-- The reference convention for the scalar electric potential. -/
inductive ElectricPotentialReference where
  | zeroAtSpatialInfinity
  | other
  deriving DecidableEq, Repr

/--
The independent physical setup.  In particular, the potential at the dot is
stored as an observable; it is not defined to be any displayed answer value.
-/
structure SplitRodPotentialSetup where
  rod : UniformOppositelyChargedRod
  observationHeight : LengthQuantity
  electricPotentialAtDot : ElectricPotentialQuantity
  electromagneticSystem : Electromagnetism.EMSystem
  potentialReference : ElectricPotentialReference
  figure : SplitChargedRodFigure

/-! ## Figure evidence and physical parameter conditions -/

/--
Transcription of the primary image: the division is the coordinate origin,
the rod endpoints are at `±L/2`, and the dot is at `(0,d)`.  This predicate
contains no potential value or answer choice.
-/
structure MatchesPrimarySplitRodFigure
    (setup : SplitRodPotentialSetup) : Prop where
  everyNamedFeatureShown :
    ∀ feature, setup.figure.shows feature = true
  lengthArrowStartsAtLeftEndpoint :
    setup.figure.lengthArrowStart = .leftEndpoint
  lengthArrowEndsAtRightEndpoint :
    setup.figure.lengthArrowEnd = .rightEndpoint
  distanceArrowStartsAtDivision :
    setup.figure.distanceArrowStart = .divisionPoint
  distanceArrowEndsAtDot :
    setup.figure.distanceArrowEnd = .observationDot
  lengthLabelDenotesTotalRodLength :
    setup.figure.lengthLabelQuantity = setup.rod.totalLength
  distanceLabelDenotesObservationHeight :
    setup.figure.distanceLabelQuantity = setup.observationHeight
  leftEndpointHorizontalCoordinate :
    setup.figure.horizontalCoordinateInMeters .leftEndpoint =
      -(lengthInMeters setup.rod.totalLength / 2)
  divisionHorizontalCoordinate :
    setup.figure.horizontalCoordinateInMeters .divisionPoint = 0
  rightEndpointHorizontalCoordinate :
    setup.figure.horizontalCoordinateInMeters .rightEndpoint =
      lengthInMeters setup.rod.totalLength / 2
  dotHorizontalCoordinate :
    setup.figure.horizontalCoordinateInMeters .observationDot = 0
  rodPointsHaveZeroVerticalCoordinate :
    setup.figure.verticalCoordinateInMeters .leftEndpoint = 0 ∧
      setup.figure.verticalCoordinateInMeters .divisionPoint = 0 ∧
      setup.figure.verticalCoordinateInMeters .rightEndpoint = 0
  dotVerticalCoordinate :
    setup.figure.verticalCoordinateInMeters .observationDot =
      lengthInMeters setup.observationHeight

/-- Positivity assumptions selecting the nondegenerate depicted setup. -/
structure HasPhysicalSplitRodParameters
    (setup : SplitRodPotentialSetup) : Prop where
  rodLengthPositive :
    0 < lengthInMeters setup.rod.totalLength
  observationHeightPositive :
    0 < lengthInMeters setup.observationHeight
  halfChargeMagnitudePositive :
    0 < chargeMagnitudeInCoulombs setup.rod.halfChargeMagnitude
  coulombConstantPositive :
    0 < setup.electromagneticSystem.coulombConstant

/-- The conventional electrostatic choice of zero potential at infinity. -/
structure UsesZeroPotentialAtSpatialInfinity
    (setup : SplitRodPotentialSetup) : Prop where
  referenceIsSpatialInfinity :
    setup.potentialReference = .zeroAtSpatialInfinity

/-! ## Uniform charge and Coulomb-superposition laws -/

/-- SI line-density readout at the axial coordinate `xMeters`. -/
def rodLineChargeDensityInCoulombsPerMeter
    (setup : SplitRodPotentialSetup) (xMeters : ℝ) : ℝ :=
  linearChargeDensityInCoulombsPerMeter
    (setup.rod.linearChargeDensityAt xMeters)

/--
Each half has length `L/2` and total charge of magnitude `Q`, so its uniform
density has magnitude `2Q/L`.  The endpoint convention at the single division
point is immaterial to the line integrals.  The two integral fields explicitly
record that the half-rod totals are `+Q` and `-Q`.
-/
structure SatisfiesUniformOppositeHalfChargeModel
    (setup : SplitRodPotentialSetup) : Prop where
  positiveLeftHalfDensity :
    ∀ xMeters,
      -(lengthInMeters setup.rod.totalLength / 2) ≤ xMeters →
      xMeters < 0 →
      rodLineChargeDensityInCoulombsPerMeter setup xMeters =
        2 * chargeMagnitudeInCoulombs setup.rod.halfChargeMagnitude /
          lengthInMeters setup.rod.totalLength
  negativeRightHalfDensity :
    ∀ xMeters,
      0 ≤ xMeters →
      xMeters ≤ lengthInMeters setup.rod.totalLength / 2 →
      rodLineChargeDensityInCoulombsPerMeter setup xMeters =
        -(2 * chargeMagnitudeInCoulombs setup.rod.halfChargeMagnitude /
          lengthInMeters setup.rod.totalLength)
  leftHalfTotalCharge :
    (∫ xMeters in -(lengthInMeters setup.rod.totalLength / 2)..0,
      rodLineChargeDensityInCoulombsPerMeter setup xMeters) =
        chargeMagnitudeInCoulombs setup.rod.halfChargeMagnitude
  rightHalfTotalCharge :
    (∫ xMeters in 0..lengthInMeters setup.rod.totalLength / 2,
      rodLineChargeDensityInCoulombsPerMeter setup xMeters) =
        -chargeMagnitudeInCoulombs setup.rod.halfChargeMagnitude

/--
Euclidean source-to-dot distance for a source element at axial coordinate
`xMeters`, using the figure coordinates `(x,0)` and `(0,d)`.
-/
def sourceToDotDistanceInMeters
    (setup : SplitRodPotentialSetup) (xMeters : ℝ) : ℝ :=
  Real.sqrt
    (xMeters ^ 2 + lengthInMeters setup.observationHeight ^ 2)

/--
The coherent-SI scalar-potential contribution density `k λ/r`, in volts per
metre, for a rod element at `xMeters`.  Physlib supplies Coulomb's constant as
`Electromagnetism.EMSystem.coulombConstant`.
-/
def potentialContributionDensityInVoltsPerMeter
    (setup : SplitRodPotentialSetup) (xMeters : ℝ) : ℝ :=
  setup.electromagneticSystem.coulombConstant *
      rodLineChargeDensityInCoulombsPerMeter setup xMeters /
    sourceToDotDistanceInMeters setup xMeters

/--
Coulomb superposition for the scalar potential, with the rod supported on
`[-L/2,L/2]`.  This is a general source integral and does not state its value.
-/
structure SatisfiesCoulombPotentialSuperpositionLaw
    (setup : SplitRodPotentialSetup) : Prop where
  potentialIsLineIntegral :
    electricPotentialInVolts setup.electricPotentialAtDot =
      ∫ xMeters in
          -(lengthInMeters setup.rod.totalLength / 2)..
            lengthInMeters setup.rod.totalLength / 2,
        potentialContributionDensityInVoltsPerMeter setup xMeters

/-! ## Symmetry consequences and the current target -/

/-- Reflection across the division leaves the source-to-dot distance fixed. -/
lemma sourceToDotDistance_reflection
    (setup : SplitRodPotentialSetup) (xMeters : ℝ) :
    sourceToDotDistanceInMeters setup (-xMeters) =
      sourceToDotDistanceInMeters setup xMeters := by
  simp [sourceToDotDistanceInMeters]

/-- Opposite source elements have cancelling potential contributions. -/
lemma pairedPotentialContributions_cancel
    (setup : SplitRodPotentialSetup)
    (hUniform : SatisfiesUniformOppositeHalfChargeModel setup)
    (xMeters : ℝ)
    (hxPositive : 0 < xMeters)
    (hxInRightHalf :
      xMeters ≤ lengthInMeters setup.rod.totalLength / 2) :
    potentialContributionDensityInVoltsPerMeter setup (-xMeters) +
        potentialContributionDensityInVoltsPerMeter setup xMeters = 0 := by
  have hLeft :=
    hUniform.positiveLeftHalfDensity
      (-xMeters) (neg_le_neg hxInRightHalf) (neg_neg_of_pos hxPositive)
  have hRight :=
    hUniform.negativeRightHalfDensity xMeters hxPositive.le hxInRightHalf
  rw [potentialContributionDensityInVoltsPerMeter,
    potentialContributionDensityInVoltsPerMeter, hLeft, hRight,
    sourceToDotDistance_reflection]
  ring

/-- Labels of the four voltage answers printed in the question. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Electric potential printed beside each choice, in volts. -/
def AnswerChoice.potentialInVolts : AnswerChoice → ℝ
  | .A => 12 / 10
  | .B => 14 / 10
  | .C => 2
  | .D => 0

/-- A choice is the unique printed value equal to the physical potential. -/
def IsUniqueExactPotentialAnswer
    (setup : SplitRodPotentialSetup) (choice : AnswerChoice) : Prop :=
  electricPotentialInVolts setup.electricPotentialAtDot =
      choice.potentialInVolts ∧
    ∀ other : AnswerChoice,
      electricPotentialInVolts setup.electricPotentialAtDot =
          other.potentialInVolts →
        other = choice

/-- The source dataset's recorded answer, retained only as unused metadata. -/
def recordedDatasetAnswer : AnswerChoice := .D

/-!
Blueprint declaration `thm:physics:phyx_mini_0863:target`.

For equal and opposite uniform half-charges, every source element on one half
has an equidistant, oppositely charged partner on the other half.  Hence the
electric potential at the dot is `0 V`, uniquely selecting answer D.
-/
theorem electricPotentialAtDotOfOppositelyChargedRod
    (setup : SplitRodPotentialSetup)
    (hFigure : MatchesPrimarySplitRodFigure setup)
    (hPhysical : HasPhysicalSplitRodParameters setup)
    (hReference : UsesZeroPotentialAtSpatialInfinity setup)
    (hUniform : SatisfiesUniformOppositeHalfChargeModel setup)
    (hSuperposition : SatisfiesCoulombPotentialSuperpositionLaw setup) :
    electricPotentialInVolts setup.electricPotentialAtDot = 0 ∧
      IsUniqueExactPotentialAnswer setup .D := by
  have hBounds :
      -(lengthInMeters setup.rod.totalLength / 2) ≤
        lengthInMeters setup.rod.totalLength / 2 := by
    linarith [hPhysical.rodLengthPositive]
  have hOddIntegral :
      (∫ xMeters in
          -(lengthInMeters setup.rod.totalLength / 2)..
            lengthInMeters setup.rod.totalLength / 2,
          potentialContributionDensityInVoltsPerMeter setup (-xMeters)) =
        ∫ xMeters in
          -(lengthInMeters setup.rod.totalLength / 2)..
            lengthInMeters setup.rod.totalLength / 2,
          -potentialContributionDensityInVoltsPerMeter setup xMeters := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [MeasureTheory.volume.ae_ne 0] with xMeters hxNonzero
    intro hxInterval
    rw [Set.uIoc_of_le hBounds] at hxInterval
    rcases lt_or_gt_of_ne hxNonzero with hxNegative | hxPositive
    · have hCancel :=
        pairedPotentialContributions_cancel setup hUniform (-xMeters)
          (neg_pos.mpr hxNegative) (by linarith [hxInterval.1])
      rw [neg_neg] at hCancel
      linarith
    · have hCancel :=
        pairedPotentialContributions_cancel setup hUniform xMeters hxPositive
          hxInterval.2
      linarith
  have hReflectedIntegral :
      (∫ xMeters in
          -(lengthInMeters setup.rod.totalLength / 2)..
            lengthInMeters setup.rod.totalLength / 2,
          potentialContributionDensityInVoltsPerMeter setup (-xMeters)) =
        ∫ xMeters in
          -(lengthInMeters setup.rod.totalLength / 2)..
            lengthInMeters setup.rod.totalLength / 2,
          potentialContributionDensityInVoltsPerMeter setup xMeters := by
    simpa only [neg_neg] using
      (intervalIntegral.integral_comp_neg
        (f := potentialContributionDensityInVoltsPerMeter setup)
        (a := -(lengthInMeters setup.rod.totalLength / 2))
        (b := lengthInMeters setup.rod.totalLength / 2))
  have hIntegralZero :
      (∫ xMeters in
          -(lengthInMeters setup.rod.totalLength / 2)..
            lengthInMeters setup.rod.totalLength / 2,
          potentialContributionDensityInVoltsPerMeter setup xMeters) = 0 := by
    rw [intervalIntegral.integral_neg] at hOddIntegral
    linarith
  have hPotential :
      electricPotentialInVolts setup.electricPotentialAtDot = 0 := by
    rw [hSuperposition.potentialIsLineIntegral, hIntegralZero]
  refine ⟨hPotential, ?_⟩
  constructor
  · simpa [AnswerChoice.potentialInVolts] using hPotential
  · intro other hOther
    rw [hPotential] at hOther
    cases other <;> norm_num [AnswerChoice.potentialInVolts] at hOther
    rfl

end PhyXMiniProblems.ProblemPhyXMini0863
