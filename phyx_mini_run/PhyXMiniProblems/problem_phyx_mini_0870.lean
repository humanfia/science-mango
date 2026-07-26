import Mathlib
import Physlib.Electromagnetism.Basic
import Physlib.SpaceAndTime.Space.LengthUnit
import Physlib.Units.WithDim.Basic

/- USER: The assigned Lean file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0870

open Dimension

/-!
# Electric-field magnitude from an equipotential map

The primary image `870.png` shows three horizontal dashed equipotential lines.
From top to bottom they are labelled `400 V`, `200 V`, and `0 V`; each
adjacent pair is separated by `1 cm`.  A black dot lies on the middle line.

Potential, length, position, and electric-field strength are represented by
unit-independent Physlib quantities.  Real numbers occur only at explicit
unit-readout boundaries, as Cartesian components of Physlib's electric field,
or as printed answer-choice values.

Assumption/target split:

* governing laws: the field norm agrees with the dimensionful strength at the
  dot, the field is normal to the horizontal equipotentials and points toward
  decreasing potential, and its magnitude is `|ΔV| / Δs` across either
  adjacent equipotential gap;
* previous-part results: none;
* figure/data readouts: the three line labels, the two `1 cm` spacings, the
  horizontal dashed-line geometry, and the dot on the `200 V` line;
* current target: the dot's field strength is `20000 V/m = 20 kV/m`, uniquely
  matching displayed answer D.

No premise below states the requested numerical field strength or selects an
answer choice.
-/

/-! ## Dimensionful quantities and coherent-SI readouts -/

/-- Electric potential has physical dimension energy per charge. -/
def electricPotentialDimension : Dimension :=
  M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹ * C𝓭⁻¹

/-- Electric-field strength has physical dimension potential per length. -/
def electricFieldStrengthDimension : Dimension :=
  M𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹ * C𝓭⁻¹

/-- A nonnegative, unit-independent physical length. -/
abbrev LengthQuantity : Type :=
  Dimensionful (WithDim L𝓭 NNReal)

/-- A signed, unit-independent electric potential. -/
abbrev ElectricPotentialQuantity : Type :=
  Dimensionful (WithDim electricPotentialDimension ℝ)

/-- A nonnegative, unit-independent electric-field magnitude. -/
abbrev ElectricFieldStrengthQuantity : Type :=
  Dimensionful (WithDim electricFieldStrengthDimension NNReal)

/-- A unit-independent physical position in the plane of the diagram. -/
abbrev PlanarPositionQuantity : Type :=
  Dimensionful (WithDim L𝓭 (EuclideanSpace ℝ (Fin 2)))

/-- Read a physical length in a selected length unit. -/
def lengthReadout (unit : LengthUnit) (length : LengthQuantity) : ℝ :=
  ((length {UnitChoices.SI with length := unit}).val : ℝ)

/-- Read a physical length in coherent-SI metres. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.meters length

/-- Read a physical length in centimetres. -/
def lengthInCentimeters (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.centimeters length

/-- Read a signed electric potential in coherent-SI volts. -/
def electricPotentialInVolts
    (potential : ElectricPotentialQuantity) : ℝ :=
  (potential UnitChoices.SI).val

/-- Read electric-field strength in coherent-SI volts per metre. -/
def electricFieldStrengthInVoltsPerMeter
    (strength : ElectricFieldStrengthQuantity) : ℝ :=
  ((strength UnitChoices.SI).val : ℝ)

/-- Read electric-field strength in kilovolts per metre. -/
def electricFieldStrengthInKilovoltsPerMeter
    (strength : ElectricFieldStrengthQuantity) : ℝ :=
  electricFieldStrengthInVoltsPerMeter strength / 1000

/-- Read a physical planar position as Cartesian coordinates in metres. -/
def positionVectorInMeters
    (position : PlanarPositionQuantity) : EuclideanSpace ℝ (Fin 2) :=
  (position UnitChoices.SI).val

/-!
View a dimensionful planar position, in the SI coordinate convention, as a
point of Physlib's `Space 2`.  This is the bridge used to evaluate the full
Physlib electric field at the marked dot.
-/
def positionInPhyslibSpace
    (position : PlanarPositionQuantity) : Space 2 :=
  ⟨fun i => positionVectorInMeters position i⟩

/-! ## Figure labels and physical setup -/

/-- The three horizontal equipotential lines, ordered as in the image. -/
inductive EquipotentialLine where
  | upper400V
  | middle200V
  | lower0V
  deriving DecidableEq, Fintype, Repr

/-- The two one-centimetre gaps explicitly indicated in the image. -/
inductive AdjacentGap where
  | upperToMiddle
  | middleToLower
  deriving DecidableEq, Fintype, Repr

/-- Coordinate `0`, horizontal and positive to the right. -/
def xAxis : Fin 2 := 0

/-- Coordinate `1`, vertical and positive upward. -/
def yAxis : Fin 2 := 1

/-!
Literal presentation data supplied by the primary raster.  Its potential and
spacing labels are physical quantities; their printed numerical readouts are
recorded separately in `MatchesSuppliedEquipotentialFigure`.
-/
structure EquipotentialMapFigure where
  lineShownAsDashed : EquipotentialLine → Bool
  lineShownAsHorizontal : EquipotentialLine → Bool
  printedPotentialText : EquipotentialLine → String
  potentialLabel : EquipotentialLine → ElectricPotentialQuantity
  gapArrowShown : AdjacentGap → Bool
  printedGapText : AdjacentGap → String
  spacingLabel : AdjacentGap → LengthQuantity
  blackDotShown : Bool
  lineCarryingBlackDot : EquipotentialLine
  containsNumericalElectricFieldReadout : Bool

/-!
The independent electrostatic observables.  In particular,
`electricFieldStrengthAtDot` is not defined from the potential labels or an
answer choice; it is constrained only by the governing laws below.
-/
structure EquipotentialMapSetup where
  lineRegion : EquipotentialLine → Set PlanarPositionQuantity
  electricPotentialAt : PlanarPositionQuantity → ElectricPotentialQuantity
  adjacentSpacing : AdjacentGap → LengthQuantity
  dotPosition : PlanarPositionQuantity
  electricFieldStrengthAtDot : ElectricFieldStrengthQuantity
  observationTime : Time
  electricField : Electromagnetism.ElectricField 2
  figure : EquipotentialMapFigure

/-- The full Physlib electric-field vector evaluated at the black dot. -/
def electricFieldVectorAtDot
    (setup : EquipotentialMapSetup) : EuclideanSpace ℝ (Fin 2) :=
  setup.electricField setup.observationTime
    (positionInPhyslibSpace setup.dotPosition)

/-! ## Primary-image readouts and governing laws -/

/-!
All unambiguous qualitative and numerical data transcribed from `870.png`.
The final field magnitude is absent: the image itself contains no numerical
electric-field readout.
-/
structure MatchesSuppliedEquipotentialFigure
    (setup : EquipotentialMapSetup) : Prop where
  everyLineDashed :
    ∀ line, setup.figure.lineShownAsDashed line = true
  everyLineHorizontal :
    ∀ line, setup.figure.lineShownAsHorizontal line = true
  upperPrintedPotential :
    setup.figure.printedPotentialText .upper400V = "400 V"
  middlePrintedPotential :
    setup.figure.printedPotentialText .middle200V = "200 V"
  lowerPrintedPotential :
    setup.figure.printedPotentialText .lower0V = "0 V"
  upperPotentialReadout :
    electricPotentialInVolts
        (setup.figure.potentialLabel .upper400V) = 400
  middlePotentialReadout :
    electricPotentialInVolts
        (setup.figure.potentialLabel .middle200V) = 200
  lowerPotentialReadout :
    electricPotentialInVolts
        (setup.figure.potentialLabel .lower0V) = 0
  everyLineHasItsLabelledPotential :
    ∀ line point, point ∈ setup.lineRegion line →
      setup.electricPotentialAt point = setup.figure.potentialLabel line
  everyGapArrowShown :
    ∀ gap, setup.figure.gapArrowShown gap = true
  upperGapPrintedText :
    setup.figure.printedGapText .upperToMiddle = "1 cm"
  lowerGapPrintedText :
    setup.figure.printedGapText .middleToLower = "1 cm"
  spacingLabelsDescribePhysicalGaps :
    ∀ gap, setup.figure.spacingLabel gap = setup.adjacentSpacing gap
  upperGapCentimeterReadout :
    lengthInCentimeters (setup.adjacentSpacing .upperToMiddle) = 1
  lowerGapCentimeterReadout :
    lengthInCentimeters (setup.adjacentSpacing .middleToLower) = 1
  upperGapMeterReadout :
    lengthInMeters (setup.adjacentSpacing .upperToMiddle) = 1 / 100
  lowerGapMeterReadout :
    lengthInMeters (setup.adjacentSpacing .middleToLower) = 1 / 100
  blackDotShown : setup.figure.blackDotShown = true
  blackDotAssignedToMiddleLine :
    setup.figure.lineCarryingBlackDot = .middle200V
  blackDotLiesOnMiddleLine :
    setup.dotPosition ∈ setup.lineRegion .middle200V
  everyLineNonempty :
    ∀ line, (setup.lineRegion line).Nonempty
  noNumericalFieldReadout :
    setup.figure.containsNumericalElectricFieldReadout = false

/-- Positivity conditions for the two physical line separations. -/
structure HasPhysicalEquipotentialSpacing
    (setup : EquipotentialMapSetup) : Prop where
  upperGapPositive :
    0 < lengthInMeters (setup.adjacentSpacing .upperToMiddle)
  lowerGapPositive :
    0 < lengthInMeters (setup.adjacentSpacing .middleToLower)

/-!
Electrostatic field laws used by the solution.  The vector field is normal to
the horizontal equipotential lines, points downward toward decreasing
potential, and has magnitude `|ΔV| / Δs`.  The upper and lower adjacent gaps
are retained separately so both halves of the supplied figure constrain the
same local field observable.  No numerical answer occurs in this structure.
-/
structure SatisfiesElectrostaticEquipotentialLaw
    (setup : EquipotentialMapSetup) : Prop where
  strengthMatchesPhyslibVectorNorm :
    ‖electricFieldVectorAtDot setup‖ =
      electricFieldStrengthInVoltsPerMeter
        setup.electricFieldStrengthAtDot
  fieldNormalToHorizontalEquipotentials :
    electricFieldVectorAtDot setup xAxis = 0
  fieldPointsTowardLowerPotential :
    electricFieldVectorAtDot setup yAxis < 0
  strengthFromUpperAdjacentPotentialDrop :
    electricFieldStrengthInVoltsPerMeter
        setup.electricFieldStrengthAtDot =
      |electricPotentialInVolts
            (setup.figure.potentialLabel .upper400V) -
        electricPotentialInVolts
            (setup.figure.potentialLabel .middle200V)| /
        lengthInMeters (setup.adjacentSpacing .upperToMiddle)
  strengthFromLowerAdjacentPotentialDrop :
    electricFieldStrengthInVoltsPerMeter
        setup.electricFieldStrengthAtDot =
      |electricPotentialInVolts
            (setup.figure.potentialLabel .middle200V) -
        electricPotentialInVolts
            (setup.figure.potentialLabel .lower0V)| /
        lengthInMeters (setup.adjacentSpacing .middleToLower)

/-! ## Displayed choices and current target -/

/-- Labels attached to the four displayed field-strength choices. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Printed field strength beside each choice, in kilovolts per metre. -/
def displayedFieldStrengthInKilovoltsPerMeter : AnswerChoice → ℝ
  | .A => 10
  | .B => 15
  | .C => 25
  | .D => 20

/-!
A displayed choice matches the independently modelled field-strength
observable when their kilovolt-per-metre readouts agree.
-/
def AnswerMatchesFieldStrength
    (setup : EquipotentialMapSetup) (choice : AnswerChoice) : Prop :=
  electricFieldStrengthInKilovoltsPerMeter
      setup.electricFieldStrengthAtDot =
    displayedFieldStrengthInKilovoltsPerMeter choice

/-!
The `200 V` potential drop across either `1 cm` gap gives `20000 V/m` at the
dot.  This numerical result is derived, not stored in the setup or a premise.
-/
lemma electricFieldStrengthAtDot_eq_twentyThousand_voltsPerMeter
    (setup : EquipotentialMapSetup)
    (h_figure : MatchesSuppliedEquipotentialFigure setup)
    (h_spacing : HasPhysicalEquipotentialSpacing setup)
    (h_law : SatisfiesElectrostaticEquipotentialLaw setup) :
    electricFieldStrengthInVoltsPerMeter
        setup.electricFieldStrengthAtDot = 20000 := by
  rw [h_law.strengthFromUpperAdjacentPotentialDrop,
    h_figure.upperPotentialReadout, h_figure.middlePotentialReadout,
    h_figure.upperGapMeterReadout]
  norm_num

/--
At the marked point, the equipotential map determines a field magnitude of
`20000 V/m = 20 kV/m`; among the displayed values, this uniquely selects D.

This is the Lean declaration corresponding to blueprint label
`thm:physics:phyx_mini_0870:target`.
-/
theorem electricFieldMagnitudeAtDot_matches_answer_D
    (setup : EquipotentialMapSetup)
    (h_figure : MatchesSuppliedEquipotentialFigure setup)
    (h_spacing : HasPhysicalEquipotentialSpacing setup)
    (h_law : SatisfiesElectrostaticEquipotentialLaw setup) :
    electricFieldStrengthInVoltsPerMeter
          setup.electricFieldStrengthAtDot = 20 * 10 ^ 3 ∧
      electricFieldStrengthInKilovoltsPerMeter
          setup.electricFieldStrengthAtDot = 20 ∧
      ∀ choice, AnswerMatchesFieldStrength setup choice ↔ choice = .D := by
  have h_strength :=
    electricFieldStrengthAtDot_eq_twentyThousand_voltsPerMeter
      setup h_figure h_spacing h_law
  have h_strength_kV :
      electricFieldStrengthInKilovoltsPerMeter
          setup.electricFieldStrengthAtDot = 20 := by
    rw [electricFieldStrengthInKilovoltsPerMeter, h_strength]
    norm_num
  refine ⟨?_, h_strength_kV, ?_⟩
  · norm_num [h_strength]
  · intro choice
    constructor
    · intro h_choice
      rw [AnswerMatchesFieldStrength, h_strength_kV] at h_choice
      cases choice with
      | A =>
          norm_num [displayedFieldStrengthInKilovoltsPerMeter] at h_choice
      | B =>
          norm_num [displayedFieldStrengthInKilovoltsPerMeter] at h_choice
      | C =>
          norm_num [displayedFieldStrengthInKilovoltsPerMeter] at h_choice
      | D => rfl
    · intro h_choice
      subst choice
      simpa [AnswerMatchesFieldStrength,
        displayedFieldStrengthInKilovoltsPerMeter] using h_strength_kV

end PhyXMiniProblems.ProblemPhyXMini0870
