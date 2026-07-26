import Mathlib.Analysis.InnerProductSpace.PiL2
import Physlib.Electromagnetism.Basic
import Physlib.Units.WithDim.Basic

/- USER: The assigned Lean file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0871

open Dimension

/-!
# Electric-field magnitude from parallel equipotential lines

The primary image shows three parallel dashed green equipotential lines.  In
the direction normal to the lines their labels increase from `-200 V` through
`0 V` to `200 V`, and each adjacent pair is separated by `1 cm`.  A black dot
lies on the central line.  The displayed `45°` angle fixes the orientation in
the pictured `x`-`y` plane but does not affect the field magnitude.

Potential, length, position, and electric field are represented by
unit-independent Physlib quantities.  Reals below occur only as coherent-SI
readouts, dimensionless direction components, printed figure values, and
displayed answer values.

Assumption/target split:

* governing laws: potential is constant on an equipotential line, the field
  at the dot is normal to the lines, and a uniform electrostatic field obeys
  `V(q) - V(p) = - E · (q - p)` in the depicted region;
* previous-part results: none;
* figure/data readouts: the three voltage labels, two perpendicular `1 cm`
  gaps, parallel dashed green lines, the dot on the central line, the `x` and
  `y` labels, and the printed `45°` angle;
* current target: the magnitude at the dot is `20 kV/m`, making answer D the
  unique exact displayed match.

No premise stores the requested field magnitude or a selected answer label.
-/

/-! ## Dimensionful physical quantities and coherent-SI readouts -/

/-- Electric potential has dimension energy per charge. -/
def electricPotentialDimension : Dimension :=
  M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹ * C𝓭⁻¹

/-- Electric field has dimension potential per length. -/
def electricFieldDimension : Dimension :=
  M𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹ * C𝓭⁻¹

/-- A nonnegative unit-independent physical length. -/
abbrev LengthQuantity : Type :=
  Dimensionful (WithDim L𝓭 NNReal)

/-- A signed unit-independent electrostatic potential. -/
abbrev ElectricPotentialQuantity : Type :=
  Dimensionful (WithDim electricPotentialDimension ℝ)

/-- A unit-independent position in the pictured two-dimensional plane. -/
abbrev PlanarPositionQuantity : Type :=
  Dimensionful (WithDim L𝓭 (EuclideanSpace ℝ (Fin 2)))

/-- A unit-independent planar electric-field vector. -/
abbrev ElectricFieldVectorQuantity : Type :=
  Dimensionful
    (WithDim electricFieldDimension (EuclideanSpace ℝ (Fin 2)))

/-- Coordinate `0`, the horizontal `x` direction in the image. -/
def xCoordinate : Fin 2 := 0

/-- Coordinate `1`, the vertical `y` direction in the image. -/
def yCoordinate : Fin 2 := 1

/-- Read a physical length in coherent-SI metres. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  ((length UnitChoices.SI).val : ℝ)

/-- Read an electrostatic potential in coherent-SI volts. -/
def electricPotentialInVolts
    (potential : ElectricPotentialQuantity) : ℝ :=
  (potential UnitChoices.SI).val

/-- Read a planar physical position as a vector of metre coordinates. -/
def positionVectorInMeters
    (position : PlanarPositionQuantity) : EuclideanSpace ℝ (Fin 2) :=
  (position UnitChoices.SI).val

/-- Regard the coherent-SI coordinates as a point of Physlib's planar space. -/
def positionInPhyslibSpace (position : PlanarPositionQuantity) : Space 2 :=
  ⟨fun i => positionVectorInMeters position i⟩

/-- Read an electric-field vector in coherent-SI volts per metre. -/
def electricFieldVectorInVoltsPerMeter
    (field : ElectricFieldVectorQuantity) : EuclideanSpace ℝ (Fin 2) :=
  (field UnitChoices.SI).val

/-! ## Figure labels and independent physical setup -/

/-- The three dashed equipotential lines, ordered by increasing potential. -/
inductive PotentialLine where
  | lower
  | middle
  | upper
  deriving DecidableEq, Fintype, Repr

/-- The two adjacent perpendicular gaps measured in the image. -/
inductive AdjacentLineGap where
  | lowerToMiddle
  | middleToUpper
  deriving DecidableEq, Fintype, Repr

/-- The two coordinate axes printed in the primary image. -/
inductive CoordinateAxis where
  | x
  | y
  deriving DecidableEq, Fintype, Repr

/-- Colors needed to transcribe the dashed-line styling. -/
inductive FigureColor where
  | green
  | other
  deriving DecidableEq, Repr

/-!
Literal qualitative and textual information visible in image `871.png`.
Numerical physical readouts are connected to the independent quantities in
`MatchesPrimaryEquipotentialFigure` below.
-/
structure EquipotentialLineFigure where
  printedAxisLabel : CoordinateAxis → String
  lineVisible : PotentialLine → Bool
  lineDashed : PotentialLine → Bool
  lineColor : PotentialLine → FigureColor
  printedPotentialLabel : PotentialLine → String
  linesShownParallel : Bool
  markedDotShown : Bool
  markedDotLine : PotentialLine
  normalSpacingArrowShown : AdjacentLineGap → Bool
  printedSpacingLabel : AdjacentLineGap → String
  printedAcuteAngleInDegrees : ℝ

/-!
Independent physical observables and geometry.  The potential and field are
not defined from the answer table; the electrostatic laws constrain them
separately.
-/
structure EquipotentialFieldSetup where
  adjacentLineSpacing : LengthQuantity
  representativePoint : PotentialLine → PlanarPositionQuantity
  markedPoint : PlanarPositionQuantity
  electricPotentialAt : PlanarPositionQuantity → ElectricPotentialQuantity
  electricFieldAtMarkedPoint : ElectricFieldVectorQuantity
  physlibElectricField : Electromagnetism.ElectricField 2
  observationTime : Time
  lineTangentDirection : EuclideanSpace ℝ (Fin 2)
  increasingPotentialNormalDirection : EuclideanSpace ℝ (Fin 2)
  liesOnShownLine : PotentialLine → PlanarPositionQuantity → Prop
  liesInDepictedUniformRegion : PlanarPositionQuantity → Prop
  figure : EquipotentialLineFigure

/-! ## Primary-image readouts and geometric interpretation -/

/-!
All quantitative and qualitative evidence extracted from the primary image.
The chosen representative points lie on a common normal through the marked
dot; parallelism makes their adjacent separations equal to the displayed
perpendicular spacing.  No electric-field magnitude occurs in this premise.
-/
structure MatchesPrimaryEquipotentialFigure
    (setup : EquipotentialFieldSetup) : Prop where
  xAxisLabel : setup.figure.printedAxisLabel .x = "x"
  yAxisLabel : setup.figure.printedAxisLabel .y = "y"
  everyLineVisible : ∀ line, setup.figure.lineVisible line = true
  everyLineDashed : ∀ line, setup.figure.lineDashed line = true
  everyLineGreen : ∀ line, setup.figure.lineColor line = .green
  lowerPrintedPotential :
    setup.figure.printedPotentialLabel .lower = "-200 V"
  middlePrintedPotential :
    setup.figure.printedPotentialLabel .middle = "0 V"
  upperPrintedPotential :
    setup.figure.printedPotentialLabel .upper = "200 V"
  linesParallel : setup.figure.linesShownParallel = true
  markedDotVisible : setup.figure.markedDotShown = true
  markedDotOnMiddleLine : setup.figure.markedDotLine = .middle
  everySpacingArrowShown :
    ∀ gap, setup.figure.normalSpacingArrowShown gap = true
  lowerGapPrintedLabel :
    setup.figure.printedSpacingLabel .lowerToMiddle = "1 cm"
  upperGapPrintedLabel :
    setup.figure.printedSpacingLabel .middleToUpper = "1 cm"
  printedAcuteAngle : setup.figure.printedAcuteAngleInDegrees = 45
  spacingReadout : lengthInMeters setup.adjacentLineSpacing = 1 / 100
  lowerPotentialReadout :
    electricPotentialInVolts
        (setup.electricPotentialAt (setup.representativePoint .lower)) = -200
  middlePotentialReadout :
    electricPotentialInVolts
        (setup.electricPotentialAt (setup.representativePoint .middle)) = 0
  upperPotentialReadout :
    electricPotentialInVolts
        (setup.electricPotentialAt (setup.representativePoint .upper)) = 200
  everyRepresentativeLiesOnItsLine : ∀ line,
    setup.liesOnShownLine line (setup.representativePoint line)
  markedPointIsMiddleRepresentative :
    setup.markedPoint = setup.representativePoint .middle
  everyRepresentativeInUniformRegion : ∀ line,
    setup.liesInDepictedUniformRegion (setup.representativePoint line)
  markedPointInUniformRegion :
    setup.liesInDepictedUniformRegion setup.markedPoint
  lowerToMiddleDisplacement :
    positionVectorInMeters (setup.representativePoint .middle) -
        positionVectorInMeters (setup.representativePoint .lower) =
      lengthInMeters setup.adjacentLineSpacing •
        setup.increasingPotentialNormalDirection
  middleToUpperDisplacement :
    positionVectorInMeters (setup.representativePoint .upper) -
        positionVectorInMeters (setup.representativePoint .middle) =
      lengthInMeters setup.adjacentLineSpacing •
        setup.increasingPotentialNormalDirection
  tangentPointsDownAndRight :
    0 < setup.lineTangentDirection xCoordinate ∧
      setup.lineTangentDirection yCoordinate < 0
  normalPointsUpAndRight :
    0 < setup.increasingPotentialNormalDirection xCoordinate ∧
      0 < setup.increasingPotentialNormalDirection yCoordinate
  fortyFiveDegreeTangentComponents :
    |setup.lineTangentDirection xCoordinate| =
      |setup.lineTangentDirection yCoordinate|
  fortyFiveDegreeNormalComponents :
    |setup.increasingPotentialNormalDirection xCoordinate| =
      |setup.increasingPotentialNormalDirection yCoordinate|
  tangentNormalOrthogonal :
    inner ℝ setup.lineTangentDirection
        setup.increasingPotentialNormalDirection = 0

/-! Positivity and normalization conditions for the physical geometry. -/
structure HasPhysicalEquipotentialGeometry
    (setup : EquipotentialFieldSetup) : Prop where
  adjacentLineSpacingPositive :
    0 < lengthInMeters setup.adjacentLineSpacing
  tangentDirectionIsUnit : ‖setup.lineTangentDirection‖ = 1
  increasingPotentialNormalIsUnit :
    ‖setup.increasingPotentialNormalDirection‖ = 1

/-! ## Governing electrostatic laws -/

/-!
The standard local model for equally spaced parallel equipotentials in a
uniform electrostatic field:

* potential is constant along each shown line;
* the electric field is normal to those lines;
* potential differences are minus the field line integral, which reduces to
  `ΔV = -E · Δr` for this uniform field; and
* the dimensionful field readout at the dot agrees with Physlib's
  `Electromagnetism.ElectricField` at the same time and position.

These are general physical relations and do not state a numerical magnitude
or identify a multiple-choice answer.
-/
structure SatisfiesUniformEquipotentialElectrostatics
    (setup : EquipotentialFieldSetup) : Prop where
  potentialConstantOnShownLine : ∀ line p q,
    setup.liesOnShownLine line p →
      setup.liesOnShownLine line q →
        electricPotentialInVolts (setup.electricPotentialAt p) =
          electricPotentialInVolts (setup.electricPotentialAt q)
  fieldAtDotIsNormalToLines :
    ∃ signedNormalComponent : ℝ,
      electricFieldVectorInVoltsPerMeter
          setup.electricFieldAtMarkedPoint =
        signedNormalComponent • setup.increasingPotentialNormalDirection
  uniformFieldPotentialDrop : ∀ p q,
    setup.liesInDepictedUniformRegion p →
      setup.liesInDepictedUniformRegion q →
        electricPotentialInVolts (setup.electricPotentialAt q) -
            electricPotentialInVolts (setup.electricPotentialAt p) =
          -inner ℝ
            (electricFieldVectorInVoltsPerMeter
              setup.electricFieldAtMarkedPoint)
            (positionVectorInMeters q - positionVectorInMeters p)
  fieldReadoutAgreesWithPhyslib :
    electricFieldVectorInVoltsPerMeter setup.electricFieldAtMarkedPoint =
      setup.physlibElectricField setup.observationTime
        (positionInPhyslibSpace setup.markedPoint)

/-! ## Requested magnitude and displayed answer choices -/

/-- Electric-field magnitude at the dot in coherent-SI volts per metre. -/
def electricFieldMagnitudeAtDotInVoltsPerMeter
    (setup : EquipotentialFieldSetup) : ℝ :=
  ‖electricFieldVectorInVoltsPerMeter setup.electricFieldAtMarkedPoint‖

/-- Electric-field magnitude at the dot in kilovolts per metre. -/
def electricFieldMagnitudeAtDotInKilovoltsPerMeter
    (setup : EquipotentialFieldSetup) : ℝ :=
  electricFieldMagnitudeAtDotInVoltsPerMeter setup / 1000

/-- Labels attached to the four displayed choices. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Printed field magnitude beside each answer, in kilovolts per metre. -/
def displayedFieldMagnitudeInKilovoltsPerMeter : AnswerChoice → ℝ
  | .A => 10
  | .B => 15
  | .C => 25
  | .D => 20

/-!
A choice is the unique exact match when its displayed value equals the
independently modeled field magnitude and no other displayed value does.
-/
def IsUniqueExactDisplayedMatch
    (setup : EquipotentialFieldSetup) (choice : AnswerChoice) : Prop :=
  electricFieldMagnitudeAtDotInKilovoltsPerMeter setup =
      displayedFieldMagnitudeInKilovoltsPerMeter choice ∧
    ∀ alternative, alternative ≠ choice →
      displayedFieldMagnitudeInKilovoltsPerMeter alternative ≠
        electricFieldMagnitudeAtDotInKilovoltsPerMeter setup

/-!
The potential change between either adjacent pair, divided by its normal
spacing, determines the electric-field magnitude.  This is a derived relation,
not a premise of the model.
-/
lemma electricFieldMagnitudeAtDot_from_adjacentEquipotentials
    (setup : EquipotentialFieldSetup)
    (h_figure : MatchesPrimaryEquipotentialFigure setup)
    (h_geometry : HasPhysicalEquipotentialGeometry setup)
    (h_laws : SatisfiesUniformEquipotentialElectrostatics setup) :
    electricFieldMagnitudeAtDotInVoltsPerMeter setup =
      |(electricPotentialInVolts
            (setup.electricPotentialAt (setup.representativePoint .upper)) -
          electricPotentialInVolts
            (setup.electricPotentialAt (setup.representativePoint .middle))) /
        lengthInMeters setup.adjacentLineSpacing| := by
  obtain ⟨a, hE⟩ := h_laws.fieldAtDotIsNormalToLines
  have hdrop := h_laws.uniformFieldPotentialDrop
    (setup.representativePoint .middle) (setup.representativePoint .upper)
    (h_figure.everyRepresentativeInUniformRegion .middle)
    (h_figure.everyRepresentativeInUniformRegion .upper)
  rw [h_figure.middleToUpperDisplacement, hE] at hdrop
  norm_num [inner_smul_left, inner_smul_right,
    h_geometry.increasingPotentialNormalIsUnit,
    h_figure.spacingReadout, h_figure.middlePotentialReadout,
    h_figure.upperPotentialReadout] at hdrop
  have ha : a = -20000 := by linarith [hdrop]
  unfold electricFieldMagnitudeAtDotInVoltsPerMeter
  rw [hE, norm_smul, h_geometry.increasingPotentialNormalIsUnit]
  norm_num [ha, Real.norm_eq_abs, h_figure.spacingReadout,
    h_figure.middlePotentialReadout, h_figure.upperPotentialReadout]

/-!
The `200 V` change over the `1 cm` perpendicular spacing gives a field
magnitude of `20 kV/m` at the marked dot.  Therefore recorded choice D is the
unique exact match among the displayed values.

This declaration corresponds to blueprint label
`thm:physics:phyx_mini_0871:target`.
-/
theorem electricFieldMagnitudeAtDot_matches_answer_D
    (setup : EquipotentialFieldSetup)
    (h_figure : MatchesPrimaryEquipotentialFigure setup)
    (h_geometry : HasPhysicalEquipotentialGeometry setup)
    (h_laws : SatisfiesUniformEquipotentialElectrostatics setup) :
    electricFieldMagnitudeAtDotInKilovoltsPerMeter setup = 20 ∧
      displayedFieldMagnitudeInKilovoltsPerMeter .D = 20 ∧
      IsUniqueExactDisplayedMatch setup .D := by
  have hmag := electricFieldMagnitudeAtDot_from_adjacentEquipotentials
    setup h_figure h_geometry h_laws
  norm_num [h_figure.spacingReadout, h_figure.middlePotentialReadout,
    h_figure.upperPotentialReadout] at hmag
  have hkV : electricFieldMagnitudeAtDotInKilovoltsPerMeter setup = 20 := by
    norm_num [electricFieldMagnitudeAtDotInKilovoltsPerMeter, hmag]
  refine ⟨hkV, rfl, ?_⟩
  refine ⟨by
    simpa [displayedFieldMagnitudeInKilovoltsPerMeter] using hkV, ?_⟩
  intro alternative hne
  fin_cases alternative <;>
    simp_all [displayedFieldMagnitudeInKilovoltsPerMeter]

end PhyXMiniProblems.ProblemPhyXMini0871
