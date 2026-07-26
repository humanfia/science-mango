import Mathlib
import Physlib.Units.WithDim.Basic

/- USER: The assigned source file did not exist when this autoformalization task began. -/

/-!
# PhyX mini problem 0872: potential change on a directed voltage loop

The primary image shows four black nodes and four green directed edges forming
the cycle `1 → 2 → 3 → 4 → 1`.  The displayed potential changes are
`ΔV₁₂ = 30 V`, `ΔV₂₃ = 50 V`, an unknown `ΔV₃₄`, and `ΔV₄₁ = -60 V`.

Potential changes are signed, unit-independent Physlib quantities with the
physical dimension energy per charge.  Real numbers occur only at the
coherent-SI readout boundary and in the numerical labels printed in the
figure and answer choices.

Assumption/target split:

* governing laws: Kirchhoff's voltage law for the displayed closed directed
  loop;
* previous-part results: none;
* figure/data readouts: node labels and placements, arrow directions, the
  single closed cycle, and the three printed values `30 V`, `50 V`, and
  `-60 V`; the `3 → 4` edge is explicitly recorded as having no numerical
  readout;
* current target conclusions: `ΔV₃₄ = -20 V` and unique selection of answer
  choice D.

The requested `-20 V` value is not a setup field, figure datum, or governing
law.  It occurs only in the answer-choice table and the theorem conclusion.
-/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0872

open Dimension

/-! ## Dimensionful potential changes and coherent-SI readouts -/

/-- The physical dimension of energy, `M L² T⁻²`. -/
def energyDimension : Dimension :=
  M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹

/-- Electric potential difference has physical dimension energy per charge. -/
def electricPotentialDifferenceDimension : Dimension :=
  energyDimension * C𝓭⁻¹

/-- A signed, unit-independent physical electric-potential difference. -/
abbrev ElectricPotentialDifferenceQuantity : Type :=
  Dimensionful (WithDim electricPotentialDifferenceDimension ℝ)

/-- Read a signed electric-potential difference in coherent-SI volts. -/
def potentialDifferenceInVolts
    (potentialDifference : ElectricPotentialDifferenceQuantity) : ℝ :=
  (potentialDifference UnitChoices.SI).val

/-! ## Nodes, directed edges, and primary-figure vocabulary -/

/-- The four numbered nodes in image `872.png`. -/
inductive CircuitNode where
  | one
  | two
  | three
  | four
  deriving DecidableEq, Fintype, Repr

/-- The four potential-change arrows in their displayed cyclic order. -/
inductive DirectedVoltageEdge where
  | oneToTwo
  | twoToThree
  | threeToFour
  | fourToOne
  deriving DecidableEq, Fintype, Repr

/-- Initial node of each arrow, as indicated by its voltage subscript. -/
def DirectedVoltageEdge.initialNode : DirectedVoltageEdge → CircuitNode
  | .oneToTwo => .one
  | .twoToThree => .two
  | .threeToFour => .three
  | .fourToOne => .four

/-- Final node of each arrow, as indicated by its voltage subscript. -/
def DirectedVoltageEdge.finalNode : DirectedVoltageEdge → CircuitNode
  | .oneToTwo => .two
  | .twoToThree => .three
  | .threeToFour => .four
  | .fourToOne => .one

/-- Printed numeral identifying each node. -/
def CircuitNode.printedLabel : CircuitNode → String
  | .one => "1"
  | .two => "2"
  | .three => "3"
  | .four => "4"

/-- Printed symbolic label attached to each directed potential change. -/
def DirectedVoltageEdge.printedDeltaVLabel : DirectedVoltageEdge → String
  | .oneToTwo => "ΔV₁₂"
  | .twoToThree => "ΔV₂₃"
  | .threeToFour => "ΔV₃₄"
  | .fourToOne => "ΔV₄₁"

/-- Coarse relative placement of a node in the supplied graph. -/
inductive FigureNodePlacement where
  | left
  | upper
  | right
  | lower
  deriving DecidableEq, Repr

/-- Placement visible in the supplied raster. -/
def figureNodePlacement : CircuitNode → FigureNodePlacement
  | .one => .left
  | .two => .upper
  | .three => .right
  | .four => .lower

/-!
Literal diagram data.  `printedVoltageInVolts edge = none` means that the
symbolic `ΔV` label is present but the raster supplies no numerical value.
-/
structure DirectedVoltageLoopFigure where
  shownNodeLabel : CircuitNode → String
  shownNodePlacement : CircuitNode → FigureNodePlacement
  nodeShownAsBlackDot : CircuitNode → Bool
  shownPotentialChangeLabel : DirectedVoltageEdge → String
  arrowInitialNode : DirectedVoltageEdge → CircuitNode
  arrowFinalNode : DirectedVoltageEdge → CircuitNode
  printedVoltageInVolts : DirectedVoltageEdge → Option ℝ
  arrowsDrawnGreen : Bool
  formsSingleClosedLoop : Bool

/-!
The four independent physical potential changes and their associated figure.
In particular, the `3 → 4` change is not defined from an answer choice.
-/
structure DirectedVoltageLoopSetup where
  potentialChange :
    DirectedVoltageEdge → ElectricPotentialDifferenceQuantity
  figure : DirectedVoltageLoopFigure

/-! ## Figure/data readouts and governing law -/

/-!
Facts transcribed from `872.png`.  The final field connects only those
physical potential changes for which the raster actually prints a number.
Since the `3 → 4` label has value `none`, this structure does not constrain
the requested potential change numerically.
-/
structure MatchesSuppliedDirectedVoltageFigure
    (setup : DirectedVoltageLoopSetup) : Prop where
  nodeLabelsMatch : ∀ node,
    setup.figure.shownNodeLabel node = node.printedLabel
  nodePlacementsMatch : ∀ node,
    setup.figure.shownNodePlacement node = figureNodePlacement node
  everyNodeShownAsBlackDot : ∀ node,
    setup.figure.nodeShownAsBlackDot node = true
  potentialChangeLabelsMatch : ∀ edge,
    setup.figure.shownPotentialChangeLabel edge = edge.printedDeltaVLabel
  arrowInitialNodesMatch : ∀ edge,
    setup.figure.arrowInitialNode edge = edge.initialNode
  arrowFinalNodesMatch : ∀ edge,
    setup.figure.arrowFinalNode edge = edge.finalNode
  arrowsAreGreen : setup.figure.arrowsDrawnGreen = true
  oneClosedDirectedLoop : setup.figure.formsSingleClosedLoop = true
  deltaV12PrintedReadout :
    setup.figure.printedVoltageInVolts .oneToTwo = some 30
  deltaV23PrintedReadout :
    setup.figure.printedVoltageInVolts .twoToThree = some 50
  deltaV34HasNoPrintedNumericalReadout :
    setup.figure.printedVoltageInVolts .threeToFour = none
  deltaV41PrintedReadout :
    setup.figure.printedVoltageInVolts .fourToOne = some (-60)
  printedReadoutsDescribePhysicalChanges :
    ∀ edge volts,
      setup.figure.printedVoltageInVolts edge = some volts →
        potentialDifferenceInVolts (setup.potentialChange edge) = volts

/-!
Kirchhoff's voltage law in the orientation of the displayed closed loop.  It
states the general closed-loop sum relation and does not assign a value to the
unknown `3 → 4` edge.
-/
structure SatisfiesClosedLoopVoltageLaw
    (setup : DirectedVoltageLoopSetup) : Prop where
  sumOfDirectedPotentialChangesIsZero :
    potentialDifferenceInVolts (setup.potentialChange .oneToTwo) +
        potentialDifferenceInVolts (setup.potentialChange .twoToThree) +
        potentialDifferenceInVolts (setup.potentialChange .threeToFour) +
        potentialDifferenceInVolts (setup.potentialChange .fourToOne) = 0

/-! ## Derived relation and requested answer -/

/-!
Rearranging the governing closed-loop law isolates the unknown edge.  This is
a derived conclusion rather than a field of either premise structure.
-/
lemma deltaV34_eq_negative_sum_of_other_directed_changes
    (setup : DirectedVoltageLoopSetup)
    (_laws : SatisfiesClosedLoopVoltageLaw setup) :
    potentialDifferenceInVolts (setup.potentialChange .threeToFour) =
      -(potentialDifferenceInVolts (setup.potentialChange .oneToTwo) +
        potentialDifferenceInVolts (setup.potentialChange .twoToThree) +
        potentialDifferenceInVolts (setup.potentialChange .fourToOne)) := by
  linarith [_laws.sumOfDirectedPotentialChangesIsZero]

/-- Labels of the four displayed answer choices. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Potential-difference value printed beside each answer, in volts. -/
def answerChoicePotentialDifferenceInVolts : AnswerChoice → ℝ
  | .A => 12
  | .B => -14
  | .C => -200
  | .D => -20

/-!
For the closed directed loop in image `872.png`, the missing potential change
is `ΔV₃₄ = -20 V`; consequently D is the unique answer choice carrying the
computed value.

This is the Lean declaration corresponding to blueprint label
`thm:physics:phyx_mini_0872:target`.
-/
theorem deltaV34_eq_negative_twenty_volts_and_matches_choice_D
    (setup : DirectedVoltageLoopSetup)
    (_figure : MatchesSuppliedDirectedVoltageFigure setup)
    (_laws : SatisfiesClosedLoopVoltageLaw setup) :
    potentialDifferenceInVolts (setup.potentialChange .threeToFour) =
        (-20 : ℝ) ∧
      answerChoicePotentialDifferenceInVolts .D = (-20 : ℝ) ∧
      ∀ choice,
        potentialDifferenceInVolts (setup.potentialChange .threeToFour) =
            answerChoicePotentialDifferenceInVolts choice →
          choice = .D := by
  have h12 :
      potentialDifferenceInVolts (setup.potentialChange .oneToTwo) = 30 :=
    _figure.printedReadoutsDescribePhysicalChanges .oneToTwo 30
      _figure.deltaV12PrintedReadout
  have h23 :
      potentialDifferenceInVolts (setup.potentialChange .twoToThree) = 50 :=
    _figure.printedReadoutsDescribePhysicalChanges .twoToThree 50
      _figure.deltaV23PrintedReadout
  have h41 :
      potentialDifferenceInVolts (setup.potentialChange .fourToOne) = -60 :=
    _figure.printedReadoutsDescribePhysicalChanges .fourToOne (-60)
      _figure.deltaV41PrintedReadout
  have h34 :=
    deltaV34_eq_negative_sum_of_other_directed_changes setup _laws
  rw [h12, h23, h41] at h34
  norm_num at h34
  refine
    ⟨h34, by norm_num [answerChoicePotentialDifferenceInVolts], ?_⟩
  intro choice hchoice
  rw [h34] at hchoice
  cases choice with
  | A => norm_num [answerChoicePotentialDifferenceInVolts] at hchoice
  | B => norm_num [answerChoicePotentialDifferenceInVolts] at hchoice
  | C => norm_num [answerChoicePotentialDifferenceInVolts] at hchoice
  | D => rfl

end PhyXMiniProblems.ProblemPhyXMini0872
