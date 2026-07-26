import Mathlib.Analysis.InnerProductSpace.PiL2
import Physlib.Electromagnetism.Basic
import Physlib.Units.WithDim.Basic

/- USER: The assigned source file did not exist when this autoformalization task began. -/

/-!
# PhyX mini problem 0858: electric potential at the marked corner

The primary image shows three positive point charges at the upper-left,
upper-right, and lower-left corners of an implied `3.0 cm` by `4.0 cm`
rectangle.  A black dot at the lower-right corner marks the observation point.
The source charges are respectively `4.0 nC`, `2.0 nC`, and `2.0 nC`.

Charge, length, position, and electric potential are represented by
unit-independent Physlib quantities.  Real numbers below are coherent-SI
readouts, printed figure values, or displayed answer values.  The scalar
point-charge potential law and potential superposition are explicit governing
assumptions.

Assumption/target split:

* governing laws: each source contributes `k q / r`, and the net electric
  potential is the scalar sum of the three contributions;
* previous-part results: none;
* figure/data readouts: the three positive charge values, the `3.0 cm` and
  `4.0 cm` separations, the rectangular corner coordinates inferred from the
  primary image, its printed labels and dashed segments, and the SI value of
  Coulomb's constant;
* current target conclusions: the exact Coulomb sum for the marked-point
  potential and that `1800 V` (answer D) is its unique closest displayed value.

Neither the governing-law structure nor the figure/readout structures contain
the requested marked-point potential or a selected answer choice.
-/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0858

open Dimension
open scoped BigOperators

/-! ## Dimensionful quantities and coherent-SI readouts -/

/-- The physical dimension of energy, `M L^2 T^-2`. -/
def energyDimension : Dimension :=
  M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹

/-- Electric potential has the physical dimension energy per charge. -/
def electricPotentialDimension : Dimension :=
  energyDimension * C𝓭⁻¹

/-- A nonnegative, unit-independent physical length. -/
abbrev LengthQuantity : Type :=
  Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative, unit-independent positive-charge magnitude. -/
abbrev ChargeMagnitudeQuantity : Type :=
  Dimensionful (WithDim C𝓭 NNReal)

/-- A unit-independent signed electric potential. -/
abbrev ElectricPotentialQuantity : Type :=
  Dimensionful (WithDim electricPotentialDimension ℝ)

/-- A unit-independent planar physical position. -/
abbrev PlanarPositionQuantity : Type :=
  Dimensionful (WithDim L𝓭 (EuclideanSpace ℝ (Fin 2)))

/-- Coordinate `0`, horizontal and positive to the right in the image. -/
def xAxis : Fin 2 := 0

/-- Coordinate `1`, vertical and positive upward in the image. -/
def yAxis : Fin 2 := 1

/-- Read a physical length in coherent-SI metres. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  ((length UnitChoices.SI).val : ℝ)

/-- Read a positive-charge magnitude in coherent-SI coulombs. -/
def chargeInCoulombs (charge : ChargeMagnitudeQuantity) : ℝ :=
  ((charge UnitChoices.SI).val : ℝ)

/-- Read a planar physical position as Cartesian coordinates in metres. -/
def positionVectorInMeters
    (position : PlanarPositionQuantity) : EuclideanSpace ℝ (Fin 2) :=
  (position UnitChoices.SI).val

/-- Read an electric potential in coherent-SI volts. -/
def electricPotentialInVolts
    (potential : ElectricPotentialQuantity) : ℝ :=
  (potential UnitChoices.SI).val

/-! ## Named sources, geometry, and primary-image vocabulary -/

/-- The three source charges, named by their locations in image `858.png`. -/
inductive SourceCharge where
  | upperLeft
  | upperRight
  | lowerLeft
  deriving DecidableEq, Fintype, Repr

/-- The sign symbol shown inside each red charge circle. -/
inductive ChargeSign where
  | positive
  | negative
  deriving DecidableEq, Repr

/-- The four sides of the rectangle implied by the charge/dot alignment. -/
inductive RectangleSide where
  | top
  | right
  | bottom
  | left
  deriving DecidableEq, Fintype, Repr

/-- The two separation labels printed beside dashed segments in the image. -/
inductive SeparationLabel where
  | horizontalThreeCentimeters
  | verticalFourCentimeters
  deriving DecidableEq, Fintype, Repr

/-- Literal qualitative and textual content of the supplied primary image. -/
structure PointChargePotentialFigure where
  shownChargeSign : SourceCharge → ChargeSign
  printedChargeLabel : SourceCharge → String
  printedSeparationLabel : SeparationLabel → String
  dashedSideShown : RectangleSide → Bool
  chargeCircleShown : SourceCharge → Bool
  blackObservationDotShownAtLowerRight : Bool

/-!
The independent physical quantities in the electrostatic model.  Each source
potential and the net potential are observables constrained only by the laws
below; they are not defined from an answer choice.
-/
structure RectangularPointChargePotentialSetup where
  horizontalSeparation : LengthQuantity
  verticalSeparation : LengthQuantity
  sourceChargeMagnitude : SourceCharge → ChargeMagnitudeQuantity
  sourcePosition : SourceCharge → PlanarPositionQuantity
  markedPointPosition : PlanarPositionQuantity
  potentialContributionAtMarkedPoint :
    SourceCharge → ElectricPotentialQuantity
  netPotentialAtMarkedPoint : ElectricPotentialQuantity
  electromagneticSystem : Electromagnetism.EMSystem
  figure : PointChargePotentialFigure

/-- Displacement in metres from a source charge to the marked point. -/
def displacementFromSourceInMeters
    (setup : RectangularPointChargePotentialSetup)
    (source : SourceCharge) : EuclideanSpace ℝ (Fin 2) :=
  positionVectorInMeters setup.markedPointPosition -
    positionVectorInMeters (setup.sourcePosition source)

/-- Euclidean source-to-observation distance in metres. -/
def sourceDistanceInMeters
    (setup : RectangularPointChargePotentialSetup)
    (source : SourceCharge) : ℝ :=
  ‖displacementFromSourceInMeters setup source‖

/-! ## Figure/data readouts and governing laws -/

/-!
Numerical and qualitative data transcribed from the problem and primary image.
The coordinate origin is chosen at the lower-left charge.  The black dot's
alignment places it at the lower-right corner.  No marked-point potential or
answer selection is included here.
-/
structure MatchesProblemAndPrimaryFigure
    (setup : RectangularPointChargePotentialSetup) : Prop where
  horizontalSeparationReadout :
    lengthInMeters setup.horizontalSeparation = 3 / 100
  verticalSeparationReadout :
    lengthInMeters setup.verticalSeparation = 4 / 100
  upperLeftChargeReadout :
    chargeInCoulombs (setup.sourceChargeMagnitude .upperLeft) = 4 / 10 ^ 9
  upperRightChargeReadout :
    chargeInCoulombs (setup.sourceChargeMagnitude .upperRight) = 2 / 10 ^ 9
  lowerLeftChargeReadout :
    chargeInCoulombs (setup.sourceChargeMagnitude .lowerLeft) = 2 / 10 ^ 9
  lowerLeftXCoordinate :
    positionVectorInMeters (setup.sourcePosition .lowerLeft) xAxis = 0
  lowerLeftYCoordinate :
    positionVectorInMeters (setup.sourcePosition .lowerLeft) yAxis = 0
  upperLeftXCoordinate :
    positionVectorInMeters (setup.sourcePosition .upperLeft) xAxis = 0
  upperLeftYCoordinate :
    positionVectorInMeters (setup.sourcePosition .upperLeft) yAxis =
      lengthInMeters setup.verticalSeparation
  upperRightXCoordinate :
    positionVectorInMeters (setup.sourcePosition .upperRight) xAxis =
      lengthInMeters setup.horizontalSeparation
  upperRightYCoordinate :
    positionVectorInMeters (setup.sourcePosition .upperRight) yAxis =
      lengthInMeters setup.verticalSeparation
  markedPointXCoordinate :
    positionVectorInMeters setup.markedPointPosition xAxis =
      lengthInMeters setup.horizontalSeparation
  markedPointYCoordinate :
    positionVectorInMeters setup.markedPointPosition yAxis = 0
  everyChargeShownPositive :
    ∀ source, setup.figure.shownChargeSign source = .positive
  upperLeftPrintedChargeLabel :
    setup.figure.printedChargeLabel .upperLeft = "4.0 nC"
  upperRightPrintedChargeLabel :
    setup.figure.printedChargeLabel .upperRight = "2.0 nC"
  lowerLeftPrintedChargeLabel :
    setup.figure.printedChargeLabel .lowerLeft = "2.0 nC"
  horizontalPrintedSeparationLabel :
    setup.figure.printedSeparationLabel .horizontalThreeCentimeters = "3.0 cm"
  verticalPrintedSeparationLabel :
    setup.figure.printedSeparationLabel .verticalFourCentimeters = "4.0 cm"
  topDashedSideShown : setup.figure.dashedSideShown .top = true
  leftDashedSideShown : setup.figure.dashedSideShown .left = true
  rightDashedSideNotShown : setup.figure.dashedSideShown .right = false
  bottomDashedSideNotShown : setup.figure.dashedSideShown .bottom = false
  everyChargeCircleShown :
    ∀ source, setup.figure.chargeCircleShown source = true
  markedPointShownAsBlackDot :
    setup.figure.blackObservationDotShownAtLowerRight = true

/-- Coherent-SI calibration of Physlib's Coulomb constant. -/
structure UsesSIReferenceData
    (setup : RectangularPointChargePotentialSetup) : Prop where
  coulombConstantCalibration :
    setup.electromagneticSystem.coulombConstant = 8.9875517923e9

/-- Positivity and source/observation separation conditions. -/
structure HasPhysicalParameters
    (setup : RectangularPointChargePotentialSetup) : Prop where
  horizontalSeparationPositive :
    0 < lengthInMeters setup.horizontalSeparation
  verticalSeparationPositive :
    0 < lengthInMeters setup.verticalSeparation
  everyChargeMagnitudePositive :
    ∀ source, 0 < chargeInCoulombs (setup.sourceChargeMagnitude source)
  coulombConstantPositive :
    0 < setup.electromagneticSystem.coulombConstant
  markedPointDistinctFromEverySource :
    ∀ source, 0 < sourceDistanceInMeters setup source

/-!
The scalar point-charge law and potential superposition.  A positive point
charge `q` at distance `r` contributes `k q / r`; electric potential is a
scalar, so the three contributions add without vector components.  These are
general governing laws and do not prescribe the requested numerical answer.
-/
structure SatisfiesPointChargePotentialLawAndSuperposition
    (setup : RectangularPointChargePotentialSetup) : Prop where
  pointChargePotential : ∀ source,
    electricPotentialInVolts
        (setup.potentialContributionAtMarkedPoint source) =
      setup.electromagneticSystem.coulombConstant *
        chargeInCoulombs (setup.sourceChargeMagnitude source) /
          sourceDistanceInMeters setup source
  potentialSuperposition :
    electricPotentialInVolts setup.netPotentialAtMarkedPoint =
      ∑ source : SourceCharge,
        electricPotentialInVolts
          (setup.potentialContributionAtMarkedPoint source)

/-! ## Derived Coulomb sum, displayed choices, and current target -/

/-!
The `3-4-5` rectangle and point-charge law give the exact coherent-SI scalar
expression from which the displayed answer is selected.  This is a derived
conclusion, not a setup field or governing-law assumption.
-/
lemma netPotentialAtMarkedPoint_coulombSum
    (setup : RectangularPointChargePotentialSetup)
    (h_figure : MatchesProblemAndPrimaryFigure setup)
    (h_physical : HasPhysicalParameters setup)
    (h_laws : SatisfiesPointChargePotentialLawAndSuperposition setup) :
    electricPotentialInVolts setup.netPotentialAtMarkedPoint =
      setup.electromagneticSystem.coulombConstant *
        (((4 : ℝ) / 10 ^ 9) / (5 / 100) +
          ((2 : ℝ) / 10 ^ 9) / (4 / 100) +
          ((2 : ℝ) / 10 ^ 9) / (3 / 100)) := by
  have h_markedPointX := h_figure.markedPointXCoordinate
  have h_markedPointY := h_figure.markedPointYCoordinate
  have h_upperLeftX := h_figure.upperLeftXCoordinate
  have h_upperLeftY := h_figure.upperLeftYCoordinate
  have h_upperRightX := h_figure.upperRightXCoordinate
  have h_upperRightY := h_figure.upperRightYCoordinate
  have h_lowerLeftX := h_figure.lowerLeftXCoordinate
  have h_lowerLeftY := h_figure.lowerLeftYCoordinate
  simp only [xAxis] at h_markedPointX h_upperLeftX h_upperRightX h_lowerLeftX
  simp only [yAxis] at h_markedPointY h_upperLeftY h_upperRightY h_lowerLeftY
  have h_upperLeftDistance :
      sourceDistanceInMeters setup .upperLeft = 5 / 100 := by
    rw [sourceDistanceInMeters, displacementFromSourceInMeters,
      EuclideanSpace.norm_eq, Fin.sum_univ_two]
    simp only [Real.norm_eq_abs, PiLp.sub_apply]
    rw [h_markedPointX,
      h_markedPointY,
      h_upperLeftX,
      h_upperLeftY,
      h_figure.horizontalSeparationReadout,
      h_figure.verticalSeparationReadout]
    norm_num [abs_of_nonneg, abs_of_nonpos]
    rw [show (400 : ℝ) = (20 : ℝ) ^ 2 by norm_num,
      Real.sqrt_sq_eq_abs]
    norm_num
  have h_upperRightDistance :
      sourceDistanceInMeters setup .upperRight = 4 / 100 := by
    rw [sourceDistanceInMeters, displacementFromSourceInMeters,
      EuclideanSpace.norm_eq, Fin.sum_univ_two]
    simp only [Real.norm_eq_abs, PiLp.sub_apply]
    rw [h_markedPointX,
      h_markedPointY,
      h_upperRightX,
      h_upperRightY,
      h_figure.horizontalSeparationReadout,
      h_figure.verticalSeparationReadout]
    norm_num [abs_of_nonneg, abs_of_nonpos]
    rw [show (625 : ℝ) = (25 : ℝ) ^ 2 by norm_num,
      Real.sqrt_sq_eq_abs]
    norm_num
  have h_lowerLeftDistance :
      sourceDistanceInMeters setup .lowerLeft = 3 / 100 := by
    rw [sourceDistanceInMeters, displacementFromSourceInMeters,
      EuclideanSpace.norm_eq, Fin.sum_univ_two]
    simp only [Real.norm_eq_abs, PiLp.sub_apply]
    rw [h_markedPointX,
      h_markedPointY,
      h_lowerLeftX,
      h_lowerLeftY,
      h_figure.horizontalSeparationReadout]
    norm_num [abs_of_nonneg, abs_of_nonpos]
    rw [show (9 : ℝ) = (3 : ℝ) ^ 2 by norm_num,
      Real.sqrt_sq_eq_abs,
      show (10000 : ℝ) = (100 : ℝ) ^ 2 by norm_num,
      Real.sqrt_sq_eq_abs]
    norm_num
  rw [h_laws.potentialSuperposition]
  rw [show
      (∑ source : SourceCharge,
          electricPotentialInVolts
            (setup.potentialContributionAtMarkedPoint source)) =
        electricPotentialInVolts
            (setup.potentialContributionAtMarkedPoint .upperLeft) +
          electricPotentialInVolts
            (setup.potentialContributionAtMarkedPoint .upperRight) +
          electricPotentialInVolts
            (setup.potentialContributionAtMarkedPoint .lowerLeft) by
    rw [show (Finset.univ : Finset SourceCharge) =
        {.upperLeft, .upperRight, .lowerLeft} by
      ext source
      fin_cases source <;> simp]
    simp
    ring]
  rw [h_laws.pointChargePotential .upperLeft,
    h_laws.pointChargePotential .upperRight,
    h_laws.pointChargePotential .lowerLeft,
    h_figure.upperLeftChargeReadout,
    h_figure.upperRightChargeReadout,
    h_figure.lowerLeftChargeReadout,
    h_upperLeftDistance, h_upperRightDistance, h_lowerLeftDistance]
  ring

/-- Labels attached to the four displayed voltage choices. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Printed electric potential beside each answer, in volts. -/
def displayedPotentialInVolts : AnswerChoice → ℝ
  | .A => 1100
  | .B => 1600
  | .C => 800
  | .D => 1800

/-!
A displayed choice is uniquely closest to the calculated marked-point
potential.  This comparison predicate is independent of which label satisfies
it and does not encode the recorded answer.
-/
def IsUniqueClosestDisplayedChoice
    (setup : RectangularPointChargePotentialSetup)
    (choice : AnswerChoice) : Prop :=
  ∀ other, other ≠ choice →
    |electricPotentialInVolts setup.netPotentialAtMarkedPoint -
        displayedPotentialInVolts choice| <
      |electricPotentialInVolts setup.netPotentialAtMarkedPoint -
        displayedPotentialInVolts other|

/--
For the three positive charges and marked corner shown in image `858.png`, the
net potential lies within `50 V` of `1800 V`, and answer D is the unique
closest displayed value.

This is the Lean declaration corresponding to blueprint label
`thm:physics:phyx_mini_0858:target`.
-/
theorem electricPotentialAtMarkedPoint_matches_answer_D
    (setup : RectangularPointChargePotentialSetup)
    (h_figure : MatchesProblemAndPrimaryFigure setup)
    (h_reference : UsesSIReferenceData setup)
    (h_physical : HasPhysicalParameters setup)
    (h_laws : SatisfiesPointChargePotentialLawAndSuperposition setup) :
    |electricPotentialInVolts setup.netPotentialAtMarkedPoint -
        displayedPotentialInVolts .D| < 50 ∧
      IsUniqueClosestDisplayedChoice setup .D := by
  have h_potential :=
    netPotentialAtMarkedPoint_coulombSum
      setup h_figure h_physical h_laws
  rw [h_reference.coulombConstantCalibration] at h_potential
  norm_num at h_potential
  constructor
  · rw [h_potential]
    norm_num [displayedPotentialInVolts, abs_of_nonneg, abs_of_nonpos]
  · unfold IsUniqueClosestDisplayedChoice
    intro other h_other
    rw [h_potential]
    fin_cases other <;>
      simp_all [displayedPotentialInVolts] <;>
      norm_num [abs_of_nonneg, abs_of_nonpos]

end PhyXMiniProblems.ProblemPhyXMini0858
