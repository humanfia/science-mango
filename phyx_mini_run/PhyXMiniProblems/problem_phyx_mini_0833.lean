import Mathlib.Analysis.InnerProductSpace.PiL2
import Physlib.Electromagnetism.Basic
import Physlib.Units.WithDim.Basic

/- USER: The assigned source file did not exist when this autoformalization task began. -/

/-!
# PhyX mini problem 0833: electric field at the fourth corner of a rectangle

The primary image places a `-5.0 nC` point charge at the upper-left corner of
a `4.0 cm` by `2.0 cm` rectangle, and `+10 nC` point charges at the upper-right
and lower-right corners.  A black dot at the lower-left corner marks the point
where the magnitude of the net electric field is requested.

Charges, lengths, planar positions, and electric-field vectors are represented
by dimensionful Physlib quantities.  Real numbers below are only coherent-SI
readouts, printed figure values, or displayed answer values.  Coulomb's vector
law and field superposition are assumptions; the recorded answer does not occur
in the physical setup, figure readouts, or governing-law structure.

Assumption/target split:

* governing laws: the vector point-charge Coulomb law and vector superposition;
* previous-part results: none;
* figure/data readouts: three signed charge values, the rectangular corner
  positions, the `4.0 cm` and `2.0 cm` separations, visible labels and dashed
  edges, and the SI value of Coulomb's constant;
* target conclusion: answer D is the unique displayed value closest to the
  magnitude of the resulting electric-field vector.
-/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0833

open Dimension
open scoped BigOperators

/-! ## Dimensionful quantities and coherent-SI readouts -/

/-- A nonnegative physical length. -/
abbrev LengthQuantity : Type :=
  Dimensionful (WithDim L𝓭 NNReal)

/-- A signed physical electric charge. -/
abbrev SignedChargeQuantity : Type :=
  Dimensionful (WithDim C𝓭 ℝ)

/-- The physical dimension `M L T⁻² C⁻¹` of electric-field strength. -/
def electricFieldStrengthDimension : Dimension :=
  M𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹ * C𝓭⁻¹

/-- A unit-independent signed planar position. -/
abbrev PlanarPositionQuantity : Type :=
  Dimensionful (WithDim L𝓭 (EuclideanSpace ℝ (Fin 2)))

/-- A unit-independent planar electric-field vector. -/
abbrev PlanarElectricFieldQuantity : Type :=
  Dimensionful
    (WithDim electricFieldStrengthDimension (EuclideanSpace ℝ (Fin 2)))

/-- Coordinate `0`, horizontal and positive to the right in the image. -/
def xAxis : Fin 2 := 0

/-- Coordinate `1`, vertical and positive upward in the image. -/
def yAxis : Fin 2 := 1

/-- Read a physical length in coherent-SI metres. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  ((length UnitChoices.SI).val : ℝ)

/-- Read a signed physical charge in coherent-SI coulombs. -/
def chargeInCoulombs (charge : SignedChargeQuantity) : ℝ :=
  (charge UnitChoices.SI).val

/-- Read a planar position as Cartesian coordinates in metres. -/
def positionVectorInMeters
    (position : PlanarPositionQuantity) : EuclideanSpace ℝ (Fin 2) :=
  (position UnitChoices.SI).val

/-- Read a planar electric-field vector in newtons per coulomb. -/
def electricFieldVectorInNewtonsPerCoulomb
    (field : PlanarElectricFieldQuantity) : EuclideanSpace ℝ (Fin 2) :=
  (field UnitChoices.SI).val

/-- Euclidean magnitude of a planar electric field, in newtons per coulomb. -/
def electricFieldMagnitudeInNewtonsPerCoulomb
    (field : PlanarElectricFieldQuantity) : ℝ :=
  ‖electricFieldVectorInNewtonsPerCoulomb field‖

/-! ## Named physical objects and primary-image vocabulary -/

/-- The three source charges, named by their corners in the primary image. -/
inductive SourceCharge where
  | upperLeft
  | upperRight
  | lowerRight
  deriving DecidableEq, Fintype, Repr

/-- The sign symbols shown inside the three coloured charge circles. -/
inductive ChargeSign where
  | positive
  | negative
  deriving DecidableEq, Repr

/-- The four dashed sides making the rectangular layout visible. -/
inductive RectangleEdge where
  | top
  | right
  | bottom
  | left
  deriving DecidableEq, Fintype, Repr

/-- The two printed separation labels and their geometric roles. -/
inductive SeparationLabel where
  | horizontalFourCentimeters
  | verticalTwoCentimeters
  deriving DecidableEq, Fintype, Repr

/-- Literal qualitative and textual content of image `833.png`. -/
structure RectangleChargeFigure where
  shownChargeSign : SourceCharge → ChargeSign
  printedChargeLabel : SourceCharge → String
  printedSeparationLabel : SeparationLabel → String
  dashedEdgeShown : RectangleEdge → Bool
  chargeCircleShown : SourceCharge → Bool
  blackObservationDotShownAtLowerLeft : Bool

/-!
The independent physical quantities in the electrostatic model.  Each field
contribution and the net field are observables, related only by the governing
laws below; their values are not defined from an answer choice.
-/
structure RectangularPointChargeSetup where
  horizontalSeparation : LengthQuantity
  verticalSeparation : LengthQuantity
  sourceCharge : SourceCharge → SignedChargeQuantity
  sourcePosition : SourceCharge → PlanarPositionQuantity
  markedPointPosition : PlanarPositionQuantity
  fieldContributionAtMarkedPoint :
    SourceCharge → PlanarElectricFieldQuantity
  netFieldAtMarkedPoint : PlanarElectricFieldQuantity
  electromagneticSystem : Electromagnetism.EMSystem
  figure : RectangleChargeFigure

/-! ## Figure/data readouts and governing laws -/

/-- Displacement in metres from a source charge to the marked field point. -/
def displacementFromSourceInMeters
    (setup : RectangularPointChargeSetup)
    (source : SourceCharge) : EuclideanSpace ℝ (Fin 2) :=
  positionVectorInMeters setup.markedPointPosition -
    positionVectorInMeters (setup.sourcePosition source)

/-!
Numerical and qualitative data transcribed from the problem and primary image.
The coordinate origin is chosen at the marked lower-left point.  No electric-
field magnitude or answer value is included here.
-/
structure MatchesProblemAndPrimaryFigure
    (setup : RectangularPointChargeSetup) : Prop where
  horizontalSeparationReadout :
    lengthInMeters setup.horizontalSeparation = 4 / 100
  verticalSeparationReadout :
    lengthInMeters setup.verticalSeparation = 2 / 100
  upperLeftChargeReadout :
    chargeInCoulombs (setup.sourceCharge .upperLeft) = -5 / 10 ^ 9
  upperRightChargeReadout :
    chargeInCoulombs (setup.sourceCharge .upperRight) = 10 / 10 ^ 9
  lowerRightChargeReadout :
    chargeInCoulombs (setup.sourceCharge .lowerRight) = 10 / 10 ^ 9
  markedPointXCoordinate :
    positionVectorInMeters setup.markedPointPosition xAxis = 0
  markedPointYCoordinate :
    positionVectorInMeters setup.markedPointPosition yAxis = 0
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
  lowerRightXCoordinate :
    positionVectorInMeters (setup.sourcePosition .lowerRight) xAxis =
      lengthInMeters setup.horizontalSeparation
  lowerRightYCoordinate :
    positionVectorInMeters (setup.sourcePosition .lowerRight) yAxis = 0
  upperLeftSignShown : setup.figure.shownChargeSign .upperLeft = .negative
  upperRightSignShown : setup.figure.shownChargeSign .upperRight = .positive
  lowerRightSignShown : setup.figure.shownChargeSign .lowerRight = .positive
  upperLeftPrintedLabel :
    setup.figure.printedChargeLabel .upperLeft = "-5.0 nC"
  upperRightPrintedLabel :
    setup.figure.printedChargeLabel .upperRight = "10 nC"
  lowerRightPrintedLabel :
    setup.figure.printedChargeLabel .lowerRight = "10 nC"
  horizontalPrintedLabel :
    setup.figure.printedSeparationLabel .horizontalFourCentimeters = "4.0 cm"
  verticalPrintedLabel :
    setup.figure.printedSeparationLabel .verticalTwoCentimeters = "2.0 cm"
  everyDashedEdgeShown : ∀ edge, setup.figure.dashedEdgeShown edge = true
  everyChargeCircleShown :
    ∀ source, setup.figure.chargeCircleShown source = true
  markedPointShownAsBlackDot :
    setup.figure.blackObservationDotShownAtLowerLeft = true

/-- Coherent-SI calibration of Physlib's Coulomb constant. -/
structure UsesSIReferenceData
    (setup : RectangularPointChargeSetup) : Prop where
  coulombConstantCalibration :
    setup.electromagneticSystem.coulombConstant = 8.9875517923e9

/-- Positivity and source/observation separation conditions. -/
structure HasPhysicalParameters
    (setup : RectangularPointChargeSetup) : Prop where
  horizontalSeparationPositive :
    0 < lengthInMeters setup.horizontalSeparation
  verticalSeparationPositive :
    0 < lengthInMeters setup.verticalSeparation
  coulombConstantPositive :
    0 < setup.electromagneticSystem.coulombConstant
  markedPointDistinctFromEverySource :
    ∀ source, 0 < ‖displacementFromSourceInMeters setup source‖

/-!
The point-charge law in vector form and linear superposition.  For displacement
`r` from source to observation point, a signed charge `q` contributes
`k q r / ‖r‖³`.  These are general physical relations and do not prescribe the
requested magnitude or any displayed answer.
-/
structure SatisfiesPointChargeCoulombLawAndSuperposition
    (setup : RectangularPointChargeSetup) : Prop where
  pointChargeField : ∀ source,
    electricFieldVectorInNewtonsPerCoulomb
        (setup.fieldContributionAtMarkedPoint source) =
      ((setup.electromagneticSystem.coulombConstant *
          chargeInCoulombs (setup.sourceCharge source)) /
        ‖displacementFromSourceInMeters setup source‖ ^ 3) •
          displacementFromSourceInMeters setup source
  fieldSuperposition :
    electricFieldVectorInNewtonsPerCoulomb setup.netFieldAtMarkedPoint =
      ∑ source : SourceCharge,
        electricFieldVectorInNewtonsPerCoulomb
          (setup.fieldContributionAtMarkedPoint source)

/-! ## Displayed choices and current target -/

/-- Labels attached to the four displayed field-strength choices. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Printed field strength beside each answer, in newtons per coulomb. -/
def displayedFieldStrengthInNewtonsPerCoulomb : AnswerChoice → ℝ
  | .A => 1.3 * 10 ^ 5
  | .B => 5.3 * 10 ^ 5
  | .C => 1.0 * 10 ^ 5
  | .D => 1.34 * 10 ^ 5

/-!
A displayed choice is uniquely closest to the calculated net-field magnitude.
This comparison predicate is independent of which label ultimately satisfies it.
-/
def IsUniqueClosestDisplayedChoice
    (setup : RectangularPointChargeSetup)
    (choice : AnswerChoice) : Prop :=
  ∀ other, other ≠ choice →
    |electricFieldMagnitudeInNewtonsPerCoulomb setup.netFieldAtMarkedPoint -
        displayedFieldStrengthInNewtonsPerCoulomb choice| <
      |electricFieldMagnitudeInNewtonsPerCoulomb setup.netFieldAtMarkedPoint -
        displayedFieldStrengthInNewtonsPerCoulomb other|

/--
For the three charges and rectangle shown in image `833.png`, Coulomb's law and
field superposition make `1.34 × 10⁵ N/C` (answer D) the unique closest
displayed magnitude.
-/
theorem electricFieldMagnitude_answer_D
    (setup : RectangularPointChargeSetup)
    (h_figure : MatchesProblemAndPrimaryFigure setup)
    (h_reference : UsesSIReferenceData setup)
    (h_physical : HasPhysicalParameters setup)
    (h_laws : SatisfiesPointChargeCoulombLawAndSuperposition setup) :
    IsUniqueClosestDisplayedChoice setup .D := by
  have h_upperLeftDisplacement :
      displacementFromSourceInMeters setup .upperLeft =
        !₂[(0 : ℝ), -(1 / 50 : ℝ)] := by
    ext i
    fin_cases i
    · change
        positionVectorInMeters setup.markedPointPosition (0 : Fin 2) -
            positionVectorInMeters (setup.sourcePosition .upperLeft) 0 = 0
      rw [show positionVectorInMeters setup.markedPointPosition (0 : Fin 2) =
            0 by simpa [xAxis] using h_figure.markedPointXCoordinate]
      rw [show positionVectorInMeters (setup.sourcePosition .upperLeft)
            (0 : Fin 2) = 0 by
          simpa [xAxis] using h_figure.upperLeftXCoordinate]
      norm_num
    · change
        positionVectorInMeters setup.markedPointPosition (1 : Fin 2) -
            positionVectorInMeters (setup.sourcePosition .upperLeft) 1 =
          -(1 / 50 : ℝ)
      rw [show positionVectorInMeters setup.markedPointPosition (1 : Fin 2) =
            0 by simpa [yAxis] using h_figure.markedPointYCoordinate]
      rw [show positionVectorInMeters (setup.sourcePosition .upperLeft)
            (1 : Fin 2) = lengthInMeters setup.verticalSeparation by
          simpa [yAxis] using h_figure.upperLeftYCoordinate]
      rw [h_figure.verticalSeparationReadout]
      norm_num
  have h_upperRightDisplacement :
      displacementFromSourceInMeters setup .upperRight =
        !₂[-(1 / 25 : ℝ), -(1 / 50 : ℝ)] := by
    ext i
    fin_cases i
    · change
        positionVectorInMeters setup.markedPointPosition (0 : Fin 2) -
            positionVectorInMeters (setup.sourcePosition .upperRight) 0 =
          -(1 / 25 : ℝ)
      rw [show positionVectorInMeters setup.markedPointPosition (0 : Fin 2) =
            0 by simpa [xAxis] using h_figure.markedPointXCoordinate]
      rw [show positionVectorInMeters (setup.sourcePosition .upperRight)
            (0 : Fin 2) = lengthInMeters setup.horizontalSeparation by
          simpa [xAxis] using h_figure.upperRightXCoordinate]
      rw [h_figure.horizontalSeparationReadout]
      norm_num
    · change
        positionVectorInMeters setup.markedPointPosition (1 : Fin 2) -
            positionVectorInMeters (setup.sourcePosition .upperRight) 1 =
          -(1 / 50 : ℝ)
      rw [show positionVectorInMeters setup.markedPointPosition (1 : Fin 2) =
            0 by simpa [yAxis] using h_figure.markedPointYCoordinate]
      rw [show positionVectorInMeters (setup.sourcePosition .upperRight)
            (1 : Fin 2) = lengthInMeters setup.verticalSeparation by
          simpa [yAxis] using h_figure.upperRightYCoordinate]
      rw [h_figure.verticalSeparationReadout]
      norm_num
  have h_lowerRightDisplacement :
      displacementFromSourceInMeters setup .lowerRight =
        !₂[-(1 / 25 : ℝ), (0 : ℝ)] := by
    ext i
    fin_cases i
    · change
        positionVectorInMeters setup.markedPointPosition (0 : Fin 2) -
            positionVectorInMeters (setup.sourcePosition .lowerRight) 0 =
          -(1 / 25 : ℝ)
      rw [show positionVectorInMeters setup.markedPointPosition (0 : Fin 2) =
            0 by simpa [xAxis] using h_figure.markedPointXCoordinate]
      rw [show positionVectorInMeters (setup.sourcePosition .lowerRight)
            (0 : Fin 2) = lengthInMeters setup.horizontalSeparation by
          simpa [xAxis] using h_figure.lowerRightXCoordinate]
      rw [h_figure.horizontalSeparationReadout]
      norm_num
    · change
        positionVectorInMeters setup.markedPointPosition (1 : Fin 2) -
            positionVectorInMeters (setup.sourcePosition .lowerRight) 1 = 0
      rw [show positionVectorInMeters setup.markedPointPosition (1 : Fin 2) =
            0 by simpa [yAxis] using h_figure.markedPointYCoordinate]
      rw [show positionVectorInMeters (setup.sourcePosition .lowerRight)
            (1 : Fin 2) = 0 by
          simpa [yAxis] using h_figure.lowerRightYCoordinate]
      norm_num
  have h_upperLeftNorm :
      ‖displacementFromSourceInMeters setup .upperLeft‖ = (1 / 50 : ℝ) := by
    have h_sq :
        ‖displacementFromSourceInMeters setup .upperLeft‖ ^ 2 =
          (1 / 2500 : ℝ) := by
      rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two,
        h_upperLeftDisplacement]
      norm_num
    have h_nonnegative :=
      norm_nonneg (displacementFromSourceInMeters setup .upperLeft)
    nlinarith
  have h_lowerRightNorm :
      ‖displacementFromSourceInMeters setup .lowerRight‖ = (1 / 25 : ℝ) := by
    have h_sq :
        ‖displacementFromSourceInMeters setup .lowerRight‖ ^ 2 =
          (1 / 625 : ℝ) := by
      rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two,
        h_lowerRightDisplacement]
      norm_num
    have h_nonnegative :=
      norm_nonneg (displacementFromSourceInMeters setup .lowerRight)
    nlinarith
  have h_sqrtFive_sq : Real.sqrt 5 ^ 2 = 5 :=
    Real.sq_sqrt (by norm_num)
  have h_sqrtFive_pos : 0 < Real.sqrt 5 :=
    Real.sqrt_pos.2 (by norm_num)
  have h_upperRightNorm :
      ‖displacementFromSourceInMeters setup .upperRight‖ =
        Real.sqrt 5 / 50 := by
    have h_sq :
        ‖displacementFromSourceInMeters setup .upperRight‖ ^ 2 =
          (1 / 500 : ℝ) := by
      rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two,
        h_upperRightDisplacement]
      norm_num
    have h_nonnegative :=
      norm_nonneg (displacementFromSourceInMeters setup .upperRight)
    nlinarith
  have h_upperLeftFieldX :
      electricFieldVectorInNewtonsPerCoulomb
          (setup.fieldContributionAtMarkedPoint .upperLeft) xAxis = 0 := by
    have h_component :=
      congrArg (fun vector => vector xAxis)
        (h_laws.pointChargeField .upperLeft)
    simp only [PiLp.smul_apply, smul_eq_mul] at h_component
    rw [h_reference.coulombConstantCalibration,
      h_figure.upperLeftChargeReadout, h_upperLeftNorm,
      h_upperLeftDisplacement] at h_component
    norm_num [xAxis] at h_component ⊢
    exact h_component
  have h_upperLeftFieldY :
      electricFieldVectorInNewtonsPerCoulomb
          (setup.fieldContributionAtMarkedPoint .upperLeft) yAxis =
        (89875517923 / 800000 : ℝ) := by
    have h_component :=
      congrArg (fun vector => vector yAxis)
        (h_laws.pointChargeField .upperLeft)
    simp only [PiLp.smul_apply, smul_eq_mul] at h_component
    rw [h_reference.coulombConstantCalibration,
      h_figure.upperLeftChargeReadout, h_upperLeftNorm,
      h_upperLeftDisplacement] at h_component
    norm_num [yAxis] at h_component ⊢
    exact h_component
  have h_upperRightFieldX :
      electricFieldVectorInNewtonsPerCoulomb
          (setup.fieldContributionAtMarkedPoint .upperRight) xAxis =
        -((89875517923 / 5000000 : ℝ) * Real.sqrt 5) := by
    have h_component :=
      congrArg (fun vector => vector xAxis)
        (h_laws.pointChargeField .upperRight)
    simp only [PiLp.smul_apply, smul_eq_mul] at h_component
    rw [h_reference.coulombConstantCalibration,
      h_figure.upperRightChargeReadout, h_upperRightNorm,
      h_upperRightDisplacement] at h_component
    norm_num [xAxis] at h_component
    change
      electricFieldVectorInNewtonsPerCoulomb
          (setup.fieldContributionAtMarkedPoint .upperRight) (0 : Fin 2) =
        -((89875517923 / 5000000 : ℝ) * Real.sqrt 5)
    rw [h_component]
    field_simp
    nlinarith
  have h_upperRightFieldY :
      electricFieldVectorInNewtonsPerCoulomb
          (setup.fieldContributionAtMarkedPoint .upperRight) yAxis =
        -((89875517923 / 10000000 : ℝ) * Real.sqrt 5) := by
    have h_component :=
      congrArg (fun vector => vector yAxis)
        (h_laws.pointChargeField .upperRight)
    simp only [PiLp.smul_apply, smul_eq_mul] at h_component
    rw [h_reference.coulombConstantCalibration,
      h_figure.upperRightChargeReadout, h_upperRightNorm,
      h_upperRightDisplacement] at h_component
    norm_num [yAxis] at h_component
    change
      electricFieldVectorInNewtonsPerCoulomb
          (setup.fieldContributionAtMarkedPoint .upperRight) (1 : Fin 2) =
        -((89875517923 / 10000000 : ℝ) * Real.sqrt 5)
    rw [h_component]
    field_simp
    nlinarith
  have h_lowerRightFieldX :
      electricFieldVectorInNewtonsPerCoulomb
          (setup.fieldContributionAtMarkedPoint .lowerRight) xAxis =
        -(89875517923 / 1600000 : ℝ) := by
    have h_component :=
      congrArg (fun vector => vector xAxis)
        (h_laws.pointChargeField .lowerRight)
    simp only [PiLp.smul_apply, smul_eq_mul] at h_component
    rw [h_reference.coulombConstantCalibration,
      h_figure.lowerRightChargeReadout, h_lowerRightNorm,
      h_lowerRightDisplacement] at h_component
    norm_num [xAxis] at h_component ⊢
    exact h_component
  have h_lowerRightFieldY :
      electricFieldVectorInNewtonsPerCoulomb
          (setup.fieldContributionAtMarkedPoint .lowerRight) yAxis = 0 := by
    have h_component :=
      congrArg (fun vector => vector yAxis)
        (h_laws.pointChargeField .lowerRight)
    simp only [PiLp.smul_apply, smul_eq_mul] at h_component
    rw [h_reference.coulombConstantCalibration,
      h_figure.lowerRightChargeReadout, h_lowerRightNorm,
      h_lowerRightDisplacement] at h_component
    norm_num [yAxis] at h_component ⊢
    exact h_component
  have h_netFieldX :
      electricFieldVectorInNewtonsPerCoulomb setup.netFieldAtMarkedPoint xAxis =
        -(89875517923 / 1600000 : ℝ) -
          (89875517923 / 5000000 : ℝ) * Real.sqrt 5 := by
    have h_superposition := h_laws.fieldSuperposition
    rw [show (Finset.univ : Finset SourceCharge) =
        {.upperLeft, .upperRight, .lowerRight} by decide] at h_superposition
    simp at h_superposition
    have h_component :=
      congrArg (fun vector => vector xAxis) h_superposition
    simp only [PiLp.add_apply] at h_component
    rw [h_upperLeftFieldX, h_upperRightFieldX,
      h_lowerRightFieldX] at h_component
    linarith
  have h_netFieldY :
      electricFieldVectorInNewtonsPerCoulomb setup.netFieldAtMarkedPoint yAxis =
        (89875517923 / 800000 : ℝ) -
          (89875517923 / 10000000 : ℝ) * Real.sqrt 5 := by
    have h_superposition := h_laws.fieldSuperposition
    rw [show (Finset.univ : Finset SourceCharge) =
        {.upperLeft, .upperRight, .lowerRight} by decide] at h_superposition
    simp at h_superposition
    have h_component :=
      congrArg (fun vector => vector yAxis) h_superposition
    simp only [PiLp.add_apply] at h_component
    rw [h_upperLeftFieldY, h_upperRightFieldY,
      h_lowerRightFieldY] at h_component
    linarith
  have h_magnitude_sq :
      electricFieldMagnitudeInNewtonsPerCoulomb
          setup.netFieldAtMarkedPoint ^ 2 =
        (89875517923 / 1000000000 : ℝ) ^ 2 * 2203125 := by
    unfold electricFieldMagnitudeInNewtonsPerCoulomb
    rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
    rw [show electricFieldVectorInNewtonsPerCoulomb
          setup.netFieldAtMarkedPoint (0 : Fin 2) =
        -(89875517923 / 1600000 : ℝ) -
          (89875517923 / 5000000 : ℝ) * Real.sqrt 5 by
        simpa [xAxis] using h_netFieldX]
    rw [show electricFieldVectorInNewtonsPerCoulomb
          setup.netFieldAtMarkedPoint (1 : Fin 2) =
        (89875517923 / 800000 : ℝ) -
          (89875517923 / 10000000 : ℝ) * Real.sqrt 5 by
        simpa [yAxis] using h_netFieldY]
    nlinarith
  have h_magnitude_nonnegative :
      0 ≤ electricFieldMagnitudeInNewtonsPerCoulomb
        setup.netFieldAtMarkedPoint :=
    norm_nonneg _
  have h_magnitude_lower :
      (132000 : ℝ) <
        electricFieldMagnitudeInNewtonsPerCoulomb
          setup.netFieldAtMarkedPoint := by
    nlinarith only [h_magnitude_sq, h_magnitude_nonnegative]
  have h_magnitude_upper :
      electricFieldMagnitudeInNewtonsPerCoulomb
          setup.netFieldAtMarkedPoint < (135000 : ℝ) := by
    nlinarith only [h_magnitude_sq, h_magnitude_nonnegative]
  unfold IsUniqueClosestDisplayedChoice
  intro other h_other
  fin_cases other
  · rw [← sq_lt_sq]
    norm_num [displayedFieldStrengthInNewtonsPerCoulomb]
    nlinarith only [h_magnitude_lower]
  · rw [← sq_lt_sq]
    norm_num [displayedFieldStrengthInNewtonsPerCoulomb]
    nlinarith only [h_magnitude_upper]
  · rw [← sq_lt_sq]
    norm_num [displayedFieldStrengthInNewtonsPerCoulomb]
    nlinarith only [h_magnitude_lower]
  · exact (h_other rfl).elim

end PhyXMiniProblems.ProblemPhyXMini0833
