import Mathlib
import Physlib.Electromagnetism.Basic
import Physlib.Electromagnetism.Charge.ChargeUnit
import Physlib.Units.WithDim.Basic

/- USER: The assigned Lean file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0831

open Dimension

/-!
# Electric-field strength at the dot between two opposite point charges

The primary image puts a `+3.0 nC` point charge 5.0 cm above a midpoint, a
`-3.0 nC` point charge 5.0 cm below that midpoint, and the observation dot
5.0 cm to its left.  Consequently, each source is `5 * sqrt 2` centimetres
from the dot.  The horizontal components of their electric fields cancel and
the downward components add.

Charge, length, planar position, electric-field vector, and field-strength
magnitude are unit-independent Physlib quantities.  Real numbers below are
explicit coherent-SI or named-unit readouts.  Coulomb's vector law and field
superposition are assumptions; the rounded field strength and choice D occur
only in the target conclusion.

Assumption/target split:

* governing laws: the point-charge vector field, linear superposition, and
  the fact that field strength is the Euclidean norm of the net field;
* previous-part results: none;
* figure/data readouts: the three 5.0 cm arms, charge values `+3.0 nC` and
  `-3.0 nC`, their relative positions, the marked dot, and a rounded
  Coulomb constant of `9.0 × 10^9 N m²/C²`;
* current target: the strength agrees with `7.6 × 10^3 N/C` to the stated
  rounding tolerance and D is the unique closest displayed answer.
-/

/-! ## Dimensionful physical quantities and coherent readouts -/

/-- The physical dimension `M L T⁻² C⁻¹` of electric-field strength. -/
def electricFieldDimension : Dimension :=
  M𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹ * C𝓭⁻¹

/-- A nonnegative unit-independent physical length. -/
abbrev LengthQuantity : Type :=
  Dimensionful (WithDim L𝓭 NNReal)

/-- A signed unit-independent electric charge. -/
abbrev ChargeQuantity : Type :=
  Dimensionful (WithDim C𝓭 ℝ)

/-- A signed position vector in the two-dimensional plane of the figure. -/
abbrev PlanarPositionQuantity : Type :=
  Dimensionful
    (WithDim L𝓭 (EuclideanSpace ℝ (Fin 2)))

/-- A physical electric-field vector in the plane of the figure. -/
abbrev PlanarElectricFieldQuantity : Type :=
  Dimensionful
    (WithDim electricFieldDimension (EuclideanSpace ℝ (Fin 2)))

/-- A nonnegative physical electric-field strength. -/
abbrev ElectricFieldStrengthQuantity : Type :=
  Dimensionful (WithDim electricFieldDimension NNReal)

/-- Coordinate `0`, horizontal and positive to the right. -/
def xAxis : Fin 2 := 0

/-- Coordinate `1`, vertical and positive upward. -/
def yAxis : Fin 2 := 1

/-- Read a physical length in coherent-SI metres. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  ((length UnitChoices.SI).val : ℝ)

/-- Read a physical length in centimetres. -/
def lengthInCentimeters (length : LengthQuantity) : ℝ :=
  100 * lengthInMeters length

/-- Read a signed physical charge in coherent-SI coulombs. -/
def chargeInCoulombs (charge : ChargeQuantity) : ℝ :=
  (charge UnitChoices.SI).val

/-- Read a signed physical charge in nanocoulombs. -/
def chargeInNanocoulombs (charge : ChargeQuantity) : ℝ :=
  1e9 * chargeInCoulombs charge

/-- Read a planar physical position as Cartesian coordinates in metres. -/
def positionInMeters (position : PlanarPositionQuantity) :
    EuclideanSpace ℝ (Fin 2) :=
  (position UnitChoices.SI).val

/-- Read a planar electric-field vector in newtons per coulomb. -/
def fieldVectorInNewtonsPerCoulomb
    (field : PlanarElectricFieldQuantity) : EuclideanSpace ℝ (Fin 2) :=
  (field UnitChoices.SI).val

/-- Read a nonnegative electric-field strength in newtons per coulomb. -/
def fieldStrengthInNewtonsPerCoulomb
    (strength : ElectricFieldStrengthQuantity) : ℝ :=
  ((strength UnitChoices.SI).val : ℝ)

/-- Physlib's Coulomb constant, interpreted as its coherent-SI readout. -/
def coulombConstantInNewtonMeterSquaredPerCoulombSquared
    (system : Electromagnetism.EMSystem) : ℝ :=
  system.coulombConstant

/-! ## Literal figure vocabulary and physical setup -/

/-- The two point-charge sources shown in the image. -/
inductive ChargeSource where
  | upperPositive
  | lowerNegative
  deriving DecidableEq, Fintype, Repr

/-- Distinguished locations shown or determined by the three distance arms. -/
inductive FigurePoint where
  | upperChargeCenter
  | midpoint
  | lowerChargeCenter
  | observationDot
  deriving DecidableEq, Fintype, Repr

/-- The three arrows whose labels all read `5.0 cm`. -/
inductive FigureArm where
  | upperToMidpoint
  | midpointToLower
  | midpointToDot
  deriving DecidableEq, Fintype, Repr

/-- Visible charge signs in the two colored circles. -/
inductive ChargeSign where
  | positive
  | negative
  deriving DecidableEq, Fintype, Repr

/-- The location occupied by each point-charge source. -/
def ChargeSource.figurePoint : ChargeSource → FigurePoint
  | .upperPositive => .upperChargeCenter
  | .lowerNegative => .lowerChargeCenter

/-- The sign visibly associated with each source. -/
def ChargeSource.expectedSign : ChargeSource → ChargeSign
  | .upperPositive => .positive
  | .lowerNegative => .negative

/-- Literal visual data from image `831.png`. -/
structure OppositeChargeFigure where
  chargeCircleShown : ChargeSource → Bool
  signShown : ChargeSource → ChargeSign
  nanocoulombLabelShown : ChargeSource → Bool
  distanceArrowShown : FigureArm → Bool
  distanceLabelFivePointZeroCentimeters : FigureArm → Bool
  observationDotShown : Bool
  verticalChargeAxisShown : Bool
  horizontalDotArmShown : Bool

/-!
The physical sources, their positions, and the fields they produce at the
observation dot.  No numerical value for the requested strength or preferred
answer choice is built into this structure.
-/
structure OppositePointChargeSetup where
  electromagneticSystem : Electromagnetism.EMSystem
  charge : ChargeSource → ChargeQuantity
  position : FigurePoint → PlanarPositionQuantity
  displayedArmLength : FigureArm → LengthQuantity
  fieldContributionAtDot : ChargeSource → PlanarElectricFieldQuantity
  netElectricFieldAtDot : PlanarElectricFieldQuantity
  electricFieldStrengthAtDot : ElectricFieldStrengthQuantity
  figure : OppositeChargeFigure

/-! ## Primary-figure evidence and independent numerical readouts -/

/-- All unambiguous qualitative information visible in the supplied image. -/
structure MatchesPrimaryFigure
    (setup : OppositePointChargeSetup) : Prop where
  bothChargeCirclesShown :
    ∀ source, setup.figure.chargeCircleShown source = true
  displayedSigns :
    ∀ source, setup.figure.signShown source = source.expectedSign
  bothChargeLabelsShown :
    ∀ source, setup.figure.nanocoulombLabelShown source = true
  everyDistanceArrowShown :
    ∀ arm, setup.figure.distanceArrowShown arm = true
  everyDistanceLabelIsFivePointZeroCentimeters :
    ∀ arm,
      setup.figure.distanceLabelFivePointZeroCentimeters arm = true
  dotShown : setup.figure.observationDotShown = true
  verticalAxisShown : setup.figure.verticalChargeAxisShown = true
  horizontalArmShown : setup.figure.horizontalDotArmShown = true

/-!
The signed charge labels, the three distance labels, and the standard rounded
Coulomb constant used by the textbook calculation.  None is the requested
electric-field strength.
-/
structure MatchesProblemReadouts
    (setup : OppositePointChargeSetup) : Prop where
  upperChargeNanocoulombs :
    chargeInNanocoulombs (setup.charge .upperPositive) = 3
  lowerChargeNanocoulombs :
    chargeInNanocoulombs (setup.charge .lowerNegative) = -3
  everyArmCentimeters :
    ∀ arm, lengthInCentimeters (setup.displayedArmLength arm) = 5
  roundedVacuumCoulombConstant :
    coulombConstantInNewtonMeterSquaredPerCoulombSquared
        setup.electromagneticSystem = 9e9

/-!
Cartesian geometry read from the primary figure.  The midpoint is chosen as
the coordinate origin.  The upper and lower charges are one displayed arm
above and below it, while the dot is one displayed arm to its left.  The
metric clauses retain the physical meaning of each arrow independently of
the coordinate choice.
-/
structure HasDepictedGeometry
    (setup : OppositePointChargeSetup) : Prop where
  midpointAtOrigin :
    positionInMeters (setup.position .midpoint) = 0
  upperChargeCoordinates :
    positionInMeters (setup.position .upperChargeCenter) xAxis = 0 ∧
      positionInMeters (setup.position .upperChargeCenter) yAxis =
        lengthInMeters (setup.displayedArmLength .upperToMidpoint)
  lowerChargeCoordinates :
    positionInMeters (setup.position .lowerChargeCenter) xAxis = 0 ∧
      positionInMeters (setup.position .lowerChargeCenter) yAxis =
        -lengthInMeters (setup.displayedArmLength .midpointToLower)
  observationDotCoordinates :
    positionInMeters (setup.position .observationDot) xAxis =
        -lengthInMeters (setup.displayedArmLength .midpointToDot) ∧
      positionInMeters (setup.position .observationDot) yAxis = 0
  upperArmIsMetricDistance :
    dist (positionInMeters (setup.position .upperChargeCenter))
        (positionInMeters (setup.position .midpoint)) =
      lengthInMeters (setup.displayedArmLength .upperToMidpoint)
  lowerArmIsMetricDistance :
    dist (positionInMeters (setup.position .midpoint))
        (positionInMeters (setup.position .lowerChargeCenter)) =
      lengthInMeters (setup.displayedArmLength .midpointToLower)
  dotArmIsMetricDistance :
    dist (positionInMeters (setup.position .midpoint))
        (positionInMeters (setup.position .observationDot)) =
      lengthInMeters (setup.displayedArmLength .midpointToDot)

/-- Positivity and noncoincidence conditions selecting the physical branch. -/
structure HasPhysicalParameters
    (setup : OppositePointChargeSetup) : Prop where
  armLengthsPositive :
    ∀ arm, 0 < lengthInMeters (setup.displayedArmLength arm)
  sourcesDoNotCoincideWithDot :
    ∀ source : ChargeSource,
      positionInMeters (setup.position (ChargeSource.figurePoint source)) ≠
        positionInMeters (setup.position .observationDot)
  coulombConstantPositive :
    0 < coulombConstantInNewtonMeterSquaredPerCoulombSquared
        setup.electromagneticSystem

/-! ## Governing point-charge electrostatics -/

/-!
Coulomb's vector law in coherent SI units, superposition of the two source
fields, and the definition of field strength as the norm of the net field.
The law is generic in the two source charges and positions and contains no
answer-choice value.
-/
structure SatisfiesPointChargeElectrostatics
    (setup : OppositePointChargeSetup) : Prop where
  pointChargeFieldLaw : ∀ source,
    let displacement :=
      positionInMeters (setup.position .observationDot) -
        positionInMeters (setup.position source.figurePoint)
    fieldVectorInNewtonsPerCoulomb
        (setup.fieldContributionAtDot source) =
      (coulombConstantInNewtonMeterSquaredPerCoulombSquared
          setup.electromagneticSystem *
        chargeInCoulombs (setup.charge source) / ‖displacement‖ ^ 3) •
        displacement
  superpositionAtDot :
    fieldVectorInNewtonsPerCoulomb setup.netElectricFieldAtDot =
      fieldVectorInNewtonsPerCoulomb
          (setup.fieldContributionAtDot .upperPositive) +
        fieldVectorInNewtonsPerCoulomb
          (setup.fieldContributionAtDot .lowerNegative)
  strengthIsNetFieldNorm :
    fieldStrengthInNewtonsPerCoulomb setup.electricFieldStrengthAtDot =
      ‖fieldVectorInNewtonsPerCoulomb setup.netElectricFieldAtDot‖

/-!
The two charge-to-dot distances implied by the three equal 5.0 cm arms.  This
is a derived geometric fact, not an assumption of the main answer.
-/
theorem source_to_dot_distances
    (setup : OppositePointChargeSetup)
    (hReadouts : MatchesProblemReadouts setup)
    (hGeometry : HasDepictedGeometry setup) :
    dist (positionInMeters (setup.position .upperChargeCenter))
        (positionInMeters (setup.position .observationDot)) =
      Real.sqrt 2 / 20 ∧
    dist (positionInMeters (setup.position .lowerChargeCenter))
        (positionInMeters (setup.position .observationDot)) =
      Real.sqrt 2 / 20 := by
  have hLength (arm : FigureArm) :
      lengthInMeters (setup.displayedArmLength arm) = (1 : ℝ) / 20 := by
    have h := hReadouts.everyArmCentimeters arm
    rw [lengthInCentimeters] at h
    norm_num at h ⊢
    linarith
  have hUpperX :
      positionInMeters (setup.position .upperChargeCenter) 0 = 0 := by
    simpa [xAxis] using hGeometry.upperChargeCoordinates.1
  have hUpperY :
      positionInMeters (setup.position .upperChargeCenter) 1 = (1 : ℝ) / 20 := by
    simpa [yAxis, hLength] using hGeometry.upperChargeCoordinates.2
  have hLowerX :
      positionInMeters (setup.position .lowerChargeCenter) 0 = 0 := by
    simpa [xAxis] using hGeometry.lowerChargeCoordinates.1
  have hLowerY :
      positionInMeters (setup.position .lowerChargeCenter) 1 = -((1 : ℝ) / 20) := by
    simpa [yAxis, hLength] using hGeometry.lowerChargeCoordinates.2
  have hDotX :
      positionInMeters (setup.position .observationDot) 0 = -((1 : ℝ) / 20) := by
    simpa [xAxis, hLength] using hGeometry.observationDotCoordinates.1
  have hDotY :
      positionInMeters (setup.position .observationDot) 1 = 0 := by
    simpa [yAxis] using hGeometry.observationDotCoordinates.2
  have hsqrt2_nonneg : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hsqrt2_sq : Real.sqrt 2 ^ 2 = (2 : ℝ) :=
    Real.sq_sqrt (by norm_num)
  have hrad :
      0 ≤ ((1 : ℝ) / 20) ^ 2 + ((1 : ℝ) / 20) ^ 2 := by
    positivity
  have hlhs_nonneg :
      0 ≤ Real.sqrt (((1 : ℝ) / 20) ^ 2 + ((1 : ℝ) / 20) ^ 2) :=
    Real.sqrt_nonneg _
  have hlhs_sq :
      Real.sqrt (((1 : ℝ) / 20) ^ 2 + ((1 : ℝ) / 20) ^ 2) ^ 2 =
        ((1 : ℝ) / 20) ^ 2 + ((1 : ℝ) / 20) ^ 2 :=
    Real.sq_sqrt hrad
  constructor
  · rw [dist_eq_norm, EuclideanSpace.norm_eq, Fin.sum_univ_two]
    change
      Real.sqrt
          (‖positionInMeters (setup.position .upperChargeCenter) 0 -
                positionInMeters (setup.position .observationDot) 0‖ ^ 2 +
            ‖positionInMeters (setup.position .upperChargeCenter) 1 -
                positionInMeters (setup.position .observationDot) 1‖ ^ 2) =
        _
    rw [hUpperX, hUpperY, hDotX, hDotY]
    simp only [sub_zero, Real.norm_eq_abs,
      abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 20)]
    nlinarith
  · rw [dist_eq_norm, EuclideanSpace.norm_eq, Fin.sum_univ_two]
    change
      Real.sqrt
          (‖positionInMeters (setup.position .lowerChargeCenter) 0 -
                positionInMeters (setup.position .observationDot) 0‖ ^ 2 +
            ‖positionInMeters (setup.position .lowerChargeCenter) 1 -
                positionInMeters (setup.position .observationDot) 1‖ ^ 2) =
        _
    rw [hLowerX, hLowerY, hDotX, hDotY]
    simp only [sub_zero, Real.norm_eq_abs, abs_neg,
      abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 20)]
    nlinarith

/-! ## Multiple-choice readout and blueprint target -/

/-- The four answer labels in the problem source. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- The electric-field-strength number printed beside each choice, in N/C. -/
def answerStrengthInNewtonsPerCoulomb : AnswerChoice → ℝ
  | .A => 1.3e3
  | .B => 5.3e3
  | .C => 1.0e4
  | .D => 7.6e3

/-- The answer label recorded in the supplied dataset metadata. -/
def recordedDatasetAnswer : AnswerChoice := .D

/-- Rounding tolerance appropriate to the two-significant-figure answer. -/
def answerAgreementToleranceInNewtonsPerCoulomb : ℝ := 1e2

/-- Absolute discrepancy between the calculated strength and a displayed value. -/
def answerDiscrepancyInNewtonsPerCoulomb
    (setup : OppositePointChargeSetup) (choice : AnswerChoice) : ℝ :=
  |fieldStrengthInNewtonsPerCoulomb setup.electricFieldStrengthAtDot -
    answerStrengthInNewtonsPerCoulomb choice|

/-- A displayed choice is strictly closer than every other displayed choice. -/
def IsUniqueClosestAnswer
    (setup : OppositePointChargeSetup) (choice : AnswerChoice) : Prop :=
  ∀ other : AnswerChoice, other ≠ choice →
    answerDiscrepancyInNewtonsPerCoulomb setup choice <
      answerDiscrepancyInNewtonsPerCoulomb setup other

/-!
**Blueprint target** `thm:physics:phyx_mini_0831:target`.

The point-charge computation gives approximately `7.64 × 10^3 N/C` when the
rounded Coulomb constant is used.  Hence it agrees with the displayed
two-significant-figure value `7.6 × 10^3 N/C`, and D is the unique closest
answer choice.  Neither conclusion is assumed by the figure, readout,
geometry, physical-parameter, or electrostatics premises.
-/
theorem electric_field_strength_at_observation_dot
    (setup : OppositePointChargeSetup)
    (hFigure : MatchesPrimaryFigure setup)
    (hReadouts : MatchesProblemReadouts setup)
    (hGeometry : HasDepictedGeometry setup)
    (hPhysical : HasPhysicalParameters setup)
    (hElectrostatics : SatisfiesPointChargeElectrostatics setup) :
    answerDiscrepancyInNewtonsPerCoulomb setup .D <
        answerAgreementToleranceInNewtonsPerCoulomb ∧
      IsUniqueClosestAnswer setup .D := by
  have hLength (arm : FigureArm) :
      lengthInMeters (setup.displayedArmLength arm) = (1 : ℝ) / 20 := by
    have h := hReadouts.everyArmCentimeters arm
    rw [lengthInCentimeters] at h
    norm_num at h ⊢
    linarith
  have hUpperX :
      positionInMeters (setup.position .upperChargeCenter) 0 = 0 := by
    simpa [xAxis] using hGeometry.upperChargeCoordinates.1
  have hUpperY :
      positionInMeters (setup.position .upperChargeCenter) 1 = (1 : ℝ) / 20 := by
    simpa [yAxis, hLength] using hGeometry.upperChargeCoordinates.2
  have hLowerX :
      positionInMeters (setup.position .lowerChargeCenter) 0 = 0 := by
    simpa [xAxis] using hGeometry.lowerChargeCoordinates.1
  have hLowerY :
      positionInMeters (setup.position .lowerChargeCenter) 1 = -((1 : ℝ) / 20) := by
    simpa [yAxis, hLength] using hGeometry.lowerChargeCoordinates.2
  have hDotX :
      positionInMeters (setup.position .observationDot) 0 = -((1 : ℝ) / 20) := by
    simpa [xAxis, hLength] using hGeometry.observationDotCoordinates.1
  have hDotY :
      positionInMeters (setup.position .observationDot) 1 = 0 := by
    simpa [yAxis] using hGeometry.observationDotCoordinates.2
  have hUpperDisplacementX :
      (positionInMeters (setup.position .observationDot) -
          positionInMeters (setup.position .upperChargeCenter)) 0 =
        -((1 : ℝ) / 20) := by
    change
      positionInMeters (setup.position .observationDot) 0 -
          positionInMeters (setup.position .upperChargeCenter) 0 =
        -((1 : ℝ) / 20)
    rw [hDotX, hUpperX]
    ring
  have hUpperDisplacementY :
      (positionInMeters (setup.position .observationDot) -
          positionInMeters (setup.position .upperChargeCenter)) 1 =
        -((1 : ℝ) / 20) := by
    change
      positionInMeters (setup.position .observationDot) 1 -
          positionInMeters (setup.position .upperChargeCenter) 1 =
        -((1 : ℝ) / 20)
    rw [hDotY, hUpperY]
    ring
  have hLowerDisplacementX :
      (positionInMeters (setup.position .observationDot) -
          positionInMeters (setup.position .lowerChargeCenter)) 0 =
        -((1 : ℝ) / 20) := by
    change
      positionInMeters (setup.position .observationDot) 0 -
          positionInMeters (setup.position .lowerChargeCenter) 0 =
        -((1 : ℝ) / 20)
    rw [hDotX, hLowerX]
    ring
  have hLowerDisplacementY :
      (positionInMeters (setup.position .observationDot) -
          positionInMeters (setup.position .lowerChargeCenter)) 1 =
        (1 : ℝ) / 20 := by
    change
      positionInMeters (setup.position .observationDot) 1 -
          positionInMeters (setup.position .lowerChargeCenter) 1 =
        (1 : ℝ) / 20
    rw [hDotY, hLowerY]
    ring
  have hUpperCharge :
      chargeInCoulombs (setup.charge .upperPositive) =
        (3 : ℝ) / 1000000000 := by
    have h := hReadouts.upperChargeNanocoulombs
    rw [chargeInNanocoulombs] at h
    norm_num at h ⊢
    linarith
  have hLowerCharge :
      chargeInCoulombs (setup.charge .lowerNegative) =
        -(3 : ℝ) / 1000000000 := by
    have h := hReadouts.lowerChargeNanocoulombs
    rw [chargeInNanocoulombs] at h
    norm_num at h ⊢
    linarith
  have hCoulombConstant :
      coulombConstantInNewtonMeterSquaredPerCoulombSquared
          setup.electromagneticSystem = (9000000000 : ℝ) := by
    have h := hReadouts.roundedVacuumCoulombConstant
    norm_num at h ⊢
    exact h
  obtain ⟨hUpperDistance, hLowerDistance⟩ :=
    source_to_dot_distances setup hReadouts hGeometry
  have hUpperNorm :
      ‖positionInMeters (setup.position .observationDot) -
          positionInMeters (setup.position .upperChargeCenter)‖ =
        Real.sqrt 2 / 20 := by
    calc
      ‖positionInMeters (setup.position .observationDot) -
          positionInMeters (setup.position .upperChargeCenter)‖ =
          dist (positionInMeters (setup.position .observationDot))
            (positionInMeters (setup.position .upperChargeCenter)) :=
        (dist_eq_norm _ _).symm
      _ = dist (positionInMeters (setup.position .upperChargeCenter))
            (positionInMeters (setup.position .observationDot)) := dist_comm _ _
      _ = Real.sqrt 2 / 20 := hUpperDistance
  have hLowerNorm :
      ‖positionInMeters (setup.position .observationDot) -
          positionInMeters (setup.position .lowerChargeCenter)‖ =
        Real.sqrt 2 / 20 := by
    calc
      ‖positionInMeters (setup.position .observationDot) -
          positionInMeters (setup.position .lowerChargeCenter)‖ =
          dist (positionInMeters (setup.position .observationDot))
            (positionInMeters (setup.position .lowerChargeCenter)) :=
        (dist_eq_norm _ _).symm
      _ = dist (positionInMeters (setup.position .lowerChargeCenter))
            (positionInMeters (setup.position .observationDot)) := dist_comm _ _
      _ = Real.sqrt 2 / 20 := hLowerDistance
  have hsqrt2_pos : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hsqrt2_ne : Real.sqrt 2 ≠ 0 := ne_of_gt hsqrt2_pos
  have hsqrt2_sq : Real.sqrt 2 ^ 2 = (2 : ℝ) :=
    Real.sq_sqrt (by norm_num)
  have hUpperCoefficient :
      (9000000000 : ℝ) * ((3 : ℝ) / 1000000000) /
          (Real.sqrt 2 / 20) ^ 3 =
        54000 * Real.sqrt 2 := by
    field_simp
    nlinarith
  have hLowerCoefficient :
      (9000000000 : ℝ) * (-(3 : ℝ) / 1000000000) /
          (Real.sqrt 2 / 20) ^ 3 =
        -54000 * Real.sqrt 2 := by
    field_simp
    nlinarith
  have hUpperLaw :=
    hElectrostatics.pointChargeFieldLaw ChargeSource.upperPositive
  simp only [ChargeSource.figurePoint] at hUpperLaw
  rw [hCoulombConstant, hUpperCharge, hUpperNorm, hUpperCoefficient] at hUpperLaw
  have hUpperFieldX :
      fieldVectorInNewtonsPerCoulomb
          (setup.fieldContributionAtDot .upperPositive) 0 =
        -2700 * Real.sqrt 2 := by
    have h := congrArg
      (fun field : EuclideanSpace ℝ (Fin 2) => field 0) hUpperLaw
    change
      fieldVectorInNewtonsPerCoulomb
            (setup.fieldContributionAtDot .upperPositive) 0 =
        (54000 * Real.sqrt 2) *
          (positionInMeters (setup.position .observationDot) -
            positionInMeters (setup.position .upperChargeCenter)) 0 at h
    rw [hUpperDisplacementX] at h
    convert h using 1 <;> ring
  have hUpperFieldY :
      fieldVectorInNewtonsPerCoulomb
          (setup.fieldContributionAtDot .upperPositive) 1 =
        -2700 * Real.sqrt 2 := by
    have h := congrArg
      (fun field : EuclideanSpace ℝ (Fin 2) => field 1) hUpperLaw
    change
      fieldVectorInNewtonsPerCoulomb
            (setup.fieldContributionAtDot .upperPositive) 1 =
        (54000 * Real.sqrt 2) *
          (positionInMeters (setup.position .observationDot) -
            positionInMeters (setup.position .upperChargeCenter)) 1 at h
    rw [hUpperDisplacementY] at h
    convert h using 1 <;> ring
  have hLowerLaw :=
    hElectrostatics.pointChargeFieldLaw ChargeSource.lowerNegative
  simp only [ChargeSource.figurePoint] at hLowerLaw
  rw [hCoulombConstant, hLowerCharge, hLowerNorm, hLowerCoefficient] at hLowerLaw
  have hLowerFieldX :
      fieldVectorInNewtonsPerCoulomb
          (setup.fieldContributionAtDot .lowerNegative) 0 =
        2700 * Real.sqrt 2 := by
    have h := congrArg
      (fun field : EuclideanSpace ℝ (Fin 2) => field 0) hLowerLaw
    change
      fieldVectorInNewtonsPerCoulomb
            (setup.fieldContributionAtDot .lowerNegative) 0 =
        (-54000 * Real.sqrt 2) *
          (positionInMeters (setup.position .observationDot) -
            positionInMeters (setup.position .lowerChargeCenter)) 0 at h
    rw [hLowerDisplacementX] at h
    convert h using 1 <;> ring
  have hLowerFieldY :
      fieldVectorInNewtonsPerCoulomb
          (setup.fieldContributionAtDot .lowerNegative) 1 =
        -2700 * Real.sqrt 2 := by
    have h := congrArg
      (fun field : EuclideanSpace ℝ (Fin 2) => field 1) hLowerLaw
    change
      fieldVectorInNewtonsPerCoulomb
            (setup.fieldContributionAtDot .lowerNegative) 1 =
        (-54000 * Real.sqrt 2) *
          (positionInMeters (setup.position .observationDot) -
            positionInMeters (setup.position .lowerChargeCenter)) 1 at h
    rw [hLowerDisplacementY] at h
    convert h using 1 <;> ring
  have hNetFieldX :
      fieldVectorInNewtonsPerCoulomb setup.netElectricFieldAtDot 0 = 0 := by
    have h := congrArg
      (fun field : EuclideanSpace ℝ (Fin 2) => field 0)
      hElectrostatics.superpositionAtDot
    change
      fieldVectorInNewtonsPerCoulomb setup.netElectricFieldAtDot 0 =
        fieldVectorInNewtonsPerCoulomb
            (setup.fieldContributionAtDot .upperPositive) 0 +
          fieldVectorInNewtonsPerCoulomb
            (setup.fieldContributionAtDot .lowerNegative) 0 at h
    rw [hUpperFieldX, hLowerFieldX] at h
    convert h using 1 <;> ring
  have hNetFieldY :
      fieldVectorInNewtonsPerCoulomb setup.netElectricFieldAtDot 1 =
        -5400 * Real.sqrt 2 := by
    have h := congrArg
      (fun field : EuclideanSpace ℝ (Fin 2) => field 1)
      hElectrostatics.superpositionAtDot
    change
      fieldVectorInNewtonsPerCoulomb setup.netElectricFieldAtDot 1 =
        fieldVectorInNewtonsPerCoulomb
            (setup.fieldContributionAtDot .upperPositive) 1 +
          fieldVectorInNewtonsPerCoulomb
            (setup.fieldContributionAtDot .lowerNegative) 1 at h
    rw [hUpperFieldY, hLowerFieldY] at h
    convert h using 1 <;> ring
  have hNetNorm :
      ‖fieldVectorInNewtonsPerCoulomb setup.netElectricFieldAtDot‖ =
        5400 * Real.sqrt 2 := by
    rw [EuclideanSpace.norm_eq, Fin.sum_univ_two]
    change
      Real.sqrt
          (‖fieldVectorInNewtonsPerCoulomb setup.netElectricFieldAtDot 0‖ ^ 2 +
            ‖fieldVectorInNewtonsPerCoulomb setup.netElectricFieldAtDot 1‖ ^ 2) =
        _
    rw [hNetFieldX, hNetFieldY]
    have hnonneg : 0 ≤ 5400 * Real.sqrt 2 := by positivity
    simp [Real.norm_eq_abs]
  have hStrength :
      fieldStrengthInNewtonsPerCoulomb setup.electricFieldStrengthAtDot =
        5400 * Real.sqrt 2 := by
    rw [hElectrostatics.strengthIsNetFieldNorm, hNetNorm]
  have hsqrt2_lower : (1414 : ℝ) / 1000 < Real.sqrt 2 := by
    nlinarith only [hsqrt2_sq, Real.sqrt_nonneg 2]
  have hsqrt2_upper : Real.sqrt 2 < (1415 : ℝ) / 1000 := by
    nlinarith only [hsqrt2_sq, Real.sqrt_nonneg 2]
  have hStrengthLower : (7600 : ℝ) <
      fieldStrengthInNewtonsPerCoulomb setup.electricFieldStrengthAtDot := by
    rw [hStrength]
    nlinarith only [hsqrt2_lower]
  have hStrengthUpper :
      fieldStrengthInNewtonsPerCoulomb setup.electricFieldStrengthAtDot <
        (7700 : ℝ) := by
    rw [hStrength]
    nlinarith only [hsqrt2_upper]
  constructor
  · rw [answerDiscrepancyInNewtonsPerCoulomb, hStrength]
    norm_num [answerStrengthInNewtonsPerCoulomb,
      answerAgreementToleranceInNewtonsPerCoulomb]
    rw [abs_of_pos (by nlinarith only [hsqrt2_lower])]
    nlinarith only [hsqrt2_upper]
  · intro other hOther
    fin_cases other
    · rw [answerDiscrepancyInNewtonsPerCoulomb,
        answerDiscrepancyInNewtonsPerCoulomb, hStrength]
      norm_num [answerStrengthInNewtonsPerCoulomb]
      rw [abs_of_pos (by nlinarith only [hsqrt2_lower]),
        abs_of_pos (by nlinarith only [hsqrt2_lower])]
      norm_num
    · rw [answerDiscrepancyInNewtonsPerCoulomb,
        answerDiscrepancyInNewtonsPerCoulomb, hStrength]
      norm_num [answerStrengthInNewtonsPerCoulomb]
      rw [abs_of_pos (by nlinarith only [hsqrt2_lower]),
        abs_of_pos (by nlinarith only [hsqrt2_lower])]
      norm_num
    · rw [answerDiscrepancyInNewtonsPerCoulomb,
        answerDiscrepancyInNewtonsPerCoulomb, hStrength]
      norm_num [answerStrengthInNewtonsPerCoulomb]
      rw [abs_of_pos (by nlinarith only [hsqrt2_lower]),
        abs_of_neg (by nlinarith only [hsqrt2_upper])]
      nlinarith only [hsqrt2_upper]
    · exact (hOther rfl).elim

end PhyXMiniProblems.ProblemPhyXMini0831
