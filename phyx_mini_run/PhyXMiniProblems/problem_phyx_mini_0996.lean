import Mathlib
import Physlib.Electromagnetism.Basic
import Physlib.SpaceAndTime.Space.CrossProduct
import Physlib.Units.WithDim.Basic

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0996

open Dimension Space Matrix

/-!
# Torque on an electric dipole in a uniform electric field

The primary raster `996.png` shows the electric-dipole-moment vector `p`
pointing down and left, a uniform electric-field vector `E` pointing to the
right, and a marked angle of `145°` between them. The written data give
opposite charges of magnitude `1.6 × 10⁻¹⁹ C`, a separation intended as
`0.125 × 10⁻⁹ m`, and a field magnitude of `5.0 × 10⁵ N/C`.

The source also contains the dimensionally contradictory transcription
`0.125 m = 0.125 × 10⁻⁹ m`. This model uses the explicit scientific-notation
value `0.125 × 10⁻⁹ m`, which is consistent with the dipole scale and the
recorded answer. It does not admit the contradictory equality as a premise.

Physical quantities use Physlib's unit-independent `Dimensionful` and
`WithDim` types. Real scalars occur only at coherent-SI readout boundaries,
for the dimensionless angle, and for displayed multiple-choice data.
-/

/-! ## Physical dimensions and coherent-SI readouts -/

/-- The dimension `M L T⁻² C⁻¹` of electric-field strength. -/
def electricFieldStrengthDimension : Dimension :=
  M𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹ * C𝓭⁻¹

/-- The dimension `C L` of electric dipole moment. -/
def electricDipoleMomentDimension : Dimension :=
  C𝓭 * L𝓭

/-- The dimension `M L² T⁻²` of torque. -/
def torqueDimension : Dimension :=
  M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹

/-- Three-dimensional vectors used at coherent-SI readout boundaries. -/
abbrev SpatialVector : Type :=
  EuclideanSpace ℝ (Fin 3)

/-- A signed, unit-independent electric charge. -/
abbrev SignedChargeQuantity : Type :=
  Dimensionful (WithDim C𝓭 ℝ)

/-- A nonnegative, unit-independent physical length. -/
abbrev LengthQuantity : Type :=
  Dimensionful (WithDim L𝓭 NNReal)

/-- A unit-independent physical position vector. -/
abbrev PositionQuantity : Type :=
  Dimensionful (WithDim L𝓭 SpatialVector)

/-- A nonnegative, unit-independent electric-field magnitude. -/
abbrev ElectricFieldStrengthQuantity : Type :=
  Dimensionful (WithDim electricFieldStrengthDimension NNReal)

/-- A unit-independent electric-field vector. -/
abbrev ElectricFieldVectorQuantity : Type :=
  Dimensionful (WithDim electricFieldStrengthDimension SpatialVector)

/-- A unit-independent electric-dipole-moment vector. -/
abbrev ElectricDipoleMomentQuantity : Type :=
  Dimensionful (WithDim electricDipoleMomentDimension SpatialVector)

/-- A unit-independent electric-torque vector. -/
abbrev TorqueVectorQuantity : Type :=
  Dimensionful (WithDim torqueDimension SpatialVector)

/-- A nonnegative, unit-independent torque magnitude. -/
abbrev TorqueMagnitudeQuantity : Type :=
  Dimensionful (WithDim torqueDimension NNReal)

/-- Read a signed charge in coherent-SI coulombs. -/
def signedChargeInCoulombs (charge : SignedChargeQuantity) : ℝ :=
  (charge UnitChoices.SI).val

/-- Read a length in coherent-SI metres. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  ((length UnitChoices.SI).val : ℝ)

/-- Read a physical position vector in coherent-SI metres. -/
def positionVectorInMeters (position : PositionQuantity) : SpatialVector :=
  (position UnitChoices.SI).val

/-- Read an electric-field magnitude in coherent-SI newtons per coulomb. -/
def electricFieldStrengthInNewtonsPerCoulomb
    (strength : ElectricFieldStrengthQuantity) : ℝ :=
  ((strength UnitChoices.SI).val : ℝ)

/-- Read an electric-field vector in coherent-SI newtons per coulomb. -/
def electricFieldVectorInNewtonsPerCoulomb
    (field : ElectricFieldVectorQuantity) : SpatialVector :=
  (field UnitChoices.SI).val

/-- Read a dipole-moment vector in coherent-SI coulomb metres. -/
def dipoleMomentVectorInCoulombMeters
    (moment : ElectricDipoleMomentQuantity) : SpatialVector :=
  (moment UnitChoices.SI).val

/-- Read an electric-torque vector in coherent-SI newton metres. -/
def torqueVectorInNewtonMeters (torque : TorqueVectorQuantity) : SpatialVector :=
  (torque UnitChoices.SI).val

/-- Read a torque magnitude in coherent-SI newton metres. -/
def torqueMagnitudeInNewtonMeters (torque : TorqueMagnitudeQuantity) : ℝ :=
  ((torque UnitChoices.SI).val : ℝ)

/-- Convert an angle measured in degrees to a dimensionless radian value. -/
def degreesToRadians (degrees : ℝ) : ℝ :=
  degrees * Real.pi / 180

/-! ## Physical roles and primary-figure vocabulary -/

/-- The signs of the two point charges making up the dipole. -/
inductive ChargeLabel where
  | negative
  | positive
  deriving DecidableEq, Fintype, Repr

/-- The three vector symbols printed in the supplied image. -/
inductive FigureVectorLabel where
  | dipoleMomentP
  | electricFieldE
  | torqueTau
  deriving DecidableEq, Fintype, Repr

/-- Qualitative arrow directions visible in the plane of the image. -/
inductive FigureArrowDirection where
  | rightward
  | downwardLeft
  | directionNotDrawn
  deriving DecidableEq, Repr

/-- Idealization of the two charges as an electric dipole. -/
inductive DipoleModel where
  | oppositePointCharges
  | other
  deriving DecidableEq, Repr

/-- Spatial dependence assigned to the external electric field. -/
inductive ElectricFieldSpatialModel where
  | uniform
  | nonuniform
  deriving DecidableEq, Repr

/-- Relation of a vector to the plane containing the primary diagram. -/
inductive FigurePlaneRelation where
  | parallel
  | perpendicular
  | oblique
  deriving DecidableEq, Repr

/-!
Literal graphical evidence from `996.png`. It records symbols, directions,
the red common origin, and the angle arc, but no torque-magnitude answer.
-/
structure ElectricDipoleTorqueFigure where
  vectorLabelShown : FigureVectorLabel → Bool
  vectorArrowDirection : FigureVectorLabel → FigureArrowDirection
  arrowsShareCentralRedOrigin : Bool
  torqueLabelAboveCentralOrigin : Bool
  angleArcShown : Bool
  angleArcStartsAt : FigureVectorLabel
  angleArcEndsAt : FigureVectorLabel
  printedAngleDegrees : ℝ

/-! ## Independent physical setup -/

/-!
The charges, positions, field, dipole moment, torque vector, and torque
magnitude are independent physical data. Their relationships occur only in
the scenario, geometry, and governing-law predicates below.
-/
structure ElectricDipoleTorqueSetup where
  dipoleModel : DipoleModel
  chargesArePointlike : Bool
  fieldSpatialModel : ElectricFieldSpatialModel
  fieldPlaneRelation : FigurePlaneRelation
  charge : ChargeLabel → SignedChargeQuantity
  chargePosition : ChargeLabel → PositionQuantity
  dipoleCenterPosition : PositionQuantity
  chargeSeparation : LengthQuantity
  electricFieldStrength : ElectricFieldStrengthQuantity
  electricFieldVector : ElectricFieldVectorQuantity
  dipoleMoment : ElectricDipoleMomentQuantity
  electricTorque : TorqueVectorQuantity
  electricTorqueMagnitude : TorqueMagnitudeQuantity
  electricField : Electromagnetism.ElectricField 3
  observationTime : Time
  dipoleFieldAngleRadians : ℝ
  pageNormal : SpatialVector
  figure : ElectricDipoleTorqueFigure

/-- Displacement from the negative charge to the positive charge, in metres. -/
def chargeSeparationVectorInMeters
    (setup : ElectricDipoleTorqueSetup) : SpatialVector :=
  positionVectorInMeters (setup.chargePosition .positive) -
    positionVectorInMeters (setup.chargePosition .negative)

/-- A vector points strictly right in the chosen in-page coordinates. -/
def PointsRightwardInFigure (vector : SpatialVector) : Prop :=
  0 < vector (0 : Fin 3) ∧
    vector (1 : Fin 3) = 0 ∧
    vector (2 : Fin 3) = 0

/-- A vector points down and left in the chosen in-page coordinates. -/
def PointsDownwardLeftInFigure (vector : SpatialVector) : Prop :=
  vector (0 : Fin 3) < 0 ∧
    vector (1 : Fin 3) < 0 ∧
    vector (2 : Fin 3) = 0

/-! ## Scenario, readout, figure, geometry, and law assumptions -/

/-- Qualitative facts stated in the written physical scenario. -/
structure MatchesWrittenScenario (setup : ElectricDipoleTorqueSetup) : Prop where
  twoOppositePointCharges : setup.dipoleModel = .oppositePointCharges
  pointlikeCharges : setup.chargesArePointlike = true
  uniformExternalField : setup.fieldSpatialModel = .uniform
  fieldParallelToFigurePlane : setup.fieldPlaneRelation = .parallel

/-!
Numerical problem data. The separation is read as `0.125 nm =
0.125 × 10⁻⁹ m`. No torque value occurs in these premises.
-/
structure MatchesProblemReadouts (setup : ElectricDipoleTorqueSetup) : Prop where
  positiveChargeMagnitude :
    signedChargeInCoulombs (setup.charge .positive) =
      (16 / 10 ^ 20 : ℝ)
  negativeChargeMagnitude :
    signedChargeInCoulombs (setup.charge .negative) =
      -(16 / 10 ^ 20 : ℝ)
  separationIsPointOneTwoFiveNanometers :
    lengthInMeters setup.chargeSeparation =
      (125 / 10 ^ 12 : ℝ)
  fieldMagnitudeIsFiveTimesTenToFive :
    electricFieldStrengthInNewtonsPerCoulomb
        setup.electricFieldStrength = 500000

/-!
Primary-image evidence and its calibration against the stored physical angle.
The raster does not supply the requested torque magnitude.
-/
structure MatchesPrimaryFigure (setup : ElectricDipoleTorqueSetup) : Prop where
  allVectorLabelsShown :
    ∀ label, setup.figure.vectorLabelShown label = true
  commonRedOriginShown : setup.figure.arrowsShareCentralRedOrigin = true
  torqueLabelAboveOrigin : setup.figure.torqueLabelAboveCentralOrigin = true
  dipoleArrowPointsDownAndLeft :
    setup.figure.vectorArrowDirection .dipoleMomentP = .downwardLeft
  fieldArrowPointsRight :
    setup.figure.vectorArrowDirection .electricFieldE = .rightward
  torqueDirectionIsNotDepicted :
    setup.figure.vectorArrowDirection .torqueTau = .directionNotDrawn
  angleArcIsShown : setup.figure.angleArcShown = true
  angleArcStartsAtDipoleMoment :
    setup.figure.angleArcStartsAt = .dipoleMomentP
  angleArcEndsAtElectricField :
    setup.figure.angleArcEndsAt = .electricFieldE
  angleLabelIsOneHundredFortyFiveDegrees :
    setup.figure.printedAngleDegrees = 145
  angleLabelRepresentsPhysicalAngle :
    setup.dipoleFieldAngleRadians =
      degreesToRadians setup.figure.printedAngleDegrees

/-!
Geometric meaning of the charge positions, in-page vectors, and marked angle.
-/
structure HasElectricDipoleGeometry
    (setup : ElectricDipoleTorqueSetup) : Prop where
  centerIsChargeMidpoint :
    positionVectorInMeters setup.dipoleCenterPosition =
      (1 / 2 : ℝ) •
        (positionVectorInMeters (setup.chargePosition .negative) +
          positionVectorInMeters (setup.chargePosition .positive))
  separationMagnitudeAgrees :
    ‖chargeSeparationVectorInMeters setup‖ =
      lengthInMeters setup.chargeSeparation
  pageNormalIsUnit : ‖setup.pageNormal‖ = 1
  chargesLieInFigurePlane :
    ∀ charge,
      inner ℝ
          (positionVectorInMeters (setup.chargePosition charge) -
            positionVectorInMeters setup.dipoleCenterPosition)
          setup.pageNormal = 0
  fieldLiesInFigurePlane :
    inner ℝ
        (electricFieldVectorInNewtonsPerCoulomb setup.electricFieldVector)
        setup.pageNormal = 0
  dipoleMomentLiesInFigurePlane :
    inner ℝ
        (dipoleMomentVectorInCoulombMeters setup.dipoleMoment)
        setup.pageNormal = 0
  dipoleMomentPointsAsDrawn :
    PointsDownwardLeftInFigure
      (dipoleMomentVectorInCoulombMeters setup.dipoleMoment)
  electricFieldPointsAsDrawn :
    PointsRightwardInFigure
      (electricFieldVectorInNewtonsPerCoulomb setup.electricFieldVector)
  angleIsBetweenDipoleMomentAndField :
    setup.dipoleFieldAngleRadians =
      InnerProductGeometry.angle
        (dipoleMomentVectorInCoulombMeters setup.dipoleMoment)
        (electricFieldVectorInNewtonsPerCoulomb setup.electricFieldVector)

/-!
Physlib's spacetime-dependent field is specialized to the stated static,
uniform vector. Its norm agrees with the dimensionful scalar field strength.
-/
structure RepresentsUniformElectricField
    (setup : ElectricDipoleTorqueSetup) : Prop where
  fieldIsStaticAndUniform :
    ∀ time position,
      setup.electricField time position =
        electricFieldVectorInNewtonsPerCoulomb setup.electricFieldVector
  scalarStrengthAgreesWithVector :
    ‖electricFieldVectorInNewtonsPerCoulomb setup.electricFieldVector‖ =
      electricFieldStrengthInNewtonsPerCoulomb
        setup.electricFieldStrength

/-!
General point-dipole and electric-torque laws. They state `q₋ = -q₊`,
`p = q₊ (r₊ - r₋)`, `τ = p × E`, and that the measured torque magnitude is
the norm of the torque vector. They contain no requested numerical answer.
-/
structure ObeysElectricDipoleTorqueLaws
    (setup : ElectricDipoleTorqueSetup) : Prop where
  chargesAreEqualAndOpposite :
    signedChargeInCoulombs (setup.charge .negative) =
      -signedChargeInCoulombs (setup.charge .positive)
  pointChargeDipoleMomentLaw :
    dipoleMomentVectorInCoulombMeters setup.dipoleMoment =
      signedChargeInCoulombs (setup.charge .positive) •
        chargeSeparationVectorInMeters setup
  uniformFieldElectricTorqueLaw :
    torqueVectorInNewtonMeters setup.electricTorque =
      dipoleMomentVectorInCoulombMeters setup.dipoleMoment ⨯ₑ₃
        electricFieldVectorInNewtonsPerCoulomb setup.electricFieldVector
  torqueMagnitudeIsVectorNorm :
    torqueMagnitudeInNewtonMeters setup.electricTorqueMagnitude =
      ‖torqueVectorInNewtonMeters setup.electricTorque‖

/-! ## Displayed answers and target conclusions -/

/-- Labels of the four multiple-choice answers in the source. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Unit text printed beside each answer choice. -/
inductive DisplayedUnit where
  | newtonMeter
  | omitted
  | joule
  | newtonPerCoulomb
  deriving DecidableEq, Repr

/-- Numerical value printed by each answer, interpreted as an SI scalar. -/
def AnswerChoice.displayedMagnitudeSI : AnswerChoice → ℝ
  | .A => 2 / 10 ^ 29
  | .B => 57 / 10 ^ 25
  | .C => 82 / 10 ^ 25
  | .D => 57 / 10 ^ 25

/-- Unit text attached to each displayed choice in the source. -/
def AnswerChoice.displayedUnit : AnswerChoice → DisplayedUnit
  | .A => .newtonMeter
  | .B => .omitted
  | .C => .joule
  | .D => .newtonPerCoulomb

/-!
The source omits B's unit. Since the question explicitly requests a torque,
the physically interpreted unit for that option is newton metres. Keeping this
separate from `displayedUnit` preserves both the literal source and the unit
needed to understand the proposed answer.
-/
def AnswerChoice.interpretedUnitForTorqueQuestion :
    AnswerChoice → DisplayedUnit
  | .B => .newtonMeter
  | choice => choice.displayedUnit

/-- One unit in the last displayed decimal place of each answer. -/
def AnswerChoice.displayResolution : AnswerChoice → ℝ
  | .A => 1 / 10 ^ 30
  | .B => 1 / 10 ^ 25
  | .C => 1 / 10 ^ 25
  | .D => 1 / 10 ^ 25

/-! Whether an explicit unit is dimensionally compatible with torque. -/
def DisplayedUnit.isTorqueCompatible : DisplayedUnit → Prop
  | .newtonMeter => True
  | .omitted => False
  | .joule => True
  | .newtonPerCoulomb => False

/-- An actual scalar rounds to a displayed scalar at the stated resolution. -/
def RoundsToAtResolution
    (actual displayed resolution : ℝ) : Prop :=
  0 < resolution ∧ |actual - displayed| < resolution / 2

/-- A choice has torque-compatible units and its displayed number matches. -/
def MatchesDisplayedTorqueChoice
    (setup : ElectricDipoleTorqueSetup) (choice : AnswerChoice) : Prop :=
  choice.interpretedUnitForTorqueQuestion.isTorqueCompatible ∧
    RoundsToAtResolution
      (torqueMagnitudeInNewtonMeters setup.electricTorqueMagnitude)
      choice.displayedMagnitudeSI
      choice.displayResolution

/-- A displayed choice is the unique match for the modeled torque magnitude. -/
def IsUniqueMatchingTorqueChoice
    (setup : ElectricDipoleTorqueSetup) (choice : AnswerChoice) : Prop :=
  MatchesDisplayedTorqueChoice setup choice ∧
    ∀ other : AnswerChoice,
      MatchesDisplayedTorqueChoice setup other → other = choice

/-- Dataset metadata recording the supplied answer key; not a theorem premise. -/
def recordedDatasetAnswer : AnswerChoice :=
  .B

/-!
The exact general magnitude relation obtained from `τ = p × E` and the angle
between `p` and `E`. This relation is derived, not stored in a law field.
-/
lemma electricDipoleTorqueMagnitude_formula
    (setup : ElectricDipoleTorqueSetup)
    (hGeometry : HasElectricDipoleGeometry setup)
    (hUniformField : RepresentsUniformElectricField setup)
    (hLaws : ObeysElectricDipoleTorqueLaws setup) :
    torqueMagnitudeInNewtonMeters setup.electricTorqueMagnitude =
      |signedChargeInCoulombs (setup.charge .positive)| *
        lengthInMeters setup.chargeSeparation *
        electricFieldStrengthInNewtonsPerCoulomb
          setup.electricFieldStrength *
        |Real.sin setup.dipoleFieldAngleRadians| := by
  have hSinNonnegative : 0 ≤ Real.sin setup.dipoleFieldAngleRadians := by
    rw [hGeometry.angleIsBetweenDipoleMomentAndField]
    exact InnerProductGeometry.sin_angle_nonneg _ _
  rw [hLaws.torqueMagnitudeIsVectorNorm,
    hLaws.uniformFieldElectricTorqueLaw]
  calc
    _ = ‖dipoleMomentVectorInCoulombMeters setup.dipoleMoment‖ *
          ‖electricFieldVectorInNewtonsPerCoulomb setup.electricFieldVector‖ *
          Real.sin
            (InnerProductGeometry.angle
              (dipoleMomentVectorInCoulombMeters setup.dipoleMoment)
              (electricFieldVectorInNewtonsPerCoulomb setup.electricFieldVector)) := by
      simpa only [WithLp.equiv_apply, WithLp.equiv_symm_apply] using
        InnerProductGeometry.norm_ofLp_crossProduct
          (dipoleMomentVectorInCoulombMeters setup.dipoleMoment)
          (electricFieldVectorInNewtonsPerCoulomb setup.electricFieldVector)
    _ = _ := by
      rw [← hGeometry.angleIsBetweenDipoleMomentAndField,
        hLaws.pointChargeDipoleMomentLaw,
        norm_smul, Real.norm_eq_abs,
        hGeometry.separationMagnitudeAgrees,
        hUniformField.scalarStrengthAgreesWithVector,
        abs_of_nonneg hSinNonnegative]

/-!
For the stated `0.125 nm` dipole, `5.0 × 10⁵ N/C` field, and `145°`
orientation, the torque magnitude rounds to `5.7 × 10⁻²⁴ N m`, uniquely
matching choice B.

This declaration formalizes `thm:physics:phyx_mini_0996:target`. The displayed
number and answer label occur only in the conclusion-side answer definitions,
not in the scenario, readout, figure, geometry, uniform-field, or governing-law
premises.
-/
theorem problem_phyx_mini_0996
    (setup : ElectricDipoleTorqueSetup)
    (hScenario : MatchesWrittenScenario setup)
    (hReadouts : MatchesProblemReadouts setup)
    (hFigure : MatchesPrimaryFigure setup)
    (hGeometry : HasElectricDipoleGeometry setup)
    (hUniformField : RepresentsUniformElectricField setup)
    (hLaws : ObeysElectricDipoleTorqueLaws setup) :
    RoundsToAtResolution
          (torqueMagnitudeInNewtonMeters setup.electricTorqueMagnitude)
          (57 / 10 ^ 25 : ℝ)
          (1 / 10 ^ 25 : ℝ) ∧
      IsUniqueMatchingTorqueChoice setup .B := by
  have hAngle :
      setup.dipoleFieldAngleRadians = 145 * Real.pi / 180 := by
    rw [hFigure.angleLabelRepresentsPhysicalAngle,
      hFigure.angleLabelIsOneHundredFortyFiveDegrees]
    rfl
  have hTorque :=
    electricDipoleTorqueMagnitude_formula setup hGeometry hUniformField hLaws
  rw [hReadouts.positiveChargeMagnitude,
    hReadouts.separationIsPointOneTwoFiveNanometers,
    hReadouts.fieldMagnitudeIsFiveTimesTenToFive,
    hAngle] at hTorque
  norm_num at hTorque
  have hSmallAnglePos : 0 < Real.pi / 36 := by positivity
  have hSmallAngleLtOne : Real.pi / 36 < 1 := by
    linarith [Real.pi_lt_four]
  have hPiSqUpper :
      Real.pi ^ 2 < (3.1416 : ℝ) ^ 2 :=
    (sq_lt_sq₀ Real.pi_nonneg (by norm_num)).2 Real.pi_lt_d4
  have hSmallAngleSqUpper :
      (Real.pi / 36) ^ 2 < (1 / 10 : ℝ) ^ 2 := by
    apply (sq_lt_sq₀ hSmallAnglePos.le (by norm_num)).2
    linarith [Real.pi_lt_d4]
  have hSmallAngleCubeUpper :
      (Real.pi / 36) ^ 3 < (1 / 10 : ℝ) ^ 3 := by
    calc
      (Real.pi / 36) ^ 3 =
          (Real.pi / 36) ^ 2 * (Real.pi / 36) := by ring
      _ < (1 / 10 : ℝ) ^ 2 * (1 / 10 : ℝ) :=
        mul_lt_mul hSmallAngleSqUpper
          (by linarith [Real.pi_lt_d4])
          hSmallAnglePos (by norm_num)
      _ = (1 / 10 : ℝ) ^ 3 := by ring
  have hSinSmallLower :
      (17 / 200 : ℝ) < Real.sin (Real.pi / 36) := by
    have hTaylor :=
      Real.sin_gt_sub_cube hSmallAnglePos hSmallAngleLtOne.le
    have hAngleLower : (87 / 1000 : ℝ) < Real.pi / 36 := by
      linarith [Real.pi_gt_d4]
    nlinarith
  have hSinSmallUpper :
      Real.sin (Real.pi / 36) < (873 / 10000 : ℝ) := by
    calc
      Real.sin (Real.pi / 36) < Real.pi / 36 :=
        Real.sin_lt hSmallAnglePos
      _ < (873 / 10000 : ℝ) := by
        linarith [Real.pi_lt_d4]
  have hCosSmallLower :
      (249 / 250 : ℝ) < Real.cos (Real.pi / 36) := by
    have hCosBound :=
      Real.one_sub_sq_div_two_le_cos (x := Real.pi / 36)
    nlinarith
  have hCosSmallUpper :
      Real.cos (Real.pi / 36) ≤ (647 / 648 : ℝ) := by
    have hAbsSmallAngle : |Real.pi / 36| ≤ Real.pi := by
      rw [abs_of_pos hSmallAnglePos]
      nlinarith [Real.pi_pos]
    calc
      Real.cos (Real.pi / 36) ≤
          1 - 2 / Real.pi ^ 2 * (Real.pi / 36) ^ 2 :=
        Real.cos_le_one_sub_mul_cos_sq hAbsSmallAngle
      _ = (647 / 648 : ℝ) := by
        field_simp [Real.pi_ne_zero]
        <;> ring
  have hSqrtThreeLower : (433 / 250 : ℝ) < √3 := by
    rw [Real.lt_sqrt (by norm_num : (0 : ℝ) ≤ 433 / 250)]
    norm_num
  have hSqrtThreeUpper : √3 < (1733 / 1000 : ℝ) := by
    rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < 1733 / 1000)]
    norm_num
  have hProductLower :
      (433 / 250 : ℝ) * (17 / 200 : ℝ) <
        √3 * Real.sin (Real.pi / 36) := by
    calc
      (433 / 250 : ℝ) * (17 / 200 : ℝ) <
          √3 * (17 / 200 : ℝ) :=
        mul_lt_mul_of_pos_right hSqrtThreeLower (by norm_num)
      _ < √3 * Real.sin (Real.pi / 36) :=
        mul_lt_mul_of_pos_left hSinSmallLower (Real.sqrt_pos.2 (by norm_num))
  have hProductUpper :
      √3 * Real.sin (Real.pi / 36) <
        (1733 / 1000 : ℝ) * (873 / 10000 : ℝ) := by
    calc
      √3 * Real.sin (Real.pi / 36) <
          √3 * (873 / 10000 : ℝ) :=
        mul_lt_mul_of_pos_left hSinSmallUpper (Real.sqrt_pos.2 (by norm_num))
      _ < (1733 / 1000 : ℝ) * (873 / 10000 : ℝ) :=
        mul_lt_mul_of_pos_right hSqrtThreeUpper (by norm_num)
  have hSinAngleExpansion :
      Real.sin (145 * Real.pi / 180) =
        (1 / 2 : ℝ) * Real.cos (Real.pi / 36) +
          √3 / 2 * Real.sin (Real.pi / 36) := by
    rw [show 145 * Real.pi / 180 =
        Real.pi - 7 * Real.pi / 36 by ring,
      Real.sin_pi_sub,
      show 7 * Real.pi / 36 =
        Real.pi / 6 + Real.pi / 36 by ring,
      Real.sin_add, Real.sin_pi_div_six, Real.cos_pi_div_six]
  have hSinAngleLower :
      (113 / 200 : ℝ) < Real.sin (145 * Real.pi / 180) := by
    rw [hSinAngleExpansion]
    nlinarith
  have hSinAngleUpper :
      Real.sin (145 * Real.pi / 180) < (23 / 40 : ℝ) := by
    rw [hSinAngleExpansion]
    nlinarith
  have hSinAnglePositive :
      0 < Real.sin (145 * Real.pi / 180) := by
    linarith
  rw [abs_of_pos hSinAnglePositive] at hTorque
  have hRound :
      RoundsToAtResolution
        (torqueMagnitudeInNewtonMeters setup.electricTorqueMagnitude)
        (57 / 10 ^ 25 : ℝ)
        (1 / 10 ^ 25 : ℝ) := by
    rw [hTorque]
    constructor
    · norm_num [RoundsToAtResolution]
    · rw [abs_lt]
      constructor <;> norm_num <;> nlinarith
  refine ⟨hRound, ?_⟩
  refine ⟨?_, ?_⟩
  · simpa [MatchesDisplayedTorqueChoice,
      AnswerChoice.interpretedUnitForTorqueQuestion,
      AnswerChoice.displayedUnit,
      DisplayedUnit.isTorqueCompatible,
      AnswerChoice.displayedMagnitudeSI,
      AnswerChoice.displayResolution] using hRound
  · intro other hOther
    fin_cases other
    · have hRoundA :
          RoundsToAtResolution
            (torqueMagnitudeInNewtonMeters setup.electricTorqueMagnitude)
            (2 / 10 ^ 29 : ℝ)
            (1 / 10 ^ 30 : ℝ) := by
        simpa [MatchesDisplayedTorqueChoice,
          AnswerChoice.interpretedUnitForTorqueQuestion,
          AnswerChoice.displayedUnit,
          DisplayedUnit.isTorqueCompatible,
          AnswerChoice.displayedMagnitudeSI,
          AnswerChoice.displayResolution] using hOther
      have hCloseA := hRoundA.2
      have hUpperA := (abs_lt.mp hCloseA).2
      rw [hTorque] at hUpperA
      norm_num at hUpperA
      exfalso
      nlinarith
    · rfl
    · have hRoundC :
          RoundsToAtResolution
            (torqueMagnitudeInNewtonMeters setup.electricTorqueMagnitude)
            (82 / 10 ^ 25 : ℝ)
            (1 / 10 ^ 25 : ℝ) := by
        simpa [MatchesDisplayedTorqueChoice,
          AnswerChoice.interpretedUnitForTorqueQuestion,
          AnswerChoice.displayedUnit,
          DisplayedUnit.isTorqueCompatible,
          AnswerChoice.displayedMagnitudeSI,
          AnswerChoice.displayResolution] using hOther
      have hCloseC := hRoundC.2
      have hLowerC := (abs_lt.mp hCloseC).1
      rw [hTorque] at hLowerC
      norm_num at hLowerC
      exfalso
      nlinarith
    · simpa [MatchesDisplayedTorqueChoice,
        AnswerChoice.interpretedUnitForTorqueQuestion,
        AnswerChoice.displayedUnit,
        DisplayedUnit.isTorqueCompatible] using hOther

end PhyXMiniProblems.ProblemPhyXMini0996
