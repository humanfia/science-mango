import Mathlib
import Physlib.Electromagnetism.Basic
import Physlib.Units.WithDim.Basic

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0842

open Dimension
open scoped BigOperators

/-!
# Electric flux through a cube enclosing negative charge

The primary image gives five constant, face-normal electric-field strengths:
`15 N/C` inward through the top, `15 N/C` outward through the bottom,
`10 N/C` outward through the left face, `15 N/C` outward through the right
face, and `20 N/C` inward through the front face.  The back-face field is the
unshown field asked about in the problem.

The field strengths, side length, face areas, enclosed charge, and total
electric flux are unit-independent Physlib quantities.  Real numbers below
are named coherent-SI readouts.  Physlib's spacetime-dependent
`Electromagnetism.ElectricField` retains the vector-field role of the field.

Assumption/target split:

* governing laws: constancy and normality of the field on every face, and
  integral Gauss's law for the closed cubical surface;
* previous-part results: none;
* figure/data readouts: the five shown arrow directions and strengths, the
  omitted back-face arrow, the `N/C` caption, cubical equal-area geometry, and
  negative enclosed charge;
* current target: the omitted field points inward, has strength strictly
  greater than `5 N/C`, and answer D is the unique displayed critical
  threshold.

In particular, neither the omitted direction nor its strength occurs in a
figure-data or governing-law hypothesis.
-/

/-! ## Dimensionful physical quantities and coherent-SI readouts -/

/-- The physical dimension `M L T⁻² C⁻¹` of electric-field strength. -/
def electricFieldStrengthDimension : Dimension :=
  M𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹ * C𝓭⁻¹

/-- The physical dimension `L²` of area. -/
def areaDimension : Dimension := L𝓭 * L𝓭

/-- The physical dimension of electric flux, electric field times area. -/
def electricFluxDimension : Dimension :=
  electricFieldStrengthDimension * areaDimension

/-- A positive-or-zero, unit-independent physical length. -/
abbrev LengthQuantity : Type :=
  Dimensionful (WithDim L𝓭 NNReal)

/-- A positive-or-zero, unit-independent physical area. -/
abbrev AreaQuantity : Type :=
  Dimensionful (WithDim areaDimension NNReal)

/-- A signed, unit-independent enclosed electric charge. -/
abbrev ChargeQuantity : Type :=
  Dimensionful (WithDim C𝓭 ℝ)

/-- A positive-or-zero, unit-independent electric-field strength. -/
abbrev ElectricFieldStrengthQuantity : Type :=
  Dimensionful (WithDim electricFieldStrengthDimension NNReal)

/-- A signed, unit-independent outward electric flux. -/
abbrev ElectricFluxQuantity : Type :=
  Dimensionful (WithDim electricFluxDimension ℝ)

/-- Read a physical length in coherent-SI metres. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  ((length UnitChoices.SI).val : ℝ)

/-- Read a physical area in coherent-SI square metres. -/
def areaInSquareMeters (area : AreaQuantity) : ℝ :=
  ((area UnitChoices.SI).val : ℝ)

/-- Read a signed physical charge in coherent-SI coulombs. -/
def chargeInCoulombs (charge : ChargeQuantity) : ℝ :=
  (charge UnitChoices.SI).val

/-- Read an electric-field strength in coherent-SI newtons per coulomb. -/
def fieldStrengthInNewtonsPerCoulomb
    (strength : ElectricFieldStrengthQuantity) : ℝ :=
  ((strength UnitChoices.SI).val : ℝ)

/-- Read electric flux in coherent-SI newton-square-metres per coulomb. -/
def electricFluxInNewtonSquareMetersPerCoulomb
    (flux : ElectricFluxQuantity) : ℝ :=
  (flux UnitChoices.SI).val

/-- Physlib's vacuum-permittivity parameter, interpreted in coherent SI. -/
def vacuumPermittivityInCoulombSquaredPerNewtonSquareMeter
    (system : Electromagnetism.EMSystem) : ℝ :=
  system.ε₀

/-! ## Cube faces, directions, and primary-figure content -/

/-- The six geometrical faces of the cube. -/
inductive CubeFace where
  | top
  | bottom
  | left
  | right
  | front
  | back
  deriving DecidableEq, Fintype, Repr

/-- The face opposite a given face of the cube. -/
def CubeFace.opposite : CubeFace → CubeFace
  | .top => .bottom
  | .bottom => .top
  | .left => .right
  | .right => .left
  | .front => .back
  | .back => .front

/-- Whether a face-normal field points with or against the outward normal. -/
inductive FaceNormalDirection where
  | outward
  | inward
  deriving DecidableEq, Fintype, Repr

/-- Sign of the outward normal component associated with a direction. -/
def FaceNormalDirection.outwardSign : FaceNormalDirection → ℝ
  | .outward => 1
  | .inward => -1

/-!
Literal visual content of image `842.png`.  A missing label is represented by
`none`, rather than by assigning the requested back-face strength in advance.
-/
structure CubeFieldFigure where
  cubeShown : Bool
  dashedHiddenEdgesShown : Bool
  fieldArrowShown : CubeFace → Bool
  arrowDirection : CubeFace → Option FaceNormalDirection
  strengthLabel : CubeFace → Option ElectricFieldStrengthQuantity
  newtonsPerCoulombCaptionShown : Bool

/-!
The physical cubical Gaussian-surface setup.  The face strengths and
directions are independent observables; in particular the back-face entries
are not defined from the answer choices.
-/
structure CubeGaussSetup where
  electromagneticSystem : Electromagnetism.EMSystem
  electricField : Electromagnetism.ElectricField 3
  observationTime : Time
  sideLength : LengthQuantity
  faceRegion : CubeFace → Set (Space 3)
  outwardUnitNormal : CubeFace → EuclideanSpace ℝ (Fin 3)
  faceArea : CubeFace → AreaQuantity
  faceFieldStrength : CubeFace → ElectricFieldStrengthQuantity
  faceDirection : CubeFace → FaceNormalDirection
  enclosedCharge : ChargeQuantity
  totalOutwardElectricFlux : ElectricFluxQuantity
  figure : CubeFieldFigure

/-- Signed outward-normal field component on a face, read in `N/C`. -/
def signedOutwardFieldInNewtonsPerCoulomb
    (setup : CubeGaussSetup) (face : CubeFace) : ℝ :=
  (setup.faceDirection face).outwardSign *
    fieldStrengthInNewtonsPerCoulomb (setup.faceFieldStrength face)

/-- The Physlib electric field has one vector value everywhere on a face. -/
def ElectricFieldIsConstantOnFace
    (setup : CubeGaussSetup) (face : CubeFace) : Prop :=
  ∃ faceValue : EuclideanSpace ℝ (Fin 3),
    ∀ position, position ∈ setup.faceRegion face →
      setup.electricField setup.observationTime position = faceValue

/-! ## Problem data, geometry, and governing laws -/

/-- The scenario states that the charge enclosed by the cube is negative. -/
structure MatchesProblemStatement (setup : CubeGaussSetup) : Prop where
  enclosedChargeIsNegative : chargeInCoulombs setup.enclosedCharge < 0

/-!
The five visible arrows and numerical labels transcribed from the primary
image.  The sixth, back-face arrow is explicitly absent.  No back-face
direction or strength is constrained here.
-/
structure MatchesPrimaryFigure (setup : CubeGaussSetup) : Prop where
  cubeIsShown : setup.figure.cubeShown = true
  dashedHiddenEdgesAreShown : setup.figure.dashedHiddenEdgesShown = true
  unitCaptionIsShown : setup.figure.newtonsPerCoulombCaptionShown = true
  shownFaceArrows :
    setup.figure.fieldArrowShown .top = true ∧
      setup.figure.fieldArrowShown .bottom = true ∧
      setup.figure.fieldArrowShown .left = true ∧
      setup.figure.fieldArrowShown .right = true ∧
      setup.figure.fieldArrowShown .front = true
  backFaceArrowIsOmitted : setup.figure.fieldArrowShown .back = false
  shownArrowDirections :
    setup.figure.arrowDirection .top = some .inward ∧
      setup.figure.arrowDirection .bottom = some .outward ∧
      setup.figure.arrowDirection .left = some .outward ∧
      setup.figure.arrowDirection .right = some .outward ∧
      setup.figure.arrowDirection .front = some .inward
  backArrowDirectionIsOmitted : setup.figure.arrowDirection .back = none
  shownDirectionsDescribePhysicalField :
    setup.faceDirection .top = .inward ∧
      setup.faceDirection .bottom = .outward ∧
      setup.faceDirection .left = .outward ∧
      setup.faceDirection .right = .outward ∧
      setup.faceDirection .front = .inward
  topLabelIsPhysicalStrength :
    setup.figure.strengthLabel .top = some (setup.faceFieldStrength .top)
  bottomLabelIsPhysicalStrength :
    setup.figure.strengthLabel .bottom = some (setup.faceFieldStrength .bottom)
  leftLabelIsPhysicalStrength :
    setup.figure.strengthLabel .left = some (setup.faceFieldStrength .left)
  rightLabelIsPhysicalStrength :
    setup.figure.strengthLabel .right = some (setup.faceFieldStrength .right)
  frontLabelIsPhysicalStrength :
    setup.figure.strengthLabel .front = some (setup.faceFieldStrength .front)
  backStrengthLabelIsOmitted : setup.figure.strengthLabel .back = none
  topStrengthReadout :
    fieldStrengthInNewtonsPerCoulomb (setup.faceFieldStrength .top) = 15
  bottomStrengthReadout :
    fieldStrengthInNewtonsPerCoulomb (setup.faceFieldStrength .bottom) = 15
  leftStrengthReadout :
    fieldStrengthInNewtonsPerCoulomb (setup.faceFieldStrength .left) = 10
  rightStrengthReadout :
    fieldStrengthInNewtonsPerCoulomb (setup.faceFieldStrength .right) = 15
  frontStrengthReadout :
    fieldStrengthInNewtonsPerCoulomb (setup.faceFieldStrength .front) = 20

/-- Positive, equal-area geometry and opposite outward normals of a cube. -/
structure HasCubeGeometry (setup : CubeGaussSetup) : Prop where
  sideLengthPositive : 0 < lengthInMeters setup.sideLength
  everyFaceRegionNonempty : ∀ face, (setup.faceRegion face).Nonempty
  everyFaceAreaPositive : ∀ face, 0 < areaInSquareMeters (setup.faceArea face)
  everyFaceHasSideSquaredArea : ∀ face,
    areaInSquareMeters (setup.faceArea face) =
      lengthInMeters setup.sideLength ^ 2
  outwardNormalsAreUnit : ∀ face, ‖setup.outwardUnitNormal face‖ = 1
  oppositeFacesHaveOppositeNormals : ∀ face,
    setup.outwardUnitNormal face.opposite = -setup.outwardUnitNormal face

/-! The vacuum-permittivity branch needed to infer the sign of total flux. -/
structure HasPhysicalVacuumParameters (setup : CubeGaussSetup) : Prop where
  vacuumPermittivityPositive :
    0 < vacuumPermittivityInCoulombSquaredPerNewtonSquareMeter
      setup.electromagneticSystem

/-!
The problem's face-uniformity assumption and the calibration of each scalar
readout against the Physlib vector field.  Each field is normal to its face:
its signed dot product with the outward unit normal is its signed strength.
-/
structure SatisfiesConstantFaceFieldModel (setup : CubeGaussSetup) : Prop where
  constantOnEveryFace : ∀ face, ElectricFieldIsConstantOnFace setup face
  strengthIsVectorNorm : ∀ face position,
    position ∈ setup.faceRegion face →
      ‖setup.electricField setup.observationTime position‖ =
        fieldStrengthInNewtonsPerCoulomb (setup.faceFieldStrength face)
  signedNormalComponent : ∀ face position,
    position ∈ setup.faceRegion face →
      inner ℝ (setup.electricField setup.observationTime position)
          (setup.outwardUnitNormal face) =
        signedOutwardFieldInNewtonsPerCoulomb setup face

/-!
Integral Gauss's law for the cubical closed surface.  The first equality is
the finite face-flux sum valid for constant normal fields; the second is
`Φ_E = Q_enclosed / ε₀`.  Neither equality states the requested back-face
threshold.
-/
structure SatisfiesIntegralGaussLaw (setup : CubeGaussSetup) : Prop where
  totalFluxIsSumOverFaces :
    electricFluxInNewtonSquareMetersPerCoulomb
        setup.totalOutwardElectricFlux =
      ∑ face : CubeFace,
        areaInSquareMeters (setup.faceArea face) *
          signedOutwardFieldInNewtonsPerCoulomb setup face
  fluxEqualsEnclosedChargeOverPermittivity :
    electricFluxInNewtonSquareMetersPerCoulomb
        setup.totalOutwardElectricFlux =
      chargeInCoulombs setup.enclosedCharge /
        vacuumPermittivityInCoulombSquaredPerNewtonSquareMeter
          setup.electromagneticSystem

/-! ## Known-face balance, answers, and formalization target -/

/-- The five faces carrying explicit arrows and strengths in the image. -/
def shownFaces : Finset CubeFace :=
  Finset.univ.erase .back

/-- Net outward field readout contributed by the five shown faces. -/
def shownFacesNetOutwardFieldInNewtonsPerCoulomb
    (setup : CubeGaussSetup) : ℝ :=
  ∑ face ∈ shownFaces,
    signedOutwardFieldInNewtonsPerCoulomb setup face

/-- The shown arrows have net outward field readout `5 N/C`. -/
lemma shownFaces_netOutwardField_eq_five
    (setup : CubeGaussSetup)
    (hFigure : MatchesPrimaryFigure setup) :
    shownFacesNetOutwardFieldInNewtonsPerCoulomb setup = 5 := by
  unfold shownFacesNetOutwardFieldInNewtonsPerCoulomb
  rw [show shownFaces =
      ({.top, .bottom, .left, .right, .front} : Finset CubeFace) by decide]
  simp [Finset.sum_insert, signedOutwardFieldInNewtonsPerCoulomb,
    hFigure.shownDirectionsDescribePhysicalField.1,
    hFigure.shownDirectionsDescribePhysicalField.2.1,
    hFigure.shownDirectionsDescribePhysicalField.2.2.1,
    hFigure.shownDirectionsDescribePhysicalField.2.2.2.1,
    hFigure.shownDirectionsDescribePhysicalField.2.2.2.2,
    hFigure.topStrengthReadout, hFigure.bottomStrengthReadout,
    hFigure.leftStrengthReadout, hFigure.rightStrengthReadout,
    hFigure.frontStrengthReadout]
  norm_num [FaceNormalDirection.outwardSign]

/-- The four answer labels printed in the problem source. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Threshold strength printed beside an answer choice, in `N/C`. -/
def answerStrengthInNewtonsPerCoulomb : AnswerChoice → ℝ
  | .A => 4
  | .B => 15
  | .C => 5.6
  | .D => 5

/-- The answer label recorded in the supplied dataset metadata. -/
def recordedDatasetAnswer : AnswerChoice := .D

/-!
A choice represents the critical threshold precisely when its displayed value
equals the independent net outward contribution of the five shown faces.
-/
def IsCriticalThresholdChoice
    (setup : CubeGaussSetup) (choice : AnswerChoice) : Prop :=
  shownFacesNetOutwardFieldInNewtonsPerCoulomb setup =
    answerStrengthInNewtonsPerCoulomb choice

/-!
Because the enclosed charge is negative, Gauss's law makes the total outward
flux negative.  The five shown faces contribute `+5 N/C`, so the unshown
back-face field must point inward with strength strictly greater than
`5 N/C`.  Choice D is uniquely the displayed critical threshold.

This is the declaration corresponding to blueprint label
`thm:physics:phyx_mini_0842:target`.
-/
theorem unshownBackFaceField_must_exceed_five_newtonsPerCoulomb
    (setup : CubeGaussSetup)
    (hProblem : MatchesProblemStatement setup)
    (hFigure : MatchesPrimaryFigure setup)
    (hGeometry : HasCubeGeometry setup)
    (hVacuum : HasPhysicalVacuumParameters setup)
    (hFaceField : SatisfiesConstantFaceFieldModel setup)
    (hGauss : SatisfiesIntegralGaussLaw setup) :
    setup.faceDirection .back = .inward ∧
      IsCriticalThresholdChoice setup .D ∧
      5 < fieldStrengthInNewtonsPerCoulomb
        (setup.faceFieldStrength .back) ∧
      (∀ choice : AnswerChoice,
        IsCriticalThresholdChoice setup choice ↔ choice = .D) := by
  have hFluxNegative :
      electricFluxInNewtonSquareMetersPerCoulomb
          setup.totalOutwardElectricFlux < 0 := by
    rw [hGauss.fluxEqualsEnclosedChargeOverPermittivity]
    exact div_neg_of_neg_of_pos hProblem.enclosedChargeIsNegative
      hVacuum.vacuumPermittivityPositive
  have hWeightedSumNegative :
      (∑ face : CubeFace,
          areaInSquareMeters (setup.faceArea face) *
            signedOutwardFieldInNewtonsPerCoulomb setup face) < 0 := by
    rw [← hGauss.totalFluxIsSumOverFaces]
    exact hFluxNegative
  have hCommonAreaPositive :
      0 < lengthInMeters setup.sideLength ^ 2 :=
    sq_pos_of_pos hGeometry.sideLengthPositive
  have hFactoredSumNegative :
      lengthInMeters setup.sideLength ^ 2 *
          (∑ face : CubeFace,
            signedOutwardFieldInNewtonsPerCoulomb setup face) < 0 := by
    rw [Finset.mul_sum]
    simpa only [hGeometry.everyFaceHasSideSquaredArea] using
      hWeightedSumNegative
  have hSignedFieldSumNegative :
      (∑ face : CubeFace,
        signedOutwardFieldInNewtonsPerCoulomb setup face) < 0 := by
    rcases (mul_neg_iff.mp hFactoredSumNegative) with hPositive | hNegative
    · exact hPositive.2
    · exact (not_lt_of_ge (le_of_lt hCommonAreaPositive) hNegative.1).elim
  have hFaceSumDecomposition :
      shownFacesNetOutwardFieldInNewtonsPerCoulomb setup +
          signedOutwardFieldInNewtonsPerCoulomb setup .back =
        ∑ face : CubeFace,
          signedOutwardFieldInNewtonsPerCoulomb setup face := by
    simpa only [shownFacesNetOutwardFieldInNewtonsPerCoulomb, shownFaces] using
      (Finset.sum_erase_add Finset.univ
        (fun face : CubeFace =>
          signedOutwardFieldInNewtonsPerCoulomb setup face)
        (Finset.mem_univ .back))
  have hShownFieldSum :
      shownFacesNetOutwardFieldInNewtonsPerCoulomb setup = 5 :=
    shownFaces_netOutwardField_eq_five setup hFigure
  have hBackSignedField :
      signedOutwardFieldInNewtonsPerCoulomb setup .back < -5 := by
    linarith
  have hBackStrengthNonnegative :
      0 ≤ fieldStrengthInNewtonsPerCoulomb
        (setup.faceFieldStrength .back) := by
    unfold fieldStrengthInNewtonsPerCoulomb
    positivity
  have hBackDirection : setup.faceDirection .back = .inward := by
    cases hDirection : setup.faceDirection .back with
    | outward =>
        simp [signedOutwardFieldInNewtonsPerCoulomb, hDirection,
          FaceNormalDirection.outwardSign] at hBackSignedField
        linarith
    | inward => rfl
  have hBackStrength :
      5 < fieldStrengthInNewtonsPerCoulomb
        (setup.faceFieldStrength .back) := by
    simp [signedOutwardFieldInNewtonsPerCoulomb, hBackDirection,
      FaceNormalDirection.outwardSign] at hBackSignedField
    linarith
  refine ⟨hBackDirection, ?_, hBackStrength, ?_⟩
  · simpa [IsCriticalThresholdChoice, answerStrengthInNewtonsPerCoulomb]
      using hShownFieldSum
  · intro choice
    cases choice <;>
      norm_num [IsCriticalThresholdChoice, answerStrengthInNewtonsPerCoulomb,
        hShownFieldSum] <;>
      decide

end PhyXMiniProblems.ProblemPhyXMini0842
