import Mathlib
import Physlib.Electromagnetism.Basic
import Physlib.Units.WithDim.Basic

/- USER: The assigned source file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0840

open Dimension

/-!
# Electric flux through a cube containing negative charge

The primary raster shows five face-normal electric-field arrows on a cube.
The `15 N/C` top arrow and the `20 N/C` right arrow point inward; the
`10 N/C` left arrow, `10 N/C` bottom arrow, and oblique `20 N/C` back-face
arrow point outward.  No arrow or strength is supplied for the front face.
This differs from the auxiliary caption, which incorrectly describes six
outward arrows.

The electric field is constant over each face, all six cube faces have the
same positive area, and the enclosed charge is negative.  Gauss's law then
requires the missing front-face field to point inward with strength strictly
greater than `5 N/C`, the threshold displayed by answer D.

Physical quantities are unit-independent Physlib `Dimensionful` values.
Real numbers occur only as coherent-SI readouts, signed normal components,
or displayed answer values.  The full electric field retains Physlib's
spacetime-dependent vector-field type.

Assumption/target split:

* governing laws: facewise constancy, calibration of the field's normal
  components, equal-area cube geometry, additivity of face fluxes, and
  Gauss's law `epsilon0 * flux = enclosedCharge`;
* previous-part results: none;
* figure/data readouts: the five shown magnitudes and their inward/outward
  directions, the absent front-face arrow, the `N/C` caption, and negative
  enclosed charge;
* current target conclusions: the known faces have signed sum `5 N/C`, and
  the missing front-face field points inward and exceeds `5 N/C` (answer D).
-/

/-! ## Dimensionful electrostatic quantities and SI readouts -/

/-- The dimension `M L T^-2 C^-1` of electric-field strength. -/
def electricFieldStrengthDimension : Dimension :=
  M𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹ * C𝓭⁻¹

/-- The dimension `M L^3 T^-2 C^-1` of electric flux `E * area`. -/
def electricFluxDimension : Dimension :=
  electricFieldStrengthDimension * L𝓭 * L𝓭

/-- The dimension `C^2 T^2 M^-1 L^-3` of electric permittivity. -/
def electricPermittivityDimension : Dimension :=
  C𝓭 * C𝓭 * T𝓭 * T𝓭 * M𝓭⁻¹ * L𝓭⁻¹ * L𝓭⁻¹ * L𝓭⁻¹

/-- A nonnegative, unit-independent physical length. -/
abbrev LengthQuantity : Type :=
  Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative, unit-independent physical area. -/
abbrev AreaQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * L𝓭) NNReal)

/-- A signed, unit-independent enclosed electric charge. -/
abbrev SignedChargeQuantity : Type :=
  Dimensionful (WithDim C𝓭 ℝ)

/-- A nonnegative electric-field magnitude. -/
abbrev ElectricFieldStrengthQuantity : Type :=
  Dimensionful (WithDim electricFieldStrengthDimension NNReal)

/-- A signed outward electric flux. -/
abbrev SignedElectricFluxQuantity : Type :=
  Dimensionful (WithDim electricFluxDimension ℝ)

/-- A nonnegative electric permittivity, used for `epsilon0`. -/
abbrev ElectricPermittivityQuantity : Type :=
  Dimensionful (WithDim electricPermittivityDimension NNReal)

/-- SI readout of a physical length, in metres. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  ((length UnitChoices.SI).val : ℝ)

/-- SI readout of a physical area, in square metres. -/
def areaInSquareMeters (area : AreaQuantity) : ℝ :=
  ((area UnitChoices.SI).val : ℝ)

/-- SI readout of signed electric charge, in coulombs. -/
def chargeInCoulombs (charge : SignedChargeQuantity) : ℝ :=
  (charge UnitChoices.SI).val

/-- SI readout of electric-field strength, in newtons per coulomb. -/
def fieldStrengthInNewtonsPerCoulomb
    (strength : ElectricFieldStrengthQuantity) : ℝ :=
  ((strength UnitChoices.SI).val : ℝ)

/-- SI readout of signed electric flux, in newton-square-metres per coulomb. -/
def electricFluxInNewtonSquareMetersPerCoulomb
    (flux : SignedElectricFluxQuantity) : ℝ :=
  (flux UnitChoices.SI).val

/-- SI readout of electric permittivity. -/
def electricPermittivityInSI
    (permittivity : ElectricPermittivityQuantity) : ℝ :=
  ((permittivity UnitChoices.SI).val : ℝ)

/-! ## Cube faces, arrow directions, and primary-figure content -/

/-- The six geometrically distinct faces of the Gaussian cube. -/
inductive CubeFace where
  | top
  | bottom
  | left
  | right
  | front
  | back
  deriving DecidableEq, Fintype, Repr

/-- Orientation of a field arrow relative to a face's outward unit normal. -/
inductive FaceNormalOrientation where
  | outward
  | inward
  deriving DecidableEq, Repr

/-- Sign of a face-normal component in the outward-positive convention. -/
def orientationSign : FaceNormalOrientation → ℝ
  | .outward => 1
  | .inward => -1

/-!
Typed content of the supplied raster.  The strength-label field is physical,
not a scalar placeholder.  Its front entry is intentionally unconstrained
because `arrowShown front = false`.
-/
structure CubeElectricFieldFigure where
  showsCube : Bool
  arrowShown : CubeFace → Bool
  arrowOrientation : CubeFace → FaceNormalOrientation
  strengthLabel : CubeFace → ElectricFieldStrengthQuantity
  showsFieldStrengthCaption : Bool
  captionUnitsAreNewtonsPerCoulomb : Bool

/-!
The independent physical setup.  In particular, neither the front-face
strength nor its orientation is defined from `5`, answer D, or the other
face values.
-/
structure ChargedCubeSetup where
  sideLength : LengthQuantity
  faceArea : CubeFace → AreaQuantity
  enclosedCharge : SignedChargeQuantity
  vacuumPermittivity : ElectricPermittivityQuantity
  totalOutwardFlux : SignedElectricFluxQuantity
  electricField : Electromagnetism.ElectricField 3
  faceRegion : CubeFace → Set (Space 3)
  representativePoint : CubeFace → Space 3
  outwardUnitNormal : CubeFace → EuclideanSpace ℝ (Fin 3)
  faceFieldStrength : CubeFace → ElectricFieldStrengthQuantity
  faceOrientation : CubeFace → FaceNormalOrientation
  figure : CubeElectricFieldFigure

/-- Signed outward normal component of a face field, in `N/C`. -/
def signedNormalFieldInNewtonsPerCoulomb
    (setup : ChargedCubeSetup) (face : CubeFace) : ℝ :=
  orientationSign (setup.faceOrientation face) *
    fieldStrengthInNewtonsPerCoulomb (setup.faceFieldStrength face)

/-!
The algebraic sum of the five components printed in the raster.  The missing
front face is deliberately excluded and no numerical answer occurs here.
-/
def knownFaceNormalComponentSumInNewtonsPerCoulomb
    (setup : ChargedCubeSetup) : ℝ :=
  signedNormalFieldInNewtonsPerCoulomb setup .top +
    signedNormalFieldInNewtonsPerCoulomb setup .bottom +
    signedNormalFieldInNewtonsPerCoulomb setup .left +
    signedNormalFieldInNewtonsPerCoulomb setup .right +
    signedNormalFieldInNewtonsPerCoulomb setup .back

/-! ## Problem data, figure evidence, geometry, and governing laws -/

/-- The prose assertion that the cube encloses a strictly negative charge. -/
structure MatchesNegativeChargeScenario (setup : ChargedCubeSetup) : Prop where
  enclosedChargeIsNegative : chargeInCoulombs setup.enclosedCharge < 0

/-!
Primary-image evidence.  There are five arrows, not the six asserted by the
auxiliary caption.  Every displayed label is tied to the corresponding
independent physical face strength before its numerical readout is stated.
-/
structure MatchesPrimaryCubeFigure (setup : ChargedCubeSetup) : Prop where
  cubeShown : setup.figure.showsCube = true
  fieldStrengthCaptionShown : setup.figure.showsFieldStrengthCaption = true
  captionUsesNewtonsPerCoulomb :
    setup.figure.captionUnitsAreNewtonsPerCoulomb = true
  topArrowShown : setup.figure.arrowShown .top = true
  bottomArrowShown : setup.figure.arrowShown .bottom = true
  leftArrowShown : setup.figure.arrowShown .left = true
  rightArrowShown : setup.figure.arrowShown .right = true
  backArrowShown : setup.figure.arrowShown .back = true
  frontArrowAbsent : setup.figure.arrowShown .front = false
  topLabelIsPhysicalStrength :
    setup.figure.strengthLabel .top = setup.faceFieldStrength .top
  bottomLabelIsPhysicalStrength :
    setup.figure.strengthLabel .bottom = setup.faceFieldStrength .bottom
  leftLabelIsPhysicalStrength :
    setup.figure.strengthLabel .left = setup.faceFieldStrength .left
  rightLabelIsPhysicalStrength :
    setup.figure.strengthLabel .right = setup.faceFieldStrength .right
  backLabelIsPhysicalStrength :
    setup.figure.strengthLabel .back = setup.faceFieldStrength .back
  topArrowPointsInward :
    setup.figure.arrowOrientation .top = .inward
  bottomArrowPointsOutward :
    setup.figure.arrowOrientation .bottom = .outward
  leftArrowPointsOutward :
    setup.figure.arrowOrientation .left = .outward
  rightArrowPointsInward :
    setup.figure.arrowOrientation .right = .inward
  backArrowPointsOutward :
    setup.figure.arrowOrientation .back = .outward
  topPhysicalOrientation : setup.faceOrientation .top = .inward
  bottomPhysicalOrientation : setup.faceOrientation .bottom = .outward
  leftPhysicalOrientation : setup.faceOrientation .left = .outward
  rightPhysicalOrientation : setup.faceOrientation .right = .inward
  backPhysicalOrientation : setup.faceOrientation .back = .outward
  topStrength :
    fieldStrengthInNewtonsPerCoulomb (setup.faceFieldStrength .top) = 15
  bottomStrength :
    fieldStrengthInNewtonsPerCoulomb (setup.faceFieldStrength .bottom) = 10
  leftStrength :
    fieldStrengthInNewtonsPerCoulomb (setup.faceFieldStrength .left) = 10
  rightStrength :
    fieldStrengthInNewtonsPerCoulomb (setup.faceFieldStrength .right) = 20
  backStrength :
    fieldStrengthInNewtonsPerCoulomb (setup.faceFieldStrength .back) = 20

/-!
Cube geometry needed by the flux argument: every face has the square of the
same positive side length, representative points lie on their faces, and the
chosen face normals are outward unit normals in opposite pairs.
-/
structure SatisfiesCubeGeometry (setup : ChargedCubeSetup) : Prop where
  sideLengthPositive : 0 < lengthInMeters setup.sideLength
  equalSquareFaceAreas : ∀ face,
    areaInSquareMeters (setup.faceArea face) =
      lengthInMeters setup.sideLength ^ 2
  representativePointOnFace : ∀ face,
    setup.representativePoint face ∈ setup.faceRegion face
  outwardNormalsAreUnit : ∀ face, ‖setup.outwardUnitNormal face‖ = 1
  topBottomNormalsOppose :
    setup.outwardUnitNormal .top = -setup.outwardUnitNormal .bottom
  leftRightNormalsOppose :
    setup.outwardUnitNormal .left = -setup.outwardUnitNormal .right
  frontBackNormalsOppose :
    setup.outwardUnitNormal .front = -setup.outwardUnitNormal .back

/-- The stated electric field is constant at every time over each cube face. -/
structure ElectricFieldIsConstantOnEachFace
    (setup : ChargedCubeSetup) : Prop where
  facewiseConstant : ∀ face time point₁ point₂,
    point₁ ∈ setup.faceRegion face →
      point₂ ∈ setup.faceRegion face →
      setup.electricField time point₁ = setup.electricField time point₂

/-!
The dimensionful scalar face data calibrate the outward normal components of
the Physlib vector field in SI units.  This is a measurement relation, not a
claim about the unknown numerical threshold.
-/
structure FaceStrengthsCalibrateElectricField
    (setup : ChargedCubeSetup) : Prop where
  normalComponent : ∀ face time point,
    point ∈ setup.faceRegion face →
      inner ℝ (setup.electricField time point) (setup.outwardUnitNormal face) =
        signedNormalFieldInNewtonsPerCoulomb setup face

/-!
Finite-face electric flux and Gauss's law.  The first field is surface-flux
additivity for constant normal components; the second is the integral law
`epsilon0 * Phi_E = Q_enclosed`.  Neither field states the requested bound.
-/
structure SatisfiesGaussLawForCube (setup : ChargedCubeSetup) : Prop where
  fluxIsSumOverFaces :
    electricFluxInNewtonSquareMetersPerCoulomb setup.totalOutwardFlux =
      ∑ face : CubeFace,
        signedNormalFieldInNewtonsPerCoulomb setup face *
          areaInSquareMeters (setup.faceArea face)
  gaussLaw :
    electricPermittivityInSI setup.vacuumPermittivity *
        electricFluxInNewtonSquareMetersPerCoulomb setup.totalOutwardFlux =
      chargeInCoulombs setup.enclosedCharge

/-- Positivity conditions for the physical areas and vacuum permittivity. -/
structure HasPhysicalCubeParameters (setup : ChargedCubeSetup) : Prop where
  everyFaceAreaPositive : ∀ face, 0 < areaInSquareMeters (setup.faceArea face)
  vacuumPermittivityPositive :
    0 < electricPermittivityInSI setup.vacuumPermittivity

/-! ## Displayed choices and formalized conclusions -/

/-- Labels of the four threshold choices printed in the source. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Threshold in `N/C` printed beside each answer choice. -/
def answerThresholdInNewtonsPerCoulomb : AnswerChoice → ℝ
  | .A => 4
  | .B => 15
  | .C => 28 / 5
  | .D => 5

/-- The answer label recorded in the dataset. -/
def recordedDatasetAnswer : AnswerChoice := .D

/-!
The five shown normal components have outward-positive sum
`-15 + 10 + 10 - 20 + 20 = 5 N/C`.
-/
lemma knownFaceNormalComponentSum_eq_five
    (setup : ChargedCubeSetup)
    (hFigure : MatchesPrimaryCubeFigure setup) :
    knownFaceNormalComponentSumInNewtonsPerCoulomb setup = 5 := by
  norm_num [knownFaceNormalComponentSumInNewtonsPerCoulomb,
    signedNormalFieldInNewtonsPerCoulomb, orientationSign,
    hFigure.topPhysicalOrientation, hFigure.bottomPhysicalOrientation,
    hFigure.leftPhysicalOrientation, hFigure.rightPhysicalOrientation,
    hFigure.backPhysicalOrientation, hFigure.topStrength,
    hFigure.bottomStrength, hFigure.leftStrength, hFigure.rightStrength,
    hFigure.backStrength]

/-!
Negative enclosed charge makes the total outward flux negative.  Since the
five displayed faces contribute `+5` times the common face area, the missing
front-face component must be inward and have magnitude greater than `5 N/C`.
-/
lemma frontFaceField_pointsInward_and_exceeds_five
    (setup : ChargedCubeSetup)
    (hCharge : MatchesNegativeChargeScenario setup)
    (hFigure : MatchesPrimaryCubeFigure setup)
    (hGeometry : SatisfiesCubeGeometry setup)
    (hPhysical : HasPhysicalCubeParameters setup)
    (hGauss : SatisfiesGaussLawForCube setup) :
    setup.faceOrientation .front = .inward ∧
      5 < fieldStrengthInNewtonsPerCoulomb
        (setup.faceFieldStrength .front) := by
  have hFluxNeg :
      electricFluxInNewtonSquareMetersPerCoulomb setup.totalOutwardFlux < 0 := by
    nlinarith [hGauss.gaussLaw, hPhysical.vacuumPermittivityPositive,
      hCharge.enclosedChargeIsNegative]
  have hSumNeg := hFluxNeg
  rw [hGauss.fluxIsSumOverFaces] at hSumNeg
  simp_rw [hGeometry.equalSquareFaceAreas] at hSumNeg
  have hFaces : (Finset.univ : Finset CubeFace) =
      {.top, .bottom, .left, .right, .front, .back} := by
    decide
  rw [hFaces] at hSumNeg
  simp only [Finset.mem_insert, reduceCtorEq, Finset.mem_singleton, or_self,
    not_false_eq_true, Finset.sum_insert, Finset.sum_singleton] at hSumNeg
  have hSideSq : 0 < lengthInMeters setup.sideLength ^ 2 :=
    sq_pos_of_pos hGeometry.sideLengthPositive
  have hFrontStrengthNonneg :
      0 ≤ fieldStrengthInNewtonsPerCoulomb
        (setup.faceFieldStrength .front) := by
    unfold fieldStrengthInNewtonsPerCoulomb
    exact NNReal.coe_nonneg _
  cases hFront : setup.faceOrientation .front with
  | outward =>
      exfalso
      norm_num [signedNormalFieldInNewtonsPerCoulomb, orientationSign,
        hFigure.topPhysicalOrientation, hFigure.bottomPhysicalOrientation,
        hFigure.leftPhysicalOrientation, hFigure.rightPhysicalOrientation,
        hFigure.backPhysicalOrientation, hFigure.topStrength,
        hFigure.bottomStrength, hFigure.leftStrength, hFigure.rightStrength,
        hFigure.backStrength, hFront] at hSumNeg
      have hProductNonneg : 0 ≤
          fieldStrengthInNewtonsPerCoulomb
              (setup.faceFieldStrength .front) *
            lengthInMeters setup.sideLength ^ 2 :=
        mul_nonneg hFrontStrengthNonneg hSideSq.le
      nlinarith
  | inward =>
      refine ⟨rfl, ?_⟩
      norm_num [signedNormalFieldInNewtonsPerCoulomb, orientationSign,
        hFigure.topPhysicalOrientation, hFigure.bottomPhysicalOrientation,
        hFigure.leftPhysicalOrientation, hFigure.rightPhysicalOrientation,
        hFigure.backPhysicalOrientation, hFigure.topStrength,
        hFigure.bottomStrength, hFigure.leftStrength, hFigure.rightStrength,
        hFigure.backStrength, hFront] at hSumNeg
      by_contra hNot
      have hStrengthLe :
          fieldStrengthInNewtonsPerCoulomb
              (setup.faceFieldStrength .front) ≤ 5 :=
        le_of_not_gt hNot
      have hProductNonneg : 0 ≤
          (5 - fieldStrengthInNewtonsPerCoulomb
              (setup.faceFieldStrength .front)) *
            lengthInMeters setup.sideLength ^ 2 :=
        mul_nonneg (sub_nonneg.mpr hStrengthLe) hSideSq.le
      nlinarith

/-!
For a cube enclosing negative charge, the five pictured face fields leave a
positive outward component of `5 N/C`.  Gauss's law therefore forces the
unpictured front-face field inward with strength exceeding the `5 N/C`
threshold printed as answer D.

This declaration formalizes `thm:physics:phyx_mini_0840:target`.  Neither the
front-face orientation, the strict lower bound, nor answer D's matching
inequality occurs in any premise.
-/
theorem problem_phyx_mini_0840
    (setup : ChargedCubeSetup)
    (hCharge : MatchesNegativeChargeScenario setup)
    (hFigure : MatchesPrimaryCubeFigure setup)
    (hGeometry : SatisfiesCubeGeometry setup)
    (hConstant : ElectricFieldIsConstantOnEachFace setup)
    (hCalibration : FaceStrengthsCalibrateElectricField setup)
    (hPhysical : HasPhysicalCubeParameters setup)
    (hGauss : SatisfiesGaussLawForCube setup) :
    setup.faceOrientation .front = .inward ∧
      answerThresholdInNewtonsPerCoulomb recordedDatasetAnswer <
        fieldStrengthInNewtonsPerCoulomb
          (setup.faceFieldStrength .front) := by
  simpa [answerThresholdInNewtonsPerCoulomb, recordedDatasetAnswer] using
    frontFaceField_pointsInward_and_exceeds_five setup hCharge hFigure hGeometry
      hPhysical hGauss

end PhyXMiniProblems.ProblemPhyXMini0840
