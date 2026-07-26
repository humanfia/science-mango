import Mathlib
import Physlib.Electromagnetism.Basic
import Physlib.Units.WithDim.Basic

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0841

open Dimension

/-!
# Electric flux through a negatively charged cube

The primary figure gives the signed normal behavior of the electric field on
five faces of a cube.  A field arrow pointing out of the cube contributes a
positive outward-normal component, while an inward arrow contributes a
negative one.  The five displayed components are therefore

* top: `-15 N/C`,
* bottom: `+10 N/C`,
* left: `+10 N/C`,
* right: `-20 N/C`, and
* front: `+20 N/C`.

The back-face component is unknown.  Since the enclosed charge is negative,
Gauss's law makes the total outward flux negative.  Equal positive face areas
then force the unknown outward-normal component to be below `-5 N/C`, or,
equivalently, to have inward magnitude greater than `5 N/C`.

The ambient electric field uses Physlib's spacetime-dependent vector-field
type.  Length, area, charge, permittivity, electric-field components, and flux
are unit-independent `Dimensionful` quantities.  Real numbers below occur
only as coherent SI readouts.
-/

/-! ## Dimensionful quantities and SI readouts -/

/-- The dimension `M L T⁻² C⁻¹` of electric-field strength. -/
def electricFieldStrengthDimension : Dimension :=
  M𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹ * C𝓭⁻¹

/-- The dimension `L²` of a surface area. -/
def areaDimension : Dimension := L𝓭 * L𝓭

/-- The dimension `M L³ T⁻² C⁻¹` of electric flux. -/
def electricFluxDimension : Dimension :=
  M𝓭 * L𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹ * C𝓭⁻¹

/-- The dimension `C² T² M⁻¹ L⁻³` of electric permittivity. -/
def electricPermittivityDimension : Dimension :=
  C𝓭 * C𝓭 * T𝓭 * T𝓭 * M𝓭⁻¹ * L𝓭⁻¹ * L𝓭⁻¹ * L𝓭⁻¹

/-- A nonnegative unit-independent physical length. -/
abbrev LengthQuantity : Type := Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative unit-independent physical area. -/
abbrev AreaQuantity : Type := Dimensionful (WithDim areaDimension NNReal)

/-- A signed electric charge. -/
abbrev SignedChargeQuantity : Type := Dimensionful (WithDim C𝓭 ℝ)

/-- A nonnegative electric-field magnitude, as printed next to an arrow. -/
abbrev ElectricFieldMagnitudeQuantity : Type :=
  Dimensionful (WithDim electricFieldStrengthDimension NNReal)

/-- An oriented outward-normal electric-field component. -/
abbrev SignedElectricFieldComponentQuantity : Type :=
  Dimensionful (WithDim electricFieldStrengthDimension ℝ)

/-- Signed electric flux through a face or a closed surface. -/
abbrev ElectricFluxQuantity : Type :=
  Dimensionful (WithDim electricFluxDimension ℝ)

/-- A nonnegative electric permittivity. -/
abbrev ElectricPermittivityQuantity : Type :=
  Dimensionful (WithDim electricPermittivityDimension NNReal)

/-- SI readout of a length, in metres. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  ((length UnitChoices.SI).val : ℝ)

/-- SI readout of an area, in square metres. -/
def areaInSquareMeters (area : AreaQuantity) : ℝ :=
  ((area UnitChoices.SI).val : ℝ)

/-- SI readout of signed charge, in coulombs. -/
def chargeInCoulombs (charge : SignedChargeQuantity) : ℝ :=
  (charge UnitChoices.SI).val

/-- SI readout of a nonnegative field magnitude, in newtons per coulomb. -/
def fieldMagnitudeInNewtonsPerCoulomb
    (magnitude : ElectricFieldMagnitudeQuantity) : ℝ :=
  ((magnitude UnitChoices.SI).val : ℝ)

/-- SI readout of a signed normal field component, in newtons per coulomb. -/
def fieldComponentInNewtonsPerCoulomb
    (component : SignedElectricFieldComponentQuantity) : ℝ :=
  (component UnitChoices.SI).val

/-- SI readout of electric flux, in newton-square-metres per coulomb. -/
def electricFluxInNewtonSquareMetersPerCoulomb
    (flux : ElectricFluxQuantity) : ℝ :=
  (flux UnitChoices.SI).val

/-- SI readout of permittivity, in coulombs squared per newton-square-metre. -/
def permittivityInSI (permittivity : ElectricPermittivityQuantity) : ℝ :=
  ((permittivity UnitChoices.SI).val : ℝ)

/-! ## Cube geometry, arrow directions, and answer-choice data -/

/-- The six faces of the Gaussian cube. -/
inductive CubeFace where
  | top
  | bottom
  | left
  | right
  | front
  | back
  deriving DecidableEq, Fintype, Repr

/-- Orientation of a pictured arrow relative to a face's outward normal. -/
inductive NormalOrientation where
  | outward
  | inward
  deriving DecidableEq, Repr

/-- The sign contributed by an arrow to the outward-normal component. -/
def NormalOrientation.outwardSign : NormalOrientation → ℝ
  | .outward => 1
  | .inward => -1

/-- Answer labels recorded in the source problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- The signed `N/C` threshold printed for each answer choice. -/
def answerChoiceReadoutInNewtonsPerCoulomb : AnswerChoice → ℝ
  | .A => -4
  | .B => -15
  | .C => -5.6
  | .D => -5

/-!
Typed content of the supplied raster image.  Magnitude labels are physical
quantities; their numerical readings and arrow directions are imposed by the
separate `MatchesProblemAndFigureReadouts` predicate.
-/
structure CubeElectricFieldFigure where
  cubeShown : Bool
  fieldArrowShown : CubeFace → Bool
  arrowOrientation : CubeFace → Option NormalOrientation
  fieldMagnitudeLabel : CubeFace → Option ElectricFieldMagnitudeQuantity
  unitsCaptionIsNewtonsPerCoulomb : Bool

/-- One pictured face has an arrow of the stated orientation and SI magnitude. -/
def CubeElectricFieldFigure.HasLabeledArrow
    (figure : CubeElectricFieldFigure) (face : CubeFace)
    (orientation : NormalOrientation) (reading : ℝ) : Prop :=
  figure.fieldArrowShown face = true ∧
    figure.arrowOrientation face = some orientation ∧
    ∃ label,
      figure.fieldMagnitudeLabel face = some label ∧
        fieldMagnitudeInNewtonsPerCoulomb label = reading

/-! ## Physical setup -/

/-!
The cube, its ambient field, the derived normal components and fluxes, and the
primary figure.  No field component is defined from the desired `-5 N/C`
threshold.
-/
structure ChargedCubeSetup where
  electricField : Electromagnetism.ElectricField 3
  observationTime : Time
  faceRegion : CubeFace → Set (Space 3)
  outwardUnitNormal : CubeFace → EuclideanSpace ℝ (Fin 3)
  constantFieldVectorOnFace : CubeFace → EuclideanSpace ℝ (Fin 3)
  outwardNormalComponent : CubeFace → SignedElectricFieldComponentQuantity
  faceFlux : CubeFace → ElectricFluxQuantity
  totalOutwardFlux : ElectricFluxQuantity
  enclosedCharge : SignedChargeQuantity
  cubeEdgeLength : LengthQuantity
  faceArea : AreaQuantity
  vacuumPermittivity : ElectricPermittivityQuantity
  figure : CubeElectricFieldFigure

/-! ## Problem data and governing laws -/

/-- Source-text and primary-image evidence, excluding the unknown back field. -/
structure MatchesProblemAndFigureReadouts (setup : ChargedCubeSetup) : Prop where
  cubeIsShown : setup.figure.cubeShown = true
  unitsCaption : setup.figure.unitsCaptionIsNewtonsPerCoulomb = true
  topArrow : setup.figure.HasLabeledArrow .top .inward 15
  bottomArrow : setup.figure.HasLabeledArrow .bottom .outward 10
  leftArrow : setup.figure.HasLabeledArrow .left .outward 10
  rightArrow : setup.figure.HasLabeledArrow .right .inward 20
  frontArrow : setup.figure.HasLabeledArrow .front .outward 20
  backFieldIsTheUnlabeledUnknown :
    setup.figure.fieldArrowShown .back = false ∧
      setup.figure.arrowOrientation .back = none ∧
      setup.figure.fieldMagnitudeLabel .back = none

/-!
The physical field is constant on each face, and the signed dimensionful
component attached to a face is its projection onto the outward unit normal.
-/
structure HasConstantFaceElectricField (setup : ChargedCubeSetup) : Prop where
  everyFaceNonempty : ∀ face, (setup.faceRegion face).Nonempty
  outwardNormalsAreUnit : ∀ face, ‖setup.outwardUnitNormal face‖ = 1
  constantOnEachFace :
    ∀ face x, x ∈ setup.faceRegion face →
      setup.electricField setup.observationTime x =
        setup.constantFieldVectorOnFace face
  componentIsOutwardProjection :
    ∀ face,
      inner ℝ (setup.constantFieldVectorOnFace face)
          (setup.outwardUnitNormal face) =
        fieldComponentInNewtonsPerCoulomb
          (setup.outwardNormalComponent face)

/-!
The image's unsigned magnitude and arrow orientation determine a known face's
signed outward-normal component.  This applies uniformly to any labeled face
and contains no condition on the unlabeled back face.
-/
structure FigureRepresentsSurfaceComponents (setup : ChargedCubeSetup) : Prop where
  labeledArrowGivesSignedComponent :
    ∀ face orientation label,
      setup.figure.arrowOrientation face = some orientation →
      setup.figure.fieldMagnitudeLabel face = some label →
      fieldComponentInNewtonsPerCoulomb
          (setup.outwardNormalComponent face) =
        orientation.outwardSign *
          fieldMagnitudeInNewtonsPerCoulomb label

/-- Positivity and charge-sign facts for the physical cube. -/
structure HasPhysicalCubeParameters (setup : ChargedCubeSetup) : Prop where
  edgeLengthPositive : 0 < lengthInMeters setup.cubeEdgeLength
  faceAreaPositive : 0 < areaInSquareMeters setup.faceArea
  vacuumPermittivityPositive : 0 < permittivityInSI setup.vacuumPermittivity
  enclosedChargeNegative : chargeInCoulombs setup.enclosedCharge < 0

/-!
Equal-area cube geometry, constant-field face flux, flux additivity, and the
integral form of Gauss's law.  The last equation is the local abstraction
needed because Physlib's available Gauss-law theorem is pointwise and
differential rather than a closed-surface integral theorem.
-/
structure SatisfiesCubeSurfaceFluxLaws (setup : ChargedCubeSetup) : Prop where
  faceAreaFromEdgeLength :
    areaInSquareMeters setup.faceArea =
      lengthInMeters setup.cubeEdgeLength ^ 2
  constantFaceFlux :
    ∀ face,
      electricFluxInNewtonSquareMetersPerCoulomb (setup.faceFlux face) =
        areaInSquareMeters setup.faceArea *
          fieldComponentInNewtonsPerCoulomb
            (setup.outwardNormalComponent face)
  totalFluxIsSumOverFaces :
    electricFluxInNewtonSquareMetersPerCoulomb setup.totalOutwardFlux =
      ∑ face : CubeFace,
        electricFluxInNewtonSquareMetersPerCoulomb (setup.faceFlux face)
  integralGaussLaw :
    electricFluxInNewtonSquareMetersPerCoulomb setup.totalOutwardFlux =
      chargeInCoulombs setup.enclosedCharge /
        permittivityInSI setup.vacuumPermittivity

/-! ## Consequences to be proved in the later physics-proof stage -/

/-- The five displayed signed components have outward-normal sum `5 N/C`. -/
lemma displayedFaceComponentsSumToFive
    (setup : ChargedCubeSetup)
    (_data : MatchesProblemAndFigureReadouts setup)
    (_representation : FigureRepresentsSurfaceComponents setup) :
    fieldComponentInNewtonsPerCoulomb
          (setup.outwardNormalComponent .top) +
        fieldComponentInNewtonsPerCoulomb
          (setup.outwardNormalComponent .bottom) +
        fieldComponentInNewtonsPerCoulomb
          (setup.outwardNormalComponent .left) +
        fieldComponentInNewtonsPerCoulomb
          (setup.outwardNormalComponent .right) +
      fieldComponentInNewtonsPerCoulomb
          (setup.outwardNormalComponent .front) = 5 := by
  rcases _data.topArrow with
    ⟨_, htopOrientation, topLabel, htopLabel, htopMagnitude⟩
  rcases _data.bottomArrow with
    ⟨_, hbottomOrientation, bottomLabel, hbottomLabel, hbottomMagnitude⟩
  rcases _data.leftArrow with
    ⟨_, hleftOrientation, leftLabel, hleftLabel, hleftMagnitude⟩
  rcases _data.rightArrow with
    ⟨_, hrightOrientation, rightLabel, hrightLabel, hrightMagnitude⟩
  rcases _data.frontArrow with
    ⟨_, hfrontOrientation, frontLabel, hfrontLabel, hfrontMagnitude⟩
  have htop := _representation.labeledArrowGivesSignedComponent
    .top .inward topLabel htopOrientation htopLabel
  have hbottom := _representation.labeledArrowGivesSignedComponent
    .bottom .outward bottomLabel hbottomOrientation hbottomLabel
  have hleft := _representation.labeledArrowGivesSignedComponent
    .left .outward leftLabel hleftOrientation hleftLabel
  have hright := _representation.labeledArrowGivesSignedComponent
    .right .inward rightLabel hrightOrientation hrightLabel
  have hfront := _representation.labeledArrowGivesSignedComponent
    .front .outward frontLabel hfrontOrientation hfrontLabel
  simp [NormalOrientation.outwardSign, htopMagnitude] at htop
  simp [NormalOrientation.outwardSign, hbottomMagnitude] at hbottom
  simp [NormalOrientation.outwardSign, hleftMagnitude] at hleft
  simp [NormalOrientation.outwardSign, hrightMagnitude] at hright
  simp [NormalOrientation.outwardSign, hfrontMagnitude] at hfront
  linarith

/-- Negative enclosed charge and positive permittivity make the total flux negative. -/
lemma totalOutwardFluxIsNegative
    (setup : ChargedCubeSetup)
    (_physical : HasPhysicalCubeParameters setup)
    (_fluxLaws : SatisfiesCubeSurfaceFluxLaws setup) :
    electricFluxInNewtonSquareMetersPerCoulomb setup.totalOutwardFlux < 0 := by
  rw [_fluxLaws.integralGaussLaw]
  exact div_neg_of_neg_of_pos _physical.enclosedChargeNegative
    _physical.vacuumPermittivityPositive

/--
Blueprint target `thm:physics:phyx_mini_0841:target`.

The unknown back-face outward-normal component must be strictly below
`-5 N/C`.  In the equivalent unsigned language, the inward field strength
must exceed `5 N/C`, which is recorded as answer choice D's signed threshold.
-/
theorem unknownBackFaceFieldMustBeBelowNegativeFive
    (setup : ChargedCubeSetup)
    (_data : MatchesProblemAndFigureReadouts setup)
    (_constantField : HasConstantFaceElectricField setup)
    (_representation : FigureRepresentsSurfaceComponents setup)
    (_physical : HasPhysicalCubeParameters setup)
    (_fluxLaws : SatisfiesCubeSurfaceFluxLaws setup) :
    fieldComponentInNewtonsPerCoulomb
        (setup.outwardNormalComponent .back) < -5 := by
  have hknown :=
    displayedFaceComponentsSumToFive setup _data _representation
  have htotalNegative :=
    totalOutwardFluxIsNegative setup _physical _fluxLaws
  rw [_fluxLaws.totalFluxIsSumOverFaces] at htotalNegative
  have huniv : (Finset.univ : Finset CubeFace) =
      {.top, .bottom, .left, .right, .front, .back} := by
    decide
  rw [huniv] at htotalNegative
  simp [_fluxLaws.constantFaceFlux] at htotalNegative
  nlinarith [_physical.faceAreaPositive]

end PhyXMiniProblems.ProblemPhyXMini0841
