import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Matrix.Mul
import Physlib.Electromagnetism.Basic
import Physlib.SpaceAndTime.Space.LengthUnit
import Physlib.Units.WithDim.Basic

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0874

open Dimension

/-!
# Potential difference in a uniform electric field

The supplied image shows three rows of two parallel electric-field arrows
pointing right, with field strength `1000 V/m`. Point `B` is `7 cm` to the
right and `3 cm` below point `A`. The recorded negative answer fixes the
requested orientation as `V_B - V_A`.

Physical quantities below are unit-independent PhysLean dimensionful values.
Real scalars and vectors occur only at named unit-readout boundaries or as
literal values transcribed from the image and answer choices.
-/

/-! ## Dimensionful physical quantities and unit readouts -/

/-- Two-dimensional coordinate vectors at a coherent-SI readout boundary. -/
abbrev SpatialReadout : Type := EuclideanSpace ℝ (Fin 2)

/-- The physical dimension `M L² T⁻² C⁻¹` of electric potential. -/
def electricPotentialDimension : Dimension :=
  M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹ * C𝓭⁻¹

/-- The physical dimension `M L T⁻² C⁻¹` of electric-field strength. -/
def electricFieldDimension : Dimension :=
  M𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹ * C𝓭⁻¹

/-- A nonnegative physical length. -/
abbrev LengthQuantity : Type :=
  Dimensionful (WithDim L𝓭 NNReal)

/-- A signed two-dimensional physical position. -/
abbrev PositionQuantity : Type :=
  Dimensionful (WithDim L𝓭 SpatialReadout)

/-- A signed two-dimensional physical electric-field vector. -/
abbrev ElectricFieldVectorQuantity : Type :=
  Dimensionful (WithDim electricFieldDimension SpatialReadout)

/-- A signed physical electric potential. -/
abbrev ElectricPotentialQuantity : Type :=
  Dimensionful (WithDim electricPotentialDimension ℝ)

/-- A signed, oriented physical electric-potential difference. -/
abbrev PotentialDifferenceQuantity : Type :=
  Dimensionful (WithDim electricPotentialDimension ℝ)

/-- Read a physical length in a selected PhysLean length unit. -/
def lengthReadout (unit : LengthUnit) (length : LengthQuantity) : ℝ :=
  ((length {UnitChoices.SI with length := unit}).val : ℝ)

/-- Read a physical length in coherent-SI metres. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.meters length

/-- Read a physical length in centimetres. -/
def lengthInCentimeters (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.centimeters length

/-- Read a physical position in coherent-SI metres. -/
def positionInMeters (position : PositionQuantity) : SpatialReadout :=
  (position UnitChoices.SI).val

/-- Read an electric-field vector in coherent-SI volts per metre. -/
def electricFieldInVoltsPerMeter
    (field : ElectricFieldVectorQuantity) : SpatialReadout :=
  (field UnitChoices.SI).val

/-- Read an electric potential in coherent-SI volts. -/
def electricPotentialInVolts
    (potential : ElectricPotentialQuantity) : ℝ :=
  (potential UnitChoices.SI).val

/-- Read a signed, oriented electric-potential difference in volts. -/
def potentialDifferenceInVolts
    (difference : PotentialDifferenceQuantity) : ℝ :=
  (difference UnitChoices.SI).val

/-- The centimetre-to-metre conversion used by the displayed geometry. -/
lemma lengthInCentimeters_eq_oneHundred_mul_lengthInMeters
    (length : LengthQuantity) :
    lengthInCentimeters length = 100 * lengthInMeters length := by
  have h := length.property UnitChoices.SI
    {UnitChoices.SI with length := LengthUnit.centimeters}
  unfold lengthInCentimeters lengthInMeters lengthReadout
  rw [h]
  norm_num [UnitChoices.dimScale, LengthUnit.centimeters, LengthUnit.scale,
    LengthUnit.meters, NNReal.smul_def, LengthUnit.div_eq_val]
  rfl

/-! ## Primary-image vocabulary and physical setup -/

/-- The two labelled observation points in the supplied image. -/
inductive DiagramPoint where
  | A
  | B
  deriving DecidableEq, Fintype, Repr

/-- The six distinct magenta field-arrow glyphs visible in the image. -/
inductive FieldArrowLabel where
  | upperLeft
  | upperRight
  | middleLeft
  | middleRight
  | lowerLeft
  | lowerRight
  deriving DecidableEq, Fintype, Repr

/-- Qualitative arrow directions in the diagram plane. -/
inductive DiagramDirection where
  | right
  | left
  | other
  deriving DecidableEq, Repr

/-- Unit glyphs available for the printed electric-field label. -/
inductive PrintedElectricFieldUnit where
  | voltsPerMeter
  | other
  deriving DecidableEq, Repr

/-- Unit glyphs available for the printed distance labels. -/
inductive PrintedLengthUnit where
  | centimeters
  | other
  deriving DecidableEq, Repr

/-!
Literal presentation data transcribed from `874.png`. Its scalar fields are
unit-labelled raster readouts, not replacements for physical quantities.
-/
structure UniformElectricFieldFigure where
  pointDotShown : DiagramPoint → Bool
  pointLabelShown : DiagramPoint → Bool
  fieldArrowShown : FieldArrowLabel → Bool
  fieldArrowDirection : FieldArrowLabel → DiagramDirection
  printedFieldStrength : ℝ
  printedFieldUnit : PrintedElectricFieldUnit
  horizontalDimensionArrowShown : Bool
  horizontalDimensionRunsFromAToB : Bool
  printedHorizontalSeparation : ℝ
  horizontalSeparationUnit : PrintedLengthUnit
  verticalDimensionArrowShown : Bool
  verticalDimensionRunsFromARowToBRow : Bool
  printedVerticalSeparation : ℝ
  verticalSeparationUnit : PrintedLengthUnit

/-!
Independent physical quantities for the uniform-field configuration.
`potentialDifference start finish` is oriented as `V(finish) - V(start)`.
-/
structure UniformElectricFieldSetup where
  horizontalSeparation : LengthQuantity
  verticalSeparation : LengthQuantity
  rightDirection : SpatialReadout
  upDirection : SpatialReadout
  position : DiagramPoint → PositionQuantity
  uniformFieldVector : ElectricFieldVectorQuantity
  electricField : Electromagnetism.ElectricField 2
  electricPotentialAt : DiagramPoint → ElectricPotentialQuantity
  potentialDifference :
    DiagramPoint → DiagramPoint → PotentialDifferenceQuantity
  figure : UniformElectricFieldFigure

/-! ## Figure readouts, geometry, and governing laws -/

/-!
Primary-image evidence and its calibration to independent physical quantities.
These assumptions contain the printed `1000`, `7`, and `3`, but do not contain
the requested potential difference.
-/
structure MatchesSuppliedUniformFieldFigure
    (setup : UniformElectricFieldSetup) : Prop where
  everyPointDotShown : ∀ point, setup.figure.pointDotShown point = true
  everyPointLabelShown : ∀ point, setup.figure.pointLabelShown point = true
  everyFieldArrowShown : ∀ arrow, setup.figure.fieldArrowShown arrow = true
  everyFieldArrowPointsRight : ∀ arrow,
    setup.figure.fieldArrowDirection arrow = .right
  printedFieldStrengthIsOneThousand :
    setup.figure.printedFieldStrength = 1000
  printedFieldUnitIsVoltsPerMeter :
    setup.figure.printedFieldUnit = .voltsPerMeter
  horizontalDimensionArrowIsShown :
    setup.figure.horizontalDimensionArrowShown = true
  horizontalDimensionConnectsPointColumns :
    setup.figure.horizontalDimensionRunsFromAToB = true
  printedHorizontalDistanceIsSeven :
    setup.figure.printedHorizontalSeparation = 7
  horizontalDistanceUnitIsCentimeters :
    setup.figure.horizontalSeparationUnit = .centimeters
  verticalDimensionArrowIsShown :
    setup.figure.verticalDimensionArrowShown = true
  verticalDimensionConnectsPointRows :
    setup.figure.verticalDimensionRunsFromARowToBRow = true
  printedVerticalDistanceIsThree :
    setup.figure.printedVerticalSeparation = 3
  verticalDistanceUnitIsCentimeters :
    setup.figure.verticalSeparationUnit = .centimeters
  horizontalLabelCalibratesPhysicalDistance :
    lengthInCentimeters setup.horizontalSeparation =
      setup.figure.printedHorizontalSeparation
  verticalLabelCalibratesPhysicalDistance :
    lengthInCentimeters setup.verticalSeparation =
      setup.figure.printedVerticalSeparation
  fieldLabelCalibratesPhysicalVector :
    electricFieldInVoltsPerMeter setup.uniformFieldVector =
      setup.figure.printedFieldStrength • setup.rightDirection

/-!
The diagram directions form an orthonormal frame, and `B` is the displayed
horizontal distance right and vertical distance below `A`. This is geometry
from the image rather than a potential conclusion.
-/
structure HasDisplayedPointGeometry
    (setup : UniformElectricFieldSetup) : Prop where
  rightDirectionIsUnit :
    dotProduct setup.rightDirection setup.rightDirection = 1
  upDirectionIsUnit :
    dotProduct setup.upDirection setup.upDirection = 1
  rightAndUpAreOrthogonal :
    dotProduct setup.rightDirection setup.upDirection = 0
  displacementFromAToB :
    positionInMeters (setup.position .B) -
        positionInMeters (setup.position .A) =
      lengthInMeters setup.horizontalSeparation • setup.rightDirection -
        lengthInMeters setup.verticalSeparation • setup.upDirection

/-- Positivity conditions for the nondegenerate distances and field label. -/
structure HasPhysicalUniformFieldData
    (setup : UniformElectricFieldSetup) : Prop where
  horizontalSeparationPositive :
    0 < lengthInMeters setup.horizontalSeparation
  verticalSeparationPositive :
    0 < lengthInMeters setup.verticalSeparation
  fieldStrengthPositive : 0 < setup.figure.printedFieldStrength

/-!
The PhysLean spacetime field is static and uniform, and agrees everywhere with
the coherent-SI readout of the independent dimensionful field vector.
-/
structure IsStaticUniformElectricField
    (setup : UniformElectricFieldSetup) : Prop where
  fieldIsConstant : ∀ time position,
    setup.electricField time position =
      electricFieldInVoltsPerMeter setup.uniformFieldVector

/-!
General electrostatic potential laws for every ordered pair of labelled
points. The first law fixes the orientation of potential difference. The
second is the constant-field relation
`V(finish) - V(start) = -E · (r(finish) - r(start))`.
-/
structure SatisfiesUniformFieldPotentialLaw
    (setup : UniformElectricFieldSetup) : Prop where
  differenceIsEndpointPotentialChange : ∀ startPoint endPoint,
    potentialDifferenceInVolts
        (setup.potentialDifference startPoint endPoint) =
      electricPotentialInVolts (setup.electricPotentialAt endPoint) -
        electricPotentialInVolts (setup.electricPotentialAt startPoint)
  endpointPotentialChangeFromField : ∀ startPoint endPoint,
    electricPotentialInVolts (setup.electricPotentialAt endPoint) -
        electricPotentialInVolts (setup.electricPotentialAt startPoint) =
      -dotProduct
        (electricFieldInVoltsPerMeter setup.uniformFieldVector)
        (positionInMeters (setup.position endPoint) -
          positionInMeters (setup.position startPoint))

/-! ## Displayed answer choices and requested conclusion -/

/-- The four answer labels supplied with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- The signed potential difference printed for each answer choice, in volts. -/
def AnswerChoice.displayedPotentialDifferenceInVolts :
    AnswerChoice → ℝ
  | .A => 12
  | .B => -14
  | .C => -200
  | .D => -70

/-- The answer label recorded in the source dataset. -/
def recordedDatasetAnswer : AnswerChoice := .D

/-!
Moving `7 cm` right along a rightward `1000 V/m` field changes potential by
`-(1000)(0.07) = -70 V`. The `3 cm` downward displacement is perpendicular to
the field and contributes zero.

This is the declaration for blueprint label
`thm:physics:phyx_mini_0874:target`. Neither `-70` nor answer choice `D` occurs
in a theorem hypothesis or a governing-law premise.
-/
theorem problem_phyx_mini_0874
    (setup : UniformElectricFieldSetup)
    (hFigure : MatchesSuppliedUniformFieldFigure setup)
    (hGeometry : HasDisplayedPointGeometry setup)
    (hPhysical : HasPhysicalUniformFieldData setup)
    (hUniform : IsStaticUniformElectricField setup)
    (hPotentialLaw : SatisfiesUniformFieldPotentialLaw setup) :
    potentialDifferenceInVolts (setup.potentialDifference .A .B) = -70 := by
  have hHorizontalMeters :
      lengthInMeters setup.horizontalSeparation = 7 / 100 := by
    have h :=
      lengthInCentimeters_eq_oneHundred_mul_lengthInMeters
        setup.horizontalSeparation
    rw [hFigure.horizontalLabelCalibratesPhysicalDistance,
      hFigure.printedHorizontalDistanceIsSeven] at h
    linarith
  have hVerticalMeters :
      lengthInMeters setup.verticalSeparation = 3 / 100 := by
    have h :=
      lengthInCentimeters_eq_oneHundred_mul_lengthInMeters
        setup.verticalSeparation
    rw [hFigure.verticalLabelCalibratesPhysicalDistance,
      hFigure.printedVerticalDistanceIsThree] at h
    linarith
  have hDisplacement :=
    congrArg (fun x : SpatialReadout => x.ofLp)
      hGeometry.displacementFromAToB
  simp only [WithLp.ofLp_sub, WithLp.ofLp_smul] at hDisplacement
  rw [hPotentialLaw.differenceIsEndpointPotentialChange,
    hPotentialLaw.endpointPotentialChangeFromField,
    hFigure.fieldLabelCalibratesPhysicalVector,
    hFigure.printedFieldStrengthIsOneThousand,
    hDisplacement, hHorizontalMeters, hVerticalMeters]
  norm_num [hGeometry.rightDirectionIsUnit,
    hGeometry.rightAndUpAreOrthogonal]

end PhyXMiniProblems.ProblemPhyXMini0874
