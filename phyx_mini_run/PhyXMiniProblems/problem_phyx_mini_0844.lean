import Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic
import Physlib.Electromagnetism.Basic
import Physlib.SpaceAndTime.Space.LengthUnit
import Physlib.Units.WithDim.Area

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0844

open Dimension

/-!
# Electric flux through an inclined square surface

The primary raster shows a `15 cm × 15 cm` planar surface in a uniform
electric field of magnitude `180 N/C`.  The field makes an acute `30°` angle
with the plane and crosses the surface opposite to the displayed outward unit
normal.  Thus the angle from the field to the outward normal is `120°`.

Lengths, area, electric-field strength, and signed electric flux are modeled
as unit-independent Physlib quantities.  Real numbers occur only as explicit
unit readouts, dimensionless direction vectors and angles, and displayed
multiple-choice values.
-/

/-! ## Dimensionful quantities and unit readouts -/

/-- Electric-field strength has dimension `M L T⁻² C⁻¹`. -/
def electricFieldStrengthDimension : Dimension :=
  M𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹ * C𝓭⁻¹

/-- Electric flux has dimension `M L³ T⁻² C⁻¹`, equivalently `N m²/C`. -/
def electricFluxDimension : Dimension :=
  M𝓭 * L𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹ * C𝓭⁻¹

/-- A nonnegative, unit-independent physical length. -/
abbrev LengthQuantity : Type :=
  Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative, unit-independent physical area. -/
abbrev AreaQuantity : Type := DimArea

/-- A nonnegative, unit-independent electric-field magnitude. -/
abbrev ElectricFieldStrengthQuantity : Type :=
  Dimensionful (WithDim electricFieldStrengthDimension NNReal)

/-- A signed, unit-independent electric flux. -/
abbrev ElectricFluxQuantity : Type :=
  Dimensionful (WithDim electricFluxDimension ℝ)

/-- Three-dimensional Euclidean directions used by the surface diagram. -/
abbrev Direction3 : Type := EuclideanSpace ℝ (Fin 3)

/-- Read a physical length in a selected named length unit. -/
def lengthReadout (unit : LengthUnit) (length : LengthQuantity) : ℝ :=
  ((length {UnitChoices.SI with length := unit}).val : ℝ)

/-- Read a physical area in the square of a selected named length unit. -/
def areaReadout (unit : LengthUnit) (area : AreaQuantity) : ℝ :=
  ((area {UnitChoices.SI with length := unit}).val : ℝ)

/-- Metre readout of a physical length. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.meters length

/-- Centimetre readout used by both side labels in the raster. -/
def lengthInCentimeters (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.centimeters length

/-- Square-metre readout of a physical area. -/
def areaInSquareMeters (area : AreaQuantity) : ℝ :=
  areaReadout LengthUnit.meters area

/-- Coherent-SI readout of electric-field strength, in newtons/coulomb. -/
def electricFieldStrengthInNewtonsPerCoulomb
    (strength : ElectricFieldStrengthQuantity) : ℝ :=
  ((strength UnitChoices.SI).val : ℝ)

/-- Coherent-SI readout of signed electric flux, in newton-square-metres/coulomb. -/
def electricFluxInNewtonSquareMetersPerCoulomb
    (flux : ElectricFluxQuantity) : ℝ :=
  (flux UnitChoices.SI).val

/-- Convert a dimensionless degree readout to radians. -/
def degreesToRadians (degrees : ℝ) : ℝ :=
  degrees * Real.pi / 180

/-! ## Physical setup and primary-figure content -/

/-- Shape categories relevant to the pictured surface. -/
inductive SurfaceShape where
  | rectangle
  | other
  deriving DecidableEq, Repr

/-- Which way the electric-field arrows cross relative to the displayed normal. -/
inductive SurfaceCrossingSense where
  | withOutwardNormal
  | againstOutwardNormal
  deriving DecidableEq, Repr

/-- The two vector symbols printed in the figure. -/
inductive FigureVectorLabel where
  | electricFieldVector
  | outwardUnitNormal
  deriving DecidableEq, Repr

/-- Named visual features in `phyx_data/test_image/844.png`. -/
inductive FigureFeature where
  | rectangularSurface
  | repeatedMagentaFieldArrows
  | electricFieldVectorLabel
  | blackNormalArrow
  | outwardUnitNormalLabel
  | squareDimensionLabel
  | thirtyDegreeArc
  | fieldStrengthLabel
  deriving DecidableEq, Fintype, Repr

/-!
Typed data transcribed from the supplied raster.  Dimension labels and the
field-strength label are physical quantities; their scalar readings are stated
separately in `MatchesProblemAndPrimaryFigure`.
-/
structure ElectricFluxFigure where
  shows : FigureFeature → Bool
  surfaceShape : SurfaceShape
  widthLabel : LengthQuantity
  heightLabel : LengthQuantity
  fieldStrengthLabel : ElectricFieldStrengthQuantity
  fieldAngleFromSurfaceLabelDegrees : ℝ
  fieldArrowLabel : FigureVectorLabel
  normalArrowLabel : FigureVectorLabel
  fieldCrossingSense : SurfaceCrossingSense

/-!
Independent physical quantities for the experiment.  The requested flux is
not defined from the field strength, geometry, or an answer choice; it is
related to them only by the governing flux law below.
-/
structure ElectricFluxSetup where
  surfaceWidth : LengthQuantity
  surfaceHeight : LengthQuantity
  surfaceArea : AreaQuantity
  electricFieldStrength : ElectricFieldStrengthQuantity
  electricFlux : ElectricFluxQuantity
  electricField : Electromagnetism.ElectricField 3
  observationTime : Time
  surfacePoints : Set (Space 3)
  referencePoint : Space 3
  fieldDirection : Direction3
  outwardUnitNormal : Direction3
  surfaceReferenceDirection : Direction3
  fieldAngleFromSurfaceRadians : ℝ
  figure : ElectricFluxFigure

/-! ## Assumptions: source readouts, geometry, and governing laws -/

/-!
Problem-statement and primary-raster evidence.  The raster itself, rather than
the auxiliary prose, fixes the `30°` as the acute angle between the field
arrow and the plane.  No electric-flux value or answer choice occurs here.
-/
structure MatchesProblemAndPrimaryFigure
    (setup : ElectricFluxSetup) : Prop where
  everyNamedFeatureShown :
    ∀ feature, setup.figure.shows feature = true
  surfaceIsRectangular : setup.figure.surfaceShape = .rectangle
  widthLabelIsSurfaceWidth :
    setup.figure.widthLabel = setup.surfaceWidth
  heightLabelIsSurfaceHeight :
    setup.figure.heightLabel = setup.surfaceHeight
  strengthLabelIsFieldStrength :
    setup.figure.fieldStrengthLabel = setup.electricFieldStrength
  fieldArrowIsElectricFieldVector :
    setup.figure.fieldArrowLabel = .electricFieldVector
  normalArrowIsOutwardUnitNormal :
    setup.figure.normalArrowLabel = .outwardUnitNormal
  fieldCrossesAgainstNormal :
    setup.figure.fieldCrossingSense = .againstOutwardNormal
  widthCentimeters :
    lengthInCentimeters setup.surfaceWidth = 15
  heightCentimeters :
    lengthInCentimeters setup.surfaceHeight = 15
  widthMeters :
    lengthInMeters setup.surfaceWidth = 15 / 100
  heightMeters :
    lengthInMeters setup.surfaceHeight = 15 / 100
  fieldStrengthNewtonsPerCoulomb :
    electricFieldStrengthInNewtonsPerCoulomb
        setup.electricFieldStrength = 180
  printedAngleDegrees :
    setup.figure.fieldAngleFromSurfaceLabelDegrees = 30
  fieldAngleAgreesWithPrintedAngle :
    setup.fieldAngleFromSurfaceRadians =
      degreesToRadians setup.figure.fieldAngleFromSurfaceLabelDegrees

/-- Positivity, non-vacuity, and unit-direction conditions for the setup. -/
structure HasPhysicalConfiguration (setup : ElectricFluxSetup) : Prop where
  widthPositive : 0 < lengthInMeters setup.surfaceWidth
  heightPositive : 0 < lengthInMeters setup.surfaceHeight
  areaPositive : 0 < areaInSquareMeters setup.surfaceArea
  fieldStrengthPositive :
    0 < electricFieldStrengthInNewtonsPerCoulomb
      setup.electricFieldStrength
  surfaceNonempty : setup.surfacePoints.Nonempty
  referencePointOnSurface : setup.referencePoint ∈ setup.surfacePoints
  fieldDirectionIsUnit : ‖setup.fieldDirection‖ = 1
  outwardNormalIsUnit : ‖setup.outwardUnitNormal‖ = 1
  surfaceReferenceDirectionIsUnit :
    ‖setup.surfaceReferenceDirection‖ = 1

/-!
The area of a rectangle is the product of its side lengths.  Stating the law
for every selected length unit keeps the dimensionful area tied to the two
dimensionful side lengths without baking in the requested flux.
-/
structure SatisfiesRectangularSurfaceAreaLaw
    (setup : ElectricFluxSetup) : Prop where
  areaIsWidthTimesHeight :
    ∀ unit : LengthUnit,
      areaReadout unit setup.surfaceArea =
        lengthReadout unit setup.surfaceWidth *
          lengthReadout unit setup.surfaceHeight

/-!
Uniform-field idealization.  Physlib's spacetime-dependent electric field is
calibrated in coherent SI units on the surface by the independent physical
field-strength quantity and a unit direction.  This law does not mention
electric flux.
-/
structure SatisfiesUniformElectricFieldModel
    (setup : ElectricFluxSetup) : Prop where
  fieldIsUniformOnSurface :
    ∀ position, position ∈ setup.surfacePoints →
      setup.electricField setup.observationTime position =
        electricFieldStrengthInNewtonsPerCoulomb
            setup.electricFieldStrength • setup.fieldDirection

/-!
Geometry inferred directly from the primary raster.  The reference direction
lies in the surface and is perpendicular to the outward normal.  The electric
field is `30°` from that in-surface direction and, because it crosses against
the normal, is `90° + 30° = 120°` from the outward normal.
-/
structure SatisfiesPrimaryFigureGeometry
    (setup : ElectricFluxSetup) : Prop where
  surfaceDirectionOrthogonalToNormal :
    inner ℝ setup.surfaceReferenceDirection setup.outwardUnitNormal = 0
  fieldAngleFromSurface :
    InnerProductGeometry.angle
        setup.fieldDirection setup.surfaceReferenceDirection =
      setup.fieldAngleFromSurfaceRadians
  fieldAngleFromOutwardNormal :
    InnerProductGeometry.angle setup.fieldDirection setup.outwardUnitNormal =
      Real.pi / 2 + setup.fieldAngleFromSurfaceRadians
  fieldHasNegativeOutwardComponent :
    inner ℝ setup.fieldDirection setup.outwardUnitNormal < 0

/-!
For a uniform electric field over a planar surface, signed electric flux is
`A (E · n̂)`.  The field model above ensures that the value at the selected
reference point is the common value everywhere on the surface.  This is the
general governing law and contains no numerical flux conclusion.
-/
structure SatisfiesUniformPlanarElectricFluxLaw
    (setup : ElectricFluxSetup) : Prop where
  fluxIsAreaTimesNormalFieldComponent :
    electricFluxInNewtonSquareMetersPerCoulomb setup.electricFlux =
      areaInSquareMeters setup.surfaceArea *
        inner ℝ
          (setup.electricField setup.observationTime setup.referencePoint)
          setup.outwardUnitNormal

/-! ## Derived flux and displayed answer -/

/-!
Combining the rectangular area, uniform-field model, raster geometry, and
planar flux law yields the exact trigonometric expression.  This is a derived
conclusion, not a field of any premise structure.
-/
lemma electricFlux_exact_trigonometric
    (setup : ElectricFluxSetup)
    (hData : MatchesProblemAndPrimaryFigure setup)
    (hPhysical : HasPhysicalConfiguration setup)
    (hArea : SatisfiesRectangularSurfaceAreaLaw setup)
    (hField : SatisfiesUniformElectricFieldModel setup)
    (hGeometry : SatisfiesPrimaryFigureGeometry setup)
    (hFlux : SatisfiesUniformPlanarElectricFluxLaw setup) :
    electricFluxInNewtonSquareMetersPerCoulomb setup.electricFlux =
      180 * ((15 : ℝ) / 100 * ((15 : ℝ) / 100)) *
        Real.cos (Real.pi / 2 + Real.pi / 6) := by
  have hAreaMeters :
      areaInSquareMeters setup.surfaceArea =
        (15 : ℝ) / 100 * ((15 : ℝ) / 100) := by
    rw [areaInSquareMeters, hArea.areaIsWidthTimesHeight]
    change
      lengthInMeters setup.surfaceWidth *
          lengthInMeters setup.surfaceHeight =
        (15 : ℝ) / 100 * ((15 : ℝ) / 100)
    rw [hData.widthMeters, hData.heightMeters]
  have hAngle :
      setup.fieldAngleFromSurfaceRadians = Real.pi / 6 := by
    rw [hData.fieldAngleAgreesWithPrintedAngle, hData.printedAngleDegrees]
    unfold degreesToRadians
    ring
  calc
    electricFluxInNewtonSquareMetersPerCoulomb setup.electricFlux =
        areaInSquareMeters setup.surfaceArea *
          inner ℝ
            (setup.electricField setup.observationTime setup.referencePoint)
            setup.outwardUnitNormal :=
      hFlux.fluxIsAreaTimesNormalFieldComponent
    _ =
        areaInSquareMeters setup.surfaceArea *
          inner ℝ
            (electricFieldStrengthInNewtonsPerCoulomb
                setup.electricFieldStrength • setup.fieldDirection)
            setup.outwardUnitNormal := by
      rw [hField.fieldIsUniformOnSurface setup.referencePoint
        hPhysical.referencePointOnSurface]
    _ =
        areaInSquareMeters setup.surfaceArea *
          (electricFieldStrengthInNewtonsPerCoulomb
              setup.electricFieldStrength *
            inner ℝ setup.fieldDirection setup.outwardUnitNormal) := by
      rw [real_inner_smul_left]
    _ =
        areaInSquareMeters setup.surfaceArea *
          (180 * Real.cos
            (InnerProductGeometry.angle
              setup.fieldDirection setup.outwardUnitNormal)) := by
      rw [hData.fieldStrengthNewtonsPerCoulomb,
        InnerProductGeometry.inner_eq_cos_angle_of_norm_eq_one
          hPhysical.fieldDirectionIsUnit hPhysical.outwardNormalIsUnit]
    _ =
        areaInSquareMeters setup.surfaceArea *
          (180 * Real.cos (Real.pi / 2 + Real.pi / 6)) := by
      rw [hGeometry.fieldAngleFromOutwardNormal, hAngle]
    _ =
        180 * ((15 : ℝ) / 100 * ((15 : ℝ) / 100)) *
          Real.cos (Real.pi / 2 + Real.pi / 6) := by
      rw [hAreaMeters]
      ring

/-!
Since `cos (120°) = -1/2`, the exact physical flux is
`-81/40 = -2.025 N m²/C`.
-/
lemma electricFlux_exact
    (setup : ElectricFluxSetup)
    (hData : MatchesProblemAndPrimaryFigure setup)
    (hPhysical : HasPhysicalConfiguration setup)
    (hArea : SatisfiesRectangularSurfaceAreaLaw setup)
    (hField : SatisfiesUniformElectricFieldModel setup)
    (hGeometry : SatisfiesPrimaryFigureGeometry setup)
    (hFlux : SatisfiesUniformPlanarElectricFluxLaw setup) :
    electricFluxInNewtonSquareMetersPerCoulomb setup.electricFlux =
      (-81 : ℝ) / 40 := by
  rw [electricFlux_exact_trigonometric setup hData hPhysical hArea hField
    hGeometry hFlux, Real.cos_add, Real.cos_pi_div_two,
    Real.sin_pi_div_two, Real.sin_pi_div_six]
  norm_num

/-- Labels of the four flux choices printed in the question. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Signed flux in `N m²/C` printed beside each answer choice. -/
def displayedFluxInNewtonSquareMetersPerCoulomb : AnswerChoice → ℝ
  | .A => (-6 : ℝ) / 5
  | .B => -10
  | .C => -2
  | .D => (-23 : ℝ) / 10

/-- The source dataset records choice D, retained here as metadata only. -/
def recordedDatasetAnswer : AnswerChoice := .D

/-!
A physical flux matches a displayed one-decimal value when it is within half
of `0.1 N m²/C` of that value.
-/
def MatchesDisplayedFluxToOneDecimalPlace
    (setup : ElectricFluxSetup) (choice : AnswerChoice) : Prop :=
  |electricFluxInNewtonSquareMetersPerCoulomb setup.electricFlux -
      displayedFluxInNewtonSquareMetersPerCoulomb choice| ≤ 1 / 20

/-- A choice is the sole displayed value matching the independently modeled flux. -/
def IsUniqueMatchingDisplayedChoice
    (setup : ElectricFluxSetup) (choice : AnswerChoice) : Prop :=
  MatchesDisplayedFluxToOneDecimalPlace setup choice ∧
    ∀ other, MatchesDisplayedFluxToOneDecimalPlace setup other →
      other = choice

/-!
The physical model gives `-2.025 N m²/C`, which rounds to choice C (`-2.0`)
and not to the dataset-recorded choice D (`-2.3`).  Keeping those conclusions
separate exposes the source-answer discrepancy without making either value a
hypothesis.

This declaration formalizes `thm:physics:phyx_mini_0844:target`.
-/
theorem problem_phyx_mini_0844
    (setup : ElectricFluxSetup)
    (hData : MatchesProblemAndPrimaryFigure setup)
    (hPhysical : HasPhysicalConfiguration setup)
    (hArea : SatisfiesRectangularSurfaceAreaLaw setup)
    (hField : SatisfiesUniformElectricFieldModel setup)
    (hGeometry : SatisfiesPrimaryFigureGeometry setup)
    (hFlux : SatisfiesUniformPlanarElectricFluxLaw setup) :
    electricFluxInNewtonSquareMetersPerCoulomb setup.electricFlux =
        (-81 : ℝ) / 40 ∧
      IsUniqueMatchingDisplayedChoice setup .C ∧
      ¬ MatchesDisplayedFluxToOneDecimalPlace
        setup recordedDatasetAnswer := by
  have hExact :
      electricFluxInNewtonSquareMetersPerCoulomb setup.electricFlux =
        (-81 : ℝ) / 40 :=
    electricFlux_exact setup hData hPhysical hArea hField hGeometry hFlux
  refine ⟨hExact, ?_, ?_⟩
  · constructor
    · unfold MatchesDisplayedFluxToOneDecimalPlace
      rw [hExact]
      norm_num [displayedFluxInNewtonSquareMetersPerCoulomb]
    · intro other hOther
      cases other with
      | A =>
          unfold MatchesDisplayedFluxToOneDecimalPlace at hOther
          rw [hExact] at hOther
          norm_num [displayedFluxInNewtonSquareMetersPerCoulomb] at hOther
      | B =>
          unfold MatchesDisplayedFluxToOneDecimalPlace at hOther
          rw [hExact] at hOther
          norm_num [displayedFluxInNewtonSquareMetersPerCoulomb] at hOther
      | C => rfl
      | D =>
          unfold MatchesDisplayedFluxToOneDecimalPlace at hOther
          rw [hExact] at hOther
          norm_num [displayedFluxInNewtonSquareMetersPerCoulomb] at hOther
  · unfold MatchesDisplayedFluxToOneDecimalPlace recordedDatasetAnswer
    rw [hExact]
    norm_num [displayedFluxInNewtonSquareMetersPerCoulomb]

end PhyXMiniProblems.ProblemPhyXMini0844
