import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Physlib.SpaceAndTime.Space.LengthUnit
import Physlib.Units.WithDim.Area

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0845

open Dimension

/-!
# Electric field strength from flux through an inclined rectangle

The primary figure shows a uniform electric field crossing a rectangular
`10 cm × 20 cm` plane.  The field direction is `60°` above the plane and the
arrow `n̂` is the oriented unit normal.  The measured electric flux is
`25 N m²/C`.

Dimensionful physical quantities are represented with Physlib's
unit-independent `Dimensionful` types.  Real numbers occur only as explicit
unit readouts, dimensionless directions and angles, and displayed answer
values.
-/

/-! ## Dimensionful quantities and SI readouts -/

/-- Electric-field strength has the dimension of force divided by charge. -/
def electricFieldStrengthDimension : Dimension :=
  M𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹ * C𝓭⁻¹

/-- Electric flux has the dimension of electric-field strength times area. -/
def electricFluxDimension : Dimension :=
  electricFieldStrengthDimension * L𝓭 * L𝓭

/-- A nonnegative, unit-independent physical length. -/
abbrev LengthQuantity : Type :=
  Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative, unit-independent physical area. -/
abbrev AreaQuantity : Type := DimArea

/-- A nonnegative, unit-independent electric-field magnitude. -/
abbrev ElectricFieldStrengthQuantity : Type :=
  Dimensionful (WithDim electricFieldStrengthDimension NNReal)

/-- Signed electric flux through an oriented surface. -/
abbrev ElectricFluxQuantity : Type :=
  Dimensionful (WithDim electricFluxDimension ℝ)

/-- Read a physical length in a selected named length unit. -/
def lengthReadout (unit : LengthUnit) (length : LengthQuantity) : ℝ :=
  ((length {UnitChoices.SI with length := unit}).val : ℝ)

/-- Read a physical length in coherent-SI metres. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.meters length

/-- Read a physical length in centimetres, as used on the figure. -/
def lengthInCentimeters (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.centimeters length

/-- Read a physical area in coherent-SI square metres. -/
def areaInSquareMeters (area : AreaQuantity) : ℝ :=
  ((area UnitChoices.SI).val : ℝ)

/-- Read electric-field strength in coherent-SI newtons per coulomb. -/
def electricFieldStrengthInNewtonsPerCoulomb
    (strength : ElectricFieldStrengthQuantity) : ℝ :=
  ((strength UnitChoices.SI).val : ℝ)

/-- Read electric flux in coherent-SI newton square metres per coulomb. -/
def electricFluxInNewtonSquareMetersPerCoulomb
    (flux : ElectricFluxQuantity) : ℝ :=
  (flux UnitChoices.SI).val

/-! ## Physical setup and primary-figure content -/

/-- Dimensionless spatial vectors used for the field direction and normal. -/
abbrev SpatialVector : Type := EuclideanSpace ℝ (Fin 3)

/--
The labelled rectangle and arrows in the primary figure.  The angle is
measured from the surface plane, rather than from its normal.
-/
structure RectangularPlaneFigure where
  shortSide : LengthQuantity
  longSide : LengthQuantity
  electricFieldDirection : SpatialVector
  outwardUnitNormal : SpatialVector
  angleFromSurfaceRadians : ℝ
  electricFieldArrowLabel : String
  unitNormalArrowLabel : String
  fieldArrowCount : ℕ
  fieldArrowsAreParallel : Bool
  normalStartsAtPlaneCenter : Bool

/-- Physical quantities associated with the flux measurement. -/
structure ElectricFluxRectangleSetup where
  figure : RectangularPlaneFigure
  surfaceArea : AreaQuantity
  electricFieldStrength : ElectricFieldStrengthQuantity
  measuredElectricFlux : ElectricFluxQuantity

/--
Problem-statement and primary-figure readouts: the two side labels, the marked
`60°` angle from the plane, the `E⃗` and `n̂` labels, and the measured flux.
-/
structure MatchesProblemAndFigureReadouts
    (setup : ElectricFluxRectangleSetup) : Prop where
  shortSideLabelCentimeters :
    lengthInCentimeters setup.figure.shortSide = 10
  longSideLabelCentimeters :
    lengthInCentimeters setup.figure.longSide = 20
  angleLabelRadians :
    setup.figure.angleFromSurfaceRadians = Real.pi / 3
  electricFieldArrowLabel :
    setup.figure.electricFieldArrowLabel = "E⃗"
  unitNormalArrowLabel :
    setup.figure.unitNormalArrowLabel = "n̂"
  figureShowsSeveralFieldArrows : 1 < setup.figure.fieldArrowCount
  fieldArrowsAreParallel : setup.figure.fieldArrowsAreParallel = true
  normalStartsAtPlaneCenter : setup.figure.normalStartsAtPlaneCenter = true
  measuredFluxReadout :
    electricFluxInNewtonSquareMetersPerCoulomb
        setup.measuredElectricFlux = 25

/-- Positivity and nondegeneracy conditions for the physical configuration. -/
structure HasPhysicalParameters
    (setup : ElectricFluxRectangleSetup) : Prop where
  shortSidePositive : 0 < lengthInMeters setup.figure.shortSide
  longSidePositive : 0 < lengthInMeters setup.figure.longSide
  areaPositive : 0 < areaInSquareMeters setup.surfaceArea
  electricFieldStrengthPositive :
    0 < electricFieldStrengthInNewtonsPerCoulomb
      setup.electricFieldStrength
  measuredFluxPositive :
    0 < electricFluxInNewtonSquareMetersPerCoulomb
      setup.measuredElectricFlux
  angleFromSurfacePositive : 0 < setup.figure.angleFromSurfaceRadians
  angleFromSurfaceLessThanRightAngle :
    setup.figure.angleFromSurfaceRadians < Real.pi / 2

/-- The physical area of a rectangle is the product of its side lengths. -/
structure SatisfiesRectangularAreaGeometry
    (setup : ElectricFluxRectangleSetup) : Prop where
  areaLaw :
    areaInSquareMeters setup.surfaceArea =
      lengthInMeters setup.figure.shortSide *
        lengthInMeters setup.figure.longSide

/-!
Both arrows represent unit directions.  Because the labelled angle is from
the plane, the component of the field direction along the oriented normal is
the sine of that angle.
-/
structure SatisfiesFigureAngleGeometry
    (setup : ElectricFluxRectangleSetup) : Prop where
  electricFieldDirectionIsUnit :
    ‖setup.figure.electricFieldDirection‖ = 1
  outwardNormalIsUnit : ‖setup.figure.outwardUnitNormal‖ = 1
  normalComponentFromSurfaceAngle :
    inner ℝ setup.figure.electricFieldDirection
        setup.figure.outwardUnitNormal =
      Real.sin setup.figure.angleFromSurfaceRadians

/-!
For a uniform electric field crossing a flat oriented surface,
`Φ = E A (ê · n̂)`.  This is the governing flux law and contains no numerical
answer for the requested field strength.
-/
structure SatisfiesUniformElectricFluxLaw
    (setup : ElectricFluxRectangleSetup) : Prop where
  fluxLaw :
    electricFluxInNewtonSquareMetersPerCoulomb
        setup.measuredElectricFlux =
      electricFieldStrengthInNewtonsPerCoulomb
          setup.electricFieldStrength *
        areaInSquareMeters setup.surfaceArea *
          inner ℝ setup.figure.electricFieldDirection
            setup.figure.outwardUnitNormal

/-! ## Derived field strength and displayed answer -/

/--
The flux law and the figure's angle geometry give the usual projected-area
formula.  No numerical readout from this problem is used in this general
relation.
-/
lemma electricFieldStrength_eq_flux_div_projected_area
    (setup : ElectricFluxRectangleSetup)
    (hPhysical : HasPhysicalParameters setup)
    (hAngle : SatisfiesFigureAngleGeometry setup)
    (hFlux : SatisfiesUniformElectricFluxLaw setup) :
    electricFieldStrengthInNewtonsPerCoulomb
        setup.electricFieldStrength =
      electricFluxInNewtonSquareMetersPerCoulomb
          setup.measuredElectricFlux /
        (areaInSquareMeters setup.surfaceArea *
          Real.sin setup.figure.angleFromSurfaceRadians) := by
  have hAngleLtPi : setup.figure.angleFromSurfaceRadians < Real.pi := by
    nlinarith [hPhysical.angleFromSurfaceLessThanRightAngle, Real.pi_pos]
  have hSinPositive :
      0 < Real.sin setup.figure.angleFromSurfaceRadians :=
    Real.sin_pos_of_pos_of_lt_pi
      hPhysical.angleFromSurfacePositive hAngleLtPi
  have hProjectedAreaNonzero :
      areaInSquareMeters setup.surfaceArea *
          Real.sin setup.figure.angleFromSurfaceRadians ≠ 0 :=
    ne_of_gt (mul_pos hPhysical.areaPositive hSinPositive)
  apply (eq_div_iff hProjectedAreaNonzero).2
  rw [← hAngle.normalComponentFromSurfaceAngle, hFlux.fluxLaw]
  ring

/-!
Substituting `Φ = 25 N m²/C`, `A = (0.10 m)(0.20 m)`, and the `60°`
surface angle yields the exact SI field-strength readout `2500 / √3`.
-/
lemma electricFieldStrength_eq_twoThousandFiveHundred_div_sqrtThree
    (setup : ElectricFluxRectangleSetup)
    (hData : MatchesProblemAndFigureReadouts setup)
    (hPhysical : HasPhysicalParameters setup)
    (hArea : SatisfiesRectangularAreaGeometry setup)
    (hAngle : SatisfiesFigureAngleGeometry setup)
    (hFlux : SatisfiesUniformElectricFluxLaw setup) :
    electricFieldStrengthInNewtonsPerCoulomb
        setup.electricFieldStrength =
      2500 / Real.sqrt 3 := by
  have lengthInCentimeters_eq
      (length : LengthQuantity) :
      lengthInCentimeters length = 100 * lengthInMeters length := by
    change
      ((length
          {UnitChoices.SI with length := LengthUnit.centimeters}).val : ℝ) =
        100 * ((length UnitChoices.SI).val : ℝ)
    rw [length.property UnitChoices.SI
      {UnitChoices.SI with length := LengthUnit.centimeters}]
    norm_num [UnitChoices.dimScale, LengthUnit.centimeters,
      LengthUnit.meters, LengthUnit.scale, LengthUnit.div_eq_val,
      NNReal.smul_def]
    left
    rfl
  have hShortSideMeters :
      lengthInMeters setup.figure.shortSide = 1 / 10 := by
    nlinarith [lengthInCentimeters_eq setup.figure.shortSide,
      hData.shortSideLabelCentimeters]
  have hLongSideMeters :
      lengthInMeters setup.figure.longSide = 1 / 5 := by
    nlinarith [lengthInCentimeters_eq setup.figure.longSide,
      hData.longSideLabelCentimeters]
  have hAreaSquareMeters :
      areaInSquareMeters setup.surfaceArea = 1 / 50 := by
    rw [hArea.areaLaw, hShortSideMeters, hLongSideMeters]
    norm_num
  have hExact :=
    electricFieldStrength_eq_flux_div_projected_area
      setup hPhysical hAngle hFlux
  rw [hData.measuredFluxReadout, hAreaSquareMeters,
    hData.angleLabelRadians, Real.sin_pi_div_three] at hExact
  have hSqrtThreePositive : 0 < Real.sqrt 3 :=
    Real.sqrt_pos.2 (by norm_num)
  rw [hExact]
  field_simp [ne_of_gt hSqrtThreePositive]
  ring

/-- Labels of the four field-strength choices printed in the question. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Electric-field strength in newtons per coulomb printed beside each choice. -/
def answerStrengthInNewtonsPerCoulomb : AnswerChoice → ℝ
  | .A => (13 / 10 : ℝ) * 10 ^ 3
  | .B => (53 / 10 : ℝ) * 10 ^ 4
  | .C => (10 / 10 : ℝ) * 10 ^ 5
  | .D => (14 / 10 : ℝ) * 10 ^ 3

/-!
Half of one unit in the last displayed significant digit.  This makes
agreement with each rounded answer choice precise.
-/
def answerRoundingToleranceInNewtonsPerCoulomb : AnswerChoice → ℝ
  | .A => 50
  | .B => 500
  | .C => 5000
  | .D => 50

/-- The answer label recorded by the source dataset. -/
def recordedDatasetAnswer : AnswerChoice := .D

/-- A displayed choice agrees with the independently modelled field strength. -/
def AnswerMatchesElectricField
    (setup : ElectricFluxRectangleSetup) (choice : AnswerChoice) : Prop :=
  |electricFieldStrengthInNewtonsPerCoulomb setup.electricFieldStrength -
      answerStrengthInNewtonsPerCoulomb choice| ≤
    answerRoundingToleranceInNewtonsPerCoulomb choice

/-!
The exact value is approximately `1.443 × 10³ N/C`, so to the precision used
by the choices it is `1.4 × 10³ N/C`, answer D.
-/
theorem electricFieldStrength_matches_choice_D
    (setup : ElectricFluxRectangleSetup)
    (hData : MatchesProblemAndFigureReadouts setup)
    (hPhysical : HasPhysicalParameters setup)
    (hArea : SatisfiesRectangularAreaGeometry setup)
    (hAngle : SatisfiesFigureAngleGeometry setup)
    (hFlux : SatisfiesUniformElectricFluxLaw setup) :
    AnswerMatchesElectricField setup .D := by
  unfold AnswerMatchesElectricField
  rw [electricFieldStrength_eq_twoThousandFiveHundred_div_sqrtThree
    setup hData hPhysical hArea hAngle hFlux]
  norm_num [answerStrengthInNewtonsPerCoulomb,
    answerRoundingToleranceInNewtonsPerCoulomb]
  have hSqrtThreePositive : 0 < Real.sqrt 3 :=
    Real.sqrt_pos.2 (by norm_num)
  have hSqrtThreeSquared : (Real.sqrt 3) ^ 2 = (3 : ℝ) :=
    Real.sq_sqrt (by norm_num)
  have hSqrtThreeLower : (173 / 100 : ℝ) < Real.sqrt 3 := by
    nlinarith
  have hSqrtThreeUpper : Real.sqrt 3 < (7 / 4 : ℝ) := by
    nlinarith
  have hFieldLower : (1400 : ℝ) ≤ 2500 / Real.sqrt 3 := by
    apply (le_div_iff₀ hSqrtThreePositive).2
    nlinarith
  have hFieldUpper : 2500 / Real.sqrt 3 ≤ (1450 : ℝ) := by
    apply (div_le_iff₀ hSqrtThreePositive).2
    nlinarith
  rw [abs_of_nonneg (by linarith)]
  linarith

end PhyXMiniProblems.ProblemPhyXMini0845
