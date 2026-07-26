import Mathlib
import Physlib.Units.WithDim.Basic

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0843

open Dimension

/-!
# Electric flux through a square surface

The supplied figure shows a `10 cm × 10 cm` plane, a uniform electric field
of magnitude `200 N/C`, and an oriented unit normal `n-hat`.  The field makes
an angle of `30 degrees` with the plane, so its component along the displayed
normal is obtained with the sine of that angle.

Lengths, the electric-field vector, and electric flux are represented as
unit-independent physical quantities.  Real numbers are used only for
calibrated unit readouts, the dimensionless angle, and direction vectors.
-/

/-! ## Dimensionful physical quantities -/

/-- The MLTQ dimension of force per charge, hence of an electric field. -/
def electricFieldDimension : Dimension :=
  M𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹ * C𝓭⁻¹

/-- Electric flux has dimension electric field times area. -/
def electricFluxDimension : Dimension :=
  electricFieldDimension * L𝓭 * L𝓭

/-- A nonnegative, unit-independent physical length. -/
abbrev LengthQuantity : Type :=
  Dimensionful (WithDim L𝓭 NNReal)

/-- A unit-independent three-dimensional electric-field vector. -/
abbrev ElectricFieldVectorQuantity : Type :=
  Dimensionful
    (WithDim electricFieldDimension (EuclideanSpace ℝ (Fin 3)))

/-- Signed electric flux through an oriented surface. -/
abbrev ElectricFluxQuantity : Type :=
  Dimensionful (WithDim electricFluxDimension ℝ)

/-- Scalar readout of a physical length in a coherent choice of units. -/
def lengthReadout (units : UnitChoices) (length : LengthQuantity) : ℝ :=
  ((length units).val : ℝ)

/-- Vector readout of an electric field in a coherent choice of units. -/
def electricFieldVectorReadout
    (units : UnitChoices) (field : ElectricFieldVectorQuantity) :
    EuclideanSpace ℝ (Fin 3) :=
  (field units).val

/-- Scalar readout of electric flux in a coherent choice of units. -/
def electricFluxReadout
    (units : UnitChoices) (flux : ElectricFluxQuantity) : ℝ :=
  (flux units).val

/-- Length readout in centimetres, matching the surface labels in the figure. -/
def lengthInCentimeters (length : LengthQuantity) : ℝ :=
  lengthReadout {UnitChoices.SI with length := LengthUnit.centimeters} length

/-- Electric-field vector readout in SI units, i.e. newtons per coulomb. -/
def electricFieldVectorInNewtonsPerCoulomb
    (field : ElectricFieldVectorQuantity) : EuclideanSpace ℝ (Fin 3) :=
  electricFieldVectorReadout UnitChoices.SI field

/-- Electric-flux readout in SI units, i.e. newton-metres squared per coulomb. -/
def electricFluxInNewtonMetresSquaredPerCoulomb
    (flux : ElectricFluxQuantity) : ℝ :=
  electricFluxReadout UnitChoices.SI flux

/-- Convert a numerical angle in degrees to its radian readout. -/
def degreesToRadians (angleInDegrees : ℝ) : ℝ :=
  angleInDegrees * Real.pi / 180

/-! ## Figure geometry and physical setup -/

/--
An oriented rectangular plane.  The two physical side lengths determine its
area, while `unitNormal` is the direction denoted by `n-hat` in the figure.
-/
structure OrientedRectangularSurface where
  width : LengthQuantity
  height : LengthQuantity
  unitNormal : EuclideanSpace ℝ (Fin 3)

/--
The physical quantities appearing in the diagram.  `electricFlux` is an
independent signed physical quantity; its relation to the other fields is
imposed only by the governing flux law below.
-/
structure RectangularSurfaceFluxSetup where
  surface : OrientedRectangularSurface
  electricField : ElectricFieldVectorQuantity
  fieldPlaneAngleRadians : ℝ
  electricFlux : ElectricFluxQuantity

/-! ## Problem and primary-image data -/

/--
Direct transcription of the primary image: both side labels are `10 cm`, the
field-magnitude label is `200 N/C`, the field-plane angle is `30 degrees`, and
the hatted normal is a unit vector.  No electric-flux value or answer choice
occurs in this structure.
-/
structure MatchesSuppliedFigure
    (setup : RectangularSurfaceFluxSetup) : Prop where
  widthLabelCentimeters :
    lengthInCentimeters setup.surface.width = 10
  heightLabelCentimeters :
    lengthInCentimeters setup.surface.height = 10
  electricFieldMagnitudeLabel :
    ‖electricFieldVectorInNewtonsPerCoulomb setup.electricField‖ = 200
  fieldPlaneAngleLabel :
    setup.fieldPlaneAngleRadians = degreesToRadians 30
  normalHatIsUnit : ‖setup.surface.unitNormal‖ = 1

/-! ## Governing geometric and electrostatic laws -/

/--
For the acute, positively oriented angle shown between the field and the
plane, the field component along the surface normal is `|E| sin(theta)`.
This is stated in every coherent unit choice and contains no numerical answer.
-/
structure SatisfiesFieldPlaneAngleGeometry
    (setup : RectangularSurfaceFluxSetup) : Prop where
  normalComponent :
    ∀ units,
      inner ℝ (electricFieldVectorReadout units setup.electricField)
          setup.surface.unitNormal =
        ‖electricFieldVectorReadout units setup.electricField‖ *
          Real.sin setup.fieldPlaneAngleRadians

/--
The uniform-field electric-flux law for an oriented rectangular plane:
`Phi_E = area * (E dot n-hat)`.  It is quantified over coherent unit choices,
so the equality retains its dimensional meaning and mentions no answer value.
-/
structure SatisfiesUniformRectangularElectricFluxLaw
    (setup : RectangularSurfaceFluxSetup) : Prop where
  fluxLaw :
    ∀ units,
      electricFluxReadout units setup.electricFlux =
        lengthReadout units setup.surface.width *
          lengthReadout units setup.surface.height *
            inner ℝ (electricFieldVectorReadout units setup.electricField)
              setup.surface.unitNormal

/-! ## Displayed answer choices and target -/

/-- Labels of the four answer choices printed with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/--
Numerical SI electric-flux readout printed beside an answer choice, in
newton-metres squared per coulomb.
-/
def displayedElectricFluxInNewtonMetresSquaredPerCoulomb : AnswerChoice → ℝ
  | .A => 1.2
  | .B => 10
  | .C => 2
  | .D => 1

/--
The electric flux through the displayed square is
`1 N m^2 / C`, which is answer D.

This formalizes blueprint label `thm:physics:phyx_mini_0843:target`.
-/
theorem problem_phyx_mini_0843
    (setup : RectangularSurfaceFluxSetup)
    (hFigure : MatchesSuppliedFigure setup)
    (hGeometry : SatisfiesFieldPlaneAngleGeometry setup)
    (hFluxLaw : SatisfiesUniformRectangularElectricFluxLaw setup) :
    electricFluxInNewtonMetresSquaredPerCoulomb setup.electricFlux =
      displayedElectricFluxInNewtonMetresSquaredPerCoulomb .D := by
  let centimeterUnits : UnitChoices :=
    {UnitChoices.SI with length := LengthUnit.centimeters}
  have hCentimeterScale :
      ((centimeterUnits.dimScale UnitChoices.SI L𝓭 : NNReal) : ℝ) =
        1 / 100 := by
    norm_num [centimeterUnits, UnitChoices.dimScale, LengthUnit.centimeters]
    rfl
  have lengthInMeters_of_centimetersTen
      (length : LengthQuantity) (hLabel : lengthInCentimeters length = 10) :
      lengthReadout UnitChoices.SI length = 1 / 10 := by
    have hScale := congrArg WithDim.val
      (length.property centimeterUnits UnitChoices.SI)
    have hScaleReal := congrArg (fun x : NNReal => (x : ℝ)) hScale
    change (↑(length UnitChoices.SI).val : ℝ) =
      ↑(centimeterUnits.dimScale UnitChoices.SI L𝓭) *
        ↑(length centimeterUnits).val at hScaleReal
    rw [hCentimeterScale] at hScaleReal
    have hLabel' : lengthReadout centimeterUnits length = 10 := by
      simpa [centimeterUnits, lengthInCentimeters] using hLabel
    change (↑(length UnitChoices.SI).val : ℝ) = 1 / 10
    change (↑(length centimeterUnits).val : ℝ) = 10 at hLabel'
    nlinarith [hScaleReal, hLabel']
  have hWidth := lengthInMeters_of_centimetersTen
    setup.surface.width hFigure.widthLabelCentimeters
  have hHeight := lengthInMeters_of_centimetersTen
    setup.surface.height hFigure.heightLabelCentimeters
  change electricFluxReadout UnitChoices.SI setup.electricFlux = 1
  rw [hFluxLaw.fluxLaw UnitChoices.SI,
    hGeometry.normalComponent UnitChoices.SI, hWidth, hHeight]
  rw [show ‖electricFieldVectorReadout UnitChoices.SI setup.electricField‖ =
      200 by
    exact hFigure.electricFieldMagnitudeLabel]
  rw [hFigure.fieldPlaneAngleLabel]
  rw [show degreesToRadians 30 = Real.pi / 6 by
    unfold degreesToRadians
    ring]
  rw [Real.sin_pi_div_six]
  norm_num

end PhyXMiniProblems.ProblemPhyXMini0843
