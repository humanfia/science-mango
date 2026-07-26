import Mathlib
import Physlib.Electromagnetism.Basic
import Physlib.SpaceAndTime.Space.LengthUnit
import Physlib.Units.WithDim.Area

/- USER: The assigned Lean file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0998

open Dimension

/-!
# Electric flux through an inclined disk

The primary raster shows an open circular disk of radius `0.10 m` in a
uniform electric field.  The field arrows point to the right, while the
chosen unit normal points up and to the right.  The marked acute angle
between the field and this normal is `30°`.  The source states that the
field magnitude is `2.0 * 10^3 N/C`.

Lengths, areas, electric-field strengths, and electric fluxes are represented
by Physlib's unit-independent `Dimensionful` quantities.  The full vector
field is Physlib's spacetime-dependent `Electromagnetism.ElectricField 3`.
Real numbers occur only as coherent-SI readouts, dimensionless vector
components, angles in radians, and displayed multiple-choice values.

Assumption/target split:

* governing laws: circular-disk area, a spatially uniform field calibrated by
  its dimensionful magnitude and direction, and planar surface flux
  `Phi = A * (E dot n)`;
* previous-part results: none;
* figure/data readouts: radius `0.10 m`, field magnitude `2000 N/C`, the chosen
  normal orientation, rightward parallel field arrows, and the `30°`
  field-to-normal angle;
* current target conclusions: the exact signed flux is
  `10 * pi * sqrt 3 N m^2/C`, and the uniquely closest displayed answer is
  choice B, `54 N m^2/C`.

Neither target conclusion is a setup field or a premise field below.
-/

/-! ## Dimensionful quantities and coherent-SI readouts -/

/-- Electric-field strength has dimension `M L T⁻² C⁻¹` (`N/C`). -/
def electricFieldStrengthDimension : Dimension :=
  M𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹ * C𝓭⁻¹

/-- Electric flux has dimension `M L³ T⁻² C⁻¹` (`N m²/C`). -/
def electricFluxDimension : Dimension :=
  electricFieldStrengthDimension * L𝓭 * L𝓭

/-- A nonnegative, unit-independent physical length. -/
abbrev LengthQuantity : Type :=
  Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative, unit-independent physical area. -/
abbrev AreaQuantity : Type := DimArea

/-- A nonnegative, unit-independent electric-field-strength magnitude. -/
abbrev ElectricFieldStrengthMagnitude : Type :=
  Dimensionful (WithDim electricFieldStrengthDimension NNReal)

/-- Signed electric flux through an oriented surface. -/
abbrev ElectricFluxQuantity : Type :=
  Dimensionful (WithDim electricFluxDimension ℝ)

/-- Read a physical length in a selected named length unit. -/
def lengthReadout (unit : LengthUnit) (length : LengthQuantity) : ℝ :=
  ((length {UnitChoices.SI with length := unit}).val : ℝ)

/-- Read a physical area in the square of a selected named length unit. -/
def areaReadout (unit : LengthUnit) (area : AreaQuantity) : ℝ :=
  ((area {UnitChoices.SI with length := unit}).val : ℝ)

/-- Read a physical length in metres. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.meters length

/-- Read a physical area in square metres. -/
def areaInSquareMeters (area : AreaQuantity) : ℝ :=
  areaReadout LengthUnit.meters area

/-- Read an electric-field-strength magnitude in newtons per coulomb. -/
def electricFieldStrengthInNewtonsPerCoulomb
    (magnitude : ElectricFieldStrengthMagnitude) : ℝ :=
  ((magnitude UnitChoices.SI).val : ℝ)

/-- Read signed electric flux in newton-square-metres per coulomb. -/
def electricFluxInNewtonSquareMetersPerCoulomb
    (flux : ElectricFluxQuantity) : ℝ :=
  (flux UnitChoices.SI).val

/-- Convert a degree readout to a real angle in radians. -/
def degreesToRadians (degrees : ℝ) : ℝ :=
  degrees * Real.pi / 180

/-! ## Disk geometry and primary-raster vocabulary -/

/-- Qualitative arrow directions visible in the supplied two-dimensional view. -/
inductive DiagramArrowDirection where
  | leftToRight
  | rightToLeft
  | upAndRight
  | downAndLeft
  | other
  deriving DecidableEq, Repr

/-- Named visual features visible in `phyx_data/test_image/998.png`. -/
inductive FigureFeature where
  | openCircularDisk
  | radiusLabel
  | chosenNormalArrow
  | electricFieldArrows
  | electricFieldVectorLabel
  | thirtyDegreeMarker
  | rightAngleMarkerOnDisk
  deriving DecidableEq, Fintype, Repr

/-!
Literal problem and raster data.  No flux value or answer label is stored in
this record.
-/
structure InclinedDiskFigure where
  shows : FigureFeature → Bool
  printedRadiusMetres : ℝ
  statedFieldStrengthNewtonsPerCoulomb : ℝ
  printedNormalFieldAngleDegrees : ℝ
  fieldArrowDirection : DiagramArrowDirection
  normalArrowDirection : DiagramArrowDirection
  fieldArrowsParallel : Bool
  normalArrowChoosesSurfaceOrientation : Bool
  containsNumericalFluxReadout : Bool

/-!
An oriented circular disk in three-dimensional physical space.  The set and
representative point preserve the surface's geometric role; its radius and
area remain dimensionful quantities.
-/
structure OrientedCircularDisk where
  center : Space 3
  surface : Set (Space 3)
  representativePoint : Space 3
  radius : LengthQuantity
  area : AreaQuantity
  orientedUnitNormal : EuclideanSpace ℝ (Fin 3)

/-!
The independent physical quantities and observables.  In particular,
`electricFlux` is not defined from an answer choice or from the requested
numerical value.
-/
structure InclinedDiskElectricFluxSetup where
  disk : OrientedCircularDisk
  observationTime : Time
  electricField : Electromagnetism.ElectricField 3
  electricFieldStrength : ElectricFieldStrengthMagnitude
  fieldDirection : EuclideanSpace ℝ (Fin 3)
  electricFlux : ElectricFluxQuantity
  figure : InclinedDiskFigure

/-! ## Figure/data readouts and governing physical laws -/

/-!
Direct source and primary-image readouts.  The prose supplies the field
magnitude, while the raster supplies the radius label, arrow directions,
chosen normal, and acute `30°` marker.  No flux result occurs here.
-/
structure MatchesProblemAndPrimaryFigure
    (setup : InclinedDiskElectricFluxSetup) : Prop where
  everyNamedFeatureShown :
    ∀ feature, setup.figure.shows feature = true
  radiusLabel : setup.figure.printedRadiusMetres = 1 / 10
  radiusLabelCalibration :
    lengthInMeters setup.disk.radius = setup.figure.printedRadiusMetres
  fieldStrengthStatement :
    setup.figure.statedFieldStrengthNewtonsPerCoulomb = 2000
  fieldStrengthCalibration :
    electricFieldStrengthInNewtonsPerCoulomb setup.electricFieldStrength =
      setup.figure.statedFieldStrengthNewtonsPerCoulomb
  angleLabel : setup.figure.printedNormalFieldAngleDegrees = 30
  fieldPointsLeftToRight :
    setup.figure.fieldArrowDirection = .leftToRight
  normalPointsUpAndRight :
    setup.figure.normalArrowDirection = .upAndRight
  parallelFieldArrows : setup.figure.fieldArrowsParallel = true
  normalChoosesOrientation :
    setup.figure.normalArrowChoosesSurfaceOrientation = true
  noFluxValueInFigure : setup.figure.containsNumericalFluxReadout = false

/-!
Regularity and circular-area geometry of the open disk.  The area relation is
a general geometric law and contains no flux value.
-/
structure HasPhysicalCircularDiskGeometry
    (setup : InclinedDiskElectricFluxSetup) : Prop where
  radiusPositive : 0 < lengthInMeters setup.disk.radius
  areaPositive : 0 < areaInSquareMeters setup.disk.area
  representativePointOnDisk :
    setup.disk.representativePoint ∈ setup.disk.surface
  centerOnDisk : setup.disk.center ∈ setup.disk.surface
  normalIsUnit : ‖setup.disk.orientedUnitNormal‖ = 1
  circularArea :
    areaInSquareMeters setup.disk.area =
      Real.pi * (lengthInMeters setup.disk.radius) ^ 2

/-!
The figure-derived spatial relation: the field direction meets the chosen
oriented unit normal at the marked acute angle.
-/
structure SatisfiesFigureDerivedOrientation
    (setup : InclinedDiskElectricFluxSetup) : Prop where
  fieldDirectionIsUnit : ‖setup.fieldDirection‖ = 1
  normalFieldAngle :
    InnerProductGeometry.angle setup.fieldDirection
        setup.disk.orientedUnitNormal =
      degreesToRadians setup.figure.printedNormalFieldAngleDegrees

/-!
Uniform-field idealization on the observation time slice.  Physlib's vector
field is calibrated in coherent-SI components by the independent dimensionful
strength magnitude and unit direction.  This premise mentions no flux.
-/
structure SatisfiesUniformElectricFieldModel
    (setup : InclinedDiskElectricFluxSetup) : Prop where
  fieldIsSpatiallyUniform : ∀ position : Space 3,
    setup.electricField setup.observationTime position =
      electricFieldStrengthInNewtonsPerCoulomb setup.electricFieldStrength •
        setup.fieldDirection

/-!
For an oriented planar surface in a uniform field, electric flux is
`A * (E dot n)`.  This is the governing surface-flux law, not the requested
numerical evaluation.
-/
structure SatisfiesPlanarElectricFluxLaw
    (setup : InclinedDiskElectricFluxSetup) : Prop where
  planarSurfaceFlux :
    electricFluxInNewtonSquareMetersPerCoulomb setup.electricFlux =
      areaInSquareMeters setup.disk.area *
        inner ℝ
          (setup.electricField setup.observationTime
            setup.disk.representativePoint)
          setup.disk.orientedUnitNormal

/-! ## Exact flux, displayed choices, and target -/

/-!
Substituting `r = 0.10 m`, `E = 2000 N/C`, and `theta = 30°` into
`Phi = E * pi * r^2 * cos theta` gives the exact idealized flux
`10 * pi * sqrt 3 N m^2/C`.
-/
lemma inclinedDiskElectricFlux_exact
    (setup : InclinedDiskElectricFluxSetup)
    (hFigure : MatchesProblemAndPrimaryFigure setup)
    (hDisk : HasPhysicalCircularDiskGeometry setup)
    (hOrientation : SatisfiesFigureDerivedOrientation setup)
    (hUniformField : SatisfiesUniformElectricFieldModel setup)
    (hFluxLaw : SatisfiesPlanarElectricFluxLaw setup) :
    electricFluxInNewtonSquareMetersPerCoulomb setup.electricFlux =
      10 * Real.pi * Real.sqrt 3 := by
  rw [hFluxLaw.planarSurfaceFlux,
    hUniformField.fieldIsSpatiallyUniform,
    inner_smul_left]
  simp only [starRingEnd_apply, star_trivial]
  rw [InnerProductGeometry.inner_eq_cos_angle_of_norm_eq_one
    hOrientation.fieldDirectionIsUnit hDisk.normalIsUnit]
  rw [hOrientation.normalFieldAngle, hFigure.angleLabel]
  have hDegrees : degreesToRadians 30 = Real.pi / 6 := by
    unfold degreesToRadians
    ring
  rw [hDegrees, Real.cos_pi_div_six]
  rw [hDisk.circularArea,
    hFigure.radiusLabelCalibration,
    hFigure.radiusLabel,
    hFigure.fieldStrengthCalibration,
    hFigure.fieldStrengthStatement]
  ring

/-- Labels of the four electric-flux choices printed with the question. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Electric-flux readout in `N m²/C` printed beside an answer choice. -/
def displayedElectricFlux : AnswerChoice → ℝ
  | .A => 108
  | .B => 54
  | .C => 58
  | .D => 60

/-- The answer label recorded by the source dataset, retained as metadata. -/
def recordedDatasetAnswer : AnswerChoice := .B

/-!
A choice is uniquely closest to the idealized signed flux when its absolute
error is strictly less than that of every other displayed readout.  This
definition does not privilege a particular label.
-/
def IsUniqueClosestDisplayedChoice
    (setup : InclinedDiskElectricFluxSetup) (choice : AnswerChoice) : Prop :=
  ∀ other : AnswerChoice, other ≠ choice →
    |electricFluxInNewtonSquareMetersPerCoulomb setup.electricFlux -
        displayedElectricFlux choice| <
      |electricFluxInNewtonSquareMetersPerCoulomb setup.electricFlux -
        displayedElectricFlux other|

/-!
The signed flux selected by the pictured normal is exactly
`10 * pi * sqrt 3 N m²/C`, approximately `54.4 N m²/C`; hence the uniquely
closest displayed value is `54`, answer B.

This declaration formalizes blueprint label
`thm:physics:phyx_mini_0998:target`.
-/
theorem problem_phyx_mini_0998
    (setup : InclinedDiskElectricFluxSetup)
    (hFigure : MatchesProblemAndPrimaryFigure setup)
    (hDisk : HasPhysicalCircularDiskGeometry setup)
    (hOrientation : SatisfiesFigureDerivedOrientation setup)
    (hUniformField : SatisfiesUniformElectricFieldModel setup)
    (hFluxLaw : SatisfiesPlanarElectricFluxLaw setup) :
    electricFluxInNewtonSquareMetersPerCoulomb setup.electricFlux =
        10 * Real.pi * Real.sqrt 3 ∧
      IsUniqueClosestDisplayedChoice setup recordedDatasetAnswer := by
  have hExact := inclinedDiskElectricFlux_exact setup hFigure hDisk
    hOrientation hUniformField hFluxLaw
  refine ⟨hExact, ?_⟩
  unfold IsUniqueClosestDisplayedChoice
  intro other hOther
  simp only [recordedDatasetAnswer, displayedElectricFlux]
  rw [hExact]
  have hSqrtLower : (43 / 25 : ℝ) < Real.sqrt 3 := by
    rw [Real.lt_sqrt (by norm_num)]
    norm_num
  have hSqrtUpper : Real.sqrt 3 < (7 / 4 : ℝ) := by
    rw [Real.sqrt_lt' (by norm_num)]
    norm_num
  have hFluxLower : 54 < 10 * Real.pi * Real.sqrt 3 := by
    have h₁ : (3.14 : ℝ) * (43 / 25) <
        Real.pi * (43 / 25) := by
      exact mul_lt_mul_of_pos_right Real.pi_gt_d2 (by norm_num)
    have h₂ : Real.pi * (43 / 25) <
        Real.pi * Real.sqrt 3 := by
      exact mul_lt_mul_of_pos_left hSqrtLower Real.pi_pos
    nlinarith
  have hFluxUpper : 10 * Real.pi * Real.sqrt 3 < 56 := by
    have h₁ : Real.pi * Real.sqrt 3 <
        (3.15 : ℝ) * Real.sqrt 3 := by
      exact mul_lt_mul_of_pos_right Real.pi_lt_d2 (Real.sqrt_pos.2 (by norm_num))
    have h₂ : (3.15 : ℝ) * Real.sqrt 3 <
        (3.15 : ℝ) * (7 / 4) := by
      exact mul_lt_mul_of_pos_left hSqrtUpper (by norm_num)
    nlinarith
  fin_cases other
  · rw [abs_of_pos (by linarith), abs_of_neg (by linarith)]
    linarith
  · exact (hOther rfl).elim
  · rw [abs_of_pos (by linarith), abs_of_neg (by linarith)]
    linarith
  · rw [abs_of_pos (by linarith), abs_of_neg (by linarith)]
    linarith

end PhyXMiniProblems.ProblemPhyXMini0998
