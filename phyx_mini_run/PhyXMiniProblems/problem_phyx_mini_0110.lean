import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Order.Bounds.Defs
import Mathlib.Order.Interval.Set.Defs
import Physlib.Units.WithDim.Basic

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0110

/-!
# Largest image made by a quinoline-filled hemispherical tube

The coordinate convention follows the source figure.  The vertex of the
convex cap has axial coordinate zero, the liquid and LED display lie below
it, and a real image lies above it.  Thus the figure labels `s` and `s'` are
positive physical lengths on opposite sides of the refracting surface, while
`H` is the physical bottom-to-vertex height of the tube.

Length-valued fields use Physlib's unit-independent `Dimensionful` type.
Real numbers are used only for dimensionless refractive indices and for
explicit scalar coordinate/readout values in centimeters.

Exact vector Snell refraction, rather than a global Gaussian/paraxial
equality, determines whether a finite-aperture image is physically attainable.
The familiar paraxial angular relation is retained only through a derivative
at the axial ray, so the first-order approximation is explicitly local.
-/

/-! ## Physical quantities and figure labels -/

/-- A signed physical length, independent of the units used to read it. -/
abbrev OpticalLength : Type := Dimensionful (WithDim Dimension.L𝓭 ℝ)

/-- Scalar readout of a physical length in the selected system of units. -/
def lengthReadout (units : UnitChoices) (length : OpticalLength) : ℝ :=
  (length units).val

/-- Scalar centimeter readout, obtained from the SI meter readout. -/
def centimeterReadout (length : OpticalLength) : ℝ :=
  100 * lengthReadout UnitChoices.SI length

/-- The two homogeneous media separated by the convex top surface. -/
inductive OpticalMedium where
  | quinoline
  | ambientAir
  deriving DecidableEq, Repr

/-- The shape of the long transparent body shown in the figure. -/
inductive TubeBodyShape where
  | circularCylinderWithFlatBottom
  deriving DecidableEq, Repr

/-- The shape of the tube's upper liquid--air interface. -/
inductive TopSurfaceShape where
  | convexHemisphere
  deriving DecidableEq, Repr

/-- Optical character of the tube wall stated in the scenario. -/
inductive TubeWallOpticalCharacter where
  | transparent
  deriving DecidableEq, Repr

/-- The luminous pattern shown both on the display and in its real image. -/
inductive DisplayPattern where
  | circledLetterA
  deriving DecidableEq, Repr

/--
Fixed physical data of the tube, liquid, and circular LED display.

`tubeHeightH` is retained because it is the label `H` in the primary figure,
even though the recorded largest diameter does not mention it explicitly.
-/
structure QuinolineTubeSetup where
  bodyShape : TubeBodyShape
  topSurfaceShape : TopSurfaceShape
  wallOpticalCharacter : TubeWallOpticalCharacter
  displayPattern : DisplayPattern
  refractiveIndex : OpticalMedium → ℝ
  tubeRadiusR : OpticalLength
  capRadiusOfCurvature : OpticalLength
  tubeHeightH : OpticalLength
  displayDiameter : OpticalLength

/--
One setting of the variable-height platform and the resulting real image.
The fields `objectDistanceS` and `imageDistanceSPrime` are precisely the
figure labels `s` and `s'`.
-/
structure AxialImageConfiguration where
  platformHeightAboveBottom : OpticalLength
  objectDistanceS : OpticalLength
  imageDistanceSPrime : OpticalLength
  imageDiameter : OpticalLength

/-! ## Figure/data readouts and physical branch -/

/--
Numerical data and geometry stated in the problem or read from the figure.
The equality of cap curvature radius and tube radius records that the convex
top is a hemisphere.  No image distance or image diameter is fixed here.
-/
structure MatchesProblemAndFigureReadouts
    (setup : QuinolineTubeSetup) : Prop where
  cylindrical_body :
    setup.bodyShape = .circularCylinderWithFlatBottom
  hemispherical_top : setup.topSurfaceShape = .convexHemisphere
  transparent_wall : setup.wallOpticalCharacter = .transparent
  circled_letter_A : setup.displayPattern = .circledLetterA
  quinoline_index :
    setup.refractiveIndex .quinoline = (1627 : ℝ) / 1000
  ambient_air_index : setup.refractiveIndex .ambientAir = 1
  tube_radius_cm : centimeterReadout setup.tubeRadiusR = (3 : ℝ) / 2
  display_diameter_cm : centimeterReadout setup.displayDiameter = 1
  cap_radius_is_tube_radius :
    setup.capRadiusOfCurvature = setup.tubeRadiusR

/--
Positivity, optical-density ordering, and the requirement that the display
fits inside the cylindrical tube.  The unspecified figure height `H` remains
a positive physical parameter.
-/
structure HasPhysicalTubeParameters (setup : QuinolineTubeSetup) : Prop where
  refractive_indices_positive :
    ∀ medium : OpticalMedium, 0 < setup.refractiveIndex medium
  air_less_refractive_than_quinoline :
    setup.refractiveIndex .ambientAir < setup.refractiveIndex .quinoline
  tube_radius_positive : 0 < centimeterReadout setup.tubeRadiusR
  cap_radius_positive : 0 < centimeterReadout setup.capRadiusOfCurvature
  tube_height_positive : 0 < centimeterReadout setup.tubeHeightH
  display_diameter_positive : 0 < centimeterReadout setup.displayDiameter
  display_fits_inside_tube :
    centimeterReadout setup.displayDiameter <
      2 * centimeterReadout setup.tubeRadiusR

/--
The platform is inside the tube, the object-to-vertex distance `s` and the
real-image height `s'` are positive, and platform height plus `s` equals the
figure height `H`.  The last equation is required in every unit system.
-/
structure HasDepictedAxialPlacement
    (setup : QuinolineTubeSetup) (image : AxialImageConfiguration) : Prop where
  platform_not_below_bottom :
    0 ≤ centimeterReadout image.platformHeightAboveBottom
  platform_below_cap_vertex :
    centimeterReadout image.platformHeightAboveBottom <
      centimeterReadout setup.tubeHeightH
  object_distance_positive : 0 < centimeterReadout image.objectDistanceS
  image_above_cap : 0 < centimeterReadout image.imageDistanceSPrime
  image_diameter_positive : 0 < centimeterReadout image.imageDiameter
  height_decomposition :
    ∀ units : UnitChoices,
      lengthReadout units image.platformHeightAboveBottom +
          lengthReadout units image.objectDistanceS =
        lengthReadout units setup.tubeHeightH

/-! ## Exact ray laws and the local paraxial contract -/

/--
The exact Snell relation has a differentiable transmitted-angle branch near
the axial ray.  The derivative `n_quinoline / n_air` is the paraxial angular
law, but it is asserted only at zero incidence.  The neighborhood equations
continue to use `sin`, so no first-order approximation is globalized into an
exact law at finite angle.
-/
def HasLocalAxialSnellLinearization
    (setup : QuinolineTubeSetup) : Prop :=
  ∃ angularNeighborhood : ℝ, ∃ transmittedAngle : ℝ → ℝ,
    0 < angularNeighborhood ∧
      angularNeighborhood ≤ Real.pi / 2 ∧
      transmittedAngle 0 = 0 ∧
      (∀ incidentAngle : ℝ, |incidentAngle| < angularNeighborhood →
        setup.refractiveIndex .quinoline * Real.sin incidentAngle =
          setup.refractiveIndex .ambientAir *
            Real.sin (transmittedAngle incidentAngle)) ∧
      (∀ incidentAngle : ℝ, |incidentAngle| < angularNeighborhood →
        |transmittedAngle incidentAngle| < Real.pi / 2) ∧
      HasDerivAt transmittedAngle
        (setup.refractiveIndex .quinoline /
          setup.refractiveIndex .ambientAir) 0

/--
A meridional ray, represented by centimeter coordinates.  The cap vertex is
at axial coordinate zero; the cap center is one radius below it.  Straight
segments join the source point to the surface point and then to the target
point, so only their three transverse/axial endpoints need to be stored.
-/
structure MeridionalCapRay where
  sourceTransverseCm : ℝ
  surfaceTransverseCm : ℝ
  surfaceAxialCm : ℝ
  targetTransverseCm : ℝ

/-- Euclidean norm of a two-dimensional scalar coordinate vector. -/
def norm2D (x z : ℝ) : ℝ :=
  Real.sqrt (x ^ 2 + z ^ 2)

/-- Oriented two-dimensional cross product. -/
def cross2D (ax az bx bz : ℝ) : ℝ :=
  ax * bz - az * bx

/-- Two-dimensional dot product. -/
def dot2D (ax az bx bz : ℝ) : ℝ :=
  ax * bx + az * bz

/-- The ray's surface point lies on the finite upper hemispherical cap. -/
def HitsFiniteHemisphericalCap
    (setup : QuinolineTubeSetup) (ray : MeridionalCapRay) : Prop :=
  let radius := centimeterReadout setup.capRadiusOfCurvature
  ray.surfaceTransverseCm ^ 2 +
        (ray.surfaceAxialCm + radius) ^ 2 = radius ^ 2 ∧
    ray.surfaceAxialCm ∈ Set.Icc (-radius) 0

/--
The source lies on the circular display and the target is the corresponding
point of an inverted circular image.  Cross multiplication retains the
physical diameter roles and avoids defining a magnification by division.
-/
def ConnectsDisplayPointToImagePoint
    (setup : QuinolineTubeSetup)
    (image : AxialImageConfiguration)
    (ray : MeridionalCapRay) : Prop :=
  let objectDiameter := centimeterReadout setup.displayDiameter
  let realImageDiameter := centimeterReadout image.imageDiameter
  ray.sourceTransverseCm ∈
      Set.Icc (-(objectDiameter / 2)) (objectDiameter / 2) ∧
    ray.targetTransverseCm * objectDiameter =
      -(realImageDiameter * ray.sourceTransverseCm)

/--
Exact vector form of Snell's law at the ray's point on the cap.  The incident
vector runs from `(source, -s)` to the cap, the transmitted vector runs from
the cap to `(target, s')`, and the outward normal runs from the hemispherical
center to the cap point.  Positive dot products select outward-propagating
rays; equality of index-weighted tangential unit-vector components is Snell's
law without introducing scalar angle aliases.
-/
def ObeysSnellLawAtHemisphericalCap
    (setup : QuinolineTubeSetup)
    (image : AxialImageConfiguration)
    (ray : MeridionalCapRay) : Prop :=
  let incidentX := ray.surfaceTransverseCm - ray.sourceTransverseCm
  let incidentZ :=
    ray.surfaceAxialCm + centimeterReadout image.objectDistanceS
  let transmittedX := ray.targetTransverseCm - ray.surfaceTransverseCm
  let transmittedZ :=
    centimeterReadout image.imageDistanceSPrime - ray.surfaceAxialCm
  let normalX := ray.surfaceTransverseCm
  let normalZ :=
    ray.surfaceAxialCm + centimeterReadout setup.capRadiusOfCurvature
  let incidentNorm := norm2D incidentX incidentZ
  let transmittedNorm := norm2D transmittedX transmittedZ
  0 < incidentNorm ∧
    0 < transmittedNorm ∧
    0 < dot2D incidentX incidentZ normalX normalZ ∧
    0 < dot2D transmittedX transmittedZ normalX normalZ ∧
    setup.refractiveIndex .quinoline *
          cross2D normalX normalZ incidentX incidentZ /
          incidentNorm =
      setup.refractiveIndex .ambientAir *
        cross2D normalX normalZ transmittedX transmittedZ /
        transmittedNorm

/-- One physically outgoing display-to-image ray through the finite cap. -/
def IsPhysicalCapRay
    (setup : QuinolineTubeSetup)
    (image : AxialImageConfiguration)
    (ray : MeridionalCapRay) : Prop :=
  HitsFiniteHemisphericalCap setup ray ∧
    ConnectsDisplayPointToImagePoint setup image ray ∧
    ObeysSnellLawAtHemisphericalCap setup image ray

/--
Every meridional point of the display is focused to its corresponding image
point by two rays meeting distinct points of the finite cap.  This separates
the aperture/sharp-image criterion implicit in the phrase "a real image is
formed" from both Gaussian imaging and the requested maximum.
-/
def FormsResolvedRealImageThroughFiniteCap
    (setup : QuinolineTubeSetup) (image : AxialImageConfiguration) : Prop :=
  let objectDiameter := centimeterReadout setup.displayDiameter
  ∀ sourceX : ℝ,
    sourceX ∈ Set.Icc (-(objectDiameter / 2)) (objectDiameter / 2) →
      ∃ rayOne rayTwo : MeridionalCapRay,
        rayOne.sourceTransverseCm = sourceX ∧
          rayTwo.sourceTransverseCm = sourceX ∧
          (rayOne.surfaceTransverseCm ≠ rayTwo.surfaceTransverseCm ∨
            rayOne.surfaceAxialCm ≠ rayTwo.surfaceAxialCm) ∧
          IsPhysicalCapRay setup image rayOne ∧
          IsPhysicalCapRay setup image rayTwo

/-! ## Attainable diameters and the largest-image target -/

/--
A configuration is physically attainable when it obeys the depicted axial
layout and the exact finite-cap Snell-ray focusing criterion.  The local
derivative contract records why paraxial reasoning is available near the axis,
without treating it as an exact finite-angle equation.  No largest diameter or
answer-choice value is built into this predicate.
-/
def IsAttainableRealImage
    (setup : QuinolineTubeSetup) (image : AxialImageConfiguration) : Prop :=
  HasLocalAxialSnellLinearization setup ∧
    HasDepictedAxialPlacement setup image ∧
    FormsResolvedRealImageThroughFiniteCap setup image

/-- The scenario's assertion that at least one real image is formed above the cap. -/
def AdmitsSomeRealImage (setup : QuinolineTubeSetup) : Prop :=
  ∃ image : AxialImageConfiguration, IsAttainableRealImage setup image

/-- The set of centimeter readouts of all physically attainable image diameters. -/
def attainableImageDiametersCm (setup : QuinolineTubeSetup) : Set ℝ :=
  {diameterCm | ∃ image : AxialImageConfiguration,
    IsAttainableRealImage setup image ∧
      diameterCm = centimeterReadout image.imageDiameter}

/-- Labels printed beside the four multiple-choice answers. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Image-diameter centimeter readout printed beside each answer choice. -/
def answerDiameterCm : AnswerChoice → ℝ
  | .A => 241 / 10
  | .B => 238 / 10
  | .C => 227 / 10
  | .D => 253 / 10

/--
An exact centimeter value rounds to the displayed value at one decimal place.
The half-open interval makes the convention unambiguous at half-tenth ties.
-/
def RoundsToDisplayedTenthCm (actualCm displayedCm : ℝ) : Prop :=
  displayedCm - 1 / 20 ≤ actualCm ∧ actualCm < displayedCm + 1 / 20

/-- A printed choice is correct when a greatest attainable diameter rounds to it. -/
def IsCorrectRoundedAnswerChoice
    (setup : QuinolineTubeSetup) (choice : AnswerChoice) : Prop :=
  ∃ largestDiameterCm : ℝ,
    IsGreatest (attainableImageDiametersCm setup) largestDiameterCm ∧
      RoundsToDisplayedTenthCm largestDiameterCm (answerDiameterCm choice)

/-- Exactly one of the four displayed choices is correct after rounding. -/
def IsUniqueCorrectRoundedAnswerChoice
    (setup : QuinolineTubeSetup) (choice : AnswerChoice) : Prop :=
  IsCorrectRoundedAnswerChoice setup choice ∧
    ∀ other : AnswerChoice, other ≠ choice →
      ¬ IsCorrectRoundedAnswerChoice setup other

/--
For the `1.50 cm`-radius hemispherical quinoline tube (`n = 1.627`) and the
`1.00 cm` circular display, the exact greatest attainable real-image diameter
rounds to `24.1 cm` at the precision of the choices, uniquely selecting answer
A.  The conclusion does not identify the exact maximum with the rounded
decimal printed by the source.

This formalizes `thm:physics:phyx_mini_0110:target`.
-/
theorem problem_phyx_mini_0110
    (setup : QuinolineTubeSetup)
    (_readouts : MatchesProblemAndFigureReadouts setup)
    (_physical : HasPhysicalTubeParameters setup)
    (_localSnell : HasLocalAxialSnellLinearization setup)
    (_realImageExists : AdmitsSomeRealImage setup) :
    ∃ largestDiameterCm : ℝ,
      IsGreatest (attainableImageDiametersCm setup) largestDiameterCm ∧
        RoundsToDisplayedTenthCm largestDiameterCm (241 / 10) ∧
        IsUniqueCorrectRoundedAnswerChoice setup .A := by
  rcases _realImageExists with ⟨image, h_image⟩
  have h_attainable_nonempty :
      (attainableImageDiametersCm setup).Nonempty := by
    refine ⟨centimeterReadout image.imageDiameter, ?_⟩
    exact ⟨image, h_image, rfl⟩
  have h_maximum_rounds_to_A :
      ∃ largestDiameterCm : ℝ,
        IsGreatest (attainableImageDiametersCm setup) largestDiameterCm ∧
          RoundsToDisplayedTenthCm largestDiameterCm (241 / 10) := by
    /-
    `h_attainable_nonempty` supplies an attainable diameter, but the current
    hypotheses do not connect the derivative in `_localSnell` to a
    differentiable family of the finite-cap rays in `h_image`.  Consequently
    they provide neither the planned paraxial image equations nor an attained
    upper bound for `attainableImageDiametersCm setup`.
    -/
    sorry
  rcases h_maximum_rounds_to_A with
    ⟨largestDiameterCm, h_largest, h_rounds_to_A⟩
  refine ⟨largestDiameterCm, h_largest, h_rounds_to_A, ?_⟩
  constructor
  · exact ⟨largestDiameterCm, h_largest, by
      simpa [answerDiameterCm] using h_rounds_to_A⟩
  · intro other h_other_ne_A h_other_correct
    rcases h_other_correct with
      ⟨otherLargestDiameterCm, h_other_largest, h_other_rounds⟩
    have h_largest_eq :
        otherLargestDiameterCm = largestDiameterCm := by
      apply le_antisymm
      · exact h_largest.2 h_other_largest.1
      · exact h_other_largest.2 h_largest.1
    subst otherLargestDiameterCm
    cases other with
    | A => exact h_other_ne_A rfl
    | B =>
        norm_num [RoundsToDisplayedTenthCm, answerDiameterCm] at h_rounds_to_A h_other_rounds
        linarith
    | C =>
        norm_num [RoundsToDisplayedTenthCm, answerDiameterCm] at h_rounds_to_A h_other_rounds
        linarith
    | D =>
        norm_num [RoundsToDisplayedTenthCm, answerDiameterCm] at h_rounds_to_A h_other_rounds
        linarith

end PhyXMiniProblems.ProblemPhyXMini0110
