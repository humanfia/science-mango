import Mathlib
import Physlib.Units.WithDim.Basic
import Physlib.SpaceAndTime.Space.LengthUnit

/- USER: The source file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0041

/-!
# Lateral magnification at a hemispherical refracting surface

A cylindrical glass rod is surrounded by water and has a hemispherical end.
The optical axis points from the water into the glass. Signed axial distances
are positive on the glass side of the surface vertex; hence the virtual image
`PPrime` drawn in the water has a negative signed image distance.

The Gaussian surface equation and the usual magnification formula are
first-order, near-axis consequences of exact Snell refraction. They are not
assumed here as globally exact laws. Instead, the setup includes an actual
near-axis ray family and a small-object image-height map. Exact Snell laws are
required in neighborhoods of the axis, while `HasDerivAt` records the relevant
first-order geometry and defines lateral magnification at zero object height.

Assumption/target split:

* governing laws: exact Snell refraction for the near-axis ray family and for
  chief rays, plus first-order geometric derivative relations at the axis;
* previous-part results: none;
* figure/data readouts: refractive indices `1.33` and `1.52`, object distance
  `8.00 cm`, hemispherical radius `2.00 cm`, and the ordering
  `PPrime < P < vertex < C` visible in the raster;
* current target conclusions: the paraxial image distance is `-64/3 cm`, the
  lateral magnification is `+7/3`, and this rounds to answer choice B.
-/

open Dimension Filter
open scoped Topology

/-! ## Dimensionful axial data and scalar readouts -/

/-- A signed, unit-independent physical length. -/
abbrev DimLength : Type := Dimensionful (WithDim L𝓭 ℝ)

/-- Unit choices in which lengths are read in centimeters and other units are SI. -/
def centimeterUnitChoices : UnitChoices :=
  { UnitChoices.SI with length := LengthUnit.centimeters }

/-- The signed scalar readout of a physical length in centimeters. -/
def lengthInCentimeters (length : DimLength) : ℝ :=
  (length centimeterUnitChoices).val

/-! ## Optical and figure roles -/

/-- The optical media on the incident and transmitted sides of the surface. -/
inductive OpticalMedium where
  | water
  | glassRod
  deriving DecidableEq, Repr

/-- Axial point labels appearing in the primary ray diagram. -/
inductive FigurePoint where
  /-- Object point `P`. -/
  | P
  /-- Paraxial virtual-image point `P'`. -/
  | PPrime
  /-- Vertex of the hemispherical glass surface. -/
  | vertex
  /-- Center of curvature `C`. -/
  | C
  deriving DecidableEq, Repr

/-!
The physical setup and its local ray observables.

The argument of each angle profile is the signed height, in centimeters, at
which a ray meets the surface. Angle values are dimensionless radian readouts.
The image-height map takes a small signed object height in centimeters to the
corresponding signed paraxial image height in centimeters. Its derivative at
zero is therefore dimensionless.

No field fixes the requested numerical magnification or the virtual-image
distance. The angle profiles and image-height map remain independent until
the governing-law hypotheses below are supplied.
-/
structure CylindricalGlassRodSetup where
  refractiveIndexDimensionless : OpticalMedium → ℝ
  axialPosition : FigurePoint → DimLength
  hemisphericalRadius : DimLength
  incidentRayAngleRadiansAtSurfaceHeightCm : ℝ → ℝ
  surfaceNormalAngleRadiansAtSurfaceHeightCm : ℝ → ℝ
  refractedRayAngleRadiansAtSurfaceHeightCm : ℝ → ℝ
  imageHeightCentimetersForObjectHeightCm : ℝ → ℝ
  lateralMagnification : ℝ

/-- The centimeter coordinate of a labelled point on the optical axis. -/
def axialCoordinateCentimeters
    (setup : CylindricalGlassRodSetup) (point : FigurePoint) : ℝ :=
  lengthInCentimeters (setup.axialPosition point)

/-- Positive object distance `s`, measured leftward from the vertex to `P`. -/
def objectDistanceCentimeters (setup : CylindricalGlassRodSetup) : ℝ :=
  axialCoordinateCentimeters setup .vertex -
    axialCoordinateCentimeters setup .P

/--
Signed paraxial image distance `s'`, negative for `P'` on the water side.
-/
def signedImageDistanceCentimeters (setup : CylindricalGlassRodSetup) : ℝ :=
  axialCoordinateCentimeters setup .PPrime -
    axialCoordinateCentimeters setup .vertex

/-- Signed vertex-to-center distance, positive toward the glass rod. -/
def signedRadiusCentimeters (setup : CylindricalGlassRodSetup) : ℝ :=
  axialCoordinateCentimeters setup .C -
    axialCoordinateCentimeters setup .vertex

/-! ## Source and primary-figure readouts -/

/-- The dimensionless refractive-index readouts stated in the problem. -/
structure HasStatedRefractiveIndices
    (setup : CylindricalGlassRodSetup) : Prop where
  waterIndex :
    setup.refractiveIndexDimensionless .water = (133 : ℝ) / 100
  glassRodIndex :
    setup.refractiveIndexDimensionless .glassRod = (152 : ℝ) / 100

/-- Positivity and nondegeneracy of the physical data used as denominators. -/
structure HasPhysicalSigns (setup : CylindricalGlassRodSetup) : Prop where
  refractiveIndexPositive :
    ∀ medium, 0 < setup.refractiveIndexDimensionless medium
  objectDistancePositive : 0 < objectDistanceCentimeters setup
  radiusPositive : 0 < lengthInCentimeters setup.hemisphericalRadius

/-!
Problem and figure readouts. The object `P` is `8.00 cm` left of the vertex,
the center `C` is one radius to its right, and that radius is `2.00 cm`.
The dashed backward extensions place the paraxial virtual image `P'` farther
left than `P`. No numerical image distance or magnification is read from the
figure.
-/
structure MatchesFigureReadout (setup : CylindricalGlassRodSetup) : Prop where
  objectDistance : objectDistanceCentimeters setup = 8
  radiusMagnitude : lengthInCentimeters setup.hemisphericalRadius = 2
  centerAtOneRadius :
    signedRadiusCentimeters setup =
      lengthInCentimeters setup.hemisphericalRadius
  virtualImageLeftOfObject :
    axialCoordinateCentimeters setup .PPrime <
      axialCoordinateCentimeters setup .P
  objectLeftOfVertex :
    axialCoordinateCentimeters setup .P <
      axialCoordinateCentimeters setup .vertex
  vertexLeftOfCenter :
    axialCoordinateCentimeters setup .vertex <
      axialCoordinateCentimeters setup .C

/-! ## Exact refraction and first-order near-axis geometry -/

/--
Exact Snell refraction for all sufficiently near-axis rays in the represented
ray family. Angles are measured from the positive optical axis, so incidence
and refraction angles relative to the surface normal are formed by subtraction.

The ray family is allowed to have spherical aberration away from the axis;
this predicate does not assert that all finite-height rays meet at `PPrime`.
-/
def ObeysExactSnellLawNearOpticalAxis
    (setup : CylindricalGlassRodSetup) : Prop :=
  ∀ᶠ rayHeightCentimeters : ℝ in 𝓝 0,
    setup.refractiveIndexDimensionless .water *
          Real.sin
            (setup.incidentRayAngleRadiansAtSurfaceHeightCm
                rayHeightCentimeters -
              setup.surfaceNormalAngleRadiansAtSurfaceHeightCm
                rayHeightCentimeters) =
      setup.refractiveIndexDimensionless .glassRod *
          Real.sin
            (setup.refractedRayAngleRadiansAtSurfaceHeightCm
                rayHeightCentimeters -
              setup.surfaceNormalAngleRadiansAtSurfaceHeightCm
                rayHeightCentimeters)

/-!
The first-order geometry of the near-axis ray family.

For surface height `h`, the incident direction has linear coefficient `1/s`.
The normal toward the center of curvature has coefficient `-1/R`. The
refracted direction has coefficient `-1/s'`, where `s'` is the signed
paraxial axis intercept. These are local derivative statements, not global
small-angle equalities and not the Gaussian surface equation itself.
-/
structure HasFirstOrderSphericalRayGeometry
    (setup : CylindricalGlassRodSetup) : Prop where
  incidentAxisAngle :
    setup.incidentRayAngleRadiansAtSurfaceHeightCm 0 = 0
  normalAxisAngle :
    setup.surfaceNormalAngleRadiansAtSurfaceHeightCm 0 = 0
  refractedAxisAngle :
    setup.refractedRayAngleRadiansAtSurfaceHeightCm 0 = 0
  incidentAngleDerivative :
    HasDerivAt setup.incidentRayAngleRadiansAtSurfaceHeightCm
      (1 / objectDistanceCentimeters setup) 0
  normalAngleDerivative :
    HasDerivAt setup.surfaceNormalAngleRadiansAtSurfaceHeightCm
      (-1 / lengthInCentimeters setup.hemisphericalRadius) 0
  refractedAngleDerivative :
    HasDerivAt setup.refractedRayAngleRadiansAtSurfaceHeightCm
      (-1 / signedImageDistanceCentimeters setup) 0

/-- Incident angle of the chief ray from an off-axis object to the vertex. -/
def chiefRayIncidentAngleRadians
    (setup : CylindricalGlassRodSetup)
    (objectHeightCentimeters : ℝ) : ℝ :=
  Real.arctan
    (-objectHeightCentimeters / objectDistanceCentimeters setup)

/--
Refracted chief-ray angle from the vertex toward the signed paraxial image
plane. For a virtual image, the ray is understood through backward extension.
-/
def chiefRayRefractedAngleRadians
    (setup : CylindricalGlassRodSetup)
    (objectHeightCentimeters : ℝ) : ℝ :=
  Real.arctan
    (setup.imageHeightCentimetersForObjectHeightCm objectHeightCentimeters /
      signedImageDistanceCentimeters setup)

/-- An on-axis object point maps to an on-axis image point. -/
def MapsOpticalAxisToItself (setup : CylindricalGlassRodSetup) : Prop :=
  setup.imageHeightCentimetersForObjectHeightCm 0 = 0

/--
Exact Snell refraction at the surface vertex for chief rays from all
sufficiently small object heights. The surface normal at the vertex is the
optical axis, so no normal-angle correction appears.
-/
def ObeysExactChiefRaySnellLawNearAxis
    (setup : CylindricalGlassRodSetup) : Prop :=
  ∀ᶠ objectHeightCentimeters : ℝ in 𝓝 0,
    setup.refractiveIndexDimensionless .water *
          Real.sin
            (chiefRayIncidentAngleRadians setup objectHeightCentimeters) =
      setup.refractiveIndexDimensionless .glassRod *
          Real.sin
            (chiefRayRefractedAngleRadians setup objectHeightCentimeters)

/--
The physical definition of paraxial lateral magnification: the derivative of
image height with respect to object height at the optical axis.
-/
def HasLateralMagnificationAtOpticalAxis
    (setup : CylindricalGlassRodSetup) : Prop :=
  HasDerivAt setup.imageHeightCentimetersForObjectHeightCm
    setup.lateralMagnification 0

/-! ## Answer-choice metadata -/

/-- Labels of the four multiple-choice answers in the source problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Dimensionless magnification printed for each answer choice. -/
def AnswerChoice.magnificationReadout : AnswerChoice → ℝ
  | .A => 856 / 1000
  | .B => 233 / 100
  | .C => 995 / 1000
  | .D => 1814 / 1000

/-- Half a unit in the last decimal place printed for an answer choice. -/
def AnswerChoice.displayTolerance : AnswerChoice → ℝ
  | .A => 1 / 2000
  | .B => 1 / 200
  | .C => 1 / 2000
  | .D => 1 / 2000

/-- The exact result rounds to the readout displayed for the chosen answer. -/
def MatchesAnswerChoice (actual : ℝ) (choice : AnswerChoice) : Prop :=
  |actual - choice.magnificationReadout| ≤ choice.displayTolerance

/-! ## Physical consequences -/

/--
Differentiating exact Snell refraction at the optical axis, using the three
first-order geometric relations, locates the paraxial virtual image at
`s' = -64/3 cm`. This is an intermediate consequence, not a figure readout.
-/
lemma signedImageDistanceCentimeters_eq_neg_sixty_four_thirds
    (setup : CylindricalGlassRodSetup)
    (h_indices : HasStatedRefractiveIndices setup)
    (h_figure : MatchesFigureReadout setup)
    (h_snell : ObeysExactSnellLawNearOpticalAxis setup)
    (h_geometry : HasFirstOrderSphericalRayGeometry setup) :
    signedImageDistanceCentimeters setup = -(64 : ℝ) / 3 := by
  have h_image_neg : signedImageDistanceCentimeters setup < 0 := by
    simp only [signedImageDistanceCentimeters]
    linarith [h_figure.virtualImageLeftOfObject,
      h_figure.objectLeftOfVertex]
  have h_image_ne : signedImageDistanceCentimeters setup ≠ 0 :=
    ne_of_lt h_image_neg
  have h_left :=
    ((h_geometry.incidentAngleDerivative.sub
      h_geometry.normalAngleDerivative).sin).const_mul
        (setup.refractiveIndexDimensionless .water)
  have h_right :=
    ((h_geometry.refractedAngleDerivative.sub
      h_geometry.normalAngleDerivative).sin).const_mul
        (setup.refractiveIndexDimensionless .glassRod)
  have h_snell_eq :
      (fun rayHeightCentimeters : ℝ =>
        setup.refractiveIndexDimensionless .water *
          Real.sin
            (setup.incidentRayAngleRadiansAtSurfaceHeightCm
                rayHeightCentimeters -
              setup.surfaceNormalAngleRadiansAtSurfaceHeightCm
                rayHeightCentimeters)) =ᶠ[𝓝 0]
      (fun rayHeightCentimeters : ℝ =>
        setup.refractiveIndexDimensionless .glassRod *
          Real.sin
            (setup.refractedRayAngleRadiansAtSurfaceHeightCm
                rayHeightCentimeters -
              setup.surfaceNormalAngleRadiansAtSurfaceHeightCm
                rayHeightCentimeters)) :=
    h_snell
  have h_derivatives := h_right.unique
    (h_left.congr_of_eventuallyEq h_snell_eq.symm)
  norm_num [h_geometry.incidentAxisAngle, h_geometry.normalAxisAngle,
    h_geometry.refractedAxisAngle, h_indices.waterIndex,
    h_indices.glassRodIndex, h_figure.objectDistance,
    h_figure.radiusMagnitude] at h_derivatives
  field_simp [h_image_ne] at h_derivatives
  nlinarith

/-
For refraction from water (`nₐ = 1.33`) into the hemispherical glass-rod end
(`n_b = 1.52`, `R = 2.00 cm`) with `P` at `s = 8.00 cm`, the paraxial
lateral magnification is exactly `+7/3`. It rounds to `+2.33`, answer B.

This formalizes `thm:physics:phyx_mini_0041:target`.
-/
theorem problem_phyx_mini_0041
    (setup : CylindricalGlassRodSetup)
    (h_indices : HasStatedRefractiveIndices setup)
    (h_signs : HasPhysicalSigns setup)
    (h_figure : MatchesFigureReadout setup)
    (h_snell : ObeysExactSnellLawNearOpticalAxis setup)
    (h_geometry : HasFirstOrderSphericalRayGeometry setup)
    (h_axis : MapsOpticalAxisToItself setup)
    (h_chiefRaySnell : ObeysExactChiefRaySnellLawNearAxis setup)
    (h_magnification : HasLateralMagnificationAtOpticalAxis setup) :
    setup.lateralMagnification = (7 : ℝ) / 3 ∧
      MatchesAnswerChoice setup.lateralMagnification .B := by
  have h_image :=
    signedImageDistanceCentimeters_eq_neg_sixty_four_thirds
      setup h_indices h_figure h_snell h_geometry
  change setup.imageHeightCentimetersForObjectHeightCm 0 = 0 at h_axis
  change HasDerivAt setup.imageHeightCentimetersForObjectHeightCm
    setup.lateralMagnification 0 at h_magnification
  have h_incident_angle :
      HasDerivAt (chiefRayIncidentAngleRadians setup)
        (-1 / objectDistanceCentimeters setup) 0 := by
    change HasDerivAt
      (fun x : ℝ => Real.arctan (-x / objectDistanceCentimeters setup))
      (-1 / objectDistanceCentimeters setup) 0
    simpa using ((hasDerivAt_id (0 : ℝ)).neg.div_const
      (objectDistanceCentimeters setup)).arctan
  have h_refracted_angle :
      HasDerivAt (chiefRayRefractedAngleRadians setup)
        (setup.lateralMagnification /
          signedImageDistanceCentimeters setup) 0 := by
    change HasDerivAt
      (fun x : ℝ => Real.arctan
        (setup.imageHeightCentimetersForObjectHeightCm x /
          signedImageDistanceCentimeters setup))
      (setup.lateralMagnification /
        signedImageDistanceCentimeters setup) 0
    simpa [h_axis] using (h_magnification.div_const
      (signedImageDistanceCentimeters setup)).arctan
  have h_left := h_incident_angle.sin.const_mul
    (setup.refractiveIndexDimensionless .water)
  have h_right := h_refracted_angle.sin.const_mul
    (setup.refractiveIndexDimensionless .glassRod)
  have h_chief_eq :
      (fun x : ℝ => setup.refractiveIndexDimensionless .water *
        Real.sin (chiefRayIncidentAngleRadians setup x)) =ᶠ[𝓝 0]
      (fun x : ℝ => setup.refractiveIndexDimensionless .glassRod *
        Real.sin (chiefRayRefractedAngleRadians setup x)) :=
    h_chiefRaySnell
  have h_derivatives := h_right.unique
    (h_left.congr_of_eventuallyEq h_chief_eq.symm)
  norm_num [chiefRayIncidentAngleRadians, chiefRayRefractedAngleRadians,
    h_axis, h_indices.waterIndex, h_indices.glassRodIndex,
    h_figure.objectDistance, h_image] at h_derivatives
  have h_mag : setup.lateralMagnification = (7 : ℝ) / 3 := by
    linarith
  refine ⟨h_mag, ?_⟩
  rw [h_mag]
  norm_num [MatchesAnswerChoice, AnswerChoice.magnificationReadout,
    AnswerChoice.displayTolerance, abs_of_nonneg]

end PhyXMiniProblems.ProblemPhyXMini0041
