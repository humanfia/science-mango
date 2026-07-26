import Mathlib
import Physlib.Units.WithDim.Basic

/- USER: The assigned Lean file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0477

open Dimension

/-!
# Refractive index of a solid transparent sphere

The narrated optics problem sends a parallel laser beam from air into a solid
transparent sphere.  In the paraxial model, refraction at the front spherical
surface forms an image at distance `v` satisfying

`v (n_sphere - n_air) = n_sphere R`.

The point image is at the back vertex, which is two radii from the front
vertex.  Lengths below are unit-independent Physlib quantities; refractive
indices are dimensionless real numbers.

The supplied raster does not depict this scenario.  It shows two piston/fluid
columns with mass, pressure, height, and area labels.  Those visible labels are
audited in a separate structure and are never used as optical premises.
-/

/-! ## Dimensionful optical lengths and geometry labels -/

/-- A signed physical length, represented coherently in every unit system. -/
abbrev OpticalLength : Type := Dimensionful (WithDim L𝓭 ℝ)

/-- Read a physical optical length in a specified system of units. -/
def lengthReadout (units : UnitChoices) (length : OpticalLength) : ℝ :=
  (length units).val

/-- Read a physical optical length in SI metres. -/
def lengthInMeters (length : OpticalLength) : ℝ :=
  lengthReadout UnitChoices.SI length

/-- The two homogeneous media encountered by an incident ray. -/
inductive OpticalMedium where
  | surroundingAir
  | sphereMaterial
  deriving DecidableEq, Repr

/-- The two boundary points of the sphere on the directed optical axis. -/
inductive SphereSurface where
  | front
  | back
  deriving DecidableEq, Repr

/-- Named axial points needed to interpret “the back of the sphere”. -/
inductive SphereAxisPoint where
  | frontVertex
  | center
  | backVertex
  | pointImage
  deriving DecidableEq, Repr

/-- The axial vertex associated with each spherical boundary surface. -/
def surfaceVertex : SphereSurface → SphereAxisPoint
  | .front => .frontVertex
  | .back => .backVertex

/-- Optical character of the body described in the problem. -/
inductive SphereBodyKind where
  | solidTransparent
  deriving DecidableEq, Repr

/-- The source named in the problem statement. -/
inductive LightSourceKind where
  | laser
  deriving DecidableEq, Repr

/-- Qualitative direction pattern of the incident geometrical-optics rays. -/
inductive IncidentRayPattern where
  | parallelToOpticalAxis
  deriving DecidableEq, Repr

/-- Approximation under which the spherical-surface imaging equation is used. -/
inductive OpticalApproximation where
  | paraxial
  deriving DecidableEq, Repr

/-! ## Provenance of the mismatched supplied raster -/

/-- The scene narrated by the problem and the unrelated scene in the raster. -/
inductive SourceScene where
  | laserIncidentOnTransparentSphere
  | twoPistonPressureComparison
  deriving DecidableEq, Repr

/-- Which source controls the optical theorem when prose and raster conflict. -/
inductive EvidencePolicy where
  | narratedOpticsControls
  deriving DecidableEq, Repr

/-- The left and right fluid columns visible in the supplied raster. -/
inductive PistonPanel where
  | left
  | right
  deriving DecidableEq, Repr

/-- Literal pressure symbols printed inside the two fluid columns. -/
inductive PressureSymbol where
  | P1
  | P2
  deriving DecidableEq, Repr

/-- Literal height symbols printed beside the two fluid columns. -/
inductive HeightSymbol where
  | h1
  | h2
  deriving DecidableEq, Repr

/-- The common literal cross-sectional-area symbol in the raster. -/
inductive AreaSymbol where
  | A
  deriving DecidableEq, Repr

/-!
An audit record for the actually supplied piston raster.  The real-valued
fields are explicitly unit-named scalar readouts rather than replacements for
physical mass or pressure types in the optical model.
-/
structure SuppliedRasterAudit where
  scene : SourceScene
  loadMassKilograms : PistonPanel → ℝ
  atmosphericPressureAtmospheres : ℝ
  pressureSymbol : PistonPanel → PressureSymbol
  heightSymbol : PistonPanel → HeightSymbol
  areaSymbol : PistonPanel → AreaSymbol
  rightPanelShowsPerson : Bool

/-!
Literal content of the inconsistent raster: `M = 20.0 kg` on the left,
an `80.0 kg` person on the right, atmospheric pressure `1 atm`, and labels
`P₁`, `P₂`, `h₁`, `h₂`, and the same area symbol `A`.
-/
structure RecordsProvidedFigureMismatch (audit : SuppliedRasterAudit) : Prop where
  piston_scene : audit.scene = .twoPistonPressureComparison
  left_load_mass_kilograms : audit.loadMassKilograms .left = 20
  right_person_mass_kilograms : audit.loadMassKilograms .right = 80
  atmospheric_pressure_atmospheres :
    audit.atmosphericPressureAtmospheres = 1
  left_pressure_label : audit.pressureSymbol .left = .P1
  right_pressure_label : audit.pressureSymbol .right = .P2
  left_height_label : audit.heightSymbol .left = .h1
  right_height_label : audit.heightSymbol .right = .h2
  left_area_label : audit.areaSymbol .left = .A
  right_area_label : audit.areaSymbol .right = .A
  person_is_drawn_on_right : audit.rightPanelShowsPerson = true

/-! ## Narrated optical setup, readouts, and laws -/

/-!
The physical state for the narrated sphere-imaging experiment.

The refractive index is a dimensionless readout indexed by the two physical
media.  Neither it nor the front-surface image distance is defined from the
recorded answer.
-/
structure TransparentSphereImagingSetup where
  bodyKind : SphereBodyKind
  sphereRadius : OpticalLength
  axialPosition : SphereAxisPoint → OpticalLength
  frontSurfaceImageDistance : OpticalLength
  refractiveIndex : OpticalMedium → ℝ
  lightSource : LightSourceKind
  incidentRayPattern : IncidentRayPattern
  approximation : OpticalApproximation
  narratedScene : SourceScene
  evidencePolicy : EvidencePolicy
  suppliedRaster : SuppliedRasterAudit

/-- Directed axial separation between two named points, in selected units. -/
def axialSeparationReadout
    (setup : TransparentSphereImagingSetup)
    (units : UnitChoices)
    (start finish : SphereAxisPoint) : ℝ :=
  lengthReadout units (setup.axialPosition finish) -
    lengthReadout units (setup.axialPosition start)

/-!
Qualitative facts in the narrated scenario.  The air calibration is the
standard dimensionless refractive-index readout implicit in the textbook
phrase “a sphere in air”.  No value is assigned to the sphere index.
-/
structure MatchesNarratedOpticsScenario
    (setup : TransparentSphereImagingSetup) : Prop where
  sphere_is_solid_and_transparent : setup.bodyKind = .solidTransparent
  source_is_laser : setup.lightSource = .laser
  incident_rays_are_parallel :
    setup.incidentRayPattern = .parallelToOpticalAxis
  narrated_scene_is_sphere_optics :
    setup.narratedScene = .laserIncidentOnTransparentSphere
  prose_controls_mismatched_raster :
    setup.evidencePolicy = .narratedOpticsControls
  surrounding_air_index : setup.refractiveIndex .surroundingAir = 1

/-!
Axial geometry and the given imaging condition.  The center and back vertex
are each one radius beyond the preceding point.  The paraxial image made by
the front surface coincides with the point at the back vertex.

These are geometry/observation premises; they do not assert the requested
refractive index.
-/
structure HasPointImageAtBackSurface
    (setup : TransparentSphereImagingSetup) : Prop where
  center_one_radius_from_front : ∀ units : UnitChoices,
    axialSeparationReadout setup units .frontVertex .center =
      lengthReadout units setup.sphereRadius
  back_one_radius_from_center : ∀ units : UnitChoices,
    axialSeparationReadout setup units .center .backVertex =
      lengthReadout units setup.sphereRadius
  point_image_is_back_vertex : ∀ units : UnitChoices,
    lengthReadout units (setup.axialPosition .pointImage) =
      lengthReadout units (setup.axialPosition .backVertex)
  image_distance_is_front_to_image_separation : ∀ units : UnitChoices,
    lengthReadout units setup.frontSurfaceImageDistance =
      axialSeparationReadout setup units .frontVertex .pointImage

/-- Positivity and optical-density conditions for the physical branch. -/
structure HasPhysicalSphereParameters
    (setup : TransparentSphereImagingSetup) : Prop where
  sphere_radius_positive : 0 < lengthInMeters setup.sphereRadius
  refractive_indices_positive :
    ∀ medium : OpticalMedium, 0 < setup.refractiveIndex medium
  sphere_is_optically_denser_than_air :
    setup.refractiveIndex .surroundingAir <
      setup.refractiveIndex .sphereMaterial

/-!
Gaussian refraction of a parallel paraxial beam at the front spherical
surface.  For air index `n₁`, sphere index `n₂`, image distance `v` measured
inside the sphere, and positive radius `R`, the law is

`v (n₂ - n₁) = n₂ R`.

It is required in every unit system and contains no numerical value of `n₂`.
-/
structure SatisfiesParallelRaySphericalRefractionLaw
    (setup : TransparentSphereImagingSetup) : Prop where
  paraxial_model : setup.approximation = .paraxial
  front_surface_refraction :
    setup.incidentRayPattern = .parallelToOpticalAxis →
      ∀ units : UnitChoices,
        lengthReadout units setup.frontSurfaceImageDistance *
            (setup.refractiveIndex .sphereMaterial -
              setup.refractiveIndex .surroundingAir) =
          setup.refractiveIndex .sphereMaterial *
            lengthReadout units setup.sphereRadius

/-!
The back-surface imaging condition and the sphere geometry make the front
surface image distance equal to the diameter.  This is a derived geometric
relation, not an assumption about the requested refractive index.
-/
lemma imageDistance_eq_two_mul_radius
    (setup : TransparentSphereImagingSetup)
    (_imageAtBack : HasPointImageAtBackSurface setup) :
    ∀ units : UnitChoices,
      lengthReadout units setup.frontSurfaceImageDistance =
        2 * lengthReadout units setup.sphereRadius := by
  intro units
  rw [_imageAtBack.image_distance_is_front_to_image_separation units]
  have hCenter := _imageAtBack.center_one_radius_from_front units
  have hBack := _imageAtBack.back_one_radius_from_center units
  have hPoint := _imageAtBack.point_image_is_back_vertex units
  unfold axialSeparationReadout at hCenter hBack ⊢
  linarith

/-! ## Displayed choices and target -/

/-- Labels of the four refractive-index choices printed in the question. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Dimensionless refractive-index readout printed beside each answer label. -/
def AnswerChoice.refractiveIndexReadout : AnswerChoice → ℝ
  | .A => 17 / 10
  | .B => 18 / 10
  | .C => 19 / 10
  | .D => 2

/-- Dataset metadata recording answer D; this is not a theorem premise. -/
def recordedAnswerChoice : AnswerChoice := .D

/-- The sphere's independent refractive index agrees with a displayed choice. -/
def MatchesAnswerChoice
    (setup : TransparentSphereImagingSetup) (choice : AnswerChoice) : Prop :=
  setup.refractiveIndex .sphereMaterial = choice.refractiveIndexReadout

/-!
The parallel-ray spherical-refraction law gives
`2 R (n - 1) = n R`.  Since `R > 0`, the sphere index is exactly `n = 2`.
-/
lemma sphereRefractiveIndex_eq_two
    (setup : TransparentSphereImagingSetup)
    (_scenario : MatchesNarratedOpticsScenario setup)
    (_imageAtBack : HasPointImageAtBackSurface setup)
    (_physical : HasPhysicalSphereParameters setup)
    (_refraction : SatisfiesParallelRaySphericalRefractionLaw setup) :
    setup.refractiveIndex .sphereMaterial = 2 := by
  have hRadius : 0 < lengthReadout UnitChoices.SI setup.sphereRadius := by
    simpa [lengthInMeters] using _physical.sphere_radius_positive
  have hLaw := _refraction.front_surface_refraction
    _scenario.incident_rays_are_parallel UnitChoices.SI
  rw [imageDistance_eq_two_mul_radius setup _imageAtBack UnitChoices.SI,
    _scenario.surrounding_air_index] at hLaw
  nlinarith

/-!
A parallel laser beam focused at the back of a solid transparent sphere in
air therefore requires refractive index `2.0`, displayed answer D.

This formalizes blueprint label `thm:physics:phyx_mini_0477:target`.
-/
theorem problem_phyx_mini_0477
    (setup : TransparentSphereImagingSetup)
    (_scenario : MatchesNarratedOpticsScenario setup)
    (_imageAtBack : HasPointImageAtBackSurface setup)
    (_figureMismatch : RecordsProvidedFigureMismatch setup.suppliedRaster)
    (_physical : HasPhysicalSphereParameters setup)
    (_refraction : SatisfiesParallelRaySphericalRefractionLaw setup) :
    MatchesAnswerChoice setup .D := by
  change setup.refractiveIndex .sphereMaterial = 2
  exact sphereRefractiveIndex_eq_two setup _scenario _imageAtBack _physical _refraction

end PhyXMiniProblems.ProblemPhyXMini0477
