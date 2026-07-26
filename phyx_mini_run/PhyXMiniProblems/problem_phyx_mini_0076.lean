import Mathlib.Data.Real.Basic
import Physlib.SpaceAndTime.Space.LengthUnit
import Physlib.Units.WithDim.Basic

namespace PhyXMiniProblems.ProblemPhyXMini0076

noncomputable section

open Dimension

/-!
# Parallel rays incident on a diverging-lens--concave-mirror system

The primary figure places a diverging thin lens to the left of a concave
spherical mirror.  Their vertex/center separation is `20 cm`.  Parallel rays
travel from left to right through the lens; after refraction they reach the
mirror as though they came from the lens's virtual focus.  The reflected rays
then meet in front of the mirror.

Axial coordinates and focal lengths are genuine Physlib dimensionful
quantities.  Real numbers occur only as signed readouts in a chosen unit and as
the scalar values printed in the multiple-choice problem.
-/

/-- A signed physical length, independent of the unit chosen to read it. -/
abbrev SignedLengthQuantity : Type := Dimensionful (WithDim L𝓭 ℝ)

/-- The scalar readout of a signed physical length in a specified unit system. -/
def signedLengthReadout
    (units : UnitChoices) (length : SignedLengthQuantity) : ℝ :=
  (length units).val

/-- Unit choices with centimeters selected as the length unit. -/
noncomputable def centimeterUnitChoices : UnitChoices :=
  { UnitChoices.SI with length := LengthUnit.centimeters }

/-- The signed centimeter readout of an axial length or position. -/
def signedLengthInCentimeters (length : SignedLengthQuantity) : ℝ :=
  signedLengthReadout centimeterUnitChoices length

/-- Distinguished points on the horizontal principal axis in the figure. -/
inductive OpticalAxisPoint where
  | divergingLensCenter
  | divergingLensVirtualFocus
  | concaveMirrorVertex
  | finalFocus
  deriving DecidableEq, Repr

/-- The two qualitative kinds of thin lens. -/
inductive ThinLensKind where
  | diverging
  | converging
  deriving DecidableEq, Repr

/-- The two qualitative kinds of spherical mirror. -/
inductive SphericalMirrorKind where
  | concave
  | convex
  deriving DecidableEq, Repr

/-- Propagation direction along the oriented horizontal optical axis. -/
inductive AxialPropagationDirection where
  | leftToRight
  | rightToLeft
  deriving DecidableEq, Repr

/-- Angular profile of a paraxial ray bundle relative to the principal axis. -/
inductive RayBundleProfile where
  | parallelToPrincipalAxis
  | diverging
  | converging
  deriving DecidableEq, Repr

/-- Qualitative information carried by the incident collection of rays. -/
structure IncidentRayBundle where
  propagationDirection : AxialPropagationDirection
  profile : RayBundleProfile
  deriving DecidableEq, Repr

/-- The optical approximation in which the imaging laws are asserted. -/
inductive OpticalApproximation where
  | exactRayTracing
  | thinParaxial
  deriving DecidableEq, Repr

/-- A thin lens with a signed focal length and a center on the optical axis. -/
structure ThinLens where
  kind : ThinLensKind
  center : OpticalAxisPoint
  signedFocalLength : SignedLengthQuantity

/-- A spherical mirror with a signed focal length and an axial vertex. -/
structure SphericalMirror where
  kind : SphericalMirrorKind
  vertex : OpticalAxisPoint
  signedFocalLength : SignedLengthQuantity

/--
The physical components, ray input, and labeled axial points of the source
figure.  The positions of the virtual source and requested final focus remain
unknown dimensionful quantities in this structure.
-/
structure LensMirrorSetup where
  axialPosition : OpticalAxisPoint → SignedLengthQuantity
  lens : ThinLens
  mirror : SphericalMirror
  incomingRays : IncidentRayBundle
  approximation : OpticalApproximation
  showsPrincipalAxis : Bool

/-- The coordinate readout of an axial label in an arbitrary unit system. -/
def axialPositionReadout
    (setup : LensMirrorSetup) (units : UnitChoices)
    (point : OpticalAxisPoint) : ℝ :=
  signedLengthReadout units (setup.axialPosition point)

/-- The signed focal-length readout of the diverging lens. -/
def lensFocalLengthReadout
    (setup : LensMirrorSetup) (units : UnitChoices) : ℝ :=
  signedLengthReadout units setup.lens.signedFocalLength

/-- The signed focal-length readout of the spherical mirror. -/
def mirrorFocalLengthReadout
    (setup : LensMirrorSetup) (units : UnitChoices) : ℝ :=
  signedLengthReadout units setup.mirror.signedFocalLength

/--
The mirror's object distance: mirror vertex minus the virtual-source
coordinate.  It is positive for the real object seen by the pictured mirror.
-/
def mirrorObjectDistanceReadout
    (setup : LensMirrorSetup) (units : UnitChoices) : ℝ :=
  axialPositionReadout setup units setup.mirror.vertex -
    axialPositionReadout setup units .divergingLensVirtualFocus

/--
The mirror-to-focus distance in front of the mirror.  Since the axis points to
the right, this is mirror vertex minus final-focus coordinate.
-/
def mirrorImageDistanceReadout
    (setup : LensMirrorSetup) (units : UnitChoices) : ℝ :=
  axialPositionReadout setup units setup.mirror.vertex -
    axialPositionReadout setup units .finalFocus

/-- The mirror's physical object-distance readout in centimeters. -/
def mirrorObjectDistanceInCentimeters (setup : LensMirrorSetup) : ℝ :=
  mirrorObjectDistanceReadout setup centimeterUnitChoices

/-- The requested mirror-to-focus distance, read in centimeters. -/
def mirrorImageDistanceInCentimeters (setup : LensMirrorSetup) : ℝ :=
  mirrorImageDistanceReadout setup centimeterUnitChoices

/-- The Gaussian focal-length sign agrees with the optical component kind. -/
def HasFocalSignsConsistentWithKinds (setup : LensMirrorSetup) : Prop :=
  (match setup.lens.kind with
    | .diverging => lensFocalLengthReadout setup centimeterUnitChoices < 0
    | .converging => 0 < lensFocalLengthReadout setup centimeterUnitChoices) ∧
  (match setup.mirror.kind with
    | .concave => 0 < mirrorFocalLengthReadout setup centimeterUnitChoices
    | .convex => mirrorFocalLengthReadout setup centimeterUnitChoices < 0)

/--
Qualitative component and ray roles supplied by the primary image.  No
position or distance for the requested final focus is included here.
-/
structure HasPhysicalLensMirrorConfiguration (setup : LensMirrorSetup) : Prop where
  lens_is_diverging : setup.lens.kind = .diverging
  mirror_is_concave : setup.mirror.kind = .concave
  lens_center_label : setup.lens.center = .divergingLensCenter
  mirror_vertex_label : setup.mirror.vertex = .concaveMirrorVertex
  rays_travel_from_left :
    setup.incomingRays.propagationDirection = .leftToRight
  incident_rays_are_parallel :
    setup.incomingRays.profile = .parallelToPrincipalAxis
  focal_signs : HasFocalSignsConsistentWithKinds setup
  lens_precedes_mirror :
    axialPositionReadout setup centimeterUnitChoices setup.lens.center <
      axialPositionReadout setup centimeterUnitChoices setup.mirror.vertex

/--
Numerical and graphical readouts in the primary image: `f₁ = -10 cm`,
`f₂ = 10 cm`, a `20 cm` component separation, and the principal axis.  The
unknown virtual-source and final-focus positions are deliberately absent.
-/
structure MatchesFigureReadouts (setup : LensMirrorSetup) : Prop where
  diverging_lens_focal_readout :
    lensFocalLengthReadout setup centimeterUnitChoices = -10
  concave_mirror_focal_readout :
    mirrorFocalLengthReadout setup centimeterUnitChoices = 10
  component_separation_readout :
    axialPositionReadout setup centimeterUnitChoices setup.mirror.vertex -
        axialPositionReadout setup centimeterUnitChoices setup.lens.center = 20
  principal_axis_is_shown : setup.showsPrincipalAxis = true

/--
The governing paraxial laws for the lens--mirror sequence.

Parallel rays leaving a diverging lens behave as if emitted from the lens's
incident-side focal point.  The mirror law is the Gaussian equation
`1/f = 1/p + 1/q`, written in the division-free, dimensionally homogeneous
form `f * (p + q) = p * q`.  Both laws are required in every unit system and
neither supplies the requested `15 cm` result.
-/
structure SatisfiesParaxialLensMirrorLaws (setup : LensMirrorSetup) : Prop where
  uses_thin_paraxial_approximation :
    setup.approximation = .thinParaxial
  diverging_lens_parallel_ray_law :
    ∀ units : UnitChoices,
      axialPositionReadout setup units .divergingLensVirtualFocus =
        axialPositionReadout setup units setup.lens.center +
          lensFocalLengthReadout setup units
  concave_mirror_equation :
    ∀ units : UnitChoices,
      mirrorFocalLengthReadout setup units *
          (mirrorObjectDistanceReadout setup units +
            mirrorImageDistanceReadout setup units) =
        mirrorObjectDistanceReadout setup units *
          mirrorImageDistanceReadout setup units

/-- Labels of the four displayed multiple-choice answers. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- The focus distance in centimeters printed beside each answer choice. -/
def AnswerChoice.distanceInCentimeters : AnswerChoice → ℝ
  | .A => 14
  | .B => 26
  | .C => 15
  | .D => 39 / 2

/-- Exact agreement between the derived focus distance and a displayed choice. -/
def MatchesAnswer (setup : LensMirrorSetup) (choice : AnswerChoice) : Prop :=
  mirrorImageDistanceInCentimeters setup = choice.distanceInCentimeters

/--
The lens's virtual source is `10 cm` left of the lens and hence `30 cm` in
front of the mirror.
-/
lemma mirrorObjectDistance_eq_thirty
    (setup : LensMirrorSetup)
    (h_figure : MatchesFigureReadouts setup)
    (h_laws : SatisfiesParaxialLensMirrorLaws setup) :
    mirrorObjectDistanceInCentimeters setup = 30 := by
  have h_virtual :=
    h_laws.diverging_lens_parallel_ray_law centimeterUnitChoices
  rw [mirrorObjectDistanceInCentimeters, mirrorObjectDistanceReadout, h_virtual]
  linarith [h_figure.diverging_lens_focal_readout,
    h_figure.component_separation_readout]

/--
The concave mirror has focal length `10 cm` and object distance `30 cm`.
Its Gaussian mirror equation therefore places the real focus `15 cm` in front
of the mirror, agreeing with answer choice C.

This formalizes `thm:physics:phyx_mini_0076:target`.
-/
theorem problem_phyx_mini_0076
    (setup : LensMirrorSetup)
    (h_physical : HasPhysicalLensMirrorConfiguration setup)
    (h_figure : MatchesFigureReadouts setup)
    (h_laws : SatisfiesParaxialLensMirrorLaws setup) :
    mirrorImageDistanceInCentimeters setup = 15 ∧
      MatchesAnswer setup .C := by
  have h_object := mirrorObjectDistance_eq_thirty setup h_figure h_laws
  have h_mirror := h_laws.concave_mirror_equation centimeterUnitChoices
  rw [h_figure.concave_mirror_focal_readout] at h_mirror
  change mirrorObjectDistanceReadout setup centimeterUnitChoices = 30 at h_object
  rw [h_object] at h_mirror
  have h_image : mirrorImageDistanceInCentimeters setup = 15 := by
    change mirrorImageDistanceReadout setup centimeterUnitChoices = 15
    nlinarith
  exact ⟨h_image, by simpa [MatchesAnswer, AnswerChoice.distanceInCentimeters] using h_image⟩

end

end PhyXMiniProblems.ProblemPhyXMini0076
