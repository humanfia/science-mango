import Mathlib
import Physlib.SpaceAndTime.Space.LengthUnit
import Physlib.Units.WithDim.Basic

/- USER: The assigned source file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0056

open Dimension

/-!
# Focal length of the pictured glass meniscus lens

The optical axis in the primary figure is horizontal.  For light propagating
from left to right, a spherical surface has negative oriented radius when its
center of curvature lies to the left of its vertex and positive oriented
radius when the center lies to the right.

Both marked centers of curvature lie to the left of their corresponding
surface vertices.  Thus the displayed radius magnitudes `R₁ = 40 cm` and
`R₂ = 20 cm` give the signed lensmaker radii `-40 cm` and `-20 cm`.

Radius magnitudes and focal length are unit-independent Physlib quantities.
Real numbers are used only for dimensionless refractive indices and for scalar
readouts in a specified unit.
-/

/-- A nonnegative physical length magnitude, independent of readout units. -/
abbrev LengthMagnitude : Type :=
  Dimensionful (WithDim L𝓭 NNReal)

/-- A signed physical length, independent of readout units. -/
abbrev SignedLengthQuantity : Type :=
  Dimensionful (WithDim L𝓭 ℝ)

/-- Unit choices whose length component is centimeters and whose others are SI. -/
def centimeterUnitChoices : UnitChoices :=
  { UnitChoices.SI with length := LengthUnit.centimeters }

/-- The scalar readout of a nonnegative physical length in a chosen unit system. -/
def lengthMagnitudeReadout
    (length : LengthMagnitude) (units : UnitChoices) : ℝ :=
  ((length units).val : ℝ)

/-- The scalar readout of a signed physical length in a chosen unit system. -/
def signedLengthReadout
    (length : SignedLengthQuantity) (units : UnitChoices) : ℝ :=
  (length units).val

/-- The scalar centimeter readout of a nonnegative physical length. -/
def lengthMagnitudeInCentimeters (length : LengthMagnitude) : ℝ :=
  lengthMagnitudeReadout length centimeterUnitChoices

/-- The scalar centimeter readout of a signed physical length. -/
def signedLengthInCentimeters (length : SignedLengthQuantity) : ℝ :=
  signedLengthReadout length centimeterUnitChoices

/-- The side of a surface vertex on which its center of curvature lies. -/
inductive AxialSide where
  | left
  | right
  deriving DecidableEq, Repr

/-- Propagation directions along the horizontal optical axis. -/
inductive PropagationDirection where
  | leftToRight
  | rightToLeft
  deriving DecidableEq, Repr

/-- The two radius labels printed in the lens diagram. -/
inductive SurfaceRadiusLabel where
  | R₁
  | R₂
  deriving DecidableEq, Repr

/-- Surface shapes used to describe the two faces of the pictured meniscus. -/
inductive SphericalSurfaceShape where
  | concave
  | convex
  deriving DecidableEq, Repr

/-- Profiles used to identify the pictured glass element. -/
inductive LensProfile where
  | meniscus
  | biconvex
  | biconcave
  deriving DecidableEq, Repr

/-- Optical media occurring in the thin-lens model. -/
inductive OpticalMedium where
  | ambientAir
  | glass
  deriving DecidableEq, Repr

/--
A spherical refracting surface retains its unsigned physical radius magnitude.
The sign used by the optical convention is recovered from the propagation
direction and the center-of-curvature side.
-/
structure SphericalLensSurface where
  figureLabel : SurfaceRadiusLabel
  shape : SphericalSurfaceShape
  radiusMagnitude : LengthMagnitude
  curvatureCenterSide : AxialSide

/--
The glass meniscus lens, its two labeled surfaces, material indices, incident
direction, and signed focal length.
-/
structure GlassMeniscusLens where
  profile : LensProfile
  lensMaterial : OpticalMedium
  surroundingMedium : OpticalMedium
  refractiveIndex : OpticalMedium → ℝ
  surface : SurfaceRadiusLabel → SphericalLensSurface
  incidentDirection : PropagationDirection
  signedFocalLength : SignedLengthQuantity

/--
The signed scalar radius readout in the coordinate direction of propagation.
A center on the incident side is negative and one on the outgoing side is
positive.
-/
def signedRadiusReadout
    (direction : PropagationDirection)
    (surface : SphericalLensSurface)
    (units : UnitChoices) : ℝ :=
  match direction, surface.curvatureCenterSide with
  | .leftToRight, .left => -lengthMagnitudeReadout surface.radiusMagnitude units
  | .leftToRight, .right => lengthMagnitudeReadout surface.radiusMagnitude units
  | .rightToLeft, .left => lengthMagnitudeReadout surface.radiusMagnitude units
  | .rightToLeft, .right => -lengthMagnitudeReadout surface.radiusMagnitude units

/-- The signed radius readout of a surface in centimeters. -/
def signedRadiusInCentimeters
    (direction : PropagationDirection) (surface : SphericalLensSurface) : ℝ :=
  signedRadiusReadout direction surface centimeterUnitChoices

/--
Data read from the primary image: lens profile and surface geometry, the two
radius labels and magnitudes, left-to-right propagation convention, and the
dimensionless glass refractive index `1.50`.  No focal-length value occurs
here.
-/
def MatchesFigureReadout (lens : GlassMeniscusLens) : Prop :=
  lens.profile = .meniscus ∧
    lens.lensMaterial = .glass ∧
    lens.surroundingMedium = .ambientAir ∧
    lens.incidentDirection = .leftToRight ∧
    lens.refractiveIndex .glass = (3 : ℝ) / 2 ∧
    (lens.surface .R₁).figureLabel = .R₁ ∧
    (lens.surface .R₁).shape = .concave ∧
    (lens.surface .R₁).curvatureCenterSide = .left ∧
    lengthMagnitudeInCentimeters (lens.surface .R₁).radiusMagnitude = 40 ∧
    (lens.surface .R₂).figureLabel = .R₂ ∧
    (lens.surface .R₂).shape = .convex ∧
    (lens.surface .R₂).curvatureCenterSide = .left ∧
    lengthMagnitudeInCentimeters (lens.surface .R₂).radiusMagnitude = 20

/--
The usual environmental idealization that the pictured lens is surrounded by
air of dimensionless refractive index one.
-/
def ModelsAmbientAir (lens : GlassMeniscusLens) : Prop :=
  lens.refractiveIndex lens.surroundingMedium = 1

/--
Positivity and optical-density conditions for ordinary glass in air.  These
conditions contain no value for the requested focal length.
-/
def HasPhysicalOpticalParameters (lens : GlassMeniscusLens) : Prop :=
  (∀ medium, 0 < lens.refractiveIndex medium) ∧
    lens.refractiveIndex lens.surroundingMedium <
      lens.refractiveIndex lens.lensMaterial ∧
    (∀ label,
      0 < lengthMagnitudeInCentimeters (lens.surface label).radiusMagnitude)

/--
The thin-lens lensmaker equation in a uniform surrounding medium,

`1 / f = (n_lens / n_medium - 1) * (1 / R₁ - 1 / R₂)`.

It is stated for every unit choice, so focal length and radii remain physical
lengths rather than being identified with bare centimeter scalars.  This is a
generic governing-law hypothesis and contains no numerical focal-length
answer.
-/
def ObeysThinLensmakerEquation (lens : GlassMeniscusLens) : Prop :=
  ∀ units : UnitChoices,
    1 / signedLengthReadout lens.signedFocalLength units =
      (lens.refractiveIndex lens.lensMaterial /
          lens.refractiveIndex lens.surroundingMedium - 1) *
        (1 / signedRadiusReadout lens.incidentDirection
              (lens.surface .R₁) units -
          1 / signedRadiusReadout lens.incidentDirection
              (lens.surface .R₂) units)

/-- Labels of the four multiple-choice answers displayed with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- The centimeter focal-length readout printed beside each answer choice. -/
def AnswerChoice.focalLengthInCentimeters : AnswerChoice → ℝ
  | .A => 14
  | .B => 86
  | .C => 80
  | .D => 74

/-- A lens's centimeter focal-length readout agrees with a displayed choice. -/
def MatchesAnswerChoice
    (lens : GlassMeniscusLens) (choice : AnswerChoice) : Prop :=
  signedLengthInCentimeters lens.signedFocalLength =
    choice.focalLengthInCentimeters

/--
The pictured center locations turn the two nonnegative radius magnitudes into
the signed lensmaker readouts `R₁ = -40 cm` and `R₂ = -20 cm`.
-/
lemma signed_radius_readouts_of_matches_figure
    (lens : GlassMeniscusLens)
    (h_figure : MatchesFigureReadout lens) :
    signedRadiusInCentimeters lens.incidentDirection (lens.surface .R₁) = -40 ∧
      signedRadiusInCentimeters lens.incidentDirection (lens.surface .R₂) = -20 := by
  rcases h_figure with
    ⟨_, _, _, hdir, _, _, _, hside1, hr1, _, _, hside2, hr2⟩
  constructor
  · simpa [signedRadiusInCentimeters, signedRadiusReadout, hdir, hside1,
      lengthMagnitudeInCentimeters] using congrArg Neg.neg hr1
  · simpa [signedRadiusInCentimeters, signedRadiusReadout, hdir, hside2,
      lengthMagnitudeInCentimeters] using congrArg Neg.neg hr2

/--
Specializing the general lensmaker law to the image data and ambient air gives
reciprocal focal length `1/80 cm⁻¹`.
-/
lemma reciprocal_focal_length_centimeters
    (lens : GlassMeniscusLens)
    (h_figure : MatchesFigureReadout lens)
    (h_air : ModelsAmbientAir lens)
    (h_lensmaker : ObeysThinLensmakerEquation lens) :
    1 / signedLengthInCentimeters lens.signedFocalLength = (1 : ℝ) / 80 := by
  rcases signed_radius_readouts_of_matches_figure lens h_figure with ⟨hr1, hr2⟩
  simp only [signedRadiusInCentimeters] at hr1 hr2
  rcases h_figure with ⟨_, h_material, _, _, h_glass, _⟩
  have h_eq := h_lensmaker centimeterUnitChoices
  rw [h_material, h_glass, h_air, hr1, hr2] at h_eq
  norm_num at h_eq
  simpa [signedLengthInCentimeters] using h_eq

/--
The pictured glass meniscus lens has signed focal length `80 cm`, answer
choice C.

This formalizes `thm:physics:phyx_mini_0056:target`.
-/
theorem focal_length_of_glass_meniscus_lens
    (lens : GlassMeniscusLens)
    (h_figure : MatchesFigureReadout lens)
    (h_air : ModelsAmbientAir lens)
    (h_physical : HasPhysicalOpticalParameters lens)
    (h_lensmaker : ObeysThinLensmakerEquation lens) :
    signedLengthInCentimeters lens.signedFocalLength = 80 ∧
      MatchesAnswerChoice lens .C := by
  have h_recip :=
    reciprocal_focal_length_centimeters lens h_figure h_air h_lensmaker
  have h_focal_ne : signedLengthInCentimeters lens.signedFocalLength ≠ 0 := by
    intro h_zero
    rw [h_zero] at h_recip
    norm_num at h_recip
  have h_focal : signedLengthInCentimeters lens.signedFocalLength = 80 := by
    field_simp [h_focal_ne] at h_recip
    linarith
  constructor
  · exact h_focal
  · simpa [MatchesAnswerChoice, AnswerChoice.focalLengthInCentimeters] using h_focal

end PhyXMiniProblems.ProblemPhyXMini0056
