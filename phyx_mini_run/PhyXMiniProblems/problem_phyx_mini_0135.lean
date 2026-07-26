import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Physlib.SpaceAndTime.Space.LengthUnit
import Physlib.Units.WithDim.Basic

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0135

/-!
# Flashlight beam refracting into a pool

The diagram is read in a vertical cross-section through the flashlight beam.
The coordinate origin for horizontal distances is the bottom of the pool wall
directly below the watchman's foot.  Lengths are dimensionful quantities;
only their explicitly named SI-meter readouts are real numbers.  Refractive
indices and normal-referenced radian angle readouts are dimensionless.
-/

open Dimension

/-- A nonnegative physical quantity carrying the dimension of length. -/
abbrev LengthMagnitude : Type := Dimensionful (WithDim L𝓭 NNReal)

/-- The real-valued readout of a physical length magnitude in SI meters. -/
def lengthInMeters (length : LengthMagnitude) : ℝ :=
  ((length UnitChoices.SI).val : ℝ)

/-- The homogeneous optical media on the two sides of the water surface. -/
inductive OpticalMedium where
  | air
  | water
  deriving DecidableEq, Repr

/-- The two directed pieces of the watchman's narrow flashlight beam. -/
inductive BeamSegment where
  | incidentInAir
  | refractedInWater
  deriving DecidableEq, Repr

/-- The optical medium traversed by each beam segment. -/
def BeamSegment.medium : BeamSegment → OpticalMedium
  | .incidentInAir => .air
  | .refractedInWater => .water

/-
The physical quantities in the pool cross-section.  The three distances from
the wall are horizontal coordinates measured from the bottom of the wall, as
requested in the problem.  No numerical value for `bottomSpotDistanceFromWall`
is stored in this setup.
-/
structure PoolSearchSetup where
  /-- Vertical height of the flashlight above the water surface. -/
  flashlightHeightAboveSurface : LengthMagnitude
  /-- Horizontal coordinate of the point where the beam meets the surface. -/
  surfaceHitDistanceFromWall : LengthMagnitude
  /-- Vertical distance from the water surface to the pool bottom. -/
  poolDepth : LengthMagnitude
  /-- Requested horizontal coordinate of the light spot on the pool bottom. -/
  bottomSpotDistanceFromWall : LengthMagnitude
  /-- Dimensionless refractive index of each homogeneous medium. -/
  refractiveIndexDimensionless : OpticalMedium → ℝ
  /-- Unsigned angle of each segment from the vertical surface normal. -/
  angleFromNormalRadians : BeamSegment → ℝ

/-- The angle of incidence in air, measured from the water-surface normal. -/
def incidenceAngleRadians (setup : PoolSearchSetup) : ℝ :=
  setup.angleFromNormalRadians .incidentInAir

/-- The angle of refraction in water, measured from the same normal. -/
def refractionAngleRadians (setup : PoolSearchSetup) : ℝ :=
  setup.angleFromNormalRadians .refractedInWater

/-
Primary-figure and problem-statement readouts.  They give the `1.3 m`
flashlight height, `2.5 m` surface-hit coordinate, and `2.1 m` pool depth.
The statement deliberately contains no bottom-spot distance or answer choice.
-/
structure MatchesPoolFigureAndReadouts (setup : PoolSearchSetup) : Prop where
  flashlightHeightReadout :
    lengthInMeters setup.flashlightHeightAboveSurface = 13 / 10
  surfaceHitDistanceReadout :
    lengthInMeters setup.surfaceHitDistanceFromWall = 5 / 2
  poolDepthReadout :
    lengthInMeters setup.poolDepth = 21 / 10

/-
Physical-domain conditions for the elementary ray model.  The acute-angle
conditions choose the forward principal branches appropriate to the depicted
downward and rightward beam.
-/
structure HasPhysicalPoolOpticsParameters (setup : PoolSearchSetup) : Prop where
  flashlightHeightPositive :
    0 < lengthInMeters setup.flashlightHeightAboveSurface
  surfaceHitDistancePositive :
    0 < lengthInMeters setup.surfaceHitDistanceFromWall
  poolDepthPositive :
    0 < lengthInMeters setup.poolDepth
  refractiveIndicesPositive :
    ∀ medium, 0 < setup.refractiveIndexDimensionless medium
  beamAnglesAcute :
    ∀ segment,
      setup.angleFromNormalRadians segment ∈ Set.Ioo 0 (Real.pi / 2)

/-
Straight-line geometry in the two right triangles cut out by the horizontal
water surface, the vertical wall/normal, and the horizontal pool bottom.  This
is a generic geometric law: it relates the unknown bottom coordinate to the
refracted angle but gives it no numerical answer value.
-/
structure SatisfiesPlanarPoolRayGeometry (setup : PoolSearchSetup) : Prop where
  incidentTriangle :
    Real.tan (incidenceAngleRadians setup) =
      lengthInMeters setup.surfaceHitDistanceFromWall /
        lengthInMeters setup.flashlightHeightAboveSurface
  refractedTriangle :
    lengthInMeters setup.bottomSpotDistanceFromWall =
      lengthInMeters setup.surfaceHitDistanceFromWall +
        lengthInMeters setup.poolDepth *
          Real.tan (refractionAngleRadians setup)

/-
Snell's law at the planar air--water boundary, with both unsigned angles
measured from the interface normal.
-/
def SatisfiesSnellsLaw (setup : PoolSearchSetup) : Prop :=
  setup.refractiveIndexDimensionless (BeamSegment.medium .incidentInAir) *
      Real.sin (incidenceAngleRadians setup) =
    setup.refractiveIndexDimensionless (BeamSegment.medium .refractedInWater) *
      Real.sin (refractionAngleRadians setup)

/-- Labels of the four bottom-distance choices printed in the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- The meter readout printed beside each answer-choice label. -/
def AnswerChoice.distanceInMeters : AnswerChoice → ℝ
  | .A => 5
  | .B => 47 / 10
  | .C => 22 / 5
  | .D => 53 / 10

/-- Dataset metadata: the recorded multiple-choice answer is C. -/
def recordedAnswerChoice : AnswerChoice := .C

/-
The incident geometry and Snell's law determine the principal refracted
angle.  The underwater right triangle then determines the wall-based bottom
coordinate.  The source provides no refractive index for either medium, so the
strongest source-supported answer is the exact symbolic coordinate below.  In
particular, the recorded answer choice remains dataset metadata and is not a
conclusion of this theorem.

This formalizes blueprint label `thm:physics:phyx_mini_0135:target`.
-/
theorem problem_phyx_mini_0135
    (setup : PoolSearchSetup)
    (hFigure : MatchesPoolFigureAndReadouts setup)
    (hPhysical : HasPhysicalPoolOpticsParameters setup)
    (hGeometry : SatisfiesPlanarPoolRayGeometry setup)
    (hSnell : SatisfiesSnellsLaw setup) :
    incidenceAngleRadians setup = Real.arctan (25 / 13) ∧
      refractionAngleRadians setup =
        Real.arcsin
          (setup.refractiveIndexDimensionless .air /
              setup.refractiveIndexDimensionless .water *
            Real.sin (Real.arctan (25 / 13))) ∧
      lengthInMeters setup.bottomSpotDistanceFromWall =
        5 / 2 + 21 / 10 *
            Real.tan
              (Real.arcsin
                (setup.refractiveIndexDimensionless .air /
                    setup.refractiveIndexDimensionless .water *
                  Real.sin (Real.arctan (25 / 13)))) := by
  sorry

end PhyXMiniProblems.ProblemPhyXMini0135
