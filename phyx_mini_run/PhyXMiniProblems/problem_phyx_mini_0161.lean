import Mathlib
import Physlib.Units.WithDim.Basic

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0161

/-!
# Apparent image of a bulb above a water-covered plane mirror

The stated problem places a small bulb a distance `d₁ = 250 cm` above a
planar air--water interface.  The pool is `d₂ = 200 cm` deep and its bottom is
a large plane mirror.  Light refracts from air into water, reflects at the
bottom mirror, and refracts back into air.  An observer above the pool sees a
virtual image below the mirror.

Lengths are genuine dimensionful physical quantities.  Refractive indices
and answer readouts are dimensionless real numbers.  The multiple-choice
answer uses the standard near-normal paraxial model and the decimal water
index `1.33`.

The bitmap attached to the source record depicts an unrelated diverging-lens
ray diagram.  Therefore no lens labels from that bitmap are asserted below;
the pool geometry formalized here comes from the problem statement and its
caption.
-/

open Dimension

/-! ## Physical quantities and qualitative labels -/

/-- A physical length represented coherently in every choice of units. -/
abbrev OpticalLength : Type := Dimensionful (WithDim L𝓭 ℝ)

/-- Scalar readout of a physical length in a selected length unit. -/
def lengthReadout (unit : LengthUnit) (length : OpticalLength) : ℝ :=
  (length ({ UnitChoices.SI with length := unit } : UnitChoices)).val

/-- Scalar readout of a physical length in centimetres. -/
def lengthInCentimeters (length : OpticalLength) : ℝ :=
  lengthReadout LengthUnit.centimeters length

/-- The homogeneous media on the two sides of the pool surface. -/
inductive OpticalMedium where
  | ambientAir
  | poolWater
  deriving DecidableEq, Repr

/-- The small bulb is treated as a point source in the axial ray model. -/
inductive SourceModel where
  | pointLikeBulb
  deriving DecidableEq, Repr

/-- Qualitative model of the reflecting bottom surface. -/
inductive BottomMirrorModel where
  | largePlaneMirror
  deriving DecidableEq, Repr

/-- Optical approximation used to turn Snell's law into apparent-distance laws. -/
inductive ViewingRegime where
  | nearNormalParaxial
  deriving DecidableEq, Repr

/-- The image requested by the problem is formed by backward ray extensions. -/
inductive ImageNature where
  | virtual
  deriving DecidableEq, Repr

/-- The observer and returning rays are on the air side above the pool. -/
inductive ObserverSide where
  | airAboveSurface
  deriving DecidableEq, Repr

/-!
The physical lengths needed for the two-interface, one-reflection ray trace.

`bulbHeightAboveSurface` and `waterDepth` are the figure labels `d₁` and `d₂`.
The remaining lengths name successive intermediate images and object
distances.  In particular, `finalImageDistanceBelowMirror` is an unknown
observable; this structure stores no numerical value for it.
-/
structure PoolMirrorDiagram where
  /-- Figure label `d₁`: bulb height above the water surface. -/
  bulbHeightAboveSurface : OpticalLength
  /-- Figure label `d₂`: water-surface-to-bottom-mirror distance. -/
  waterDepth : OpticalLength
  /-- Virtual bulb height inferred by rays after their first refraction into water. -/
  waterSideVirtualBulbHeight : OpticalLength
  /-- Object distance from that virtual bulb to the bottom mirror. -/
  mirrorObjectDistance : OpticalLength
  /-- Equal virtual-image distance behind the plane mirror, measured in water. -/
  waterSideImageDistanceBelowMirror : OpticalLength
  /-- Depth of that mirror image below the water surface before the return refraction. -/
  waterSideImageDepthBelowSurface : OpticalLength
  /-- Apparent depth of the final virtual image as viewed from air. -/
  finalApparentImageDepthBelowSurface : OpticalLength
  /-- Requested distance from the mirror down to the final apparent image. -/
  finalImageDistanceBelowMirror : OpticalLength
  /-- Dimensionless refractive index of each medium. -/
  refractiveIndex : OpticalMedium → ℝ
  sourceModel : SourceModel
  bottomMirrorModel : BottomMirrorModel
  viewingRegime : ViewingRegime
  finalImageNature : ImageNature
  observerSide : ObserverSide

/-! ## Problem data and physical assumptions -/

/-!
The two stated distance readouts and the qualitative optical layout.  These
are inputs from the text, not consequences about the requested image distance.
-/
structure MatchesStatedPoolMirrorProblem
    (diagram : PoolMirrorDiagram) : Prop where
  bulbHeightReadout :
    lengthInCentimeters diagram.bulbHeightAboveSurface = 250
  waterDepthReadout : lengthInCentimeters diagram.waterDepth = 200
  source_is_small_bulb : diagram.sourceModel = .pointLikeBulb
  bottom_is_large_plane_mirror :
    diagram.bottomMirrorModel = .largePlaneMirror
  uses_near_normal_paraxial_model :
    diagram.viewingRegime = .nearNormalParaxial
  final_image_is_virtual : diagram.finalImageNature = .virtual
  viewed_from_air_above_surface : diagram.observerSide = .airAboveSurface

/-!
Dimensionless refractive-index readouts used by the recorded multiple-choice
answer: `n_air = 1.00` and `n_water = 1.33`.
-/
structure UsesStandardAirWaterIndices
    (diagram : PoolMirrorDiagram) : Prop where
  airIndexReadout : diagram.refractiveIndex .ambientAir = 1
  waterIndexReadout : diagram.refractiveIndex .poolWater = 133 / 100

/-!
Positivity and ordering conditions for the physical branch in which the final
virtual image really lies below the bottom mirror.
-/
structure HasPhysicalPoolMirrorParameters
    (diagram : PoolMirrorDiagram) : Prop where
  refractiveIndexPositive :
    ∀ medium, 0 < diagram.refractiveIndex medium
  bulbHeightPositive :
    0 < lengthInCentimeters diagram.bulbHeightAboveSurface
  waterDepthPositive : 0 < lengthInCentimeters diagram.waterDepth
  waterSideVirtualBulbHeightPositive :
    0 < lengthInCentimeters diagram.waterSideVirtualBulbHeight
  mirrorObjectDistancePositive :
    0 < lengthInCentimeters diagram.mirrorObjectDistance
  waterSideImageDistancePositive :
    0 < lengthInCentimeters diagram.waterSideImageDistanceBelowMirror
  waterSideImageDepthPositive :
    0 < lengthInCentimeters diagram.waterSideImageDepthBelowSurface
  finalApparentImageDepthPositive :
    0 < lengthInCentimeters diagram.finalApparentImageDepthBelowSurface
  finalImageDistancePositive :
    0 < lengthInCentimeters diagram.finalImageDistanceBelowMirror
  finalImageBelowMirror :
    lengthInCentimeters diagram.waterDepth <
      lengthInCentimeters diagram.finalApparentImageDepthBelowSurface

/-! ## Governing paraxial refraction and plane-mirror laws -/

/-!
The first interface makes the bulb appear farther above the surface to rays
inside the water.  The plane mirror then forms an image the same axial
distance behind its surface as the effective object is in front.  On the
return path, the water--air interface makes the submerged mirror image appear
shallower.  All distance relations hold in every length unit.

These are general governing laws and geometric incidence relations.  No field
mentions `351`, `46650 / 133`, or any answer label.
-/
structure SatisfiesParaxialPoolMirrorOptics
    (diagram : PoolMirrorDiagram) : Prop where
  air_to_water_apparent_object_law :
    ∀ unit : LengthUnit,
      diagram.refractiveIndex .ambientAir *
          lengthReadout unit diagram.waterSideVirtualBulbHeight =
        diagram.refractiveIndex .poolWater *
          lengthReadout unit diagram.bulbHeightAboveSurface
  mirror_object_distance_geometry :
    ∀ unit : LengthUnit,
      lengthReadout unit diagram.mirrorObjectDistance =
        lengthReadout unit diagram.waterSideVirtualBulbHeight +
          lengthReadout unit diagram.waterDepth
  plane_mirror_equal_object_image_distance :
    ∀ unit : LengthUnit,
      lengthReadout unit diagram.waterSideImageDistanceBelowMirror =
        lengthReadout unit diagram.mirrorObjectDistance
  water_side_image_depth_geometry :
    ∀ unit : LengthUnit,
      lengthReadout unit diagram.waterSideImageDepthBelowSurface =
        lengthReadout unit diagram.waterDepth +
          lengthReadout unit diagram.waterSideImageDistanceBelowMirror
  water_to_air_apparent_image_law :
    ∀ unit : LengthUnit,
      diagram.refractiveIndex .poolWater *
          lengthReadout unit diagram.finalApparentImageDepthBelowSurface =
        diagram.refractiveIndex .ambientAir *
          lengthReadout unit diagram.waterSideImageDepthBelowSurface
  final_distance_from_mirror_geometry :
    ∀ unit : LengthUnit,
      lengthReadout unit diagram.finalImageDistanceBelowMirror =
        lengthReadout unit diagram.finalApparentImageDepthBelowSurface -
          lengthReadout unit diagram.waterDepth

/-! ## Derived relations and answer choice -/

/-!
Before the returning rays leave the water, the plane-mirror image has axial
depth governed by the bulb height and two traversals of the water depth.
-/
lemma water_side_image_depth_index_relation
    (diagram : PoolMirrorDiagram)
    (physical : HasPhysicalPoolMirrorParameters diagram)
    (optics : SatisfiesParaxialPoolMirrorOptics diagram)
    (unit : LengthUnit) :
    diagram.refractiveIndex .ambientAir *
        lengthReadout unit diagram.waterSideImageDepthBelowSurface =
      diagram.refractiveIndex .poolWater *
          lengthReadout unit diagram.bulbHeightAboveSurface +
        2 * diagram.refractiveIndex .ambientAir *
          lengthReadout unit diagram.waterDepth := by
  rw [optics.water_side_image_depth_geometry unit,
    optics.plane_mirror_equal_object_image_distance unit,
    optics.mirror_object_distance_geometry unit,
    ← optics.air_to_water_apparent_object_law unit]
  ring

/-!
After the return refraction, subtracting the physical water depth gives the
general final-image relation
`n_water D = n_water d₁ + (2 n_air - n_water) d₂`.
-/
lemma final_image_distance_index_relation
    (diagram : PoolMirrorDiagram)
    (physical : HasPhysicalPoolMirrorParameters diagram)
    (optics : SatisfiesParaxialPoolMirrorOptics diagram)
    (unit : LengthUnit) :
    diagram.refractiveIndex .poolWater *
        lengthReadout unit diagram.finalImageDistanceBelowMirror =
      diagram.refractiveIndex .poolWater *
          lengthReadout unit diagram.bulbHeightAboveSurface +
        (2 * diagram.refractiveIndex .ambientAir -
            diagram.refractiveIndex .poolWater) *
          lengthReadout unit diagram.waterDepth := by
  rw [optics.final_distance_from_mirror_geometry unit]
  nlinarith [optics.water_to_air_apparent_image_law unit,
    water_side_image_depth_index_relation diagram physical optics unit]

/-- Labels of the four answers printed with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Distance below the mirror, in centimetres, printed beside each choice. -/
def displayedDistanceInCentimeters : AnswerChoice → ℝ
  | .A => 314
  | .B => 326
  | .C => 338
  | .D => 351

/-- The answer label recorded by the source dataset. -/
def recordedDatasetAnswer : AnswerChoice := .D

/-- A displayed integer-centimetre answer is within half a centimetre of the model. -/
def MatchesAnswerToNearestCentimeter
    (diagram : PoolMirrorDiagram) (choice : AnswerChoice) : Prop :=
  |lengthInCentimeters diagram.finalImageDistanceBelowMirror -
      displayedDistanceInCentimeters choice| ≤ (1 / 2 : ℝ)

/-- The selected answer is strictly closer than each competing display value. -/
def IsUniqueClosestAnswer
    (diagram : PoolMirrorDiagram) (choice : AnswerChoice) : Prop :=
  ∀ other, other ≠ choice →
    |lengthInCentimeters diagram.finalImageDistanceBelowMirror -
        displayedDistanceInCentimeters choice| <
      |lengthInCentimeters diagram.finalImageDistanceBelowMirror -
        displayedDistanceInCentimeters other|

/-!
With `d₁ = 250 cm`, `d₂ = 200 cm`, `n_air = 1`, and `n_water = 1.33`, the
paraxial model gives the exact decimal-data value `46650 / 133 cm`, about
`350.752 cm`.  It rounds to `351 cm`, uniquely selecting choice D.

This formalizes `thm:physics:phyx_mini_0161:target`.
-/
theorem problem_phyx_mini_0161
    (diagram : PoolMirrorDiagram)
    (problemData : MatchesStatedPoolMirrorProblem diagram)
    (indices : UsesStandardAirWaterIndices diagram)
    (physical : HasPhysicalPoolMirrorParameters diagram)
    (optics : SatisfiesParaxialPoolMirrorOptics diagram) :
    lengthInCentimeters diagram.finalImageDistanceBelowMirror =
        (46650 / 133 : ℝ) ∧
      MatchesAnswerToNearestCentimeter diagram .D ∧
      IsUniqueClosestAnswer diagram .D := by
  have hRelation :=
    final_image_distance_index_relation diagram physical optics
      LengthUnit.centimeters
  change diagram.refractiveIndex .poolWater *
        lengthInCentimeters diagram.finalImageDistanceBelowMirror =
      diagram.refractiveIndex .poolWater *
          lengthInCentimeters diagram.bulbHeightAboveSurface +
        (2 * diagram.refractiveIndex .ambientAir -
            diagram.refractiveIndex .poolWater) *
          lengthInCentimeters diagram.waterDepth at hRelation
  norm_num [indices.waterIndexReadout, indices.airIndexReadout,
    problemData.bulbHeightReadout, problemData.waterDepthReadout] at hRelation
  have hDistance :
      lengthInCentimeters diagram.finalImageDistanceBelowMirror =
        (46650 / 133 : ℝ) := by
    linarith
  refine ⟨hDistance, ?_, ?_⟩
  · norm_num [MatchesAnswerToNearestCentimeter,
      displayedDistanceInCentimeters, hDistance, abs_of_nonpos, abs_of_nonneg]
  · intro other hne
    cases other with
    | A =>
        norm_num [hDistance, displayedDistanceInCentimeters,
          abs_of_nonpos, abs_of_nonneg]
    | B =>
        norm_num [hDistance, displayedDistanceInCentimeters,
          abs_of_nonpos, abs_of_nonneg]
    | C =>
        norm_num [hDistance, displayedDistanceInCentimeters,
          abs_of_nonpos, abs_of_nonneg]
    | D => exact (hne rfl).elim

end PhyXMiniProblems.ProblemPhyXMini0161
