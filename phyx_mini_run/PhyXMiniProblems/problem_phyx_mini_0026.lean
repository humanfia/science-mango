import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Geometry.Euclidean.Projection
import Physlib.Units.WithDim.Basic

/-!
# Final image in a two-mirror periscope

The diagram is modeled in a vertical two-dimensional Euclidean cross-section.
Coordinates are SI-metre readouts, while the labels `p₁` and `h` are genuine
dimensionful lengths.  The two mirror centers, the object, the observer's eye,
and both virtual images are retained as distinct physical points.
-/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0026

open Dimension CarriesDimension UnitChoices

/-- The Euclidean cross-section containing the object, mirrors, images, and eye. -/
abbrev Space := EuclideanSpace ℝ (Fin 2)

/-- A physical quantity carrying the dimension of length. -/
abbrev LengthQuantity := Dimensionful (WithDim L𝓭 ℝ)

/-- Turn an SI-metre scalar readout into a dimensionful physical length. -/
noncomputable def metres (value : ℝ) : LengthQuantity :=
  toDimensionful SI ⟨value⟩

/-- Read a physical length as a real number of SI metres. -/
noncomputable def siMetres (length : LengthQuantity) : ℝ :=
  (length SI).val

/-- The dimensionful Euclidean distance between two points with SI-metre coordinates. -/
noncomputable def physicalDistance (p q : Space) : LengthQuantity :=
  metres (dist p q)

/-- An ideal flat mirror in the two-dimensional periscope cross-section. -/
structure PlaneMirror where
  /-- The affine line occupied by the reflecting surface. -/
  surface : AffineSubspace ℝ Space
  /-- A plane mirror has a nonempty reflecting surface. -/
  surface_nonempty : Nonempty surface
  /-- The center marked in the periscope figure. -/
  center : Space
  /-- The marked center lies on the reflecting surface. -/
  center_mem : center ∈ surface

namespace PlaneMirror

/-- The virtual image of a point in an ideal plane mirror. -/
noncomputable def reflectPoint (mirror : PlaneMirror) (point : Space) : Space :=
  letI : Nonempty mirror.surface := mirror.surface_nonempty
  EuclideanGeometry.reflection mirror.surface point

end PlaneMirror

/--
All named physical objects and figure labels in the periscope diagram.

`horizontalAxis` points toward the observer and `verticalAxis` points upward.
The angles are real radian readouts.  No field contains the requested final
image distance.
-/
structure PeriscopeSetup where
  upperMirror : PlaneMirror
  lowerMirror : PlaneMirror
  objectPosition : Space
  eyePosition : Space
  firstVirtualImage : Space
  finalVirtualImage : Space
  horizontalAxis : Space
  verticalAxis : Space
  /-- Figure label `p₁`: object-to-upper-mirror-center distance. -/
  p₁ : LengthQuantity
  /-- Figure label `h`: separation of the two mirror centers. -/
  h : LengthQuantity
  upperMirrorTiltRadians : ℝ
  lowerMirrorTiltRadians : ℝ

/-- The two labeled distances are strictly positive physical lengths. -/
def HasPositiveFigureLengths (setup : PeriscopeSetup) : Prop :=
  0 < siMetres setup.p₁ ∧ 0 < siMetres setup.h

/--
Geometric and scalar readouts supplied by the figure.  In the chosen axes the
object is `p₁` to the left of the upper center, and the lower center is `h`
below the upper center.  The eye is on the positive, outgoing horizontal side.
-/
def MatchesPeriscopeFigure (setup : PeriscopeSetup) : Prop :=
  ‖setup.horizontalAxis‖ = 1 ∧
    ‖setup.verticalAxis‖ = 1 ∧
    @inner ℝ Space _ setup.horizontalAxis setup.verticalAxis = 0 ∧
    setup.objectPosition =
      setup.upperMirror.center -
        siMetres setup.p₁ • setup.horizontalAxis ∧
    setup.lowerMirror.center =
      setup.upperMirror.center -
        siMetres setup.h • setup.verticalAxis ∧
    physicalDistance setup.objectPosition setup.upperMirror.center = setup.p₁ ∧
    physicalDistance setup.upperMirror.center setup.lowerMirror.center = setup.h ∧
    setup.upperMirrorTiltRadians = Real.pi / 4 ∧
    setup.lowerMirrorTiltRadians = Real.pi / 4 ∧
    0 < @inner ℝ Space _
      (setup.eyePosition - setup.lowerMirror.center) setup.horizontalAxis

/--
The affine-reflection behavior of the two depicted 45-degree mirrors.

The upper mirror sends any point a distance `d` left of its center to a virtual
image the same distance above its center.  The lower mirror sends any point a
distance `d` above its center to a virtual image the same distance to its left.
These universally quantified relations express mirror orientation and the
equal-object/equal-image-distance law; neither mentions `p₁ + h`.
-/
def HasFortyFiveDegreeMirrorGeometry (setup : PeriscopeSetup) : Prop :=
  (∀ d : ℝ, 0 ≤ d →
    setup.upperMirror.reflectPoint
        (setup.upperMirror.center - d • setup.horizontalAxis) =
      setup.upperMirror.center + d • setup.verticalAxis) ∧
  (∀ d : ℝ, 0 ≤ d →
    setup.lowerMirror.reflectPoint
        (setup.lowerMirror.center + d • setup.verticalAxis) =
      setup.lowerMirror.center - d • setup.horizontalAxis)

/-- Each successive virtual image is formed by reflection in the relevant mirror. -/
def SatisfiesPlaneMirrorImageFormation (setup : PeriscopeSetup) : Prop :=
  setup.firstVirtualImage =
      setup.upperMirror.reflectPoint setup.objectPosition ∧
    setup.finalVirtualImage =
      setup.lowerMirror.reflectPoint setup.firstVirtualImage

/-- The first mirror places its virtual image `p₁` above the upper mirror center. -/
lemma first_virtual_image_position
    (setup : PeriscopeSetup)
    (h_positive : HasPositiveFigureLengths setup)
    (h_figure : MatchesPeriscopeFigure setup)
    (h_mirrors : HasFortyFiveDegreeMirrorGeometry setup)
    (h_images : SatisfiesPlaneMirrorImageFormation setup) :
    setup.firstVirtualImage =
      setup.upperMirror.center +
        siMetres setup.p₁ • setup.verticalAxis := by
  rw [h_images.1, h_figure.2.2.2.1]
  exact h_mirrors.1 _ h_positive.1.le

/--
Because the lower mirror center is `h` below the upper center, the first
virtual image is `p₁ + h` above the lower center.
-/
lemma first_virtual_image_position_from_lower
    (setup : PeriscopeSetup)
    (h_positive : HasPositiveFigureLengths setup)
    (h_figure : MatchesPeriscopeFigure setup)
    (h_mirrors : HasFortyFiveDegreeMirrorGeometry setup)
    (h_images : SatisfiesPlaneMirrorImageFormation setup) :
    setup.firstVirtualImage =
      setup.lowerMirror.center +
        (siMetres setup.p₁ + siMetres setup.h) • setup.verticalAxis := by
  rw [first_virtual_image_position setup h_positive h_figure h_mirrors h_images,
    h_figure.2.2.2.2.1, add_smul]
  abel

/-- The lower mirror moves the final virtual image onto the horizontal output axis. -/
lemma final_virtual_image_position
    (setup : PeriscopeSetup)
    (h_positive : HasPositiveFigureLengths setup)
    (h_figure : MatchesPeriscopeFigure setup)
    (h_mirrors : HasFortyFiveDegreeMirrorGeometry setup)
    (h_images : SatisfiesPlaneMirrorImageFormation setup) :
    setup.finalVirtualImage =
      setup.lowerMirror.center -
        (siMetres setup.p₁ + siMetres setup.h) • setup.horizontalAxis := by
  rw [h_images.2,
    first_virtual_image_position_from_lower setup h_positive h_figure h_mirrors h_images]
  exact h_mirrors.2 _ (add_nonneg h_positive.1.le h_positive.2.le)

/-- The four answer labels printed with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- The SI-metre expression printed beside each answer choice. -/
def answerDistanceInMetres
    (setup : PeriscopeSetup) : AnswerChoice → ℝ
  | .A => siMetres setup.p₁ - 2 * siMetres setup.h
  | .B => siMetres setup.p₁ + 2 * siMetres setup.h
  | .C => siMetres setup.p₁ - siMetres setup.h
  | .D => siMetres setup.p₁ + siMetres setup.h

/-- A choice agrees exactly with the final-image distance along the central output ray. -/
def FinalImageMatchesChoice
    (setup : PeriscopeSetup) (choice : AnswerChoice) : Prop :=
  siMetres
      (physicalDistance setup.finalVirtualImage setup.lowerMirror.center) =
    answerDistanceInMetres setup choice

/--
The final virtual image is `p₁ + h` from the lower mirror center along the
horizontal output direction, so the correct answer is D.

This formalizes `thm:physics:phyx_mini_0026:target`.
-/
theorem problem_phyx_mini_0026
    (setup : PeriscopeSetup)
    (h_positive : HasPositiveFigureLengths setup)
    (h_figure : MatchesPeriscopeFigure setup)
    (h_mirrors : HasFortyFiveDegreeMirrorGeometry setup)
    (h_images : SatisfiesPlaneMirrorImageFormation setup) :
    physicalDistance setup.finalVirtualImage setup.lowerMirror.center =
        metres (siMetres setup.p₁ + siMetres setup.h) ∧
      FinalImageMatchesChoice setup .D := by
  have h_sum_nonneg : 0 ≤ siMetres setup.p₁ + siMetres setup.h :=
    add_nonneg h_positive.1.le h_positive.2.le
  have h_dist :
      dist setup.finalVirtualImage setup.lowerMirror.center =
        siMetres setup.p₁ + siMetres setup.h := by
    rw [final_virtual_image_position setup h_positive h_figure h_mirrors h_images,
      dist_eq_norm]
    simp [norm_smul, h_figure.1, Real.norm_eq_abs, abs_of_nonneg h_sum_nonneg]
  constructor
  · simp [physicalDistance, h_dist]
  · simp [FinalImageMatchesChoice, answerDistanceInMetres, physicalDistance,
      h_dist, siMetres, metres, toDimensionful_apply_apply]

end PhyXMiniProblems.ProblemPhyXMini0026
