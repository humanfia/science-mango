import Mathlib
import Physlib.Units.WithDim.Basic

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0032

open Dimension

/-!
# Overall magnification of a concave mirror followed by a diverging lens

The optical axis in the figure is coordinatized from the lens toward the
mirror. Light from the object first travels right to the concave mirror. The
reflected light then travels left through the diverging lens, so the real image
formed by the mirror is a virtual object for the return passage through the
lens.

All positions, focal lengths, radii, and object/image distances are signed
physical lengths. Real numbers occur only as centimeter readouts and as the
dimensionless transverse magnifications.
-/

/-- A signed physical length, independent of the unit in which it is read. -/
abbrev LengthQuantity : Type := Dimensionful (WithDim L𝓭 ℝ)

/-- Unit choices whose length component is the centimeter used in the source. -/
noncomputable def centimeterUnitChoices : UnitChoices :=
  { UnitChoices.SI with length := LengthUnit.centimeters }

/-- The signed scalar centimeter readout of a dimensionful length. -/
def lengthInCentimeters (length : LengthQuantity) : ℝ :=
  (length centimeterUnitChoices).val

/-- The three labeled components, ordered left-to-right in the figure. -/
inductive FigureComponent where
  | lens
  | object
  | mirror
  deriving DecidableEq, Repr

/--
Physical quantities for the two-stage paraxial imaging process.

`mirrorImagePosition` is the real intermediate image formed after reflection.
It becomes the signed object position for the return passage through the lens.
The sign convention takes positive mirror object/image distances on the side
facing the lens, and a positive lens object distance on the incident (right)
side of the lens. Thus the intermediate image to the left of the lens gives a
negative `returnLensObjectDistance`.
-/
structure LensMirrorSetup where
  axisPosition : FigureComponent → LengthQuantity
  lensFocalLength : LengthQuantity
  mirrorRadiusMagnitude : LengthQuantity
  mirrorFocalLength : LengthQuantity
  mirrorObjectDistance : LengthQuantity
  mirrorImageDistance : LengthQuantity
  mirrorImagePosition : LengthQuantity
  returnLensObjectDistance : LengthQuantity
  returnLensImageDistance : LengthQuantity
  mirrorMagnification : ℝ
  returnLensMagnification : ℝ
  overallMagnification : ℝ

/--
Spatial and numerical readouts supplied by the source and the primary image:
the lens is left of the object, the object is at the midpoint of the `25.0 cm`
bench, the concave mirror has radius magnitude `20.0 cm`, and the diverging
lens has signed focal length `-16.7 cm`.
-/
structure MatchesFigureReadouts (setup : LensMirrorSetup) : Prop where
  component_order :
    lengthInCentimeters (setup.axisPosition .lens) <
        lengthInCentimeters (setup.axisPosition .object) ∧
      lengthInCentimeters (setup.axisPosition .object) <
        lengthInCentimeters (setup.axisPosition .mirror)
  lens_mirror_separation :
    lengthInCentimeters (setup.axisPosition .mirror) -
        lengthInCentimeters (setup.axisPosition .lens) = 25
  object_is_midway :
    2 * lengthInCentimeters (setup.axisPosition .object) =
      lengthInCentimeters (setup.axisPosition .lens) +
        lengthInCentimeters (setup.axisPosition .mirror)
  mirror_radius_magnitude :
    lengthInCentimeters setup.mirrorRadiusMagnitude = 20
  diverging_lens_focal_length :
    lengthInCentimeters setup.lensFocalLength = -16.7

/--
The physical sign branch depicted in the problem: a diverging lens, a concave
mirror, and a real first-stage mirror image. These are qualitative optical
properties, not the requested numerical magnification.
-/
structure HasDepictedOpticalTypes (setup : LensMirrorSetup) : Prop where
  lens_is_diverging : lengthInCentimeters setup.lensFocalLength < 0
  mirror_radius_is_positive :
    0 < lengthInCentimeters setup.mirrorRadiusMagnitude
  mirror_is_concave : 0 < lengthInCentimeters setup.mirrorFocalLength
  object_is_in_front_of_mirror :
    0 < lengthInCentimeters setup.mirrorObjectDistance
  mirror_image_is_real : 0 < lengthInCentimeters setup.mirrorImageDistance

/--
Geometry connecting the mirror image to the return pass through the lens.
Positions increase from the lens toward the mirror. For the reflected,
left-moving light, the signed lens object distance is the intermediate image
position minus the lens position.
-/
structure ConnectsImagingStages (setup : LensMirrorSetup) : Prop where
  mirror_object_distance_geometry :
    lengthInCentimeters setup.mirrorObjectDistance =
      lengthInCentimeters (setup.axisPosition .mirror) -
        lengthInCentimeters (setup.axisPosition .object)
  mirror_image_position_geometry :
    lengthInCentimeters setup.mirrorImagePosition =
      lengthInCentimeters (setup.axisPosition .mirror) -
        lengthInCentimeters setup.mirrorImageDistance
  return_lens_object_distance_geometry :
    lengthInCentimeters setup.returnLensObjectDistance =
      lengthInCentimeters setup.mirrorImagePosition -
        lengthInCentimeters (setup.axisPosition .lens)

/--
Standard paraxial governing laws for the concave-mirror stage and the return
thin-lens stage. The equations use signed centimeter readouts, while each
magnification is dimensionless. The final field is the general composition
law for successive transverse magnifications; it contains no numerical answer.
-/
structure SatisfiesParaxialGoverningLaws (setup : LensMirrorSetup) : Prop where
  spherical_mirror_focal_length :
    2 * lengthInCentimeters setup.mirrorFocalLength =
      lengthInCentimeters setup.mirrorRadiusMagnitude
  spherical_mirror_equation :
    1 / lengthInCentimeters setup.mirrorFocalLength =
      1 / lengthInCentimeters setup.mirrorObjectDistance +
        1 / lengthInCentimeters setup.mirrorImageDistance
  mirror_transverse_magnification :
    setup.mirrorMagnification =
      -(lengthInCentimeters setup.mirrorImageDistance /
        lengthInCentimeters setup.mirrorObjectDistance)
  return_thin_lens_equation :
    1 / lengthInCentimeters setup.lensFocalLength =
      1 / lengthInCentimeters setup.returnLensObjectDistance +
        1 / lengthInCentimeters setup.returnLensImageDistance
  lens_transverse_magnification :
    setup.returnLensMagnification =
      -(lengthInCentimeters setup.returnLensImageDistance /
        lengthInCentimeters setup.returnLensObjectDistance)
  successive_magnifications_multiply :
    setup.overallMagnification =
      setup.mirrorMagnification * setup.returnLensMagnification

/-- The four displayed multiple-choice labels. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- The dimensionless overall magnification printed beside each choice. -/
def answerMagnification : AnswerChoice → ℝ
  | .A => 4.78
  | .B => 4.50
  | .C => 5.52
  | .D => 8.05

/-- Agreement with a magnification displayed to the nearest hundredth. -/
def MatchesAnswerToNearestHundredth
    (magnification : ℝ) (choice : AnswerChoice) : Prop :=
  |magnification - answerMagnification choice| ≤ 1 / 200

/--
The mirror data determine `fₘ = 10 cm`, `pₘ = 12.5 cm`, `qₘ = 50 cm`, and
mirror magnification `-4`.
-/
lemma mirror_stage_values
    (setup : LensMirrorSetup)
    (_figure : MatchesFigureReadouts setup)
    (_geometry : ConnectsImagingStages setup)
    (_laws : SatisfiesParaxialGoverningLaws setup) :
    lengthInCentimeters setup.mirrorFocalLength = 10 ∧
      lengthInCentimeters setup.mirrorObjectDistance = 25 / 2 ∧
      lengthInCentimeters setup.mirrorImageDistance = 50 ∧
      setup.mirrorMagnification = -4 := by
  rcases _figure with ⟨_, hseparation, hmidpoint, hradius, _⟩
  rcases _geometry with ⟨hobjectDistance, _, _⟩
  rcases _laws with ⟨hfocal, hmirrorEquation, hmagnification, _, _, _⟩
  have hfocalValue :
      lengthInCentimeters setup.mirrorFocalLength = 10 := by
    linarith
  have hobjectDistanceValue :
      lengthInCentimeters setup.mirrorObjectDistance = 25 / 2 := by
    linarith
  have himageDistanceValue :
      lengthInCentimeters setup.mirrorImageDistance = 50 := by
    rw [hfocalValue, hobjectDistanceValue] at hmirrorEquation
    have himageDistance_ne :
        lengthInCentimeters setup.mirrorImageDistance ≠ 0 := by
      intro himageDistance_zero
      rw [himageDistance_zero] at hmirrorEquation
      norm_num at hmirrorEquation
    field_simp [himageDistance_ne] at hmirrorEquation
    linarith
  have hmagnificationValue : setup.mirrorMagnification = -4 := by
    rw [himageDistanceValue, hobjectDistanceValue] at hmagnification
    norm_num at hmagnification ⊢
    exact hmagnification
  exact ⟨hfocalValue, hobjectDistanceValue, himageDistanceValue,
    hmagnificationValue⟩

/--
The mirror image lies `25 cm` left of the lens and is therefore a virtual
object for the return lens pass. The signed lens equation gives
`qₗ = -4175/83 cm` and lens magnification `-167/83`.
-/
lemma return_lens_stage_values
    (setup : LensMirrorSetup)
    (_figure : MatchesFigureReadouts setup)
    (_geometry : ConnectsImagingStages setup)
    (_laws : SatisfiesParaxialGoverningLaws setup) :
    lengthInCentimeters setup.returnLensObjectDistance = -25 ∧
      lengthInCentimeters setup.returnLensImageDistance = -(4175 / 83) ∧
      setup.returnLensMagnification = -(167 / 83) := by
  rcases mirror_stage_values setup _figure _geometry _laws with
    ⟨_, _, hmirrorImageDistance, _⟩
  rcases _figure with ⟨_, hseparation, _, _, hlensFocalLength⟩
  rcases _geometry with
    ⟨_, hmirrorImagePosition, hreturnObjectDistance⟩
  rcases _laws with ⟨_, _, _, hlensEquation, hlensMagnification, _⟩
  have hreturnObjectDistanceValue :
      lengthInCentimeters setup.returnLensObjectDistance = -25 := by
    linarith
  have hreturnImageDistanceValue :
      lengthInCentimeters setup.returnLensImageDistance = -(4175 / 83) := by
    rw [hlensFocalLength, hreturnObjectDistanceValue] at hlensEquation
    have hreturnImageDistance_ne :
        lengthInCentimeters setup.returnLensImageDistance ≠ 0 := by
      intro hreturnImageDistance_zero
      rw [hreturnImageDistance_zero] at hlensEquation
      norm_num at hlensEquation
    field_simp [hreturnImageDistance_ne] at hlensEquation
    norm_num at hlensEquation ⊢
    linarith
  have hlensMagnificationValue :
      setup.returnLensMagnification = -(167 / 83) := by
    rw [hreturnImageDistanceValue, hreturnObjectDistanceValue] at hlensMagnification
    norm_num at hlensMagnification ⊢
    exact hlensMagnification
  exact ⟨hreturnObjectDistanceValue, hreturnImageDistanceValue,
    hlensMagnificationValue⟩

/--
The signed overall magnification is exactly `668/83 ≈ 8.04819`, which rounds
to `8.05`, answer choice D.

This formalizes `thm:physics:phyx_mini_0032:target`.
-/
theorem problem_phyx_mini_0032
    (setup : LensMirrorSetup)
    (_figure : MatchesFigureReadouts setup)
    (_opticalTypes : HasDepictedOpticalTypes setup)
    (_geometry : ConnectsImagingStages setup)
    (_laws : SatisfiesParaxialGoverningLaws setup) :
    setup.overallMagnification = 668 / 83 ∧
      MatchesAnswerToNearestHundredth setup.overallMagnification .D := by
  rcases mirror_stage_values setup _figure _geometry _laws with
    ⟨_, _, _, hmirrorMagnification⟩
  rcases return_lens_stage_values setup _figure _geometry _laws with
    ⟨_, _, hlensMagnification⟩
  have hoverallMagnification : setup.overallMagnification = 668 / 83 := by
    rw [_laws.successive_magnifications_multiply, hmirrorMagnification,
      hlensMagnification]
    norm_num
  refine ⟨hoverallMagnification, ?_⟩
  rw [hoverallMagnification]
  norm_num [MatchesAnswerToNearestHundredth, answerMagnification,
    abs_of_nonpos]

end PhyXMiniProblems.ProblemPhyXMini0032
