import Mathlib
import Physlib.Optics.Basic
import Physlib.Units.WithDim.Basic
import Physlib.SpaceAndTime.Space.LengthUnit

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0055

open Dimension Filter

/-!
# First-order virtual image of a fish at a spherical water--air interface

The primary figure orients the optical axis from water to air. Its spherical
surface has signed radius `R = -25 cm`; the fish is `s = 10 cm` from the near
surface vertex. The virtual image below is the axial back-projection obtained
from the first derivative of the refracted ray family at the central ray. It is
therefore explicitly a first-order (paraxial) image, not an assertion that all
finite-angle rays from a spherical interface meet at one exact point.

Lengths remain dimensionful. Real numbers are used only for dimensionless
refractive indices, radian angle readouts, and centimeter coordinate readouts.
-/

/-- A signed physical length, independent of the unit used to read it. -/
abbrev OpticalLength : Type := Dimensionful (WithDim L𝓭 ℝ)

/-- The scalar readout of a physical length in the selected length unit. -/
def lengthReadout (unit : LengthUnit) (length : OpticalLength) : ℝ :=
  (length { UnitChoices.SI with length := unit }).val

/--
Dimensionful data for the pictured spherical bowl. The four axial positions
name the center of curvature, fish, first-order virtual image, and near surface
vertex in the left-to-right optical-axis orientation.
-/
structure FishBowlRefractionSetup where
  waterRefractiveIndex : ℝ
  airRefractiveIndex : ℝ
  centerOfCurvaturePosition : OpticalLength
  fishPosition : OpticalLength
  virtualImagePosition : OpticalLength
  nearSurfaceVertexPosition : OpticalLength
  bowlDiameter : OpticalLength

/--
A meridional ray family parametrized by signed ray height at the surface in
centimeters. The values are oriented direction-angle readouts in radians from
the left-to-right optical axis.
-/
structure MeridionalRayFamily where
  incidentDirectionRadians : ℝ → ℝ
  outwardNormalDirectionRadians : ℝ → ℝ
  refractedDirectionRadians : ℝ → ℝ

/-- Labels of the four displayed multiple-choice answers. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Distance in centimeters printed beside each displayed answer choice. -/
def answerDistanceInCentimeters : AnswerChoice → ℝ
  | .A => 14
  | .B => 86 / 10
  | .C => 83 / 10
  | .D => 74 / 10

/--
For the pictured bowl, exact Snell refraction near the central ray determines
the first-order virtual image as `5000/599 cm` from the near edge. This is about
`8.347 cm`, so it agrees to the printed precision with `8.3 cm`, choice C, and
C is uniquely closest among the displayed choices.

The three `HasDerivAt` premises are local first-order geometry contracts with
little-o remainders in the ray height: their slopes are respectively `1/s`,
`-1/R`, and `1/q`, where `q` is the positive axial back-projection distance.
Snell's sine law itself is imposed exactly for all sufficiently small ray
heights, so no premise globalizes the approximation `sin θ ≈ θ`.

This formalizes `thm:physics:phyx_mini_0055:target`.
-/
theorem problem_phyx_mini_0055
    (setup : FishBowlRefractionSetup)
    (rays : MeridionalRayFamily)
    (h_waterIndex : setup.waterRefractiveIndex = (133 / 100 : ℝ))
    (h_airIndex : setup.airRefractiveIndex = 1)
    (h_positiveIndices :
      0 < setup.waterRefractiveIndex ∧ 0 < setup.airRefractiveIndex)
    (h_bowlDiameter :
      lengthReadout LengthUnit.centimeters setup.bowlDiameter = 50)
    (h_positiveDiameter :
      0 < lengthReadout LengthUnit.centimeters setup.bowlDiameter)
    (h_objectDistance :
      lengthReadout LengthUnit.centimeters setup.nearSurfaceVertexPosition -
          lengthReadout LengthUnit.centimeters setup.fishPosition = 10)
    (h_signedRadius :
      lengthReadout LengthUnit.centimeters setup.centerOfCurvaturePosition -
          lengthReadout LengthUnit.centimeters setup.nearSurfaceVertexPosition = -25)
    (h_radiusDiameterGeometry :
      lengthReadout LengthUnit.centimeters setup.centerOfCurvaturePosition -
          lengthReadout LengthUnit.centimeters setup.nearSurfaceVertexPosition =
        -(lengthReadout LengthUnit.centimeters setup.bowlDiameter / 2))
    (h_axialOrder :
      lengthReadout LengthUnit.centimeters setup.centerOfCurvaturePosition <
          lengthReadout LengthUnit.centimeters setup.fishPosition ∧
        lengthReadout LengthUnit.centimeters setup.fishPosition <
          lengthReadout LengthUnit.centimeters setup.virtualImagePosition ∧
        lengthReadout LengthUnit.centimeters setup.virtualImagePosition <
          lengthReadout LengthUnit.centimeters setup.nearSurfaceVertexPosition)
    (h_centralRay :
      rays.incidentDirectionRadians 0 = 0 ∧
        rays.outwardNormalDirectionRadians 0 = 0 ∧
        rays.refractedDirectionRadians 0 = 0)
    (h_exactLocalSnellLaw :
      ∀ᶠ heightInCentimeters in nhds 0,
        setup.waterRefractiveIndex *
            Real.sin (rays.incidentDirectionRadians heightInCentimeters -
              rays.outwardNormalDirectionRadians heightInCentimeters) =
          setup.airRefractiveIndex *
            Real.sin (rays.refractedDirectionRadians heightInCentimeters -
              rays.outwardNormalDirectionRadians heightInCentimeters))
    (h_incidentFirstOrderGeometry :
      HasDerivAt rays.incidentDirectionRadians
        (1 /
          (lengthReadout LengthUnit.centimeters setup.nearSurfaceVertexPosition -
            lengthReadout LengthUnit.centimeters setup.fishPosition)) 0)
    (h_sphericalNormalFirstOrderGeometry :
      HasDerivAt rays.outwardNormalDirectionRadians
        (-1 /
          (lengthReadout LengthUnit.centimeters setup.centerOfCurvaturePosition -
            lengthReadout LengthUnit.centimeters setup.nearSurfaceVertexPosition)) 0)
    (h_virtualImageFirstOrderBackProjection :
      HasDerivAt rays.refractedDirectionRadians
        (1 /
          (lengthReadout LengthUnit.centimeters setup.nearSurfaceVertexPosition -
            lengthReadout LengthUnit.centimeters setup.virtualImagePosition)) 0) :
    let imageDistanceInCentimeters :=
      lengthReadout LengthUnit.centimeters setup.nearSurfaceVertexPosition -
        lengthReadout LengthUnit.centimeters setup.virtualImagePosition
    imageDistanceInCentimeters = (5000 / 599 : ℝ) ∧
      |imageDistanceInCentimeters - answerDistanceInCentimeters .C| ≤
        (1 / 20 : ℝ) ∧
      ∀ other : AnswerChoice, other ≠ .C →
        |imageDistanceInCentimeters - answerDistanceInCentimeters .C| <
          |imageDistanceInCentimeters - answerDistanceInCentimeters other| := by
  dsimp
  have h_incidentMinusNormal :
      HasDerivAt
        (fun heightInCentimeters =>
          rays.incidentDirectionRadians heightInCentimeters -
            rays.outwardNormalDirectionRadians heightInCentimeters)
        ((1 /
            (lengthReadout LengthUnit.centimeters setup.nearSurfaceVertexPosition -
              lengthReadout LengthUnit.centimeters setup.fishPosition)) -
          (-1 /
            (lengthReadout LengthUnit.centimeters setup.centerOfCurvaturePosition -
              lengthReadout LengthUnit.centimeters setup.nearSurfaceVertexPosition))) 0 :=
    h_incidentFirstOrderGeometry.sub h_sphericalNormalFirstOrderGeometry
  have h_refractedMinusNormal :
      HasDerivAt
        (fun heightInCentimeters =>
          rays.refractedDirectionRadians heightInCentimeters -
            rays.outwardNormalDirectionRadians heightInCentimeters)
        ((1 /
            (lengthReadout LengthUnit.centimeters setup.nearSurfaceVertexPosition -
              lengthReadout LengthUnit.centimeters setup.virtualImagePosition)) -
          (-1 /
            (lengthReadout LengthUnit.centimeters setup.centerOfCurvaturePosition -
              lengthReadout LengthUnit.centimeters setup.nearSurfaceVertexPosition))) 0 :=
    h_virtualImageFirstOrderBackProjection.sub h_sphericalNormalFirstOrderGeometry
  have h_leftDerivative :
      HasDerivAt
        (fun heightInCentimeters =>
          setup.waterRefractiveIndex *
            Real.sin (rays.incidentDirectionRadians heightInCentimeters -
              rays.outwardNormalDirectionRadians heightInCentimeters))
        (setup.waterRefractiveIndex *
          ((1 /
              (lengthReadout LengthUnit.centimeters setup.nearSurfaceVertexPosition -
                lengthReadout LengthUnit.centimeters setup.fishPosition)) -
            (-1 /
              (lengthReadout LengthUnit.centimeters setup.centerOfCurvaturePosition -
                lengthReadout LengthUnit.centimeters setup.nearSurfaceVertexPosition)))) 0 := by
    simpa [h_centralRay.1, h_centralRay.2.1] using
      h_incidentMinusNormal.sin.const_mul setup.waterRefractiveIndex
  have h_rightDerivative :
      HasDerivAt
        (fun heightInCentimeters =>
          setup.airRefractiveIndex *
            Real.sin (rays.refractedDirectionRadians heightInCentimeters -
              rays.outwardNormalDirectionRadians heightInCentimeters))
        (setup.airRefractiveIndex *
          ((1 /
              (lengthReadout LengthUnit.centimeters setup.nearSurfaceVertexPosition -
                lengthReadout LengthUnit.centimeters setup.virtualImagePosition)) -
            (-1 /
              (lengthReadout LengthUnit.centimeters setup.centerOfCurvaturePosition -
                lengthReadout LengthUnit.centimeters setup.nearSurfaceVertexPosition)))) 0 := by
    simpa [h_centralRay.2.1, h_centralRay.2.2] using
      h_refractedMinusNormal.sin.const_mul setup.airRefractiveIndex
  have h_derivativeEquality :
      setup.waterRefractiveIndex *
          ((1 /
              (lengthReadout LengthUnit.centimeters setup.nearSurfaceVertexPosition -
                lengthReadout LengthUnit.centimeters setup.fishPosition)) -
            (-1 /
              (lengthReadout LengthUnit.centimeters setup.centerOfCurvaturePosition -
                lengthReadout LengthUnit.centimeters setup.nearSurfaceVertexPosition))) =
        setup.airRefractiveIndex *
          ((1 /
              (lengthReadout LengthUnit.centimeters setup.nearSurfaceVertexPosition -
                lengthReadout LengthUnit.centimeters setup.virtualImagePosition)) -
            (-1 /
              (lengthReadout LengthUnit.centimeters setup.centerOfCurvaturePosition -
                lengthReadout LengthUnit.centimeters setup.nearSurfaceVertexPosition))) := by
    exact h_leftDerivative.unique
      (h_rightDerivative.congr_of_eventuallyEq h_exactLocalSnellLaw)
  have h_positiveImageDistance :
      0 <
        lengthReadout LengthUnit.centimeters setup.nearSurfaceVertexPosition -
          lengthReadout LengthUnit.centimeters setup.virtualImagePosition :=
    sub_pos.mpr h_axialOrder.2.2
  have h_imageDistance :
      lengthReadout LengthUnit.centimeters setup.nearSurfaceVertexPosition -
          lengthReadout LengthUnit.centimeters setup.virtualImagePosition =
        (5000 / 599 : ℝ) := by
    rw [h_waterIndex, h_airIndex, h_objectDistance, h_signedRadius] at h_derivativeEquality
    field_simp at h_derivativeEquality ⊢
    nlinarith
  refine ⟨h_imageDistance, ?_, ?_⟩
  · rw [h_imageDistance]
    norm_num [answerDistanceInCentimeters, abs_of_nonneg, abs_of_nonpos]
  · intro other h_other
    rw [h_imageDistance]
    cases other <;>
      simp_all [answerDistanceInCentimeters] <;>
      norm_num [abs_of_nonneg, abs_of_nonpos]

end PhyXMiniProblems.ProblemPhyXMini0055
