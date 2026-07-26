import Physlib.Optics.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic

namespace PhyXMiniProblems.ProblemPhyXMini0007

/-- Geometric data read from the pictured air--glass interface in its two-dimensional
plane. The three propagation directions describe rays based at `incidencePoint`, while
`surfaceNormalTowardAir` fixes the orientation of the interface normal. -/
structure AirGlassRayDiagram where
  incidencePoint : EuclideanSpace ℝ (Fin 2)
  surfaceNormalTowardAir : EuclideanSpace ℝ (Fin 2)
  incidentDirection : EuclideanSpace ℝ (Fin 2)
  reflectedDirection : EuclideanSpace ℝ (Fin 2)
  refractedDirection : EuclideanSpace ℝ (Fin 2)

/-- For a beam incident from air (refractive index one) into glass, if reflection
obeys equality of incidence and reflection angles, refraction obeys Snell's law, and
the reflected and refracted rays have the perpendicular layout shown in the figure,
then the incidence angle is the arctangent of the glass refractive index.

This is the declaration corresponding to
`thm:physics:phyx_mini_0007:target`. -/
theorem incidenceAngle_eq_arctan_glassRefractiveIndex
    (diagram : AirGlassRayDiagram)
    (airRefractiveIndex glassRefractiveIndex : ℝ)
    (incidentAngleRadians reflectedAngleRadians refractedAngleRadians : ℝ)
    (hUnitDirections :
      ‖diagram.surfaceNormalTowardAir‖ = 1 ∧
        ‖diagram.incidentDirection‖ = 1 ∧
        ‖diagram.reflectedDirection‖ = 1 ∧
        ‖diagram.refractedDirection‖ = 1)
    (hIncidentAngleReadout :
      incidentAngleRadians =
        InnerProductGeometry.angle
          (-diagram.incidentDirection) diagram.surfaceNormalTowardAir)
    (hReflectedAngleReadout :
      reflectedAngleRadians =
        InnerProductGeometry.angle
          diagram.reflectedDirection diagram.surfaceNormalTowardAir)
    (hRefractedAngleReadout :
      refractedAngleRadians =
        InnerProductGeometry.angle
          diagram.refractedDirection (-diagram.surfaceNormalTowardAir))
    (hPerpendicularFigureReadout :
      InnerProductGeometry.angle
          diagram.reflectedDirection diagram.refractedDirection =
        Real.pi / 2)
    (hFigureBranchRelation :
      reflectedAngleRadians + refractedAngleRadians = Real.pi / 2)
    (hAirRefractiveIndex : airRefractiveIndex = 1)
    (hGlassRefractiveIndex : 1 < glassRefractiveIndex)
    (hIncidentAngleRange :
      0 < incidentAngleRadians ∧ incidentAngleRadians < Real.pi / 2)
    (hReflectedAngleRange :
      0 < reflectedAngleRadians ∧ reflectedAngleRadians < Real.pi / 2)
    (hRefractedAngleRange :
      0 < refractedAngleRadians ∧ refractedAngleRadians < Real.pi / 2)
    (hReflectionLaw : reflectedAngleRadians = incidentAngleRadians)
    (hSnellLaw :
      airRefractiveIndex * Real.sin incidentAngleRadians =
        glassRefractiveIndex * Real.sin refractedAngleRadians) :
    incidentAngleRadians = Real.arctan glassRefractiveIndex := by
  have href :
      refractedAngleRadians = Real.pi / 2 - incidentAngleRadians := by
    linarith [hFigureBranchRelation, hReflectionLaw]
  have hsin :
      Real.sin incidentAngleRadians =
        glassRefractiveIndex * Real.cos incidentAngleRadians := by
    rw [hAirRefractiveIndex, one_mul, href, Real.sin_pi_div_two_sub] at hSnellLaw
    exact hSnellLaw
  have hcospos : 0 < Real.cos incidentAngleRadians :=
    Real.cos_pos_of_mem_Ioo
      ⟨by linarith [hIncidentAngleRange.1], hIncidentAngleRange.2⟩
  have htan : Real.tan incidentAngleRadians = glassRefractiveIndex := by
    rw [Real.tan_eq_sin_div_cos, hsin]
    exact mul_div_cancel_right₀ glassRefractiveIndex hcospos.ne'
  exact
    (Real.arctan_eq_of_tan_eq htan
      ⟨by linarith [hIncidentAngleRange.1], hIncidentAngleRange.2⟩).symm

end PhyXMiniProblems.ProblemPhyXMini0007
