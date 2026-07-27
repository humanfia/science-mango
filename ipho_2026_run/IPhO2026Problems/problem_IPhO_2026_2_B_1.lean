import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Ray
import Physlib.Units.WithDim.Basic

/-!
# IPhO 2026, theoretical problem 2, part B.1

This file models the transverse cross-section of the solar cooker in Figure 2f.
Lengths, radiant power, and solar intensity carry their physical dimensions.
Real numbers are used only for dimensionless angles, scalar factors, and
coordinate readouts in the selected unit system.
-/

namespace IPhO2026Problems.IPhO2026_2_B_1

open scoped Real

/-- A physical length, represented by a dimension-tagged real readout. -/
abbrev PhysicalLength := WithDim Dimension.L𝓭 ℝ

/-- The physical dimension `mass * length^2 * time^(-3)` of radiant power. -/
def radiantPowerDimension : Dimension :=
  Dimension.M𝓭 * Dimension.L𝓭 ^ (2 : ℚ) * Dimension.T𝓭 ^ (-3 : ℚ)

/-- The physical dimension `mass * time^(-3)` of irradiance. -/
def solarIntensityDimension : Dimension :=
  Dimension.M𝓭 * Dimension.T𝓭 ^ (-3 : ℚ)

/-- Radiant power, such as the no-mirror reference power `P₀`. -/
abbrev RadiantPower := WithDim radiantPowerDimension ℝ

/-- Uniform solar power per unit area. -/
abbrev SolarIntensity := WithDim solarIntensityDimension ℝ

/-- Dimension-preserving multiplication of a length by a dimensionless scalar. -/
def scaleLength (c : ℝ) (ℓ : PhysicalLength) : PhysicalLength :=
  ⟨c * ℓ.val⟩

/-- The two-dimensional cross-section normal to the parallel cylinder axes. -/
abbrev CrossSection := EuclideanSpace ℝ (Fin 2)

/-- A three-dimensional direction used for a cylinder axis. -/
abbrev AxisDirection := RayVector ℝ (EuclideanSpace ℝ (Fin 3))

/-- A nonzero direction in the optical cross-section. -/
abbrev RayDirection2D := RayVector ℝ CrossSection

/-- Two nonzero directions are parallel when one is a nonzero scalar multiple
of the other. -/
def ParallelDirections {n : ℕ}
    (u v : RayVector ℝ (EuclideanSpace ℝ (Fin n))) : Prop :=
  ∃ c : ℝ, c ≠ 0 ∧ v.val = c • u.val

/-- A directed geometrical-optics ray in the transverse cross-section. -/
structure LightRay2D where
  origin : CrossSection
  direction : RayDirection2D

/-- A point lies on the forward half-line of a directed ray. -/
def PointLiesOnForwardRay (p : CrossSection) (ray : LightRay2D) : Prop :=
  ∃ t : ℝ, 0 ≤ t ∧ p = ray.origin + t • ray.direction.val

/-- A ray path together with all mirror-reflected segments and reflection
points. The list representation permits the one-reflection condition to be
stated as a physical law rather than built into the data type. -/
structure OpticalPath2D where
  incoming : LightRay2D
  reflectedSegments : List LightRay2D
  reflectionPoints : List CrossSection

/-- The apparatus and the observable quantities named in the problem.

`radiusAtIncidence θ` is the radius selected by the limiting-ray construction
when the maximum incidence angle is `θ`; it is left abstract here so that the
ray-tracing law, rather than a definition, determines it.
-/
structure SolarCookerSetup where
  unitSystem : UnitChoices
  mirrorCenter : CrossSection
  containerCenter : CrossSection
  opticalAxis : RayDirection2D
  mirrorAxis : AxisDirection
  containerAxis : AxisDirection
  mirrorRadius : PhysicalLength
  containerRadius : PhysicalLength
  sunlightIntensity : SolarIntensity
  noMirrorPower : RadiantPower
  thetaMax : ℝ
  radiusAtIncidence : ℝ → PhysicalLength
  onReflectingHalf : CrossSection → Prop
  onMirrorSurface : CrossSection → Prop
  onContainerBoundary : CrossSection → Prop
  mirrorNormalAt : CrossSection → RayDirection2D
  angleBetweenDirections : RayDirection2D → RayDirection2D → ℝ
  isIncomingSunRay : LightRay2D → Prop
  rayIntensity : LightRay2D → SolarIntensity
  isPhysicalPath : OpticalPath2D → Prop
  hitsContainer : OpticalPath2D → Prop
  absorbedByContainer : OpticalPath2D → Prop
  incidenceAngle : OpticalPath2D → ℝ
  reflectionAngle : OpticalPath2D → ℝ
  isLimitingPathForRadius : OpticalPath2D → PhysicalLength → Prop
  isTangentToContainer : OpticalPath2D → PhysicalLength → Prop

/-- The dimensionless angular range relevant to the half-cylinder
cross-section. -/
def IsAdmissibleIncidenceAngle (θ : ℝ) : Prop :=
  0 ≤ θ ∧ θ ≤ Real.pi / 2

/-- Scalar and geometric labels read directly from Figure 2f.

The figure labels the mirror diameter by `2R`, the container radius by `a`,
and the center displacement on the symmetry axis by `R/2`.
-/
structure Figure2fReadout (setup : SolarCookerSetup) where
  mirrorDiameterLabel : PhysicalLength
  containerRadiusLabel : PhysicalLength
  centerOffsetLabel : PhysicalLength
  mirrorDiameter_is_two_R :
    mirrorDiameterLabel = scaleLength 2 setup.mirrorRadius
  containerRadiusLabel_is_a :
    containerRadiusLabel = setup.containerRadius
  centerOffset_is_half_R :
    centerOffsetLabel = scaleLength (1 / 2) setup.mirrorRadius
  centers_have_labeled_separation :
    dist setup.mirrorCenter setup.containerCenter = centerOffsetLabel.val
  centers_lie_on_symmetry_axis :
    ∃ t : ℝ, 0 ≤ t ∧
      setup.containerCenter =
        setup.mirrorCenter + t • setup.opticalAxis.val
  actual_radius_matches_thetaMax :
    setup.containerRadius = setup.radiusAtIncidence setup.thetaMax

/-- Governing geometrical-optics and absorption laws for the apparatus.

No coefficient value is included here. In particular, the response
`radiusAtIncidence` remains constrained only through realizable limiting,
tangent, specular ray paths.
-/
structure ValidSolarCookerPhysics (setup : SolarCookerSetup) : Prop where
  mirrorRadius_positive : 0 < setup.mirrorRadius.val
  containerRadius_positive : 0 < setup.containerRadius.val
  sunlightIntensity_positive : 0 < setup.sunlightIntensity.val
  noMirrorPower_positive : 0 < setup.noMirrorPower.val
  cylinder_axes_parallel :
    ParallelDirections setup.mirrorAxis setup.containerAxis
  mirror_is_circular_arc :
    ∀ p, setup.onMirrorSurface p →
      setup.onReflectingHalf p ∧
        dist p setup.mirrorCenter = setup.mirrorRadius.val
  mirror_normal_is_radial :
    ∀ p, setup.onMirrorSurface p →
      ∃ c : ℝ, c ≠ 0 ∧
        (setup.mirrorNormalAt p).val =
          c • (p - setup.mirrorCenter)
  container_is_circle :
    ∀ p, setup.onContainerBoundary p →
      dist p setup.containerCenter = setup.containerRadius.val
  sunlight_parallel_to_optical_axis :
    ∀ ray, setup.isIncomingSunRay ray →
      ParallelDirections ray.direction setup.opticalAxis
  sunlight_uniform :
    ∀ ray, setup.isIncomingSunRay ray →
      setup.rayIntensity ray = setup.sunlightIntensity
  reflection_points_match_segments :
    ∀ path, setup.isPhysicalPath path →
      path.reflectionPoints.length = path.reflectedSegments.length
  reflections_occur_on_mirror :
    ∀ path, setup.isPhysicalPath path →
      ∀ p ∈ path.reflectionPoints, setup.onMirrorSurface p
  once_reflected_segments_meet_at_surface :
    ∀ path p reflected, setup.isPhysicalPath path →
      path.reflectionPoints = [p] →
      path.reflectedSegments = [reflected] →
        PointLiesOnForwardRay p path.incoming ∧ reflected.origin = p
  incidence_measured_from_normal :
    ∀ path p, setup.isPhysicalPath path →
      p ∈ path.reflectionPoints →
        setup.incidenceAngle path =
          setup.angleBetweenDirections
            path.incoming.direction (setup.mirrorNormalAt p)
  reflection_measured_from_normal :
    ∀ path p reflected, setup.isPhysicalPath path →
      path.reflectionPoints = [p] →
      path.reflectedSegments = [reflected] →
        setup.reflectionAngle path =
          setup.angleBetweenDirections
            reflected.direction (setup.mirrorNormalAt p)
  specular_reflection_law :
    ∀ path, setup.isPhysicalPath path →
      path.reflectedSegments ≠ [] →
        setup.incidenceAngle path = setup.reflectionAngle path
  fully_absorbing_container :
    ∀ path, setup.isPhysicalPath path →
      setup.hitsContainer path → setup.absorbedByContainer path
  absorbed_paths_reflect_at_most_once :
    ∀ path, setup.isPhysicalPath path →
      setup.absorbedByContainer path →
        path.reflectionPoints.length ≤ 1
  thetaMax_admissible :
    IsAdmissibleIncidenceAngle setup.thetaMax
  thetaMax_is_upper_bound :
    ∀ path, setup.isPhysicalPath path →
      setup.absorbedByContainer path →
      path.reflectionPoints.length = 1 →
        setup.incidenceAngle path ≤ setup.thetaMax
  thetaMax_is_attained :
    ∃ path, setup.isPhysicalPath path ∧
      setup.absorbedByContainer path ∧
      path.reflectionPoints.length = 1 ∧
      setup.incidenceAngle path = setup.thetaMax
  limiting_tangent_path_exists :
    ∀ θ, IsAdmissibleIncidenceAngle θ →
      ∃ path, setup.isPhysicalPath path ∧
        setup.isLimitingPathForRadius path (setup.radiusAtIncidence θ) ∧
        setup.isTangentToContainer path (setup.radiusAtIncidence θ) ∧
        path.reflectionPoints.length = 1 ∧
        setup.incidenceAngle path = θ

/-- The sinusoidal coefficient form supplied in part B.1, interpreted as a
symbolic identity for the radius response over the admissible angle range. -/
def IsRadiusCoefficientFormula
    (setup : SolarCookerSetup) (α β : PhysicalLength) : Prop :=
  ∀ θ, IsAdmissibleIncidenceAngle θ →
    setup.radiusAtIncidence θ =
      scaleLength (Real.sin θ) α +
        scaleLength (Real.sin (2 * θ)) β

/-- The ray geometry of Figure 2f gives the radius response before its two
trigonometric coefficients are read off. -/
theorem radiusAtIncidence_from_figure2f
    (setup : SolarCookerSetup)
    (figure : Figure2fReadout setup)
    (physics : ValidSolarCookerPhysics setup)
    (θ : ℝ)
    (hθ : IsAdmissibleIncidenceAngle θ) :
    setup.radiusAtIncidence θ =
      scaleLength
        (Real.sin θ - (1 / 2) * Real.sin (2 * θ))
        setup.mirrorRadius := by
  rcases physics.limiting_tangent_path_exists θ hθ with
    ⟨path, hpath, hlimiting, htangent, hreflection, hincidence⟩
  -- The present abstract predicates do not state the geometric consequence of
  -- a limiting tangent path, so these hypotheses cannot yet determine the
  -- numerical value of `radiusAtIncidence θ`.
  sorry

/-- In the formula
`a = α sin θ_max + β sin (2 θ_max)`, Figure 2f and geometrical optics determine
`α = R` and `β = -R/2`. -/
theorem problem_IPhO_2026_2_B_1
    (setup : SolarCookerSetup)
    (figure : Figure2fReadout setup)
    (physics : ValidSolarCookerPhysics setup)
    (α β : PhysicalLength)
    (coefficientFormula : IsRadiusCoefficientFormula setup α β) :
    α = setup.mirrorRadius ∧
      β = scaleLength (-(1 / 2)) setup.mirrorRadius := by
  have h_half : IsAdmissibleIncidenceAngle (Real.pi / 2) := by
    constructor
    · positivity
    · exact le_rfl
  have hgeometry_half :=
    radiusAtIncidence_from_figure2f setup figure physics (Real.pi / 2) h_half
  have hformula_half :=
    coefficientFormula (Real.pi / 2) h_half
  have htwice_half : 2 * (Real.pi / 2) = Real.pi := by
    ring
  have hα : α = setup.mirrorRadius := by
    apply WithDim.ext
    have hval :=
      congrArg WithDim.val (hformula_half.symm.trans hgeometry_half)
    simp only [scaleLength, WithDim.val_add] at hval
    rw [htwice_half, Real.sin_pi_div_two, Real.sin_pi] at hval
    norm_num at hval
    exact hval
  refine ⟨hα, ?_⟩
  have h_quarter : IsAdmissibleIncidenceAngle (Real.pi / 4) := by
    constructor <;> dsimp [IsAdmissibleIncidenceAngle] at *
    · positivity
    · nlinarith [Real.pi_pos]
  have hgeometry_quarter :=
    radiusAtIncidence_from_figure2f setup figure physics (Real.pi / 4) h_quarter
  have hformula_quarter :=
    coefficientFormula (Real.pi / 4) h_quarter
  have htwice_quarter : 2 * (Real.pi / 4) = Real.pi / 2 := by
    ring
  apply WithDim.ext
  have hval :=
    congrArg WithDim.val (hformula_quarter.symm.trans hgeometry_quarter)
  rw [hα] at hval
  simp only [scaleLength, WithDim.val_add] at hval
  rw [htwice_quarter, Real.sin_pi_div_two] at hval
  change β.val = (-(1 / 2) : ℝ) * setup.mirrorRadius.val
  norm_num at hval
  linarith

end IPhO2026Problems.IPhO2026_2_B_1
