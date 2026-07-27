import Mathlib
import Physlib.Units.WithDim.Basic

/-!
# IPhO 2026, problem 2, part B.1

This file formalizes the cross-sectional geometric-optics model in Figure 2f.
Lengths are tagged with PhysLean's length dimension.  Coordinates are real
readouts in metres, and angles are real readouts in radians.
-/

namespace IPhO2026Problems.IPhO2026_2_B_1

noncomputable section

/-- The two-dimensional cross-section perpendicular to the parallel cylinder axes. -/
abbrev CrossSection := EuclideanSpace ℝ (Fin 2)

/-- The ambient space in which the two cylinder-axis directions are compared. -/
abbrev AxisSpace := EuclideanSpace ℝ (Fin 3)

/-- A dimension-tagged length.  Coefficients may be signed, although physical radii are positive. -/
abbrev Length := WithDim Dimension.L𝓭 ℝ

/-- The physical dimension of power, `mass * length^2 / time^3`. -/
def powerDimension : Dimension := ⟨2, -3, 1, 0, 0⟩

/-- The physical dimension of irradiance, power per unit area. -/
def irradianceDimension : Dimension := ⟨0, -3, 1, 0, 0⟩

/-- A dimension-tagged power, used for the source quantity `P₀`. -/
abbrev Power := WithDim powerDimension ℝ

/-- A dimension-tagged irradiance (power per unit area). -/
abbrev Irradiance := WithDim irradianceDimension ℝ

/-- The oriented scalar cross product of two vectors in the cross-section. -/
def cross2D (u v : CrossSection) : ℝ :=
  u 0 * v 1 - u 1 * v 0

/-- Multiplication of a dimension-tagged length by a signed dimensionless scalar. -/
def scaledLength (c : ℝ) (x : Length) : Length :=
  ⟨c * x.val⟩

/--
The physical and coordinate data of the solar cooker.

The common orientation chosen for the two unit axis vectors is a coordinate
choice; their equality records the source statement that the axes are parallel.
The optical axis points in the direction of the incoming sunlight and from the
mirror center toward the container center.
-/
structure SolarCookerSetup where
  mirrorRadius : Length
  containerRadius : Length
  mirrorRadius_pos : 0 < mirrorRadius.val
  containerRadius_pos : 0 < containerRadius.val
  mirrorCenterMeters : CrossSection
  containerCenterMeters : CrossSection
  mirrorAxisDirection : AxisSpace
  containerAxisDirection : AxisSpace
  mirrorAxis_unit : ‖mirrorAxisDirection‖ = 1
  containerAxis_unit : ‖containerAxisDirection‖ = 1
  axes_parallel : containerAxisDirection = mirrorAxisDirection
  opticalAxis : CrossSection
  transverseAxis : CrossSection
  opticalAxis_unit : ‖opticalAxis‖ = 1
  transverseAxis_unit : ‖transverseAxis‖ = 1
  basis_orthogonal : inner ℝ transverseAxis opticalAxis = 0
  basis_orientation : cross2D transverseAxis opticalAxis = 1
  sunlightDirection : CrossSection
  sunlight_along_opticalAxis : sunlightDirection = opticalAxis
  sunlightIrradiance : CrossSection → Irradiance
  sunlight_uniform : ∀ p q, sunlightIrradiance p = sunlightIrradiance q
  sunlightIrradiance_pos : ∀ p, 0 < (sunlightIrradiance p).val
  center_on_symmetry_plane :
    containerCenterMeters - mirrorCenterMeters =
      (mirrorRadius.val / 2) • opticalAxis
  powerWithoutMirror : Power
  powerWithoutMirror_pos : 0 < powerWithoutMirror.val

/-- Membership in the half-circular mirror in the Figure 2f cross-section. -/
def OnHalfMirror (setup : SolarCookerSetup) (p : CrossSection) : Prop :=
  ‖p - setup.mirrorCenterMeters‖ = setup.mirrorRadius.val ∧
    0 ≤ inner ℝ (p - setup.mirrorCenterMeters) setup.opticalAxis

/-- Membership in the circular boundary of the absorbing container. -/
def OnContainerBoundary (setup : SolarCookerSetup) (p : CrossSection) : Prop :=
  ‖p - setup.containerCenterMeters‖ = setup.containerRadius.val

/-- Membership in the closed cross-sectional disk of the absorbing container. -/
def InContainer (setup : SolarCookerSetup) (p : CrossSection) : Prop :=
  ‖p - setup.containerCenterMeters‖ ≤ setup.containerRadius.val

/--
The mirror incidence point corresponding to an incidence angle `theta`.
The coordinate readout is measured in metres.
-/
def canonicalIncidencePoint (setup : SolarCookerSetup) (theta : ℝ) : CrossSection :=
  setup.mirrorCenterMeters +
    setup.mirrorRadius.val •
      (Real.sin theta • setup.transverseAxis + Real.cos theta • setup.opticalAxis)

/-- The outward radial unit normal at the canonical incidence point. -/
def canonicalOutwardNormal (setup : SolarCookerSetup) (theta : ℝ) : CrossSection :=
  Real.sin theta • setup.transverseAxis + Real.cos theta • setup.opticalAxis

/--
The reflected direction obtained from the vector form of the specular
reflection law, `v_out = v_in - 2 ⟪v_in,n⟫ n`.
-/
def canonicalReflectedDirection (setup : SolarCookerSetup) (theta : ℝ) : CrossSection :=
  setup.sunlightDirection -
    (2 * inner ℝ setup.sunlightDirection (canonicalOutwardNormal setup theta)) •
      canonicalOutwardNormal setup theta

/--
The signed perpendicular-distance readout from the canonical reflected line
to the container center.  The branch convention in Figure 2f makes it
nonnegative for the limiting ray.
-/
def limitingRadiusMeters (setup : SolarCookerSetup) (theta : ℝ) : ℝ :=
  cross2D (canonicalReflectedDirection setup theta)
    (setup.containerCenterMeters - canonicalIncidencePoint setup theta)

/-- A directed light ray with its number of previous mirror reflections. -/
structure DirectedRay where
  originMeters : CrossSection
  direction : CrossSection
  direction_unit : ‖direction‖ = 1
  reflectionCount : ℕ

/--
The vector form of specular reflection.  This local interface is used because
Mathlib's affine reflection does not supply a geometric-optics ray law.
-/
structure SpecularReflection
    (incoming normal outgoing : CrossSection) : Prop where
  incoming_unit : ‖incoming‖ = 1
  normal_unit : ‖normal‖ = 1
  outgoing_eq :
    outgoing = incoming - (2 * inner ℝ incoming normal) • normal

/-- A forward ray intersects the closed absorbing cylinder cross-section. -/
def RayHitsContainer
    (setup : SolarCookerSetup) (origin direction : CrossSection) : Prop :=
  ∃ travelMeters : ℝ,
    0 ≤ travelMeters ∧
      InContainer setup (origin + travelMeters • direction)

/--
A limiting reflected ray is tangent to the container on the forward branch.
The last two fields preserve both the tangency equation and the signed-side
choice needed to recover a positive radius.
-/
def LimitingTangentRay
    (setup : SolarCookerSetup) (origin direction : CrossSection) : Prop :=
  ‖direction‖ = 1 ∧
    ∃ travelMeters : ℝ,
      0 ≤ travelMeters ∧
        OnContainerBoundary setup (origin + travelMeters • direction) ∧
        inner ℝ
            (origin + travelMeters • direction - setup.containerCenterMeters)
            direction = 0 ∧
        0 ≤ cross2D direction (setup.containerCenterMeters - origin)

/--
The governing ray-optics model.  Its `Prop`-valued classifications are not
opaque witnesses: the fields below expose absorption, reflection-count,
incidence-coordinate, specular-reflection, and container-hit consequences.
-/
structure SolarOpticsModel (setup : SolarCookerSetup) where
  isIncidentSunRay : DirectedRay → Prop
  isReflectedFromMirror : DirectedRay → Prop
  strikesContainer : DirectedRay → Prop
  isAbsorbedByContainer : DirectedRay → Prop
  incidencePointMeters : DirectedRay → CrossSection
  surfaceNormal : DirectedRay → CrossSection
  reflectedDirection : DirectedRay → CrossSection
  incidenceAngleRadians : DirectedRay → ℝ
  fully_absorbing :
    ∀ ray, strikesContainer ray → isAbsorbedByContainer ray
  absorbed_ray_reflects_at_most_once :
    ∀ ray, isAbsorbedByContainer ray → ray.reflectionCount ≤ 1
  reflected_ray_has_one_reflection :
    ∀ ray, isReflectedFromMirror ray → ray.reflectionCount = 1
  reflected_ray_is_incident_sunlight :
    ∀ ray, isReflectedFromMirror ray → isIncidentSunRay ray
  sunlight_rays_parallel :
    ∀ ray, isIncidentSunRay ray → ray.direction = setup.sunlightDirection
  reflected_ray_hits_half_mirror :
    ∀ ray, isReflectedFromMirror ray →
      OnHalfMirror setup (incidencePointMeters ray)
  incidence_point_is_canonical :
    ∀ ray, isReflectedFromMirror ray →
      incidencePointMeters ray =
        canonicalIncidencePoint setup (incidenceAngleRadians ray)
  surface_normal_is_canonical :
    ∀ ray, isReflectedFromMirror ray →
      surfaceNormal ray =
        canonicalOutwardNormal setup (incidenceAngleRadians ray)
  incidence_angle_range :
    ∀ ray, isReflectedFromMirror ray →
      0 ≤ incidenceAngleRadians ray ∧ incidenceAngleRadians ray ≤ Real.pi / 2
  specular_reflection :
    ∀ ray, isReflectedFromMirror ray →
      SpecularReflection ray.direction (surfaceNormal ray) (reflectedDirection ray)
  reflected_direction_is_canonical :
    ∀ ray, isReflectedFromMirror ray →
      reflectedDirection ray =
        canonicalReflectedDirection setup (incidenceAngleRadians ray)
  reflected_hit_geometry :
    ∀ ray, isReflectedFromMirror ray → strikesContainer ray →
      RayHitsContainer setup (incidencePointMeters ray) (reflectedDirection ray)

/-- `thetaMax` is attained and bounds every reflected ray that strikes the container. -/
def IsMaximumIncidenceAngle
    {setup : SolarCookerSetup} (model : SolarOpticsModel setup) (thetaMax : ℝ) : Prop :=
  (∃ ray,
      model.isReflectedFromMirror ray ∧
      model.strikesContainer ray ∧
      model.incidenceAngleRadians ray = thetaMax) ∧
    ∀ ray,
      model.isReflectedFromMirror ray →
      model.strikesContainer ray →
      model.incidenceAngleRadians ray ≤ thetaMax

/--
The geometric extremality law saying that a largest-angle ray which still
strikes the convex cylinder is tangent to it.  This is an explicit bridge,
not an assumption about the requested coefficients.
-/
structure MaximalRayTangencyLaw
    {setup : SolarCookerSetup} (model : SolarOpticsModel setup) : Prop where
  tangent_of_maximum :
    ∀ thetaMax, IsMaximumIncidenceAngle model thetaMax →
      ∃ ray,
        model.isReflectedFromMirror ray ∧
        model.strikesContainer ray ∧
        model.incidenceAngleRadians ray = thetaMax ∧
        LimitingTangentRay setup
          (model.incidencePointMeters ray) (model.reflectedDirection ray)

/-- Elimination form of the maximal-ray tangency law. -/
theorem maximum_incidence_ray_is_tangent
    {setup : SolarCookerSetup} (model : SolarOpticsModel setup)
    (law : MaximalRayTangencyLaw model) (thetaMax : ℝ)
    (hMax : IsMaximumIncidenceAngle model thetaMax) :
    ∃ ray,
      model.isReflectedFromMirror ray ∧
      model.strikesContainer ray ∧
      model.incidenceAngleRadians ray = thetaMax ∧
      LimitingTangentRay setup
        (model.incidencePointMeters ray) (model.reflectedDirection ray) := by
  exact law.tangent_of_maximum thetaMax hMax

/--
Tangency converts the physical container radius into the signed perpendicular
distance from the ray to the container center.
-/
theorem limiting_tangent_radius_eq_signedDistance
    (setup : SolarCookerSetup) (origin direction : CrossSection)
    (hTangent : LimitingTangentRay setup origin direction) :
    setup.containerRadius.val =
      cross2D direction (setup.containerCenterMeters - origin) := by
  rcases hTangent with
    ⟨hDirectionNorm, travelMeters, _hTravelNonnegative, hBoundary,
      hOrthogonal, hSignedNonnegative⟩
  change
    ‖origin + travelMeters • direction - setup.containerCenterMeters‖ =
      setup.containerRadius.val at hBoundary
  let residual : CrossSection :=
    origin + travelMeters • direction - setup.containerCenterMeters
  have hResidualNorm :
      ‖residual‖ = setup.containerRadius.val := by
    exact hBoundary
  have hResidualOrthogonal : inner ℝ residual direction = 0 := by
    exact hOrthogonal
  have hCenterDisplacement :
      setup.containerCenterMeters - origin =
        travelMeters • direction - residual := by
    dsimp [residual]
    module
  have hDirectionCoordinates :
      direction 0 ^ 2 + direction 1 ^ 2 = 1 := by
    have h := real_inner_self_eq_norm_sq direction
    rw [hDirectionNorm] at h
    rw [PiLp.inner_apply, Fin.sum_univ_two] at h
    simp only [Real.inner_apply] at h
    nlinarith
  have hResidualCoordinates :
      residual 0 ^ 2 + residual 1 ^ 2 =
        setup.containerRadius.val ^ 2 := by
    have h := real_inner_self_eq_norm_sq residual
    rw [hResidualNorm] at h
    rw [PiLp.inner_apply, Fin.sum_univ_two] at h
    simp only [Real.inner_apply] at h
    nlinarith
  have hOrthogonalCoordinates :
      direction 0 * residual 0 + direction 1 * residual 1 = 0 := by
    rw [PiLp.inner_apply, Fin.sum_univ_two] at hResidualOrthogonal
    simp only [Real.inner_apply] at hResidualOrthogonal
    nlinarith
  have hSignedSquare :
      cross2D direction (setup.containerCenterMeters - origin) ^ 2 =
        setup.containerRadius.val ^ 2 := by
    rw [hCenterDisplacement]
    unfold cross2D
    simp only [PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
    linear_combination
      (residual 0 ^ 2 + residual 1 ^ 2) * hDirectionCoordinates +
        hResidualCoordinates -
        (direction 0 * residual 0 + direction 1 * residual 1) *
          hOrthogonalCoordinates
  nlinarith [setup.containerRadius_pos]

/--
For the maximum-incidence ray in the ray model, the actual container radius
equals the canonical limiting-radius readout.
-/
theorem maximum_ray_containerRadius_eq_limitingRadius
    {setup : SolarCookerSetup} (model : SolarOpticsModel setup)
    (law : MaximalRayTangencyLaw model) (thetaMax : ℝ)
    (hMax : IsMaximumIncidenceAngle model thetaMax) :
    setup.containerRadius.val = limitingRadiusMeters setup thetaMax := by
  obtain ⟨ray, hReflected, _hStrikes, hAngle, hTangent⟩ :=
    maximum_incidence_ray_is_tangent model law thetaMax hMax
  calc
    setup.containerRadius.val =
        cross2D (model.reflectedDirection ray)
          (setup.containerCenterMeters - model.incidencePointMeters ray) :=
      limiting_tangent_radius_eq_signedDistance setup
        (model.incidencePointMeters ray) (model.reflectedDirection ray) hTangent
    _ = limitingRadiusMeters setup thetaMax := by
      rw [model.reflected_direction_is_canonical ray hReflected,
        model.incidence_point_is_canonical ray hReflected, hAngle]
      rfl

/--
Expanding the canonical incidence point, specular-reflection equation, and
center offset from Figure 2f gives the two-term trigonometric radius formula.
-/
theorem limitingRadiusMeters_eq_trigFormula
    (setup : SolarCookerSetup) (theta : ℝ) :
    limitingRadiusMeters setup theta =
      setup.mirrorRadius.val * Real.sin theta -
        (setup.mirrorRadius.val / 2) * Real.sin (2 * theta) := by
  have hOrthogonal :
      inner ℝ setup.opticalAxis setup.transverseAxis = 0 := by
    rw [real_inner_comm]
    exact setup.basis_orthogonal
  have hInner :
      inner ℝ setup.sunlightDirection (canonicalOutwardNormal setup theta) =
        Real.cos theta := by
    rw [setup.sunlight_along_opticalAxis]
    simp [canonicalOutwardNormal, inner_add_right, inner_smul_right,
      hOrthogonal, setup.opticalAxis_unit]
  have hCenter :
      setup.containerCenterMeters - canonicalIncidencePoint setup theta =
        (setup.mirrorRadius.val / 2) • setup.opticalAxis -
          setup.mirrorRadius.val • canonicalOutwardNormal setup theta := by
    rw [canonicalIncidencePoint]
    unfold canonicalOutwardNormal
    calc
      setup.containerCenterMeters -
            (setup.mirrorCenterMeters +
              setup.mirrorRadius.val •
                (Real.sin theta • setup.transverseAxis +
                  Real.cos theta • setup.opticalAxis)) =
          (setup.containerCenterMeters - setup.mirrorCenterMeters) -
            setup.mirrorRadius.val •
              (Real.sin theta • setup.transverseAxis +
                Real.cos theta • setup.opticalAxis) := by
        module
      _ = (setup.mirrorRadius.val / 2) • setup.opticalAxis -
            setup.mirrorRadius.val •
              (Real.sin theta • setup.transverseAxis +
                Real.cos theta • setup.opticalAxis) := by
        rw [setup.center_on_symmetry_plane]
  have hOrientation := setup.basis_orientation
  unfold cross2D at hOrientation
  rw [limitingRadiusMeters, canonicalReflectedDirection, hInner,
    setup.sunlight_along_opticalAxis, hCenter]
  simp only [cross2D, canonicalOutwardNormal, PiLp.add_apply, PiLp.smul_apply,
    PiLp.sub_apply, smul_eq_mul]
  rw [Real.sin_two_mul]
  linear_combination
    (setup.mirrorRadius.val * Real.sin theta * (1 - Real.cos theta)) *
      hOrientation

/--
`alpha` and `beta` are the two universal coefficients of the limiting-radius
function, rather than two arbitrary unknowns satisfying one numerical equation.
This functional reading is the coefficient-identification content of B.1.
-/
def AreTrigCoefficients
    (setup : SolarCookerSetup) (alpha beta : Length) : Prop :=
  ∀ theta,
    alpha.val * Real.sin theta + beta.val * Real.sin (2 * theta) =
      limitingRadiusMeters setup theta

/--
The answer to IPhO 2026 problem 2, part B.1:
`alpha = R` and `beta = -R/2`.

The coefficients are exhibited for the actual container-radius equation
derived from the attained maximum ray and the Figure 2f tangency law.  They
are not arbitrary unknowns inferred from a single underdetermined equation.
-/
theorem coefficients_from_solar_cooker_geometry
    (setup : SolarCookerSetup) (model : SolarOpticsModel setup)
    (tangencyLaw : MaximalRayTangencyLaw model) (thetaMax : ℝ)
    (thetaMax_is_maximum : IsMaximumIncidenceAngle model thetaMax) :
    ∃ alpha beta : Length,
      setup.containerRadius.val =
          alpha.val * Real.sin thetaMax + beta.val * Real.sin (2 * thetaMax) ∧
        alpha = setup.mirrorRadius ∧
        beta = scaledLength (-(1 / 2 : ℝ)) setup.mirrorRadius := by
  refine ⟨setup.mirrorRadius,
    scaledLength (-(1 / 2 : ℝ)) setup.mirrorRadius, ?_, rfl, rfl⟩
  calc
    setup.containerRadius.val =
        limitingRadiusMeters setup thetaMax :=
      maximum_ray_containerRadius_eq_limitingRadius
        model tangencyLaw thetaMax thetaMax_is_maximum
    _ = setup.mirrorRadius.val * Real.sin thetaMax -
          (setup.mirrorRadius.val / 2) * Real.sin (2 * thetaMax) :=
      limitingRadiusMeters_eq_trigFormula setup thetaMax
    _ = setup.mirrorRadius.val * Real.sin thetaMax +
          (scaledLength (-(1 / 2 : ℝ)) setup.mirrorRadius).val *
            Real.sin (2 * thetaMax) := by
      simp only [scaledLength]
      ring

end

end IPhO2026_2_B_1

end IPhO2026Problems
