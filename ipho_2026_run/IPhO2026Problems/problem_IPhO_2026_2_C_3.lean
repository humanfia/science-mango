import Mathlib
import Physlib.Units.WithDim.Basic

open Filter Topology Asymptotics

namespace IPhO2026Problems.IPhO2026_2_C_3

/-!
# IPhO 2026, theoretical problem 2, part C.3

The types below distinguish physical lengths from their numerical coordinates.
All equations and limits are expressed through one named projection to the
common length unit of Figure 2g.
-/

/-- A physical length whose values in different unit systems obey Physlib's
dimensional scaling law. -/
abbrev PhysicalLength :=
  Dimensionful (WithDim Dimension.L𝓭 ℝ)

/-- The chosen length-unit projection for the common coordinate frame of
Figure 2g. -/
structure Figure2gLengthProjection where
  unitChoice : UnitChoices

/-- The real coordinate readout of a physical length in the fixed Figure 2g
length unit. -/
def Figure2gLengthProjection.readout
    (projection : Figure2gLengthProjection) (length : PhysicalLength) : ℝ :=
  (length projection.unitChoice).val

/-- The half-cylindrical mirror in the coordinate system of Figure 2g.

The radius is a physical length, rather than a bare scalar readout. -/
structure Figure2gMirror where
  radius : PhysicalLength
  radius_pos : ∀ unitChoice : UnitChoices, 0 < (radius unitChoice).val

/-- A point represented by two physical length coordinates in Figure 2g. -/
structure Figure2gPoint where
  xCoordinate : PhysicalLength
  yCoordinate : PhysicalLength

/-- The reflecting upper semicircle shown in Figure 2g. -/
def Figure2gMirror.OnReflectingSurface
    (projection : Figure2gLengthProjection)
    (mirror : Figure2gMirror) (point : Figure2gPoint) : Prop :=
  projection.readout point.xCoordinate ^ 2 +
        projection.readout point.yCoordinate ^ 2 =
      projection.readout mirror.radius ^ 2 ∧
    0 ≤ projection.readout point.yCoordinate

/-- The supporting affine line of a reflected optical ray in Figure 2g.

The slope is dimensionless, while the intercept is a physical length. -/
structure ReflectedRayLine where
  slopeRatio : ℝ
  yIntercept : PhysicalLength

/-- A Figure 2g point lies on the supporting line of a reflected ray. -/
def ReflectedRayLine.Contains
    (projection : Figure2gLengthProjection)
    (ray : ReflectedRayLine) (point : Figure2gPoint) : Prop :=
  projection.readout point.yCoordinate =
    ray.slopeRatio * projection.readout point.xCoordinate +
      projection.readout ray.yIntercept

/-- A point is the intersection of the reflected ray at incidence angle `θ`
(ray A) and the reflected ray at the neighboring angle `θ + Δθ` (ray B). -/
def IsNeighboringReflectedIntersection
    (projection : Figure2gLengthProjection)
    (reflectedRayAtIncidenceAngle : ℝ → ReflectedRayLine)
    (θ Δθ : ℝ) (point : Figure2gPoint) : Prop :=
  (reflectedRayAtIncidenceAngle θ).Contains projection point ∧
    (reflectedRayAtIncidenceAngle (θ + Δθ)).Contains projection point

/-- For the half-cylindrical mirror of Figure 2g, the intersections of ray A
with neighboring reflected rays tend to the stated point of the caustic.

The two Big-O hypotheses are precisely the first-order ray-B data from part
C.2, expressed without choosing a particular nonzero `Δθ`. The two equalities
for ray A are the reusable conclusions of part C.1. Every length occurring in
these assumptions and in the conclusion is read through the same
`lengthProjection`. -/
theorem limitingIntersectionCoordinates
    (lengthProjection : Figure2gLengthProjection)
    (mirror : Figure2gMirror)
    (θ : ℝ)
    (reflectedRayAtIncidenceAngle : ℝ → ReflectedRayLine)
    (neighboringIntersection : ℝ → Figure2gPoint)
    (hθ_pos : 0 < θ)
    (hθ_acute : θ < Real.pi / 2)
    (hRayA_slope :
      (reflectedRayAtIncidenceAngle θ).slopeRatio =
        Real.cot (2 * θ))
    (hRayA_intercept :
      lengthProjection.readout
          (reflectedRayAtIncidenceAngle θ).yIntercept =
        lengthProjection.readout mirror.radius / (2 * Real.cos θ))
    (hRayB_slope_firstOrder :
      (fun Δθ : ℝ ↦
          (reflectedRayAtIncidenceAngle (θ + Δθ)).slopeRatio -
            (Real.cot (2 * θ) -
              2 * (Real.sin (2 * θ))⁻¹ ^ 2 * Δθ))
        =O[𝓝 0] (fun Δθ : ℝ ↦ Δθ ^ 2))
    (hRayB_intercept_firstOrder :
      (fun Δθ : ℝ ↦
          lengthProjection.readout
              (reflectedRayAtIncidenceAngle (θ + Δθ)).yIntercept -
            ((lengthProjection.readout mirror.radius /
                (2 * Real.cos θ)) *
              (1 + Real.tan θ * Δθ)))
        =O[𝓝 0] (fun Δθ : ℝ ↦ Δθ ^ 2))
    (hNeighboringIntersection :
      ∀ᶠ Δθ in 𝓝[≠] (0 : ℝ),
        IsNeighboringReflectedIntersection
          lengthProjection reflectedRayAtIncidenceAngle
          θ Δθ (neighboringIntersection Δθ)) :
    Tendsto
        (fun Δθ ↦
          lengthProjection.readout
            (neighboringIntersection Δθ).xCoordinate)
        (𝓝[≠] (0 : ℝ))
        (𝓝
          (lengthProjection.readout mirror.radius *
            (Real.sin θ) ^ 3)) ∧
      Tendsto
        (fun Δθ ↦
          lengthProjection.readout
            (neighboringIntersection Δθ).yCoordinate)
        (𝓝[≠] (0 : ℝ))
        (𝓝
          ((lengthProjection.readout mirror.radius / 2) * Real.cos θ *
            (2 - Real.cos (2 * θ)))) := by
  have hθ_lt_pi : θ < Real.pi := by
    linarith [Real.pi_pos]
  have hsinθ_pos : 0 < Real.sin θ :=
    Real.sin_pos_of_pos_of_lt_pi hθ_pos hθ_lt_pi
  have hcosθ_pos : 0 < Real.cos θ :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hθ_acute⟩
  have hsin_twoθ_pos : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have hSlopeErrorLittle :
      (fun Δθ : ℝ ↦
          (reflectedRayAtIncidenceAngle (θ + Δθ)).slopeRatio -
            (Real.cot (2 * θ) -
              2 * (Real.sin (2 * θ))⁻¹ ^ 2 * Δθ))
        =o[𝓝 0] (fun Δθ : ℝ ↦ Δθ) :=
    hRayB_slope_firstOrder.trans_isLittleO
      (isLittleO_pow_id (by norm_num))
  have hSlopeErrorQuotient :
      Tendsto
        (fun Δθ : ℝ ↦
          ((reflectedRayAtIncidenceAngle (θ + Δθ)).slopeRatio -
            (Real.cot (2 * θ) -
              2 * (Real.sin (2 * θ))⁻¹ ^ 2 * Δθ)) / Δθ)
        (𝓝[≠] (0 : ℝ)) (𝓝 0) :=
    hSlopeErrorLittle.tendsto_div_nhds_zero.mono_left inf_le_left
  have hSlopeQuotient :
      Tendsto
        (fun Δθ : ℝ ↦
          ((reflectedRayAtIncidenceAngle (θ + Δθ)).slopeRatio -
            Real.cot (2 * θ)) / Δθ)
        (𝓝[≠] (0 : ℝ))
        (𝓝 (-(2 * (Real.sin (2 * θ))⁻¹ ^ 2))) := by
    have hLimit :=
      (tendsto_const_nhds.add hSlopeErrorQuotient :
        Tendsto
          (fun Δθ : ℝ ↦
            -(2 * (Real.sin (2 * θ))⁻¹ ^ 2) +
              ((reflectedRayAtIncidenceAngle (θ + Δθ)).slopeRatio -
                (Real.cot (2 * θ) -
                  2 * (Real.sin (2 * θ))⁻¹ ^ 2 * Δθ)) / Δθ)
          (𝓝[≠] (0 : ℝ))
          (𝓝 (-(2 * (Real.sin (2 * θ))⁻¹ ^ 2) + 0)))
    have hEventually :
        (fun Δθ : ℝ ↦
            -(2 * (Real.sin (2 * θ))⁻¹ ^ 2) +
              ((reflectedRayAtIncidenceAngle (θ + Δθ)).slopeRatio -
                (Real.cot (2 * θ) -
                  2 * (Real.sin (2 * θ))⁻¹ ^ 2 * Δθ)) / Δθ)
          =ᶠ[𝓝[≠] (0 : ℝ)]
        (fun Δθ : ℝ ↦
          ((reflectedRayAtIncidenceAngle (θ + Δθ)).slopeRatio -
            Real.cot (2 * θ)) / Δθ) := by
      filter_upwards [self_mem_nhdsWithin] with Δθ hΔθ
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hΔθ
      field_simp
      ring
    simpa using hLimit.congr' hEventually
  have hInterceptErrorLittle :
      (fun Δθ : ℝ ↦
          lengthProjection.readout
              (reflectedRayAtIncidenceAngle (θ + Δθ)).yIntercept -
            ((lengthProjection.readout mirror.radius /
                (2 * Real.cos θ)) *
              (1 + Real.tan θ * Δθ)))
        =o[𝓝 0] (fun Δθ : ℝ ↦ Δθ) :=
    hRayB_intercept_firstOrder.trans_isLittleO
      (isLittleO_pow_id (by norm_num))
  have hInterceptErrorQuotient :
      Tendsto
        (fun Δθ : ℝ ↦
          (lengthProjection.readout
                (reflectedRayAtIncidenceAngle (θ + Δθ)).yIntercept -
              ((lengthProjection.readout mirror.radius /
                  (2 * Real.cos θ)) *
                (1 + Real.tan θ * Δθ))) / Δθ)
        (𝓝[≠] (0 : ℝ)) (𝓝 0) :=
    hInterceptErrorLittle.tendsto_div_nhds_zero.mono_left inf_le_left
  have hInterceptQuotient :
      Tendsto
        (fun Δθ : ℝ ↦
          (lengthProjection.readout
                (reflectedRayAtIncidenceAngle (θ + Δθ)).yIntercept -
              lengthProjection.readout mirror.radius /
                (2 * Real.cos θ)) / Δθ)
        (𝓝[≠] (0 : ℝ))
        (𝓝
          ((lengthProjection.readout mirror.radius /
              (2 * Real.cos θ)) * Real.tan θ)) := by
    have hLimit :=
      (tendsto_const_nhds.add hInterceptErrorQuotient :
        Tendsto
          (fun Δθ : ℝ ↦
            (lengthProjection.readout mirror.radius /
                (2 * Real.cos θ)) * Real.tan θ +
              (lengthProjection.readout
                    (reflectedRayAtIncidenceAngle (θ + Δθ)).yIntercept -
                  ((lengthProjection.readout mirror.radius /
                      (2 * Real.cos θ)) *
                    (1 + Real.tan θ * Δθ))) / Δθ)
          (𝓝[≠] (0 : ℝ))
          (𝓝
            ((lengthProjection.readout mirror.radius /
                (2 * Real.cos θ)) * Real.tan θ + 0)))
    have hEventually :
        (fun Δθ : ℝ ↦
            (lengthProjection.readout mirror.radius /
                (2 * Real.cos θ)) * Real.tan θ +
              (lengthProjection.readout
                    (reflectedRayAtIncidenceAngle (θ + Δθ)).yIntercept -
                  ((lengthProjection.readout mirror.radius /
                      (2 * Real.cos θ)) *
                    (1 + Real.tan θ * Δθ))) / Δθ)
          =ᶠ[𝓝[≠] (0 : ℝ)]
        (fun Δθ : ℝ ↦
          (lengthProjection.readout
                (reflectedRayAtIncidenceAngle (θ + Δθ)).yIntercept -
              lengthProjection.readout mirror.radius /
                (2 * Real.cos θ)) / Δθ) := by
      filter_upwards [self_mem_nhdsWithin] with Δθ hΔθ
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hΔθ
      field_simp
      ring
    simpa using hLimit.congr' hEventually
  have hSlopeLimit_ne :
      -(2 * (Real.sin (2 * θ))⁻¹ ^ 2) ≠ 0 := by
    exact neg_ne_zero.mpr
      (mul_ne_zero (by norm_num)
        (pow_ne_zero 2 (inv_ne_zero hsin_twoθ_pos.ne')))
  have hSlopeQuotient_ne :
      ∀ᶠ Δθ in 𝓝[≠] (0 : ℝ),
        ((reflectedRayAtIncidenceAngle (θ + Δθ)).slopeRatio -
            Real.cot (2 * θ)) / Δθ ≠ 0 :=
    hSlopeQuotient.eventually_ne hSlopeLimit_ne
  have hXEventual :
      (fun Δθ : ℝ ↦
          lengthProjection.readout
            (neighboringIntersection Δθ).xCoordinate)
        =ᶠ[𝓝[≠] (0 : ℝ)]
      (fun Δθ : ℝ ↦
        -((lengthProjection.readout
                (reflectedRayAtIncidenceAngle (θ + Δθ)).yIntercept -
              lengthProjection.readout mirror.radius /
                (2 * Real.cos θ)) / Δθ) /
          (((reflectedRayAtIncidenceAngle (θ + Δθ)).slopeRatio -
              Real.cot (2 * θ)) / Δθ)) := by
    filter_upwards [hNeighboringIntersection, hSlopeQuotient_ne,
      self_mem_nhdsWithin] with Δθ hIntersection hSlopeNe hΔθ
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hΔθ
    rcases hIntersection with ⟨hRayA, hRayB⟩
    rw [ReflectedRayLine.Contains] at hRayA hRayB
    rw [hRayA_slope, hRayA_intercept] at hRayA
    have hLineDifference :
        ((reflectedRayAtIncidenceAngle (θ + Δθ)).slopeRatio -
            Real.cot (2 * θ)) *
              lengthProjection.readout
                (neighboringIntersection Δθ).xCoordinate +
          (lengthProjection.readout
                (reflectedRayAtIncidenceAngle (θ + Δθ)).yIntercept -
            lengthProjection.readout mirror.radius /
              (2 * Real.cos θ)) = 0 := by
      linarith
    have hSlopeDifference_ne :
        (reflectedRayAtIncidenceAngle (θ + Δθ)).slopeRatio -
            Real.cot (2 * θ) ≠ 0 := by
      intro h
      apply hSlopeNe
      simp [h]
    have hSolved :
        lengthProjection.readout
              (neighboringIntersection Δθ).xCoordinate =
          -(lengthProjection.readout
                (reflectedRayAtIncidenceAngle (θ + Δθ)).yIntercept -
              lengthProjection.readout mirror.radius /
                (2 * Real.cos θ)) /
            ((reflectedRayAtIncidenceAngle (θ + Δθ)).slopeRatio -
              Real.cot (2 * θ)) := by
      apply (eq_div_iff hSlopeDifference_ne).2
      linarith
    rw [hSolved]
    field_simp [hΔθ, hSlopeDifference_ne]
  have hXRatioLimit :
      Tendsto
        (fun Δθ : ℝ ↦
          -((lengthProjection.readout
                  (reflectedRayAtIncidenceAngle (θ + Δθ)).yIntercept -
                lengthProjection.readout mirror.radius /
                  (2 * Real.cos θ)) / Δθ) /
            (((reflectedRayAtIncidenceAngle (θ + Δθ)).slopeRatio -
                Real.cot (2 * θ)) / Δθ))
        (𝓝[≠] (0 : ℝ))
        (𝓝
          (-
              ((lengthProjection.readout mirror.radius /
                (2 * Real.cos θ)) * Real.tan θ) /
            (-(2 * (Real.sin (2 * θ))⁻¹ ^ 2)))) :=
    hInterceptQuotient.neg.div hSlopeQuotient hSlopeLimit_ne
  have hXValue :
      (-
            ((lengthProjection.readout mirror.radius /
              (2 * Real.cos θ)) * Real.tan θ) /
          (-(2 * (Real.sin (2 * θ))⁻¹ ^ 2))) =
        lengthProjection.readout mirror.radius * Real.sin θ ^ 3 := by
    rw [Real.tan_eq_sin_div_cos, Real.sin_two_mul]
    field_simp
  have hXLimit :
      Tendsto
        (fun Δθ : ℝ ↦
          lengthProjection.readout
            (neighboringIntersection Δθ).xCoordinate)
        (𝓝[≠] (0 : ℝ))
        (𝓝
          (lengthProjection.readout mirror.radius *
            Real.sin θ ^ 3)) := by
    rw [← hXValue]
    exact hXRatioLimit.congr' hXEventual.symm
  have hYEventual :
      (fun Δθ : ℝ ↦
          lengthProjection.readout
            (neighboringIntersection Δθ).yCoordinate)
        =ᶠ[𝓝[≠] (0 : ℝ)]
      (fun Δθ : ℝ ↦
        Real.cot (2 * θ) *
            lengthProjection.readout
              (neighboringIntersection Δθ).xCoordinate +
          lengthProjection.readout mirror.radius /
            (2 * Real.cos θ)) := by
    filter_upwards [hNeighboringIntersection] with Δθ hIntersection
    rcases hIntersection with ⟨hRayA, _⟩
    rw [ReflectedRayLine.Contains] at hRayA
    simpa only [hRayA_slope, hRayA_intercept] using hRayA
  have hYRawLimit :
      Tendsto
        (fun Δθ : ℝ ↦
          Real.cot (2 * θ) *
              lengthProjection.readout
                (neighboringIntersection Δθ).xCoordinate +
            lengthProjection.readout mirror.radius /
              (2 * Real.cos θ))
        (𝓝[≠] (0 : ℝ))
        (𝓝
          (Real.cot (2 * θ) *
              (lengthProjection.readout mirror.radius *
                Real.sin θ ^ 3) +
            lengthProjection.readout mirror.radius /
              (2 * Real.cos θ))) :=
    (tendsto_const_nhds.mul hXLimit).add tendsto_const_nhds
  have hYValue :
      Real.cot (2 * θ) *
            (lengthProjection.readout mirror.radius *
              Real.sin θ ^ 3) +
          lengthProjection.readout mirror.radius /
            (2 * Real.cos θ) =
        (lengthProjection.readout mirror.radius / 2) * Real.cos θ *
          (2 - Real.cos (2 * θ)) := by
    rw [Real.cot_eq_cos_div_sin, Real.sin_two_mul,
      Real.cos_two_mul_eq_one_sub]
    field_simp
    have hcos_sq : Real.cos θ ^ 2 = 1 - Real.sin θ ^ 2 := by
      nlinarith [Real.sin_sq_add_cos_sq θ]
    rw [hcos_sq]
    ring
  constructor
  · exact hXLimit
  · rw [← hYValue]
    exact hYRawLimit.congr' hYEventual.symm

end IPhO2026Problems.IPhO2026_2_C_3
