import Mathlib
import Physlib.Units.WithDim.Basic

open Filter Topology Asymptotics

namespace IPhO2026Problems.IPhO2026_2_C_3

/-!
# IPhO 2026, theoretical problem 2, part C.3 (Figure 2g)

The types below distinguish physical lengths from their numerical
coordinate readouts.  All equations and limits are expressed through one
named projection to the common length unit of Figure 2g, so that the
formalization never identifies a physical length with a bare real number.
-/

/-- A physical length: values in different unit systems obey Physlib's
dimensional scaling law for the length dimension `L𝓭`. -/
abbrev PhysicalLength :=
  Dimensionful (WithDim Dimension.L𝓭 ℝ)

/-- The chosen length-unit projection for the common coordinate frame of
Figure 2g.  All coordinate readouts below are taken with respect to this
single fixed unit choice. -/
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

/-- The reflecting upper semicircle shown in Figure 2g: the upper half of
the circle of radius `R` centred at the origin. -/
def Figure2gMirror.OnReflectingSurface
    (projection : Figure2gLengthProjection)
    (mirror : Figure2gMirror) (point : Figure2gPoint) : Prop :=
  projection.readout point.xCoordinate ^ 2 +
        projection.readout point.yCoordinate ^ 2 =
      projection.readout mirror.radius ^ 2 ∧
    0 ≤ projection.readout point.yCoordinate

/-- The supporting affine line `y = m x + b` of a reflected optical ray in
Figure 2g.  The slope `m` is dimensionless, while the intercept `b` is a
physical length. -/
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
(ray A) and the reflected ray at the neighboring incidence angle `θ + Δθ`
(ray B): both line equations hold simultaneously. -/
def IsNeighboringReflectedIntersection
    (projection : Figure2gLengthProjection)
    (reflectedRayAtIncidenceAngle : ℝ → ReflectedRayLine)
    (θ Δθ : ℝ) (point : Figure2gPoint) : Prop :=
  (reflectedRayAtIncidenceAngle θ).Contains projection point ∧
    (reflectedRayAtIncidenceAngle (θ + Δθ)).Contains projection point

/-- For the half-cylindrical mirror of radius `R` of Figure 2g, the
intersection of the reflected ray A with the reflected neighboring ray B
tends, as `Δθ → 0`, to the caustic point
`X_c = R sin³θ`, `Y_c = (R/2) cos θ (2 - cos 2θ)`.

Assumption/target split:
* `hRayA_slope`, `hRayA_intercept` — the part C.1 results
  `m_A = cot 2θ`, `b_A = R/(2 cos θ)`, reusable previous-part conclusions;
* `hRayB_slope_firstOrder`, `hRayB_intercept_firstOrder` — the part C.2
  first-order expansions of `m_B` and `b_B` in `Δθ`, stated as genuine
  `O(Δθ²)` asymptotic hypotheses on the ray family rather than as the
  values of the limit;
* `hNeighboringIntersection` — for all sufficiently small nonzero `Δθ`
  the two reflected lines meet at `neighboringIntersection Δθ`;
* the conclusion — the limit statement, which is the current target and
  does not occur among the hypotheses. -/
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
            Real.sin θ ^ 3)) ∧
      Tendsto
        (fun Δθ ↦
          lengthProjection.readout
            (neighboringIntersection Δθ).yCoordinate)
        (𝓝[≠] (0 : ℝ))
        (𝓝
          ((lengthProjection.readout mirror.radius / 2) * Real.cos θ *
            (2 - Real.cos (2 * θ)))) := by
  -- Abbreviations for the recurring slope/intercept/point-coordinate readouts.
  set slopeval : ℝ → ℝ :=
    fun a ↦ (reflectedRayAtIncidenceAngle a).slopeRatio with hslopeval
  set icept : ℝ → ℝ :=
    fun a ↦
      lengthProjection.readout
        (reflectedRayAtIncidenceAngle a).yIntercept with hicept
  set xcoord : ℝ → ℝ :=
    fun d ↦
      lengthProjection.readout
        (neighboringIntersection d).xCoordinate with hxcoord
  set ycoord : ℝ → ℝ :=
    fun d ↦
      lengthProjection.readout
        (neighboringIntersection d).yCoordinate with hycoord
  set radiusval : ℝ :=
    lengthProjection.readout mirror.radius with hradiusval
  set tanθ : ℝ := Real.tan θ with htanθ
  set cot2θ : ℝ := Real.cot (2 * θ) with hcot2θ
  set s2inv : ℝ := (Real.sin (2 * θ))⁻¹ ^ 2 with hs2inv
  -- Positivity / non-vanishing of the trigonometric data on `(0, π/2)`.
  have hcosθ : 0 < Real.cos θ := by
    apply Real.cos_pos_of_mem_Ioo
    exact ⟨by linarith [Real.pi_pos], hθ_acute⟩
  have hs2θ : 0 < Real.sin (2 * θ) := by
    apply Real.sin_pos_of_pos_of_lt_pi
    · linarith
    · linarith [Real.pi_pos]
  have hradius : 0 < radiusval := mirror.radius_pos _
  have hs2inv_pos : 0 < s2inv := by positivity
  have htwo : (2 : ℝ) ≠ 0 := by norm_num
  have hslope : slopeval θ = cot2θ := by
    rw [hcot2θ]; exact hRayA_slope
  have hiceptA : icept θ = radiusval / (2 * Real.cos θ) :=
    hRayA_intercept
  -- Remainder functions of the two first-order expansions.
  set fslope : ℝ → ℝ :=
    fun d ↦
      slopeval (θ + d) - (Real.cot (2 * θ) - 2 * (Real.sin (2 * θ))⁻¹ ^ 2 * d)
      with hfslope
  set ficept : ℝ → ℝ :=
    fun d ↦
      icept (θ + d) -
        radiusval / (2 * Real.cos θ) * (1 + Real.tan θ * d) with hficept
  have hfslopeO : fslope =O[𝓝 0] fun d : ℝ ↦ d ^ 2 :=
    hRayB_slope_firstOrder
  have hficeptO : ficept =O[𝓝 0] fun d : ℝ ↦ d ^ 2 :=
    hRayB_intercept_firstOrder
  -- The remainders are `o(Δθ)`, hence `remainder/Δθ → 0`.
  have hpow : (fun d : ℝ ↦ d ^ 2) =o[𝓝 0] fun d : ℝ ↦ d := by
    have h := Asymptotics.isLittleO_pow_pow (𝕜 := ℝ) (m := 1) (n := 2)
      (by norm_num : 1 < 2)
    simpa using h
  have hfslopeLittle : fslope =o[𝓝 0] fun d : ℝ ↦ d :=
    hfslopeO.trans_isLittleO hpow
  have hficeptLittle : ficept =o[𝓝 0] fun d : ℝ ↦ d :=
    hficeptO.trans_isLittleO hpow
  have hfslopeLim : Tendsto (fun d : ℝ ↦ fslope d / d) (𝓝 0) (𝓝 0) :=
    hfslopeLittle.tendsto_div_nhds_zero
  have hficeptLim : Tendsto (fun d : ℝ ↦ ficept d / d) (𝓝 0) (𝓝 0) :=
    hficeptLittle.tendsto_div_nhds_zero
  -- The slope-difference and intercept-difference decompositions.
  have hSDiff : ∀ d : ℝ, slopeval θ - slopeval (θ + d) =
      2 * s2inv * d - fslope d := by
    intro d
    have hf1 : fslope d =
        slopeval (θ + d) -
          (Real.cot (2 * θ) - 2 * (Real.sin (2 * θ))⁻¹ ^ 2 * d) := by
      simp only [hslopeval, hfslope]
    rw [hf1, hslope]
    simp only [hcot2θ, hs2inv]
    ring
  have hySub : ∀ d : ℝ, icept (θ + d) - icept θ =
      radiusval * tanθ / (2 * Real.cos θ) * d + ficept d := by
    intro d
    have hficept_d : ficept d =
        icept (θ + d) -
          radiusval / (2 * Real.cos θ) * (1 + tanθ * d) := by
      calc ficept d
          = icept (θ + d) -
              radiusval / (2 * Real.cos θ) * (1 + Real.tan θ * d) := by
            rw [hficept]
        _ = icept (θ + d) -
              radiusval / (2 * Real.cos θ) * (1 + tanθ * d) := by
            rw [htanθ]
    have h3 : icept (θ + d) =
        radiusval / (2 * Real.cos θ) * (1 + tanθ * d) + ficept d := by
      linarith [hficept_d]
    rw [h3, hiceptA]
    ring
  -- Eventual non-vanishing of the slope difference for small nonzero `d`.
  have hSDiffNe : ∀ᶠ d in 𝓝[≠] (0 : ℝ),
      slopeval θ - slopeval (θ + d) ≠ 0 := by
    have hEv : ∀ᶠ d in 𝓝 (0 : ℝ), fslope d / d ≠ 2 * s2inv :=
      hfslopeLim.eventually_ne (show (0 : ℝ) ≠ 2 * s2inv by positivity)
    filter_upwards [hEv.filter_mono nhdsWithin_le_nhds,
      self_mem_nhdsWithin] with d hfne hdmem
    have hdne : d ≠ 0 := Set.mem_compl_singleton_iff.1 hdmem
    intro hzero
    have h5 : fslope d = 2 * s2inv * d := by linarith [hzero]
    have h4 : fslope d / d = 2 * s2inv := by
      rw [div_eq_iff hdne]
      exact h5
    exact hfne h4
  -- The x-coordinate of the intersection, in division form.
  have hXDiv : ∀ᶠ d in 𝓝[≠] (0 : ℝ),
      xcoord d =
        (radiusval * tanθ / (2 * Real.cos θ) + ficept d / d) /
          (2 * s2inv - fslope d / d) := by
    filter_upwards [hSDiffNe, hNeighboringIntersection,
      self_mem_nhdsWithin] with d hsne hd hmem
    obtain ⟨hd₁, hd₂⟩ := hd
    have hdne : d ≠ 0 := Set.mem_compl_singleton_iff.1 hmem
    have hdA : ycoord d = slopeval θ * xcoord d + icept θ := hd₁
    have hdB : ycoord d = slopeval (θ + d) * xcoord d + icept (θ + d) := hd₂
    have hsub_sub : (slopeval θ - slopeval (θ + d)) * xcoord d =
        icept (θ + d) - icept θ := by linarith
    have h4 : xcoord d =
        (icept (θ + d) - icept θ) / (slopeval θ - slopeval (θ + d)) := by
      rw [eq_div_iff hsne]
      linarith [hsub_sub]
    rw [h4, hySub d, hSDiff d]
    have h5 : (radiusval * tanθ / (2 * Real.cos θ) * d + ficept d) /
          (2 * s2inv * d - fslope d) =
        (radiusval * tanθ / (2 * Real.cos θ) + ficept d / d) /
          (2 * s2inv - fslope d / d) := by
      have hn1 : radiusval * tanθ / (2 * Real.cos θ) * d + ficept d =
          (radiusval * tanθ / (2 * Real.cos θ) + ficept d / d) * d := by
        rw [add_mul, div_mul_cancel₀ _ hdne]
      have hn2 : 2 * s2inv * d - fslope d =
          (2 * s2inv - fslope d / d) * d := by
        rw [sub_mul, div_mul_cancel₀ _ hdne]
      rw [hn1, hn2]
      exact mul_div_mul_right _ _ hdne
    exact h5
  -- Limits of the two sides of the x-coordinate division.
  have hnumLim : Tendsto
      (fun d : ℝ ↦ radiusval * tanθ / (2 * Real.cos θ) + ficept d / d)
      (𝓝[≠] (0 : ℝ))
      (𝓝 (radiusval * tanθ / (2 * Real.cos θ))) := by
    have h1 := (tendsto_const_nhds
        (x := radiusval * tanθ / (2 * Real.cos θ))).add hficeptLim
    have h2 : Tendsto
        (fun d : ℝ ↦ radiusval * tanθ / (2 * Real.cos θ) + ficept d / d)
        (𝓝[≠] 0) (𝓝 (radiusval * tanθ / (2 * Real.cos θ) + 0)) :=
      h1.mono_left nhdsWithin_le_nhds
    simpa using h2
  have hdenLim : Tendsto (fun d : ℝ ↦ 2 * s2inv - fslope d / d)
      (𝓝[≠] (0 : ℝ)) (𝓝 (2 * s2inv)) := by
    have h1 := (tendsto_const_nhds (x := 2 * s2inv)).sub hfslopeLim
    have h2 : Tendsto (fun d : ℝ ↦ 2 * s2inv - fslope d / d) (𝓝[≠] 0)
        (𝓝 (2 * s2inv - 0)) :=
      h1.mono_left nhdsWithin_le_nhds
    simpa using h2
  have h2s2inv_ne : (2 : ℝ) * s2inv ≠ 0 := mul_ne_zero htwo (ne_of_gt hs2inv_pos)
  -- Limit of the x-coordinate.
  have hXLim : Tendsto xcoord (𝓝[≠] (0 : ℝ))
      (𝓝 (radiusval * tanθ / (2 * Real.cos θ) / (2 * s2inv))) :=
    (tendsto_congr' hXDiv).mpr (hnumLim.div hdenLim h2s2inv_ne)
  -- The trig identity reducing the quotient to `radiusval * sin³θ`.
  have hXTrig : radiusval * tanθ / (2 * Real.cos θ) / (2 * s2inv) =
      radiusval * Real.sin θ ^ 3 := by
    have hcθ : Real.cos θ ≠ 0 := ne_of_gt hcosθ
    have hs2 : Real.sin (2 * θ) ≠ 0 := ne_of_gt hs2θ
    rw [htanθ, Real.tan_eq_sin_div_cos, hs2inv, Real.sin_two_mul]
    field_simp [hcθ, hs2]
  -- The y-coordinate: rewrite through the ray A line.
  have hYEq : ∀ᶠ d in 𝓝[≠] (0 : ℝ),
      ycoord d = slopeval θ * xcoord d + icept θ := by
    filter_upwards [hNeighboringIntersection] with d hd
    exact hd.1
  have hYLim : Tendsto ycoord (𝓝[≠] (0 : ℝ))
      (𝓝 (cot2θ * (radiusval * Real.sin θ ^ 3) +
        radiusval / (2 * Real.cos θ))) := by
    have h1 : Tendsto (fun d : ℝ ↦ slopeval θ * xcoord d + icept θ)
        (𝓝[≠] (0 : ℝ))
        (𝓝 (slopeval θ * (radiusval * Real.sin θ ^ 3) + icept θ)) := by
      have h2 : Tendsto xcoord (𝓝[≠] (0 : ℝ))
          (𝓝 (radiusval * Real.sin θ ^ 3)) := by
        rw [← hXTrig]; exact hXLim
      exact (tendsto_const_nhds.mul h2).add tendsto_const_nhds
    have h3 : Tendsto ycoord (𝓝[≠] (0 : ℝ))
        (𝓝 (slopeval θ * (radiusval * Real.sin θ ^ 3) + icept θ)) :=
      (tendsto_congr' hYEq).mpr h1
    rw [hslope, hiceptA] at h3
    exact h3
  -- The final trig identity for `Y_c`.
  have hYTrig : cot2θ * (radiusval * Real.sin θ ^ 3) +
        radiusval / (2 * Real.cos θ) =
      radiusval / 2 * Real.cos θ * (2 - Real.cos (2 * θ)) := by
    have hcθ : Real.cos θ ≠ 0 := ne_of_gt hcosθ
    have hs2 : Real.sin (2 * θ) ≠ 0 := ne_of_gt hs2θ
    have hcub : Real.sin θ ^ 3 = Real.sin θ ^ 2 * Real.sin θ := by ring
    rw [hcot2θ, Real.cot_eq_cos_div_sin, Real.sin_two_mul, Real.cos_two_mul,
      hcub, Real.sin_sq]
    have hsin_ne : Real.sin θ ≠ 0 := by
      intro hz
      have : Real.sin (2 * θ) = 0 := by
        rw [Real.sin_two_mul, hz]
        ring
      exact ne_of_gt hs2θ this
    field_simp [hcθ, hsin_ne, htwo, mul_ne_zero hcθ hsin_ne]
    ring
  -- Conclude both coordinates.
  constructor
  · have h1 : Tendsto xcoord (𝓝[≠] (0 : ℝ))
        (𝓝 (radiusval * Real.sin θ ^ 3)) := by
      rw [← hXTrig]; exact hXLim
    simpa only [hxcoord, hradiusval] using h1
  · have h1 : Tendsto ycoord (𝓝[≠] (0 : ℝ))
        (𝓝 (radiusval / 2 * Real.cos θ * (2 - Real.cos (2 * θ)))) := by
      rw [← hYTrig]; exact hYLim
    simpa only [hycoord, hradiusval] using h1

end IPhO2026Problems.IPhO2026_2_C_3
