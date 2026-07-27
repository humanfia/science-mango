import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.Defs.Filter
import Physlib.Units.WithDim.Basic

/-!
# IPhO 2026, theoretical problem 2, part C.4

This file models the small-angle cusp of the caustic produced by the
half-cylindrical mirror in Figure 2g.  Scalar values are read in one fixed
length unit, while `WithDim` records their physical dimensions.
-/

namespace IPhO2026Problems.IPhO2026_2_C_4

open Filter
open scoped Topology

noncomputable section

/-- A scalar reading of a physical length. -/
abbrev LengthReading := WithDim Dimension.L𝓭 ℝ

/-- The dimension of the coefficient multiplying a length to the power `2 / 3`. -/
abbrev CubeRootLengthReading :=
  WithDim (Dimension.L𝓭 ^ (1 / 3 : ℚ)) ℝ

/--
The slope and intercept of a reflected ray in the Cartesian coordinate frame
of Figure 2g.  The slope is dimensionless and the intercept has length
dimension.
-/
structure ReflectedLineReadout where
  slope : ℝ
  intercept : LengthReading

/--
The optical data used in part C.4.

The angle parameter is dimensionless.  `causticX` and `causticY` are readings
in the Figure 2g frame: its origin is the center of the mirror's diameter, its
horizontal axis is that diameter, and the half-cylindrical mirror lies above
the axis.
-/
structure Figure2gOpticalSystem where
  radius : LengthReading
  radius_pos : 0 < radius.val
  reflectedLine : ℝ → ReflectedLineReadout
  causticX : ℝ → LengthReading
  causticY : ℝ → LengthReading

/--
The `x`-coordinate of the intersection of reflected ray `A`, incident at
angle `θ`, and neighboring reflected ray `B`, incident at `θ + Δθ`.
-/
def neighboringIntersectionX
    (system : Figure2gOpticalSystem) (θ Δθ : ℝ) : ℝ :=
  let rayA := system.reflectedLine θ
  let rayB := system.reflectedLine (θ + Δθ)
  (rayB.intercept.val - rayA.intercept.val) / (rayA.slope - rayB.slope)

/--
The `y`-coordinate of the same neighboring-ray intersection, obtained from
the reflected-line equation `y = m_A x + b_A`.
-/
def neighboringIntersectionY
    (system : Figure2gOpticalSystem) (θ Δθ : ℝ) : ℝ :=
  let rayA := system.reflectedLine θ
  rayA.slope * neighboringIntersectionX system θ Δθ + rayA.intercept.val

/--
The governing caustic-envelope law: the caustic point at angle `θ` is the
limit of intersections of reflected rays whose incidence-angle separation
`Δθ` tends to zero through nonzero values.
-/
def NeighboringReflectedRaysGenerateCaustic
    (system : Figure2gOpticalSystem) : Prop :=
  ∀ θ : ℝ,
    Tendsto (fun Δθ => neighboringIntersectionX system θ Δθ)
        (𝓝[≠] 0) (𝓝 (system.causticX θ).val) ∧
      Tendsto (fun Δθ => neighboringIntersectionY system θ Δθ)
        (𝓝[≠] 0) (𝓝 (system.causticY θ).val)

/--
The reusable conclusion of part C.3, stated directly rather than importing
that part's Lean output.
-/
def HasPreviousPartC3Coordinates
    (system : Figure2gOpticalSystem) : Prop :=
  ∀ θ : ℝ,
    (system.causticX θ).val = system.radius.val * Real.sin θ ^ 3 ∧
      (system.causticY θ).val =
        (system.radius.val / 2) * Real.cos θ * (2 - Real.cos (2 * θ))

/--
For small nonzero `θ`, the Figure 2g caustic has the leading-order cusp
`Y_c = v |X_c|^(p/q) + u`.  The `Tendsto` conclusion is the rigorous
leading-order interpretation: `(Y_c - u) / |X_c|^(p/q)` tends to `v`.

The theorem determines the two dimensioned coefficients and the two integer
exponents requested in part C.4.
-/
theorem determineSmallAngleCaustic
    (system : Figure2gOpticalSystem)
    (hEnvelope : NeighboringReflectedRaysGenerateCaustic system)
    (hC3 : HasPreviousPartC3Coordinates system) :
    ∃ (u : LengthReading) (v : CubeRootLengthReading) (p q : ℤ),
      u.val = system.radius.val / 2 ∧
      v.val =
        (3 / 4 : ℝ) * Real.rpow system.radius.val (1 / 3 : ℝ) ∧
      p = 2 ∧
      q = 3 ∧
      Tendsto
          (fun θ =>
            ((system.causticY θ).val - u.val) /
              Real.rpow |(system.causticX θ).val|
                ((p : ℝ) / (q : ℝ)))
          (𝓝[≠] 0) (𝓝 v.val) := by
  let R := system.radius.val
  have hR : 0 < R := system.radius_pos
  let u : LengthReading := ⟨R / 2⟩
  let v : CubeRootLengthReading :=
    ⟨(3 / 4 : ℝ) * Real.rpow R (1 / 3 : ℝ)⟩
  refine ⟨u, v, 2, 3, rfl, rfl, rfl, rfl, ?_⟩
  have hRsplit :
      R =
        Real.rpow R (1 / 3 : ℝ) *
          Real.rpow R (2 / 3 : ℝ) := by
    calc
      R = Real.rpow R 1 := (Real.rpow_one R).symm
      _ = Real.rpow R ((1 / 3 : ℝ) + 2 / 3) := by norm_num
      _ =
          Real.rpow R (1 / 3 : ℝ) *
            Real.rpow R (2 / 3 : ℝ) :=
        Real.rpow_add hR _ _
  have hsmall :
      ∀ᶠ θ : ℝ in 𝓝[≠] 0, θ ∈ Set.Ioo (-Real.pi) Real.pi := by
    apply Filter.Eventually.filter_mono inf_le_left
    exact isOpen_Ioo.mem_nhds ⟨neg_lt_zero.mpr Real.pi_pos, Real.pi_pos⟩
  have hformula :
      (fun θ =>
          ((system.causticY θ).val - u.val) /
            Real.rpow |(system.causticX θ).val| ((2 : ℝ) / 3))
        =ᶠ[𝓝[≠] 0]
      (fun θ =>
        (Real.rpow R (1 / 3 : ℝ) / 2) *
          ((2 * Real.cos θ ^ 2 + 2 * Real.cos θ - 1) /
            (1 + Real.cos θ))) := by
    filter_upwards [self_mem_nhdsWithin, hsmall] with θ hθ_ne hθ_small
    have hsin_ne : Real.sin θ ≠ 0 := by
      rcases lt_or_gt_of_ne hθ_ne with hθ_neg | hθ_pos
      · exact ne_of_lt (Real.sin_neg_of_neg_of_neg_pi_lt hθ_neg hθ_small.1)
      · exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi hθ_pos hθ_small.2)
    have hsin_sq_ne : Real.sin θ ^ 2 ≠ 0 := pow_ne_zero _ hsin_ne
    have hcos_add_ne : 1 + Real.cos θ ≠ 0 := by
      intro h
      have htrig := Real.sin_sq θ
      apply hsin_sq_ne
      nlinarith
    have habspow :
        Real.rpow (|Real.sin θ| ^ 3) (2 / 3 : ℝ) =
          Real.sin θ ^ 2 := by
      calc
        Real.rpow (|Real.sin θ| ^ 3) (2 / 3 : ℝ) =
            Real.rpow (Real.rpow |Real.sin θ| (3 : ℝ)) (2 / 3 : ℝ) := by
              exact congrArg (fun x => Real.rpow x (2 / 3 : ℝ))
                (Real.rpow_natCast |Real.sin θ| 3).symm
        _ = Real.rpow |Real.sin θ| ((3 : ℝ) * (2 / 3 : ℝ)) :=
          (Real.rpow_mul (abs_nonneg (Real.sin θ)) _ _).symm
        _ = Real.sin θ ^ 2 := by
          norm_num [Real.rpow_two, sq_abs]
    have hden :
        Real.rpow |R * Real.sin θ ^ 3| (2 / 3 : ℝ) =
          Real.rpow R (2 / 3 : ℝ) * Real.sin θ ^ 2 := by
      rw [abs_mul, abs_of_pos hR, abs_pow]
      calc
        Real.rpow (R * |Real.sin θ| ^ 3) (2 / 3 : ℝ) =
            Real.rpow R (2 / 3 : ℝ) *
              Real.rpow (|Real.sin θ| ^ 3) (2 / 3 : ℝ) :=
          Real.mul_rpow hR.le (pow_nonneg (abs_nonneg (Real.sin θ)) _)
        _ = Real.rpow R (2 / 3 : ℝ) * Real.sin θ ^ 2 := by
          rw [habspow]
    rw [show u.val = R / 2 by rfl]
    rw [(hC3 θ).1, (hC3 θ).2, hden, Real.cos_two_mul, Real.sin_sq]
    have hRpow_ne : Real.rpow R (2 / 3 : ℝ) ≠ 0 :=
      ne_of_gt (Real.rpow_pos_of_pos hR _)
    have hone_minus_cos_sq_ne : 1 - Real.cos θ ^ 2 ≠ 0 := by
      rw [← Real.sin_sq]
      exact hsin_sq_ne
    dsimp [R] at hRsplit hRpow_ne ⊢
    field_simp [hRpow_ne, hcos_add_ne, hone_minus_cos_sq_ne]
    calc
      system.radius.val *
            (Real.cos θ * (2 - (2 * Real.cos θ ^ 2 - 1)) - 1) *
          (1 + Real.cos θ) =
          system.radius.val *
            ((1 - Real.cos θ ^ 2) *
              (2 * Real.cos θ ^ 2 + 2 * Real.cos θ - 1)) := by
        ring
      _ =
          (system.radius.val ^ (1 / 3 : ℝ) *
              system.radius.val ^ (2 / 3 : ℝ)) *
            ((1 - Real.cos θ ^ 2) *
              (2 * Real.cos θ ^ 2 + 2 * Real.cos θ - 1)) := by
        rw [← hRsplit]
      _ =
          system.radius.val ^ (2 / 3 : ℝ) *
              (1 - Real.cos θ ^ 2) *
            system.radius.val ^ (1 / 3 : ℝ) *
              (2 * Real.cos θ * (Real.cos θ + 1) - 1) := by
        ring
  have hcontinuous :
      ContinuousAt
        (fun θ : ℝ =>
          (Real.rpow R (1 / 3 : ℝ) / 2) *
            ((2 * Real.cos θ ^ 2 + 2 * Real.cos θ - 1) /
              (1 + Real.cos θ)))
        0 := by
    have hcos : ContinuousAt (fun θ : ℝ => Real.cos θ) 0 :=
      Real.continuous_cos.continuousAt
    have hnum :
        ContinuousAt
          (fun θ : ℝ =>
            2 * Real.cos θ ^ 2 + 2 * Real.cos θ - 1)
          0 := by
      exact ((continuousAt_const.mul (hcos.pow 2)).add
        (continuousAt_const.mul hcos)).sub continuousAt_const
    have hden :
        ContinuousAt (fun θ : ℝ => 1 + Real.cos θ) 0 :=
      continuousAt_const.add hcos
    exact continuousAt_const.mul (hnum.div hden (by norm_num))
  have hlimit :
      Tendsto
        (fun θ : ℝ =>
          (Real.rpow R (1 / 3 : ℝ) / 2) *
            ((2 * Real.cos θ ^ 2 + 2 * Real.cos θ - 1) /
              (1 + Real.cos θ)))
        (𝓝[≠] 0)
        (𝓝
          ((Real.rpow R (1 / 3 : ℝ) / 2) *
            ((2 * Real.cos 0 ^ 2 + 2 * Real.cos 0 - 1) /
              (1 + Real.cos 0)))) :=
    hcontinuous.tendsto.mono_left inf_le_left
  have hlimit' :
      Tendsto
        (fun θ : ℝ =>
          (Real.rpow R (1 / 3 : ℝ) / 2) *
            ((2 * Real.cos θ ^ 2 + 2 * Real.cos θ - 1) /
              (1 + Real.cos θ)))
        (𝓝[≠] 0) (𝓝 v.val) := by
    convert hlimit using 1
    norm_num [v, R]
    ring
  simpa using Filter.Tendsto.congr' hformula.symm hlimit'

end

end IPhO2026Problems.IPhO2026_2_C_4
