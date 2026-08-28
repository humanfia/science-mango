import Mathlib.Analysis.Calculus.Deriv.MeanValue
import ArchonPhysics.EqualMassPeriodicFPUTContinuumFourWaveGeometry

/-!
# Equal-mass periodic FPUT: conditional Umklapp transversality

This module isolates the one-dimensional analytic input needed to count the
nontrivial Umklapp near-resonant shell.  The derivative in the free momentum
`k₂` factors into a structural cosine and a moving cosine.  Its degeneracy
set is therefore classified exactly.

On any interval where that derivative has a fixed sign and absolute value at
least `γ > 0`, the mean-value theorem bounds the diameter of the
`|Ω| ≤ Δ` slice by `2Δ/γ`.  The lower derivative bound is deliberately
an explicit hypothesis: no global transversality or kinetic limit is claimed.
-/

namespace ArchonPhysics.EqualMassPeriodicFPUTUmklappTransversality

open Set
open ArchonPhysics.EqualMassPeriodicFPUTContinuumFourWaveGeometry

noncomputable section

/-! ## Exact derivative factorization and degeneracy -/

/-- Factored `k₂` derivative of the one-wrap Umklapp mismatch. -/
def umklappK₂DerivativeFactor (k₀ k₁ k₂ : Real) : Real :=
  -2 * Real.cos ((k₀ + k₁) / 4) *
    Real.cos ((2 * k₂ - k₀ - k₁) / 4)

/-- The unfactored derivative from the continuum four-wave geometry equals
the product of the structural and moving cosine factors. -/
theorem umklappK₂Derivative_factor (k₀ k₁ k₂ : Real) :
    -Real.cos (k₂ / 2) - Real.cos ((k₀ + k₁ - k₂) / 2) =
      umklappK₂DerivativeFactor k₀ k₁ k₂ := by
  unfold umklappK₂DerivativeFactor
  calc
    -Real.cos (k₂ / 2) - Real.cos ((k₀ + k₁ - k₂) / 2) =
        -(Real.cos (k₂ / 2) +
          Real.cos ((k₀ + k₁ - k₂) / 2)) := by ring
    _ = -(2 * Real.cos
          (((k₂ / 2) + ((k₀ + k₁ - k₂) / 2)) / 2) *
        Real.cos
          (((k₂ / 2) - ((k₀ + k₁ - k₂) / 2)) / 2)) := by
      rw [Real.cos_add_cos]
    _ = -2 * Real.cos ((k₀ + k₁) / 4) *
        Real.cos ((2 * k₂ - k₀ - k₁) / 4) := by ring_nf

/-- Exact differentiability statement with the factored derivative. -/
theorem hasDerivAt_umklappReducedFourWaveMismatch_k₂_factor
    (k₀ k₁ k₂ : Real) :
    HasDerivAt (fun z ↦ umklappReducedFourWaveMismatch k₀ k₁ z)
      (umklappK₂DerivativeFactor k₀ k₁ k₂) k₂ := by
  exact (hasDerivAt_umklappReducedFourWaveMismatch_k₂ k₀ k₁ k₂).congr_deriv
    (umklappK₂Derivative_factor k₀ k₁ k₂)

@[simp] theorem deriv_umklappReducedFourWaveMismatch_k₂
    (k₀ k₁ k₂ : Real) :
    deriv (fun z ↦ umklappReducedFourWaveMismatch k₀ k₁ z) k₂ =
      umklappK₂DerivativeFactor k₀ k₁ k₂ :=
  (hasDerivAt_umklappReducedFourWaveMismatch_k₂_factor k₀ k₁ k₂).deriv

/-- Degeneracy means precisely that the `k₂` derivative vanishes. -/
def UmklappK₂DerivativeDegenerate (k₀ k₁ k₂ : Real) : Prop :=
  umklappK₂DerivativeFactor k₀ k₁ k₂ = 0

theorem umklappK₂DerivativeDegenerate_iff_cosine_factor
    (k₀ k₁ k₂ : Real) :
    UmklappK₂DerivativeDegenerate k₀ k₁ k₂ ↔
      Real.cos ((k₀ + k₁) / 4) = 0 ∨
        Real.cos ((2 * k₂ - k₀ - k₁) / 4) = 0 := by
  simp [UmklappK₂DerivativeDegenerate, umklappK₂DerivativeFactor]

/-- Exact periodic classification of the derivative-degenerate set. -/
theorem umklappK₂DerivativeDegenerate_iff_integer_phase
    (k₀ k₁ k₂ : Real) :
    UmklappK₂DerivativeDegenerate k₀ k₁ k₂ ↔
      (∃ n : Int, (k₀ + k₁) / 4 =
        (2 * (n : Real) + 1) * Real.pi / 2) ∨
      (∃ n : Int, (2 * k₂ - k₀ - k₁) / 4 =
        (2 * (n : Real) + 1) * Real.pi / 2) := by
  rw [umklappK₂DerivativeDegenerate_iff_cosine_factor]
  simp only [Real.cos_eq_zero_iff]

/-! ## A generic conditional small-slice estimate -/

/-- If `f' ≥ γ > 0` on an interval, two points of its `|·| ≤ Δ`
sublevel slice cannot be separated by more than `2Δ/γ`. -/
theorem nearLevel_pair_sub_le_of_deriv_ge
    {f : Real → Real} {a b γ Δ x y : Real}
    (hγ : 0 < γ) (_hΔ : 0 ≤ Δ)
    (hcontinuous : ContinuousOn f (Icc a b))
    (hdifferentiable : DifferentiableOn Real f (interior (Icc a b)))
    (hderiv : ∀ z ∈ interior (Icc a b), γ ≤ deriv f z)
    (hxIcc : x ∈ Icc a b) (hyIcc : y ∈ Icc a b) (hxy : x ≤ y)
    (hxnear : |f x| ≤ Δ) (hynear : |f y| ≤ Δ) :
    y - x ≤ 2 * Δ / γ := by
  have hgrowth : γ * (y - x) ≤ f y - f x :=
    (convex_Icc a b).mul_sub_le_image_sub_of_le_deriv
      hcontinuous hdifferentiable hderiv x hxIcc y hyIcc hxy
  have hxlower : -Δ ≤ f x := (abs_le.mp hxnear).1
  have hyupper : f y ≤ Δ := (abs_le.mp hynear).2
  apply (le_div_iff₀ hγ).2
  nlinarith

/-- The analogous estimate for a negative derivative bounded away from zero. -/
theorem nearLevel_pair_sub_le_of_deriv_le_neg
    {f : Real → Real} {a b γ Δ x y : Real}
    (hγ : 0 < γ) (_hΔ : 0 ≤ Δ)
    (hcontinuous : ContinuousOn f (Icc a b))
    (hdifferentiable : DifferentiableOn Real f (interior (Icc a b)))
    (hderiv : ∀ z ∈ interior (Icc a b), deriv f z ≤ -γ)
    (hxIcc : x ∈ Icc a b) (hyIcc : y ∈ Icc a b) (hxy : x ≤ y)
    (hxnear : |f x| ≤ Δ) (hynear : |f y| ≤ Δ) :
    y - x ≤ 2 * Δ / γ := by
  have hdecay : f y - f x ≤ -γ * (y - x) :=
    (convex_Icc a b).image_sub_le_mul_sub_of_deriv_le
      hcontinuous hdifferentiable hderiv x hxIcc y hyIcc hxy
  have hxupper : f x ≤ Δ := (abs_le.mp hxnear).2
  have hylower : -Δ ≤ f y := (abs_le.mp hynear).1
  apply (le_div_iff₀ hγ).2
  nlinarith

/-- Transparent interval condition used below: the derivative factor has one
fixed sign and magnitude at least `γ` throughout the interval interior. -/
def UmklappK₂FixedSignTransverseOn
    (k₀ k₁ a b γ : Real) : Prop :=
  (∀ z ∈ interior (Icc a b),
      γ ≤ umklappK₂DerivativeFactor k₀ k₁ z) ∨
    (∀ z ∈ interior (Icc a b),
      umklappK₂DerivativeFactor k₀ k₁ z ≤ -γ)

/-- Conditional Umklapp small-slice theorem.  Any two `Δ`-near-resonant
points in a fixed-sign `γ`-transverse interval are at distance at most
`2Δ/γ`; in particular this bounds the slice diameter/interval length. -/
theorem umklapp_nearResonant_pair_distance_le
    {k₀ k₁ a b γ Δ x y : Real}
    (hγ : 0 < γ) (hΔ : 0 ≤ Δ)
    (htransverse : UmklappK₂FixedSignTransverseOn k₀ k₁ a b γ)
    (hxIcc : x ∈ Icc a b) (hyIcc : y ∈ Icc a b)
    (hxnear : |umklappReducedFourWaveMismatch k₀ k₁ x| ≤ Δ)
    (hynear : |umklappReducedFourWaveMismatch k₀ k₁ y| ≤ Δ) :
    dist x y ≤ 2 * Δ / γ := by
  let f : Real → Real := fun z ↦ umklappReducedFourWaveMismatch k₀ k₁ z
  have hdiff : Differentiable Real f := by
    intro z
    exact (hasDerivAt_umklappReducedFourWaveMismatch_k₂_factor
      k₀ k₁ z).differentiableAt
  have hcontinuous : ContinuousOn f (Icc a b) :=
    hdiff.continuous.continuousOn
  have hdifferentiable : DifferentiableOn Real f (interior (Icc a b)) :=
    hdiff.differentiableOn
  rcases htransverse with hincreasing | hdecreasing
  · by_cases hxy : x ≤ y
    · rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hxy)]
      simpa only [neg_sub] using nearLevel_pair_sub_le_of_deriv_ge hγ hΔ hcontinuous
        hdifferentiable (by
          intro z hz
          simpa [f] using hincreasing z hz)
        hxIcc hyIcc hxy hxnear hynear
    · have hyx : y ≤ x := le_of_not_ge hxy
      rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hyx)]
      exact nearLevel_pair_sub_le_of_deriv_ge hγ hΔ hcontinuous
        hdifferentiable (by
          intro z hz
          simpa [f] using hincreasing z hz)
        hyIcc hxIcc hyx hynear hxnear
  · by_cases hxy : x ≤ y
    · rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hxy)]
      simpa only [neg_sub] using nearLevel_pair_sub_le_of_deriv_le_neg hγ hΔ hcontinuous
        hdifferentiable (by
          intro z hz
          simpa [f] using hdecreasing z hz)
        hxIcc hyIcc hxy hxnear hynear
    · have hyx : y ≤ x := le_of_not_ge hxy
      rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hyx)]
      exact nearLevel_pair_sub_le_of_deriv_le_neg hγ hΔ hcontinuous
        hdifferentiable (by
          intro z hz
          simpa [f] using hdecreasing z hz)
        hyIcc hxIcc hyx hynear hxnear

end

end ArchonPhysics.EqualMassPeriodicFPUTUmklappTransversality
