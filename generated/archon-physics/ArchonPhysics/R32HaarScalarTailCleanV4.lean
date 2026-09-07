import ArchonPhysics.FiniteProductBoundedDifferences
import ArchonPhysics.RandomPhaseMoments

/-!
# Clean finite-product Haar scalar tails, V4

This file proves a fixed-time concentration estimate for a real linear
combination of finitely many normalized Haar phases.  A deterministic
frequency and time only translate each circle coordinate, so the statistic
still has exact mean zero.  Changing coordinate `k` changes the statistic by
at most `2 * |coefficient k|`; the finite-product bounded-differences theorem
therefore gives the exact variance proxy

`sum k, coefficient k ^ 2`.

The proof deliberately uses the genuine product Haar law from
`RandomPhaseMoments` and the internal McDiarmid bridge from
`FiniteProductBoundedDifferences`.  It does not import the earlier
`R32HaarScalarSubgaussian` module.
-/

namespace ArchonPhysics.R32HaarScalarTailCleanV4

open MeasureTheory ProbabilityTheory Set
open ArchonPhysics.FiniteProductBoundedDifferences
open ArchonPhysics.RandomPhaseMoments
open scoped BigOperators ENNReal NNReal

noncomputable section

local instance : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩

local instance : Measure.IsAddHaarMeasure
    (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

local instance finitePhaseHaarLawIsProbability
    (d : Type*) [Fintype d] : IsProbabilityMeasure (finitePhaseHaarLaw d) := by
  unfold finitePhaseHaarLaw
  infer_instance

/-! ## The fixed-time scalar field -/

/-- The deterministic phase advance, measured in turns. -/
def fixedTimePhaseAdvance (frequency time : Real) : UnitAddCircle :=
  ((frequency * time / (2 * Real.pi) : Real) : UnitAddCircle)

/-- The real first Fourier character after a deterministic fixed-time phase
translation. -/
def fixedTimeHaarCarrier (frequency time : Real)
    (phase : UnitAddCircle) : Real :=
  (fourier 1 (fixedTimePhaseAdvance frequency time + phase)).re

/-- The unshifted real Haar linear statistic. -/
def haarScalarSum {n : Nat} (coefficient : Fin n → Real)
    (phase : Fin n → UnitAddCircle) : Real :=
  ∑ k, coefficient k * (fourier 1 (phase k)).re

/-- The vector of deterministic phase advances at a fixed time. -/
def fixedTimePhaseAdvanceVector {n : Nat}
    (frequency : Fin n → Real) (time : Real) :
    Fin n → UnitAddCircle :=
  fun k ↦ fixedTimePhaseAdvance (frequency k) time

/-- A finite real linear statistic of fixed-time Haar phases. -/
def fixedTimeHaarScalarSum {n : Nat}
    (coefficient frequency : Fin n → Real) (time : Real)
    (phase : Fin n → UnitAddCircle) : Real :=
  ∑ k, coefficient k * fixedTimeHaarCarrier (frequency k) time (phase k)

/-- The exact bounded-differences variance proxy. -/
def haarScalarVarianceProxy {n : Nat}
    (coefficient : Fin n → Real) : NNReal :=
  ⟨∑ k, coefficient k ^ 2,
    Finset.sum_nonneg fun k _hk ↦ sq_nonneg (coefficient k)⟩

@[simp] theorem coe_haarScalarVarianceProxy {n : Nat}
    (coefficient : Fin n → Real) :
    (haarScalarVarianceProxy coefficient : Real) =
      ∑ k, coefficient k ^ 2 := by
  rfl

/-! ## Pointwise bounds and measurability -/

theorem abs_fixedTimeHaarCarrier_le_one
    (frequency time : Real) (phase : UnitAddCircle) :
    |fixedTimeHaarCarrier frequency time phase| ≤ 1 := by
  unfold fixedTimeHaarCarrier
  calc
    |(fourier 1 (fixedTimePhaseAdvance frequency time + phase)).re| ≤
        ‖fourier 1 (fixedTimePhaseAdvance frequency time + phase)‖ :=
      Complex.abs_re_le_norm _
    _ = 1 := by rw [fourier_apply, Circle.norm_coe]

theorem measurable_fixedTimeHaarCarrier (frequency time : Real) :
    Measurable (fixedTimeHaarCarrier frequency time) := by
  unfold fixedTimeHaarCarrier fixedTimePhaseAdvance
  fun_prop

theorem measurable_fixedTimeHaarScalarSum {n : Nat}
    (coefficient frequency : Fin n → Real) (time : Real) :
    Measurable (fixedTimeHaarScalarSum coefficient frequency time) := by
  unfold fixedTimeHaarScalarSum
  exact Finset.measurable_sum Finset.univ fun k _ ↦
    measurable_const.mul
      ((measurable_fixedTimeHaarCarrier (frequency k) time).comp
        (measurable_pi_apply k))

theorem abs_fixedTimeHaarScalarSum_le_sum_abs {n : Nat}
    (coefficient frequency : Fin n → Real) (time : Real)
    (phase : Fin n → UnitAddCircle) :
    |fixedTimeHaarScalarSum coefficient frequency time phase| ≤
      ∑ k, |coefficient k| := by
  unfold fixedTimeHaarScalarSum
  calc
    |∑ k, coefficient k * fixedTimeHaarCarrier (frequency k) time (phase k)| ≤
        ∑ k, |coefficient k *
          fixedTimeHaarCarrier (frequency k) time (phase k)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k, |coefficient k| := by
      apply Finset.sum_le_sum
      intro k _hk
      rw [abs_mul]
      exact mul_le_of_le_one_right (abs_nonneg (coefficient k))
        (abs_fixedTimeHaarCarrier_le_one
          (frequency k) time (phase k))

/-! ## Exact fixed-time centering -/

private theorem integrable_haarCoordinateFourier {n : Nat} (k : Fin n) :
    Integrable (fun phase : Fin n → UnitAddCircle ↦ fourier 1 (phase k))
      (finitePhaseHaarLaw (Fin n)) := by
  apply Integrable.of_bound
    (((map_continuous (fourier 1)).measurable.comp
      (measurable_pi_apply k)).aestronglyMeasurable) 1
  exact ae_of_all _ fun phase ↦ by
    change ‖fourier 1 (phase k)‖ ≤ 1
    exact ((fourier 1).norm_coe_le_norm (phase k)).trans_eq
      (fourier_norm 1)

/-- Exact first-character cancellation, proved from the charge-selection
rule in `RandomPhaseMoments`. -/
theorem integral_haarRealCoordinate_eq_zero {n : Nat} (k : Fin n) :
    (∫ phase : Fin n → UnitAddCircle,
      (fourier 1 (phase k)).re
      ∂finitePhaseHaarLaw (Fin n)) = 0 := by
  let charge : Fin n → Int := Pi.single k 1
  have hcharge : charge ≠ 0 := by
    intro h
    have hk := congr_fun h k
    simp [charge] at hk
  have hcomplex :
      (∫ phase : Fin n → UnitAddCircle, fourier 1 (phase k)
        ∂finitePhaseHaarLaw (Fin n)) = 0 := by
    simpa only [charge, UnitAddTorus.mFourier_single] using
      (integral_mFourier_eq_zero (d := Fin n) hcharge)
  calc
    (∫ phase : Fin n → UnitAddCircle,
        (fourier 1 (phase k)).re
        ∂finitePhaseHaarLaw (Fin n)) =
        ((∫ phase : Fin n → UnitAddCircle, fourier 1 (phase k)
          ∂finitePhaseHaarLaw (Fin n)) : Complex).re :=
      integral_re (integrable_haarCoordinateFourier k)
    _ = 0 := by rw [hcomplex]; simp

/-- The unshifted finite Haar scalar sum has exact mean zero. -/
theorem integral_haarScalarSum_eq_zero {n : Nat}
    (coefficient : Fin n → Real) :
    (∫ phase : Fin n → UnitAddCircle, haarScalarSum coefficient phase
      ∂finitePhaseHaarLaw (Fin n)) = 0 := by
  have hintegrable (k : Fin n) : Integrable
      (fun phase : Fin n → UnitAddCircle ↦
        coefficient k * (fourier 1 (phase k)).re)
      (finitePhaseHaarLaw (Fin n)) := by
    exact (integrable_haarCoordinateFourier k).re.const_mul _
  unfold haarScalarSum
  rw [integral_finsetSum Finset.univ (fun k _hk ↦ hintegrable k)]
  simp only [integral_const_mul, integral_haarRealCoordinate_eq_zero,
    mul_zero, Finset.sum_const_zero]

theorem fixedTimeHaarScalarSum_eq_translate {n : Nat}
    (coefficient frequency : Fin n → Real) (time : Real)
    (phase : Fin n → UnitAddCircle) :
    fixedTimeHaarScalarSum coefficient frequency time phase =
      haarScalarSum coefficient
        (fixedTimePhaseAdvanceVector frequency time + phase) := by
  rfl

/-- Fixed-time deterministic phase translation preserves the exact zero
mean. -/
theorem integral_fixedTimeHaarScalarSum_eq_zero {n : Nat}
    (coefficient frequency : Fin n → Real) (time : Real) :
    (∫ phase : Fin n → UnitAddCircle,
      fixedTimeHaarScalarSum coefficient frequency time phase
      ∂finitePhaseHaarLaw (Fin n)) = 0 := by
  calc
    (∫ phase : Fin n → UnitAddCircle,
        fixedTimeHaarScalarSum coefficient frequency time phase
        ∂finitePhaseHaarLaw (Fin n)) =
        ∫ phase : Fin n → UnitAddCircle,
          haarScalarSum coefficient
            (fixedTimePhaseAdvanceVector frequency time + phase)
          ∂finitePhaseHaarLaw (Fin n) := by
      congr 1
    _ = ∫ phase : Fin n → UnitAddCircle,
        haarScalarSum coefficient phase
        ∂finitePhaseHaarLaw (Fin n) := by
      unfold finitePhaseHaarLaw
      exact integral_add_left_eq_self (haarScalarSum coefficient)
        (fixedTimePhaseAdvanceVector frequency time)
    _ = 0 := integral_haarScalarSum_eq_zero coefficient

/-! ## Bounded differences and the exact proxy -/

theorem fixedTimeHaarScalarSum_hasBoundedDifferences {n : Nat}
    (coefficient frequency : Fin n → Real) (time : Real) :
    HasFinBoundedDifferences
      (fixedTimeHaarScalarSum coefficient frequency time)
      (fun k ↦ 2 * ‖coefficient k‖₊) := by
  intro x y i hoff
  unfold fixedTimeHaarScalarSum
  rw [← Finset.sum_sub_distrib]
  have hcollapse :
      (∑ k : Fin n,
        (coefficient k * fixedTimeHaarCarrier (frequency k) time (x k) -
          coefficient k * fixedTimeHaarCarrier (frequency k) time (y k))) =
        coefficient i * fixedTimeHaarCarrier (frequency i) time (x i) -
          coefficient i * fixedTimeHaarCarrier (frequency i) time (y i) := by
    rw [Finset.sum_eq_single i]
    · intro b _hb hbi
      simp [hoff b hbi]
    · intro hi
      simp at hi
  rw [hcollapse]
  calc
    |coefficient i * fixedTimeHaarCarrier (frequency i) time (x i) -
        coefficient i * fixedTimeHaarCarrier (frequency i) time (y i)| =
        |coefficient i| *
          |fixedTimeHaarCarrier (frequency i) time (x i) -
            fixedTimeHaarCarrier (frequency i) time (y i)| := by
      rw [← mul_sub, abs_mul]
    _ ≤ |coefficient i| * 2 := by
      gcongr
      have hx := abs_le.mp (abs_fixedTimeHaarCarrier_le_one
        (frequency i) time (x i))
      have hy := abs_le.mp (abs_fixedTimeHaarCarrier_le_one
        (frequency i) time (y i))
      rw [abs_le]
      constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]
    _ = ((2 * ‖coefficient i‖₊ : NNReal) : Real) := by
      simp [mul_comm]

@[simp] theorem varianceProxy_fixedTimeHaarScalarSum {n : Nat}
    (coefficient : Fin n → Real) :
    varianceProxy (fun k ↦ 2 * ‖coefficient k‖₊) =
      haarScalarVarianceProxy coefficient := by
  apply NNReal.eq
  change
    (varianceProxy (fun k ↦ 2 * ‖coefficient k‖₊) : Real) =
      ∑ k, coefficient k ^ 2
  simp [varianceProxy, NNReal.coe_sum, sq_abs]

/-! ## Centered sub-Gaussian estimate -/

/-- Affine normalization extends the `[0,1]` finite-product theorem to a
symmetrically bounded real statistic without changing its variance proxy. -/
private theorem hasSubgaussianMGF_finitePi_of_boundedDifferences_symmetric
    {alpha : Type*} [MeasurableSpace alpha]
    (mu : Measure alpha) [IsProbabilityMeasure mu]
    (n : Nat) (f : (Fin n → alpha) → Real) (c : Fin n → NNReal)
    (radius : Real) (hradius : 0 < radius)
    (hf : Measurable f)
    (hrange : ∀ x, |f x| ≤ radius)
    (hbounded : HasFinBoundedDifferences f c) :
    HasSubgaussianMGF
      (fun x ↦ f x - ∫ y, f y ∂(Measure.pi fun _ : Fin n ↦ mu))
      (varianceProxy c) (Measure.pi fun _ : Fin n ↦ mu) := by
  let scaled : (Fin n → alpha) → Real :=
    fun x ↦ (f x + radius) / (2 * radius)
  let scaledBound : Fin n → NNReal :=
    fun i ↦ ⟨(c i : Real) / (2 * radius),
      div_nonneg (c i).property (by positivity)⟩
  have hscaledMeasurable : Measurable scaled := by
    exact (hf.add_const radius).div_const (2 * radius)
  have hdenpos : 0 < 2 * radius := by positivity
  have hscaledRange : ∀ x, scaled x ∈ Set.Icc 0 1 := by
    intro x
    have hx := abs_le.mp (hrange x)
    constructor
    · change 0 ≤ (f x + radius) / (2 * radius)
      exact div_nonneg (by linarith [hx.1]) hdenpos.le
    · change (f x + radius) / (2 * radius) ≤ 1
      exact (div_le_iff₀ hdenpos).2 (by linarith [hx.2])
  have hscaledBounded : HasFinBoundedDifferences scaled scaledBound := by
    intro x y i hoff
    have hxy := hbounded x y i hoff
    simp only [scaled, scaledBound]
    rw [div_sub_div_same, abs_div]
    have hden : |2 * radius| = 2 * radius := abs_of_pos (by positivity)
    rw [hden]
    exact (div_le_div_iff_of_pos_right (by positivity)).2 (by
      simpa using hxy)
  have hscaled := hasSubgaussianMGF_finitePi_of_boundedDifferences
    mu n scaled scaledBound hscaledMeasurable hscaledRange hscaledBounded
  have hrescaled := hscaled.const_mul (2 * radius)
  let scaleVariance : NNReal :=
    ⟨(2 * radius) ^ 2, sq_nonneg (2 * radius)⟩
  have hrescaled' :
      HasSubgaussianMGF
        (fun x ↦ (2 * radius) *
          (scaled x -
            ∫ y, scaled y ∂(Measure.pi fun _ : Fin n ↦ mu)))
        (varianceProxy c) (Measure.pi fun _ : Fin n ↦ mu) := by
    change HasSubgaussianMGF _
      (scaleVariance * varianceProxy scaledBound)
      (Measure.pi fun _ : Fin n ↦ mu) at hrescaled
    refine hasSubgaussianMGF_mono_parameter hrescaled ?_
    apply NNReal.coe_le_coe.mp
    apply le_of_eq
    rw [NNReal.coe_mul]
    have hscale : (scaleVariance : Real) = (2 * radius) ^ 2 := rfl
    have hscaledVar :
        (varianceProxy scaledBound : Real) =
          ∑ i : Fin n, ((((c i : Real) / (2 * radius)) / 2) ^ 2) := by
      unfold varianceProxy
      change NNReal.toRealHom
          (∑ i : Fin n, (scaledBound i / (2 : NNReal)) ^ 2) = _
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro i _hi
      change
        ((((scaledBound i / (2 : NNReal)) ^ 2 : NNReal) : Real)) = _
      rfl
    have hcVar :
        (varianceProxy c : Real) =
          ∑ i : Fin n, (((c i : Real) / 2) ^ 2) := by
      unfold varianceProxy
      change NNReal.toRealHom
          (∑ i : Fin n, (c i / (2 : NNReal)) ^ 2) = _
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro i _hi
      change ((((c i / (2 : NNReal)) ^ 2 : NNReal) : Real)) = _
      rfl
    rw [hscale, hscaledVar, hcVar]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _hi
    have hne : 2 * radius ≠ 0 := by positivity
    field_simp [hne]
  apply hrescaled'.congr
  apply Filter.Eventually.of_forall
  intro x
  have hfIntegrable : Integrable f
      (Measure.pi fun _ : Fin n ↦ mu) := by
    apply Integrable.of_mem_Icc (-radius) radius hf.aemeasurable
    exact ae_of_all _ fun y ↦ abs_le.mp (hrange y)
  have hsumIntegral :
      (∫ y, f y + radius ∂(Measure.pi fun _ : Fin n ↦ mu)) =
        (∫ y, f y ∂(Measure.pi fun _ : Fin n ↦ mu)) + radius := by
    calc
      (∫ y, f y + radius ∂(Measure.pi fun _ : Fin n ↦ mu)) =
          (∫ y, f y ∂(Measure.pi fun _ : Fin n ↦ mu)) +
            ∫ _ : Fin n → alpha, radius
              ∂(Measure.pi fun _ : Fin n ↦ mu) :=
        integral_add hfIntegrable (integrable_const radius)
      _ = (∫ y, f y ∂(Measure.pi fun _ : Fin n ↦ mu)) + radius := by
        simp
  have hscaledIntegral :
      (∫ y, scaled y ∂(Measure.pi fun _ : Fin n ↦ mu)) =
        ((∫ y, f y ∂(Measure.pi fun _ : Fin n ↦ mu)) + radius) /
          (2 * radius) := by
    calc
      (∫ y, scaled y ∂(Measure.pi fun _ : Fin n ↦ mu)) =
          (∫ y, f y + radius
            ∂(Measure.pi fun _ : Fin n ↦ mu)) * (2 * radius)⁻¹ := by
        simp only [scaled, div_eq_mul_inv]
        exact integral_mul_const (2 * radius)⁻¹
          (fun y ↦ f y + radius)
      _ = ((∫ y, f y ∂(Measure.pi fun _ : Fin n ↦ mu)) + radius) /
          (2 * radius) := by
        simp only [hsumIntegral, div_eq_mul_inv]
  dsimp [scaled]
  rw [hscaledIntegral]
  field_simp <;> ring

/-- The fixed-time scalar sum, centered by its product-Haar expectation, is
sub-Gaussian with the exact coefficient-square proxy. -/
theorem hasSubgaussianMGF_centered_fixedTimeHaarScalarSum {n : Nat}
    (coefficient frequency : Fin n → Real) (time : Real) :
    HasSubgaussianMGF
      (fun phase ↦ fixedTimeHaarScalarSum coefficient frequency time phase -
        ∫ phase', fixedTimeHaarScalarSum coefficient frequency time phase'
          ∂finitePhaseHaarLaw (Fin n))
      (haarScalarVarianceProxy coefficient)
      (finitePhaseHaarLaw (Fin n)) := by
  let radius : Real := 1 + ∑ k, |coefficient k|
  have hradius : 0 < radius := by
    dsimp only [radius]
    positivity
  have hrange (phase : Fin n → UnitAddCircle) :
      |fixedTimeHaarScalarSum coefficient frequency time phase| ≤ radius := by
    exact (abs_fixedTimeHaarScalarSum_le_sum_abs
      coefficient frequency time phase).trans (by
        dsimp only [radius]
        linarith)
  have h := hasSubgaussianMGF_finitePi_of_boundedDifferences_symmetric
    (volume : Measure UnitAddCircle) n
    (fixedTimeHaarScalarSum coefficient frequency time)
    (fun k ↦ 2 * ‖coefficient k‖₊)
    radius hradius
    (measurable_fixedTimeHaarScalarSum coefficient frequency time)
    hrange
    (fixedTimeHaarScalarSum_hasBoundedDifferences
      coefficient frequency time)
  unfold finitePhaseHaarLaw
  rw [volume_pi]
  simpa only [varianceProxy_fixedTimeHaarScalarSum] using h

/-- Since the exact fixed-time Haar mean is zero, the scalar sum itself is
sub-Gaussian with the coefficient-square proxy. -/
theorem hasSubgaussianMGF_fixedTimeHaarScalarSum {n : Nat}
    (coefficient frequency : Fin n → Real) (time : Real) :
    HasSubgaussianMGF
      (fixedTimeHaarScalarSum coefficient frequency time)
      (haarScalarVarianceProxy coefficient)
      (finitePhaseHaarLaw (Fin n)) := by
  simpa [integral_fixedTimeHaarScalarSum_eq_zero coefficient frequency time]
    using hasSubgaussianMGF_centered_fixedTimeHaarScalarSum
      coefficient frequency time

/-! ## Two-sided `measureReal` tails -/

/-- A reusable two-sided real-measure tail estimate for a sub-Gaussian
variable. -/
theorem measureReal_abs_gt_le_of_hasSubgaussianMGF
    {Omega : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega} [IsFiniteMeasure mu]
    {X : Omega → Real} {c : NNReal}
    (h : HasSubgaussianMGF X c mu) {u : Real} (hu : 0 ≤ u) :
    mu.real {omega | |X omega| > u} ≤
      2 * Real.exp (-u ^ 2 / (2 * (c : Real))) := by
  let upper : Set Omega := {omega | u ≤ X omega}
  let lower : Set Omega := {omega | u ≤ -X omega}
  calc
    mu.real {omega | |X omega| > u} ≤ mu.real (upper ∪ lower) := by
      apply measureReal_mono (h₂ := by finiteness)
      intro omega homega
      change |X omega| > u at homega
      by_cases hnonneg : 0 ≤ X omega
      · left
        change u ≤ X omega
        rw [abs_of_nonneg hnonneg] at homega
        exact homega.le
      · right
        change u ≤ -X omega
        rw [abs_of_neg (lt_of_not_ge hnonneg)] at homega
        exact homega.le
    _ ≤ mu.real upper + mu.real lower := measureReal_union_le _ _
    _ ≤ Real.exp (-u ^ 2 / (2 * (c : Real))) +
        Real.exp (-u ^ 2 / (2 * (c : Real))) := by
      apply add_le_add
      · exact h.measure_ge_le hu
      · simpa [lower] using h.neg.measure_ge_le hu
    _ = 2 * Real.exp (-u ^ 2 / (2 * (c : Real))) := by ring

/-- The fixed-time two-sided Haar tail with exact coefficient-square proxy
and universal exponent constant `1 / 2`. -/
theorem measureReal_abs_fixedTimeHaarScalarSum_gt_le {n : Nat}
    (coefficient frequency : Fin n → Real) (time : Real)
    {u : Real} (hu : 0 ≤ u) :
    (finitePhaseHaarLaw (Fin n)).real
        {phase |
          |fixedTimeHaarScalarSum coefficient frequency time phase| > u} ≤
      2 * Real.exp
        (-u ^ 2 / (2 * (∑ k, coefficient k ^ 2))) := by
  simpa using measureReal_abs_gt_le_of_hasSubgaussianMGF
    (hasSubgaussianMGF_fixedTimeHaarScalarSum coefficient frequency time) hu

end

end ArchonPhysics.R32HaarScalarTailCleanV4
