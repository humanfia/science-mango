import Mathlib

/-!
# Finite modal-energy diagnostics for approximate equipartition

This module formalizes the finite, late-window observables described in
`references/Thermal_physics_README.md`, Section 5.  The real arguments `t` and
`T` are coordinates in one fixed time unit, and the values of `E` are
coordinates in one fixed energy unit.  Consequently the averaging factor and
the normalization are explicit in the formulas below.

It provides diagnostic definitions only: it asserts neither that a window
occurs nor that a microscopic trajectory thermalizes.
-/

namespace ArchonPhysics.EquipartitionEntropy

noncomputable section

/-- The late-time average of the modal energy in the interval `[mu * T, T]`. -/
def lateWindowAverage {ι : Type} (E : Real → ι → Real) (mu T : Real) : ι → Real :=
  fun i => ((1 - mu) * T)⁻¹ * ∫ t in mu * T..T, E t i

/-- The total of a finite collection of modal weights. -/
def totalWeight {ι : Type} [Fintype ι] (w : ι → Real) : Real :=
  ∑ i, w i

/-- Weights normalized by their total. -/
def normalizedWeights {ι : Type} [Fintype ι] (w : ι → Real) : ι → Real :=
  fun i => w i / totalWeight w

/-- Uniform weights on a finite mode set. -/
def uniformWeights {ι : Type} [Fintype ι] : ι → Real :=
  fun _ => ((Fintype.card ι : Real))⁻¹

/-- The finite `ℓ¹` distance between two weight functions. -/
def l1Distance {ι : Type} [Fintype ι] (w u : ι → Real) : Real :=
  ∑ i, |w i - u i|

/-- Approximate equipartition on a positive late window. -/
def ApproxEquipartition {ι : Type} [Fintype ι] [Nonempty ι]
    (E : Real → ι → Real) (mu delta T : Real) : Prop :=
  0 ≤ mu ∧ mu < 1 ∧ 0 < T ∧
    0 < totalWeight (lateWindowAverage E mu T) ∧
      l1Distance (normalizedWeights (lateWindowAverage E mu T))
        (uniformWeights : ι → Real) ≤ delta

/-- Spectral entropy, with Mathlib's `negMulLog` convention at zero. -/
def spectralEntropy {ι : Type} [Fintype ι] (w : ι → Real) : Real :=
  ∑ i, Real.negMulLog (w i)

/-- The entropy deficit from the uniform finite distribution. -/
def entropyDeficit {ι : Type} [Fintype ι] (w : ι → Real) : Real :=
  Real.log (Fintype.card ι) - spectralEntropy w

/-- The entropy-derived effective number of occupied modes. -/
def participationNumber {ι : Type} [Fintype ι] (w : ι → Real) : Real :=
  Real.exp (spectralEntropy w)

/-- The late-window average of a pointwise nonnegative energy is nonnegative. -/
theorem lateWindowAverage_nonneg {ι : Type} (E : Real → ι → Real) (mu T : Real)
    (_hmu : 0 ≤ mu) (hmu_lt_one : mu < 1) (hT : 0 < T)
    (hE : ∀ t i, 0 ≤ E t i) : ∀ i, 0 ≤ lateWindowAverage E mu T i := by
  intro i
  unfold lateWindowAverage
  have hinterval : mu * T ≤ T := by
    calc
      mu * T ≤ 1 * T := mul_le_mul_of_nonneg_right
        (by linarith [_hmu, hmu_lt_one]) (le_of_lt hT)
      _ = T := one_mul T
  have hfactor : 0 ≤ ((1 - mu) * T)⁻¹ := by
    exact inv_nonneg.mpr (le_of_lt (mul_pos (sub_pos.mpr hmu_lt_one) hT))
  exact mul_nonneg hfactor
    (intervalIntegral.integral_nonneg hinterval (fun t _ => hE t i))

/-- Positive total weight makes the normalized finite weights sum to one. -/
theorem sum_normalizedWeights {ι : Type} [Fintype ι] (w : ι → Real)
    (hpositive : 0 < totalWeight w) : ∑ i, normalizedWeights w i = 1 := by
  unfold normalizedWeights totalWeight at *
  rw [← Finset.sum_div]
  exact div_self (ne_of_gt hpositive)

/-- The normalized weight vector is at `ℓ¹` distance at most two from uniform. -/
theorem l1Distance_normalized_uniform_le_two {ι : Type} [Fintype ι] [Nonempty ι]
    (w : ι → Real) (hw : ∀ i, 0 ≤ w i) (hpositive : 0 < totalWeight w) :
    l1Distance (normalizedWeights w) (uniformWeights : ι → Real) ≤ 2 := by
  have hnormalized_nonneg : ∀ i, 0 ≤ normalizedWeights w i := by
    intro i
    exact div_nonneg (hw i) (le_of_lt hpositive)
  have huniform_nonneg : ∀ i, 0 ≤ (uniformWeights : ι → Real) i := by
    intro i
    exact inv_nonneg.mpr (Nat.cast_nonneg _)
  have hterm : ∀ i, |normalizedWeights w i - (uniformWeights : ι → Real) i| ≤
      normalizedWeights w i + (uniformWeights : ι → Real) i := by
    intro i
    rw [abs_le]
    constructor <;> linarith [hnormalized_nonneg i, huniform_nonneg i]
  have huniform_sum : ∑ i, (uniformWeights : ι → Real) i = 1 := by
    simp [uniformWeights, (ne_of_gt (Nat.cast_pos.mpr Fintype.card_pos) :
      (Fintype.card ι : Real) ≠ 0)]
  calc
    l1Distance (normalizedWeights w) (uniformWeights : ι → Real) =
        ∑ i, |normalizedWeights w i - (uniformWeights : ι → Real) i| := rfl
    _ ≤ ∑ i, (normalizedWeights w i + (uniformWeights : ι → Real) i) :=
      Finset.sum_le_sum (fun i _ => hterm i)
    _ = (∑ i, normalizedWeights w i) + ∑ i, (uniformWeights : ι → Real) i :=
      Finset.sum_add_distrib
    _ = 2 := by rw [sum_normalizedWeights w hpositive, huniform_sum]; norm_num

/-- Entropy of a finite probability vector is between zero and `log(card)`. -/
theorem spectralEntropy_bounds {ι : Type} [Fintype ι] [Nonempty ι]
    (w : ι → Real) (hw : ∀ i, 0 ≤ w i) (hsum : totalWeight w = 1) :
    0 ≤ spectralEntropy w ∧ spectralEntropy w ≤ Real.log (Fintype.card ι) := by
  have hweight_sum : ∑ i, w i = 1 := hsum
  have hweight_le_one : ∀ i, w i ≤ 1 := by
    intro i
    calc
      w i ≤ ∑ j, w j := Finset.single_le_sum (fun j _ => hw j) (Finset.mem_univ i)
      _ = 1 := hweight_sum
  constructor
  · unfold spectralEntropy
    exact Finset.sum_nonneg (fun i _ =>
      Real.negMulLog_nonneg (hw i) (hweight_le_one i))
  · have hcard_pos : 0 < (Fintype.card ι : Real) :=
      Nat.cast_pos.mpr Fintype.card_pos
    have hcard_ne : (Fintype.card ι : Real) ≠ 0 := ne_of_gt hcard_pos
    have hmul_log (x : Real) (hx : 0 ≤ x) : x - 1 ≤ x * Real.log x := by
      by_cases hx_zero : x = 0
      · simp [hx_zero]
      · have hx_pos : 0 < x := lt_of_le_of_ne hx (Ne.symm hx_zero)
        have hinv : Real.log x⁻¹ ≤ x⁻¹ - 1 :=
          Real.log_le_sub_one_of_pos (inv_pos.mpr hx_pos)
        rw [Real.log_inv] at hinv
        have hscaled := mul_le_mul_of_nonneg_left hinv hx
        calc
          x - 1 = -(x * (x⁻¹ - 1)) := by
            rw [mul_sub, mul_inv_cancel₀ hx_zero]
            ring
          _ ≤ -(x * -Real.log x) := neg_le_neg hscaled
          _ = x * Real.log x := by ring
    have hterm : ∀ i, w i - (Fintype.card ι : Real)⁻¹ ≤
        w i * Real.log ((Fintype.card ι : Real) * w i) := by
      intro i
      have hbase := hmul_log ((Fintype.card ι : Real) * w i)
        (mul_nonneg (le_of_lt hcard_pos) (hw i))
      calc
        w i - (Fintype.card ι : Real)⁻¹ =
            (Fintype.card ι : Real)⁻¹ * ((Fintype.card ι : Real) * w i - 1) := by
          field_simp [hcard_ne]
        _ ≤ (Fintype.card ι : Real)⁻¹ *
            (((Fintype.card ι : Real) * w i) *
              Real.log ((Fintype.card ι : Real) * w i)) :=
          mul_le_mul_of_nonneg_left hbase (inv_nonneg.mpr (le_of_lt hcard_pos))
        _ = w i * Real.log ((Fintype.card ι : Real) * w i) := by
          field_simp [hcard_ne]
    have hterm_sum : ∑ i, (w i - (Fintype.card ι : Real)⁻¹) ≤
        ∑ i, w i * Real.log ((Fintype.card ι : Real) * w i) :=
      Finset.sum_le_sum (fun i _ => hterm i)
    have huniform_sum : ∑ _ : ι, (Fintype.card ι : Real)⁻¹ = 1 := by
      simp [hcard_ne]
    have hlog_sum_nonneg : 0 ≤ ∑ i, w i *
        Real.log ((Fintype.card ι : Real) * w i) := by
      rw [Finset.sum_sub_distrib, hweight_sum, huniform_sum] at hterm_sum
      linarith
    have hlog_term : ∀ i, w i * Real.log ((Fintype.card ι : Real) * w i) =
        w i * Real.log (Fintype.card ι) + w i * Real.log (w i) := by
      intro i
      by_cases hwi_zero : w i = 0
      · simp [hwi_zero]
      · rw [Real.log_mul hcard_ne hwi_zero]
        ring
    have hentropy : spectralEntropy w = -∑ i, w i * Real.log (w i) := by
      unfold spectralEntropy
      calc
        (∑ i, Real.negMulLog (w i)) = ∑ i, -(w i * Real.log (w i)) := by
          apply Finset.sum_congr rfl
          intro i _
          unfold Real.negMulLog
          ring
        _ = -∑ i, w i * Real.log (w i) :=
          Finset.sum_neg_distrib (fun i => w i * Real.log (w i))
    have hlog_sum : ∑ i, w i * Real.log ((Fintype.card ι : Real) * w i) =
        Real.log (Fintype.card ι) - spectralEntropy w := by
      calc
        (∑ i, w i * Real.log ((Fintype.card ι : Real) * w i)) =
            ∑ i, (w i * Real.log (Fintype.card ι) + w i * Real.log (w i)) := by
          apply Finset.sum_congr rfl
          intro i _
          exact hlog_term i
        _ = (∑ i, w i) * Real.log (Fintype.card ι) +
            ∑ i, w i * Real.log (w i) := by
          rw [Finset.sum_add_distrib, ← Finset.sum_mul]
        _ = Real.log (Fintype.card ι) - spectralEntropy w := by
          rw [hweight_sum, hentropy]
          ring
    linarith

/-- Uniform finite weights attain the maximal spectral entropy. -/
theorem spectralEntropy_uniform {ι : Type} [Fintype ι] [Nonempty ι] :
    spectralEntropy (uniformWeights : ι → Real) = Real.log (Fintype.card ι) := by
  have hcard : (Fintype.card ι : Real) ≠ 0 :=
    ne_of_gt (Nat.cast_pos.mpr Fintype.card_pos)
  simp [spectralEntropy, uniformWeights, Real.negMulLog, Real.log_inv, hcard]

/-- Formula-level specification of the window average and normalized weights. -/
theorem windowWeights_spec {ι : Type} [Fintype ι] (E : Real → ι → Real)
    (mu T : Real) (w : ι → Real) :
    (∀ i, lateWindowAverage E mu T i = ((1 - mu) * T)⁻¹ * ∫ t in mu * T..T, E t i) ∧
      totalWeight w = ∑ i, w i ∧
        (∀ i, normalizedWeights w i = w i / totalWeight w) := by
  exact ⟨fun _ => rfl, rfl, fun _ => rfl⟩

/-- Formula-level specification of the entropy diagnostics. -/
theorem entropyDiagnostics_spec {ι : Type} [Fintype ι] (w : ι → Real) :
    spectralEntropy w = ∑ i, Real.negMulLog (w i) ∧
      entropyDeficit w = Real.log (Fintype.card ι) - spectralEntropy w ∧
        participationNumber w = Real.exp (spectralEntropy w) := by
  exact ⟨rfl, rfl, rfl⟩

/-- Formula-level specification of approximate equipartition and its observables. -/
theorem equipartition_spec {ι : Type} [Fintype ι] [Nonempty ι]
    (E : Real → ι → Real) (mu delta T : Real) (w u : ι → Real) :
    (∀ i : ι, uniformWeights i = ((Fintype.card ι : Real))⁻¹) ∧
      l1Distance w u = (∑ i : ι, |w i - u i|) ∧
        (ApproxEquipartition E mu delta T ↔
          0 ≤ mu ∧ mu < 1 ∧ 0 < T ∧ 0 < totalWeight (lateWindowAverage E mu T) ∧
            l1Distance (normalizedWeights (lateWindowAverage E mu T))
              (uniformWeights : ι → Real) ≤ delta) := by
  exact ⟨fun _ => rfl, rfl, Iff.rfl⟩

end

end ArchonPhysics.EquipartitionEntropy
