import Mathlib

/-!
# Extending block-subsequence spatial averages to every volume

A bounded sequence whose prefix averages converge along the multiples of one
fixed positive block width has the same prefix-average limit along every
natural volume.  The omitted terminal block has length `n % W`, hence its
normalized contribution vanishes.  This deterministic bridge lets fixed-window
strong laws feed varying-size thermodynamic limits without restricting the
volume sequence to multiples of the window width.
-/

namespace ArchonPhysics.SpatialAverageBlockExtension

open Filter Topology

noncomputable section

/-- Prefix average, totalized to zero at the empty prefix. -/
def prefixAverage (u : Nat → Real) (n : Nat) : Real :=
  (∑ i ∈ Finset.range n, u i) / (n : Real)

/-- Largest multiple of `W` not exceeding `n`. -/
def blockBase (W n : Nat) : Nat := W * (n / W)

theorem blockBase_add_mod (W n : Nat) :
    blockBase W n + n % W = n := by
  simpa [blockBase, Nat.mul_comm] using Nat.div_add_mod n W

theorem blockBase_le (W n : Nat) : blockBase W n ≤ n := by
  have h := blockBase_add_mod W n
  omega

theorem card_Ico_blockBase (W n : Nat) :
    (Finset.Ico (blockBase W n) n).card = n % W := by
  rw [Nat.card_Ico]
  have h := blockBase_add_mod W n
  omega

theorem remainder_norm_le
    (u : Nat → Real) (W n : Nat) (C : Real)
    (hC : ∀ i, ‖u i‖ ≤ C) :
    ‖∑ i ∈ Finset.Ico (blockBase W n) n, u i‖ ≤
      ((n % W : Nat) : Real) * C := by
  calc
    ‖∑ i ∈ Finset.Ico (blockBase W n) n, u i‖ ≤
        ∑ i ∈ Finset.Ico (blockBase W n) n, ‖u i‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _i ∈ Finset.Ico (blockBase W n) n, C := by
      exact Finset.sum_le_sum fun i _hi ↦ hC i
    _ = ((Finset.Ico (blockBase W n) n).card : Real) * C := by simp
    _ = ((n % W : Nat) : Real) * C := by
      rw [card_Ico_blockBase]

theorem remainder_div_tendsto_zero
    (u : Nat → Real) {W : Nat} (hW : 0 < W) (C : Real)
    (hC : ∀ i, ‖u i‖ ≤ C) :
    Tendsto (fun n : Nat ↦
      (∑ i ∈ Finset.Ico (blockBase W n) n, u i) / (n : Real))
      atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  apply squeeze_zero (g := fun n : Nat ↦
    C * (((n % W : Nat) : Real) / (n : Real)))
  · intro n
    exact norm_nonneg _
  · intro n
    rw [norm_div, Real.norm_natCast]
    calc
      ‖∑ i ∈ Finset.Ico (blockBase W n) n, u i‖ / (n : Real) ≤
          (((n % W : Nat) : Real) * C) / (n : Real) :=
        div_le_div_of_nonneg_right (remainder_norm_le u W n C hC)
          (by positivity)
      _ = C * (((n % W : Nat) : Real) / (n : Real)) := by ring
  · simpa using
      (tendsto_mod_div_atTop_nhds_zero_nat (m := W) hW).const_mul C

theorem blockBase_ratio_tendsto_one {W : Nat} (hW : 0 < W) :
    Tendsto (fun n : Nat ↦ (blockBase W n : Real) / (n : Real))
      atTop (𝓝 1) := by
  have hmod := tendsto_mod_div_atTop_nhds_zero_nat (m := W) hW
  have hone : Tendsto
      (fun n : Nat ↦ 1 - ((n % W : Nat) : Real) / (n : Real))
      atTop (𝓝 (1 - 0)) := tendsto_const_nhds.sub hmod
  have heq :
      (fun n : Nat ↦ 1 - ((n % W : Nat) : Real) / (n : Real)) =ᶠ[atTop]
        (fun n : Nat ↦ (blockBase W n : Real) / (n : Real)) := by
    filter_upwards [eventually_ne_atTop 0] with n hn
    have hnreal : (n : Real) ≠ 0 := by exact_mod_cast hn
    have hbase := congrArg (fun x : Nat ↦ (x : Real))
      (blockBase_add_mod W n)
    push_cast at hbase
    field_simp [hnreal]
    linarith
  simpa using hone.congr' heq

theorem prefixAverage_blockBase_tendsto
    (u : Nat → Real) {W : Nat} (hW : 0 < W) {L : Real}
    (h : Tendsto (fun k : Nat ↦ prefixAverage u (W * k)) atTop (𝓝 L)) :
    Tendsto (fun n : Nat ↦ prefixAverage u (blockBase W n))
      atTop (𝓝 L) := by
  exact h.comp (Nat.tendsto_div_const_atTop hW.ne')

theorem prefixAverage_eq_blockBase_add_remainder
    (u : Nat → Real) {W n : Nat} (hW : 0 < W) (hn : W ≤ n) :
    prefixAverage u n =
      ((blockBase W n : Real) / (n : Real)) *
          prefixAverage u (blockBase W n) +
        (∑ i ∈ Finset.Ico (blockBase W n) n, u i) / (n : Real) := by
  have hbasePos : 0 < blockBase W n := by
    unfold blockBase
    have hdiv : 0 < n / W := Nat.div_pos hn hW
    positivity
  have hbaseNe : (blockBase W n : Real) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hbasePos)
  have hnPos : 0 < n := lt_of_lt_of_le hW hn
  have hnNe : (n : Real) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hnPos)
  unfold prefixAverage
  rw [← Finset.sum_range_add_sum_Ico _ (blockBase_le W n)]
  field_simp

/-- Convergence on block multiples plus a uniform term bound implies
convergence of prefix averages at every natural volume. -/
theorem tendsto_prefixAverage_of_mul
    (u : Nat → Real) {W : Nat} (hW : 0 < W) (C : Real)
    (hC : ∀ i, ‖u i‖ ≤ C) {L : Real}
    (h : Tendsto (fun k : Nat ↦ prefixAverage u (W * k)) atTop (𝓝 L)) :
    Tendsto (prefixAverage u) atTop (𝓝 L) := by
  have hmain := (blockBase_ratio_tendsto_one hW).mul
    (prefixAverage_blockBase_tendsto u hW h)
  have hrem := remainder_div_tendsto_zero u hW C hC
  have hsum : Tendsto (fun n : Nat ↦
      ((blockBase W n : Real) / (n : Real)) *
          prefixAverage u (blockBase W n) +
        (∑ i ∈ Finset.Ico (blockBase W n) n, u i) / (n : Real))
      atTop (𝓝 (1 * L + 0)) := hmain.add hrem
  have heq :
      (fun n : Nat ↦
        ((blockBase W n : Real) / (n : Real)) *
            prefixAverage u (blockBase W n) +
          (∑ i ∈ Finset.Ico (blockBase W n) n, u i) / (n : Real)) =ᶠ[atTop]
        prefixAverage u := by
    filter_upwards [eventually_ge_atTop W] with n hn
    exact (prefixAverage_eq_blockBase_add_remainder u hW hn).symm
  simpa using hsum.congr' heq

end


end ArchonPhysics.SpatialAverageBlockExtension
