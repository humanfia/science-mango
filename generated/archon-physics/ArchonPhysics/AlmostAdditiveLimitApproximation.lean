import ArchonPhysics.AlmostSubadditiveLimit

/-!
# Quantitative approximation of an almost-additive limit

If a real sequence is additive up to a fixed two-sided defect `C`, every
positive block size approximates any existing volume-normalized limit with
error at most `C / k`.  The estimate is uniform in any external parameter
which does not enter `C`; this is the deterministic step used to approximate
an IDS by fixed-volume expected counting functions uniformly in the energy
threshold.
-/

namespace ArchonPhysics.AlmostAdditiveLimitApproximation

open Filter Set Topology

noncomputable section

/-- `u` is additive up to the fixed two-sided defect `C`. -/
def AlmostAdditive (u : Nat → Real) (C : Real) : Prop :=
  ∀ m n, u m + u n ≤ u (m + n) + C ∧
    u (m + n) ≤ u m + u n + C

/-- Iterating the lower gluing inequality along `q` equal blocks. -/
theorem iterated_lower {u : Nat → Real} {C : Real}
    (hC : 0 ≤ C) (h : AlmostAdditive u C)
    (k q : Nat) (hq : 1 ≤ q) :
    (q : Real) * (u k - C) ≤ u (q * k) := by
  induction q with
  | zero => omega
  | succ q ih =>
      by_cases hq0 : q = 0
      · subst q
        norm_num
        exact hC
      · have ih' : (q : Real) * (u k - C) ≤ u (q * k) :=
          ih (by omega)
        have hadd := (h (q * k) k).1
        calc
          ((q + 1 : Nat) : Real) * (u k - C) =
              (q : Real) * (u k - C) + (u k - C) := by
                push_cast
                ring
          _ ≤ u (q * k) + (u k - C) := by linarith
          _ ≤ u (q * k + k) := by linarith
          _ = u ((q + 1) * k) := by rw [Nat.add_mul, one_mul]

/-- Iterating the upper gluing inequality along `q` equal blocks. -/
theorem iterated_upper {u : Nat → Real} {C : Real}
    (hC : 0 ≤ C) (h : AlmostAdditive u C)
    (k q : Nat) (hq : 1 ≤ q) :
    u (q * k) ≤ (q : Real) * (u k + C) := by
  induction q with
  | zero => omega
  | succ q ih =>
      by_cases hq0 : q = 0
      · subst q
        norm_num
        exact hC
      · have ih' : u (q * k) ≤ (q : Real) * (u k + C) :=
          ih (by omega)
        have hadd := (h (q * k) k).2
        calc
          u ((q + 1) * k) = u (q * k + k) := by rw [Nat.add_mul, one_mul]
          _ ≤ u (q * k) + u k + C := hadd
          _ ≤ (q : Real) * (u k + C) + u k + C := by linarith
          _ = ((q + 1 : Nat) : Real) * (u k + C) := by
            push_cast
            ring

/-- Every positive multiple of a block has normalized value in the interval
obtained by adding and subtracting one defect from the block value. -/
theorem normalized_multiple_mem_interval {u : Nat → Real} {C : Real}
    (hC : 0 ≤ C) (h : AlmostAdditive u C)
    (k q : Nat) (hk : 0 < k) (hq : 0 < q) :
    (u k - C) / (k : Real) ≤
        u (q * k) / ((q * k : Nat) : Real) ∧
      u (q * k) / ((q * k : Nat) : Real) ≤
        (u k + C) / (k : Real) := by
  have hkR : (0 : Real) < (k : Real) := by exact_mod_cast hk
  have hqkR : (0 : Real) < ((q * k : Nat) : Real) := by positivity
  constructor
  · apply (div_le_div_iff₀ hkR hqkR).2
    have hlower := iterated_lower hC h k q (by omega)
    push_cast at hlower ⊢
    nlinarith
  · apply (div_le_div_iff₀ hqkR hkR).2
    have hupper := iterated_upper hC h k q (by omega)
    push_cast at hupper ⊢
    nlinarith

/-- Any existing normalized limit is within `C / k` of the normalized value
of every positive block `k`.  No remainder-volume argument is needed: the
proof restricts the given full limit to the cofinal sequence of multiples of
`k`. -/
theorem limit_within_defect_over_block {u : Nat → Real} {C L : Real}
    (hC : 0 ≤ C) (h : AlmostAdditive u C)
    (hlim : Tendsto (fun n : Nat => u n / (n : Real)) atTop (nhds L))
    (k : Nat) (hk : 0 < k) :
    |L - u k / (k : Real)| ≤ C / (k : Real) := by
  have hindex : Tendsto (fun n : Nat => (n + 1) * k) atTop atTop := by
    rw [tendsto_atTop]
    intro b
    filter_upwards [eventually_ge_atTop b] with a ha
    have hk1 : 1 ≤ k := hk
    have hscale : a + 1 ≤ (a + 1) * k := by
      simpa using Nat.mul_le_mul_left (a + 1) hk1
    exact ha.trans ((Nat.le_succ a).trans hscale)
  have hsub : Tendsto
      (fun n : Nat => u ((n + 1) * k) / (((n + 1) * k : Nat) : Real))
      atTop (nhds L) :=
    hlim.comp hindex
  have hlower : (u k - C) / (k : Real) ≤ L := by
    apply ge_of_tendsto' hsub
    intro n
    exact (normalized_multiple_mem_interval hC h k (n + 1) hk (by omega)).1
  have hupper : L ≤ (u k + C) / (k : Real) := by
    apply le_of_tendsto' hsub
    intro n
    exact (normalized_multiple_mem_interval hC h k (n + 1) hk (by omega)).2
  have hkR : (k : Real) ≠ 0 := by exact_mod_cast hk.ne'
  have hlower' : u k / (k : Real) - C / (k : Real) ≤ L := by
    convert hlower using 1; field_simp
  have hupper' : L ≤ u k / (k : Real) + C / (k : Real) := by
    convert hupper using 1; field_simp
  rw [abs_le]
  constructor <;> linarith

end

end ArchonPhysics.AlmostAdditiveLimitApproximation
