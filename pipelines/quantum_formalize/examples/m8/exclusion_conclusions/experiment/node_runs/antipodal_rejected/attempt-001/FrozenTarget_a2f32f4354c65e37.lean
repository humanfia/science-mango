import M8Exclusion

theorem M8.Exclusion.antipodal_span : ∀ (N : ℕ) [NeZero N] (v : ℕ), 3 ≤ v → N = 2^v → ∀ g : M7.Action.Record N, M8.Cutoff.limit N < M8.Anchor.span (M7.Action.act g (M8.AntipodalFamily.recipe N)) := by
  intro N inst v hv hN
  have hc := M8.AntipodalFamily.cutoff_half v hv
  have hmul : N = 2 * 2^(v-1) := by
    calc
      N = 2^v := hN
      _ = 2^((v-1)+1) := by congr 1; omega
      _ = 2 * 2^(v-1) := by simp [pow_succ, Nat.mul_comm]
  have hhalf : N/2 = 2^(v-1) := by omega
  have h8 : 8 ≤ N := by omega
  have heven : Even N := ⟨2^(v-1), by omega⟩
  have hd := M8.AntipodalFamily.support_data N h8 heven
  have ha : M8.ExclusionGeometry.Antipodal (N/2) (M8.AntipodalFamily.support N) := by
    refine ⟨0, hd.2.1, ?_⟩
    simpa only [zero_add] using hd.2.2.2
  apply M8.ExclusionGeometry.antipodal_exclusion N (N/2) (M8.Cutoff.limit N) (M8.AntipodalFamily.recipe N)
  · omega
  · exact Or.inl ha
  · rw [hN, hc.1]
    rw [hN] at hhalf
    omega

theorem M8.Exclusion.span_rejected : ∀ (N : ℕ) [NeZero N] (w : ℕ) (c : M7.Action.Recipe N), 0 < w → M8.PhysicalBridge.Valid w c → M8.PhysicalBridge.signature c ≠ 1 → (∀ g : M7.Action.Record N, M8.Cutoff.limit N < M8.Anchor.span (M7.Action.act g c)) → M8.Solver.run c = M8.Solver.Outcome.unrecognized (M8.PhysicalBridge.signature c) := by
  intro N inst w c hw hvalid hF hspan
  apply (M8.Solver.unrecognized_exact N c w hw hvalid).2
  refine ⟨hF, ?_⟩
  apply lt_of_not_ge
  intro hle
  have hd : M8.Discovery.discover c ≠ none :=
    (M8.Solver.discovery_span N c w hw hvalid).2 hle
  rcases (M8.Discovery.complete N c).1 hd with ⟨g, _, hg⟩
  exact (not_lt_of_ge hg) (hspan g)
def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N] (v : ℕ), 3 ≤ v → N = 2^v → M8.Solver.run (M8.AntipodalFamily.recipe N) = M8.Solver.Outcome.unrecognized (M8.AntipodalFamily.polynomial N)
