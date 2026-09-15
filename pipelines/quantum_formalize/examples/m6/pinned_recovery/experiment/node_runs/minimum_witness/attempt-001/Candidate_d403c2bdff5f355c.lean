import FrozenTarget_d403c2bdff5f355c
theorem M6.Pinned.minimum_witness : QuantumHarnessFrozenTarget := by
  classical
  unfold QuantumHarnessFrozenTarget
  intro m L hL
  have hspec := M6.Pinned.solve_exact m L (M6.Pinned.enumerator L) (fun P => rfl)
  cases hs : M6.Pinned.solve (M6.Pinned.enumerator L) with
  | none =>
      exact False.elim (hL.ne_empty (hspec.1.mp hs))
  | some result =>
      rcases result with ⟨d, v, k⟩
      exact ⟨d, v, k, rfl, hspec.2 d v k hs⟩
