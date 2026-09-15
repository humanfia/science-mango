import FrozenTarget_b10c3f89fc23165f
theorem M6.Euclid.remainder_safe : QuantumHarnessFrozenTarget := by
  change ∀ (fuel : ℕ) (p q : M6.Euclid.BP) (width : ℕ), M6.Euclid.rank p ≤ width → M6.Euclid.rank q ≤ width → M6.Euclid.remainderSafe fuel p q width
  intro fuel
  induction fuel with
  | zero =>
      intro p q width hp hq
      simp [M6.Euclid.remainderSafe, hp, hq]
  | succ fuel ih =>
      intro p q width hp hq
      by_cases hp0 : p = 0
      · simp [M6.Euclid.remainderSafe, hp0, hp, hq]
      by_cases hq0 : q = 0
      · simp [M6.Euclid.remainderSafe, hq0, hp, hq]
      by_cases hlt : p.degree < q.degree
      · simp [M6.Euclid.remainderSafe, hp0, hq0, hlt, hp, hq]
      have hdrop := M6.Euclid.cancel_drop p q hp0 hq0 (le_of_not_gt hlt)
      have hc : M6.Euclid.rank (M6.Euclid.cancel p q) ≤ width :=
        le_trans (Nat.le_of_lt hdrop) hp
      have hs := ih (M6.Euclid.cancel p q) q width hc hq
      simpa [M6.Euclid.remainderSafe, hp0, hq0, hlt, hp, hq, hc] using hs
