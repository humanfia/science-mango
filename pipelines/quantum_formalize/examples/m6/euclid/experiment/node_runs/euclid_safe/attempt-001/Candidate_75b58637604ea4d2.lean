import FrozenTarget_75b58637604ea4d2
theorem M6.Euclid.euclid_safe : QuantumHarnessFrozenTarget := by
  change ∀ (fuel : ℕ) (p q : M6.Euclid.BP) (width : ℕ), M6.Euclid.rank p ≤ width → M6.Euclid.rank q ≤ width → M6.Euclid.euclidSafe fuel p q width
  intro fuel
  induction fuel with
  | zero =>
      intro p q width hp hq
      simp [M6.Euclid.euclidSafe, hp, hq]
  | succ fuel ih =>
      intro p q width hp hq
      by_cases hq0 : q = 0
      · subst q
        simp [M6.Euclid.euclidSafe, hp, hq]
      · have hr : M6.Euclid.rank (M6.Euclid.remainder p q).value ≤ width := by
          have hc := (M6.Euclid.remainder_correct p q).2.1
          omega
        have hs : ∀ n, M6.Euclid.remainderSafe n p q width :=
          fun n => M6.Euclid.remainder_safe n p q width hp hq
        have ht := ih q (M6.Euclid.remainder p q).value width hq hr
        simp [M6.Euclid.euclidSafe, hq0, hp, hq, hs, ht]
