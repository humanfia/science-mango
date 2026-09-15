import FrozenTarget_fe79d7f264c55150
theorem M6.Euclid.euclid_output_width : QuantumHarnessFrozenTarget := by
  change ∀ (fuel : ℕ) (p q : M6.Euclid.BP), M6.Euclid.rank (M6.Euclid.euclidAux fuel p q).value ≤ max (M6.Euclid.rank p) (M6.Euclid.rank q)
  intro fuel
  induction fuel with
  | zero =>
      intro p q
      simpa [M6.Euclid.euclidAux] using (le_max_left (M6.Euclid.rank p) (M6.Euclid.rank q))
  | succ fuel ih =>
      intro p q
      by_cases hq : q = 0
      · simpa [M6.Euclid.euclidAux, hq] using (le_max_left (M6.Euclid.rank p) (M6.Euclid.rank q))
      · have hr := (M6.Euclid.remainder_correct p q).2.1
        have hi := ih q (M6.Euclid.remainder p q).value
        have hb : M6.Euclid.rank (M6.Euclid.euclidAux fuel q (M6.Euclid.remainder p q).value).value ≤ max (M6.Euclid.rank p) (M6.Euclid.rank q) := by
          omega
        simpa [M6.Euclid.euclidAux, hq] using hb
