import FrozenTarget_426d4bf2d692d4fd
theorem M5.ResidueCount.rawA_nonnegative_and_positive : QuantumHarnessFrozenTarget := by
  classical
  intro T w F hT hw hF hFT
  rw [M5.ResidueCount.exact_rawA T w F hT hw hF hFT]
  constructor
  · positivity
  · rw [Int.natCast_pos, Finset.card_pos]
    constructor
    · rintro ⟨⟨a, b⟩, hab⟩
      exact ⟨a, b, by simpa [M5.ResidueCount.validTailPairs] using hab⟩
    · rintro ⟨a, b, hab⟩
      exact ⟨(a, b), by simpa [M5.ResidueCount.validTailPairs] using hab⟩
