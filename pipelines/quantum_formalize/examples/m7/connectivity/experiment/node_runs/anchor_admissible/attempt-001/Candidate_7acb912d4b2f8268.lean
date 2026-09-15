import FrozenTarget_7acb912d4b2f8268
theorem M7.Connectivity.anchor_admissible : QuantumHarnessFrozenTarget := by
  change ∀ (N w : ℕ) [NeZero N] (c : M7.Connectivity.Recipe N), 0 < w → c.1.card = w → c.2.card = w → M7.Connectivity.connected c → ∃ q ∈ c.1, ∃ r ∈ c.2, M6.Final.Admissible N (M7.Supports.polynomial (M7.Domain.shift c.1 (-q))) (M7.Supports.polynomial (M7.Domain.shift c.2 (-r)))
  intro N w inst c hw hA hB hc
  classical
  have hApos : 0 < c.1.card := by simpa only [hA] using hw
  have hBpos : 0 < c.2.card := by simpa only [hB] using hw
  obtain ⟨q, hq⟩ := Finset.card_pos.mp hApos
  obtain ⟨r, hr⟩ := Finset.card_pos.mp hBpos
  refine ⟨q, hq, r, hr, ?_⟩
  apply M7.Connectivity.connected_admissible N w (M7.Domain.shift c.1 (-q), M7.Domain.shift c.2 (-r))
  · exact (M7.Domain.shift_card N c.1 (-q)).trans hA
  · exact (M7.Domain.shift_card N c.2 (-r)).trans hB
  · exact M7.Domain.shift_anchor N c.1 q hq
  · exact M7.Domain.shift_anchor N c.2 r hr
  · exact (M7.Connectivity.connected_shift N c (-q) (-r)).mpr hc
