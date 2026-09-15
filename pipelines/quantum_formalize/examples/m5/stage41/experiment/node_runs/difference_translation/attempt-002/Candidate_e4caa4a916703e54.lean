import FrozenTarget_e4caa4a916703e54
theorem M5.Translation.difference_translation : QuantumHarnessFrozenTarget := by
  intro N inst S c
  classical
  have hs (x : ZMod N) : x ∈ M5.Translation.shift S c ↔ x - c ∈ S := by
    simp [M5.Translation.shift, sub_eq_add_neg]
  ext z
  simp only [M5.Translation.differences, Finset.mem_biUnion, Finset.mem_image, hs]
  constructor
  · rintro ⟨x, hx, y, hy, hxy⟩
    refine ⟨x - c, hx, y - c, hy, ?_⟩
    calc
      (x - c) - (y - c) = x - y := by abel
      _ = z := hxy
  · rintro ⟨x, hx, y, hy, hxy⟩
    refine ⟨x + c, ?_, y + c, ?_, ?_⟩
    · simpa using hx
    · simpa using hy
    · calc
        (x + c) - (y + c) = x - y := by abel
        _ = z := hxy
