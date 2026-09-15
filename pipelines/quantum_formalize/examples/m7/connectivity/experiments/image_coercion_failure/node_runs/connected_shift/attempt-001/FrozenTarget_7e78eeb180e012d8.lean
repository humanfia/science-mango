import M7Connectivity

theorem M7.Connectivity.difference_shift : ∀ (N : ℕ) [NeZero N] (A : Finset (ZMod N)) (s : ZMod N), M7.Connectivity.differences (M7.Domain.shift A s) = M7.Connectivity.differences A := by
  change ∀ (N : ℕ) [NeZero N] (A : Finset (ZMod N)) (s : ZMod N), M7.Connectivity.differences (M7.Domain.shift A s) = M7.Connectivity.differences A
  intro N inst A s
  classical
  ext x
  change (∃ a ∈ M7.Domain.shift A s, ∃ b ∈ M7.Domain.shift A s, x = a - b) ↔ (∃ a ∈ A, ∃ b ∈ A, x = a - b)
  constructor
  · rintro ⟨a, ha, b, hb, h⟩
    have ha' : a + -s ∈ A := by simpa [M7.Domain.shift] using ha
    have hb' : b + -s ∈ A := by simpa [M7.Domain.shift] using hb
    refine ⟨a + -s, ha', b + -s, hb', ?_⟩
    calc
      x = a - b := h
      _ = (a + -s) - (b + -s) := by ring
  · rintro ⟨a, ha, b, hb, h⟩
    have ha' : a + s ∈ M7.Domain.shift A s := by simpa [M7.Domain.shift] using ha
    have hb' : b + s ∈ M7.Domain.shift A s := by simpa [M7.Domain.shift] using hb
    refine ⟨a + s, ha', b + s, hb', ?_⟩
    calc
      x = a - b := h
      _ = (a + s) - (b + s) := by ring
def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N] (c : M7.Connectivity.Recipe N) (s t : ZMod N), M7.Connectivity.connected (M7.Domain.shift c.1 s, M7.Domain.shift c.2 t) ↔ M7.Connectivity.connected c
