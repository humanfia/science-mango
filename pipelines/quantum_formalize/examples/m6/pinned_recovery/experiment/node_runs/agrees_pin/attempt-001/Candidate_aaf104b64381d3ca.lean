import FrozenTarget_aaf104b64381d3ca
theorem M6.Pinned.agrees_pin : QuantumHarnessFrozenTarget := by
  classical
  unfold QuantumHarnessFrozenTarget
  intro m P v i b hP
  unfold M6.Pinned.agrees
  constructor
  · intro h
    constructor
    · intro j
      by_cases hji : j = i
      · subst j
        simp [hP]
      · simpa [M6.Pinned.pin, Function.update, hji, Ne.symm hji] using h j
    · simpa [M6.Pinned.pin, Function.update] using h i
  · rintro ⟨h, hv⟩ j
    by_cases hji : j = i
    · subst j
      simp [M6.Pinned.pin, Function.update, hv]
    · simpa [M6.Pinned.pin, Function.update, hji, Ne.symm hji] using h j
