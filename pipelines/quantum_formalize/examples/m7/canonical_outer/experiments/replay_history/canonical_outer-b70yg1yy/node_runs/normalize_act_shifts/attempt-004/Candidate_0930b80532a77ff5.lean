import FrozenTarget_0930b80532a77ff5
theorem M7.CanonicalOuter.normalize_act_shifts : QuantumHarnessFrozenTarget := by
    change ∀ (N : ℕ) [NeZero N], ∀ (g : M7.Action.Record N) (c : M7.Action.Recipe N), M7.CanonicalOuter.normalizePair (M7.Action.act g c) = M7.CanonicalOuter.normalizePair (M7.Action.act (⟨g.unit, g.exchange, 0, 0⟩ : M7.Action.Record N) c)
    intro N inst g c
    classical
    have h (u : (ZMod N)ˣ) (s : ZMod N) (A : Finset (ZMod N)) :
        M7.CanonicalBlock.normalize (A.image (M7.Action.affine u s)) =
        M7.CanonicalBlock.normalize (A.image (M7.Action.affine u 0)) := by
      simpa [M7.CanonicalBlock.shift, Finset.image_image, M7.Action.affine,
        Function.comp_def, add_comm] using
        (M7.CanonicalBlock.normalize_shift N s (A.image (M7.Action.affine u 0)))
    rcases g with ⟨u, e, s, t⟩
    cases e <;> simp [M7.CanonicalOuter.normalizePair, M7.Action.act, h]
