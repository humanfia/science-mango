import FrozenTarget_7f8631c5787bf110
theorem M7.CanonicalOuter.normalize_act_shifts : QuantumHarnessFrozenTarget := by
    intro N inst g c
    classical
    have h (u : (ZMod N)ˣ) (s : ZMod N) (A : Finset (ZMod N)) :
        M7.CanonicalBlock.normalize (A.image (M7.Action.affine u s)) =
          M7.CanonicalBlock.normalize (A.image (M7.Action.affine u 0)) := by
      simpa [M7.CanonicalBlock.shift, M7.Action.affine, Finset.image_image,
        Function.comp_def, add_comm] using
        (M7.CanonicalBlock.normalize_shift N s (A.image (M7.Action.affine u 0)))
    rcases g with ⟨u, e, s, t⟩
    cases e <;> simp [M7.CanonicalOuter.normalizePair, M7.Action.act, h]
