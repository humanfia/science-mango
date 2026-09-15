import FrozenTarget_c3f39ccec969b85c
theorem M7.CanonicalOuter.normalize_act_shifts : QuantumHarnessFrozenTarget := by
    intro N inst g c
    classical
    have h (u : (ZMod N)ˣ) (s : ZMod N) (A : Finset (ZMod N)) :
        M7.CanonicalBlock.normalize (A.image (M7.Action.affine u s)) =
          M7.CanonicalBlock.normalize (A.image (M7.Action.affine u 0)) := by
      have he : A.image (M7.Action.affine u s) =
          M7.CanonicalBlock.shift s (A.image (M7.Action.affine u 0)) := by
        unfold M7.CanonicalBlock.shift
        rw [Finset.image_image]
        congr 1
        funext i
        simp [M7.Action.affine, Function.comp_def]
      rw [he]
      exact M7.CanonicalBlock.normalize_shift N s (A.image (M7.Action.affine u 0))
    rcases g with ⟨u, e, s, t⟩
    cases e <;> simp [M7.CanonicalOuter.normalizePair, M7.Action.act, h]
