import FrozenTarget_093d1ed4c2453f9d
theorem M7.CanonicalOuter.normalize_act_shifts : QuantumHarnessFrozenTarget := by
  intro N inst g c
  classical
  have h (u : (ZMod N)ˣ) (s : ZMod N) (A : M7.CanonicalBlock.Support N) :
      M7.CanonicalBlock.normalize (A.image (M7.Action.affine u s)) =
        M7.CanonicalBlock.normalize (A.image (M7.Action.affine u 0)) := by
    have hs : A.image (M7.Action.affine u s) =
        M7.CanonicalBlock.shift s (A.image (M7.Action.affine u 0)) := by
      simp [M7.CanonicalBlock.shift, Finset.image_image,
        M7.Action.affine, Function.comp_def, add_comm]
    rw [hs, M7.CanonicalBlock.normalize_shift]
  cases he : g.exchange <;>
    simp [M7.CanonicalOuter.normalizePair, M7.Action.act, he, h]
