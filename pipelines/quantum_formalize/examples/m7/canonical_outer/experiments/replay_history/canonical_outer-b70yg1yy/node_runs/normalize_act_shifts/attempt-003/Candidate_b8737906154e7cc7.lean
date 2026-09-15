import FrozenTarget_b8737906154e7cc7
theorem M7.CanonicalOuter.normalize_act_shifts : QuantumHarnessFrozenTarget := by
  by
    intro N inst g c
    classical
    have h (u : (ZMod N)ˣ) (s : ZMod N)
        (A : M7.CanonicalBlock.Support N) :
        M7.CanonicalBlock.normalize (A.image (M7.Action.affine u s)) =
          M7.CanonicalBlock.normalize (A.image (fun x => (u : ZMod N) * x)) := by
      have he : A.image (M7.Action.affine u s) =
          M7.CanonicalBlock.shift s (A.image (fun x => (u : ZMod N) * x)) := by
        simp [M7.CanonicalBlock.shift, Finset.image_image,
          M7.Action.affine, Function.comp_def, add_comm]
      rw [he, M7.CanonicalBlock.normalize_shift N]
    rcases g with ⟨u, e, s, t⟩
    cases e <;> simp [M7.CanonicalOuter.normalizePair, M7.Action.act, h]
