import FrozenTarget_8375a69b8828e645
theorem M7.ResiduePrefix.residue_roundtrip : QuantumHarnessFrozenTarget := by
  classical
  intro N hN A
  change (A.image (fun x : ZMod N => x.val)).image (fun i : ℕ => (i : ZMod N)) = A
  simp [Finset.image_image, ZMod.natCast_zmod_val]
