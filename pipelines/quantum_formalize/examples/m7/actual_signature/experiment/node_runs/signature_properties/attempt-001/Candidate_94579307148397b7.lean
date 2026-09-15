import FrozenTarget_94579307148397b7
theorem M7.RecipeSignature.signature_properties : QuantumHarnessFrozenTarget := by
  change ∀ (N : ℕ) [NeZero N], ∀ c : M7.Action.Recipe N, (M7.RecipeSignature.signature c).Monic ∧ M7.RecipeSignature.signature c ∣ M6.Cyclic.modulus N
  intro N inst c
  have hd : M7.RecipeSignature.signature c ∣ M6.Cyclic.modulus N := by
    unfold M7.RecipeSignature.signature
    first
    | exact M6.Cyclic.signature_divides _ _ _
    | exact (M6.Cyclic.signature_divides _ _ _).2.2
    | exact (M6.Cyclic.signature_divides _ _ _).2
  refine ⟨M7.SignatureTau.binary_monic _ ?_, hd⟩
  intro hz
  have hm := (M7.SignatureTau.modulus_monic N).ne_zero
  apply hm
  simpa only [hz, zero_dvd_iff] using hd
