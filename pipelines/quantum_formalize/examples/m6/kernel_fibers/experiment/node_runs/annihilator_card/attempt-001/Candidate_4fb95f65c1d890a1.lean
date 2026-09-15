import FrozenTarget_4fb95f65c1d890a1
theorem M6.KernelFibers.annihilator_card : QuantumHarnessFrozenTarget := by
  change ∀ (F K : M6.KernelFibers.BP), F.Monic → K ≠ 0 → Nat.card (M6.KernelFibers.annihilator F K) = 2 ^ F.natDegree
  intro F K hF hK
  classical
  let f : AdjoinRoot F → M6.KernelFibers.annihilator F K :=
    fun z => ⟨M6.KernelFibers.embed F K hF z,
      M6.KernelFibers.embed_annihilated F K hF z⟩
  have hf : Function.Bijective f := by
    constructor
    · intro x y hxy
      apply M6.KernelFibers.embed_injective F K hF hK
      exact congrArg Subtype.val hxy
    · intro z
      obtain ⟨t, ht⟩ := M6.KernelFibers.embed_surjective_kernel F K hF z.val z.property
      refine ⟨t, ?_⟩
      apply Subtype.ext
      exact ht
  calc
    Nat.card (M6.KernelFibers.annihilator F K) = Nat.card (AdjoinRoot F) :=
      (Nat.card_congr (Equiv.ofBijective f hf)).symm
    _ = 2 ^ F.natDegree := M6.KernelFibers.quotient_card F hF
