import M6BoundaryFibers

theorem M6.BoundaryFibers.annihilator_general : ∀ (F M : M6.BoundaryFibers.BP), F.Monic → F ∣ M → M ≠ 0 → Nat.card {h : AdjoinRoot M // AdjoinRoot.mk M F * h = 0} = 2^F.natDegree := by
  intro F M hF hFM hM
  rcases hFM with ⟨K, rfl⟩
  have hK : K ≠ 0 := by
    intro hK
    apply hM
    simp [hK]
  simpa only [M6.KernelFibers.annihilator] using
    (M6.KernelFibers.annihilator_card F K hF hK)

theorem M6.BoundaryFibers.boundary_add : ∀ (a b M : M6.BoundaryFibers.BP) (h k : AdjoinRoot M), M6.BoundaryFibers.boundary a b M (h+k) = M6.BoundaryFibers.boundary a b M h + M6.BoundaryFibers.boundary a b M k := by
  intro a b M h k
  unfold M6.BoundaryFibers.boundary
  apply Prod.ext <;> exact mul_add _ _ _

theorem M6.BoundaryFibers.kernel_iff : ∀ (a b M : M6.BoundaryFibers.BP) (h : AdjoinRoot M), M6.BoundaryFibers.boundary a b M h = (0,0) ↔ AdjoinRoot.mk M (M6.Cyclic.signature a b M) * h = 0 := by
  change ∀ (a b M : M6.BoundaryFibers.BP) (h : AdjoinRoot M), M6.BoundaryFibers.boundary a b M h = (0, 0) ↔ AdjoinRoot.mk M (M6.Cyclic.signature a b M) * h = 0
  intro a b M h
  refine AdjoinRoot.induction_on M h ?_
  intro p
  simpa only [M6.BoundaryFibers.boundary, Prod.mk.injEq, ← map_mul, AdjoinRoot.mk_eq_zero, and_comm] using M6.Cyclic.kernel_divisibility a b M p

theorem M6.BoundaryFibers.nonzero_monic : ∀ p : M6.BoundaryFibers.BP, p ≠ 0 → p.Monic := by
  change ∀ p : M6.BoundaryFibers.BP, p ≠ 0 → p.Monic
  intro p hp
  have hlc : p.leadingCoeff ≠ 0 := by
    intro h
    exact hp (Polynomial.leadingCoeff_eq_zero.mp h)
  change p.leadingCoeff = 1
  have hbinary : ∀ x : ZMod 2, x ≠ 0 → x = 1 := by decide
  exact hbinary p.leadingCoeff hlc

theorem M6.BoundaryFibers.signature_nonzero : ∀ a b M : M6.BoundaryFibers.BP, M ≠ 0 → M6.Cyclic.signature a b M ≠ 0 := by
  change ∀ a b M : M6.BoundaryFibers.BP, M ≠ 0 → M6.Cyclic.signature a b M ≠ 0
  intro a b M hM hs
  have hd := (M6.Cyclic.signature_divides a b M).2.2
  apply hM
  simpa [hs] using hd

theorem M6.BoundaryFibers.kernel_card : ∀ a b M : M6.BoundaryFibers.BP, M ≠ 0 → Nat.card {h : AdjoinRoot M // M6.BoundaryFibers.boundary a b M h = (0,0)} = 2^(M6.Cyclic.signature a b M).natDegree := by
  change ∀ a b M : M6.BoundaryFibers.BP, M ≠ 0 → Nat.card {h : AdjoinRoot M // M6.BoundaryFibers.boundary a b M h = (0, 0)} = 2 ^ (M6.Cyclic.signature a b M).natDegree
  intro a b M hM
  simp_rw [M6.BoundaryFibers.kernel_iff]
  exact M6.BoundaryFibers.annihilator_general
    (M6.Cyclic.signature a b M) M
    (M6.BoundaryFibers.nonzero_monic _ (M6.BoundaryFibers.signature_nonzero a b M hM))
    (M6.Cyclic.signature_divides a b M).2.2 hM
def QuantumHarnessFrozenTarget : Prop :=
  ∀ (a b M : M6.BoundaryFibers.BP), M ≠ 0 → ∀ h₀ : AdjoinRoot M, Nat.card {h : AdjoinRoot M // M6.BoundaryFibers.boundary a b M h = M6.BoundaryFibers.boundary a b M h₀} = 2^(M6.Cyclic.signature a b M).natDegree
