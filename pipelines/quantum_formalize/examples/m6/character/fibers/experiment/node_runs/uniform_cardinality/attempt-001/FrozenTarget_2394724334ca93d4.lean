import M6CharacterAccepted
import M6Normalization

theorem M6.FiberSum.sum_by_fibers : ∀ (α β : Type) [Fintype α] [Fintype β] (L : α → β) (w : β → Polynomial ℤ), M6.FiberSum.pullbackSum L w = M6.FiberSum.fiberSum L w := by
  classical
  change ∀ (α β : Type) [Fintype α] [Fintype β] (L : α → β) (w : β → Polynomial ℤ), M6.FiberSum.pullbackSum L w = M6.FiberSum.fiberSum L w
  intro α β _ _ L w
  simpa [M6.FiberSum.pullbackSum, M6.FiberSum.fiberSum, M6.FiberSum.fiber,
    Fintype.card_subtype, nsmul_eq_mul] using (Fintype.sum_fiberwise' L w).symm

theorem M6.FiberSum.uniform_weighted_sum : ∀ (α β : Type) [Fintype α] [Fintype β] (L : α → β) (k : ℕ), M6.FiberSum.UniformFibers L k → ∀ (w : β → Polynomial ℤ), M6.FiberSum.pullbackSum L w = Polynomial.C (k : ℤ) * ∑ b, w b := by
  classical
  change ∀ (α β : Type) [Fintype α] [Fintype β] (L : α → β) (k : ℕ), M6.FiberSum.UniformFibers L k → ∀ (w : β → Polynomial ℤ), M6.FiberSum.pullbackSum L w = Polynomial.C (k : ℤ) * ∑ b, w b
  intro α β _ _ L k h w
  change ∀ b, (M6.FiberSum.fiber L b).card = k at h
  rw [M6.FiberSum.sum_by_fibers α β L w]
  simp only [M6.FiberSum.fiberSum, h, Finset.mul_sum]
def QuantumHarnessFrozenTarget : Prop :=
  ∀ (α β : Type) [Fintype α] [Fintype β] (L : α → β) (k : ℕ), M6.FiberSum.UniformFibers L k → Fintype.card α = k * Fintype.card β
