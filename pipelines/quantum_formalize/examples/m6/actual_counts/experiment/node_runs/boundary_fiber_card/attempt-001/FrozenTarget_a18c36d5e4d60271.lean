import M6ActualCounts
import M6ActualCountsDependencies

theorem M6.ActualCounts.encoded_boundary : ∀ (N : ℕ) [NeZero N] (a b : M6.ActualCounts.BP), a.degree < (N : WithBot ℕ) → b.degree < (N : WithBot ℕ) → ∀ h : M6.Physical.Block N, (M6.Coordinates.encode N (M6.Physical.conv N (M6.Coordinates.coefficients N a) h), M6.Coordinates.encode N (M6.Physical.conv N (M6.Coordinates.coefficients N b) h)) = M6.BoundaryFibers.boundary a b (M6.Cyclic.modulus N) (M6.Coordinates.encode N h) := by
  intro N inst a b ha hb h
  rw [M6.Coordinates.encode_conv N (M6.Coordinates.coefficients N a) h,
      M6.Coordinates.encode_conv N (M6.Coordinates.coefficients N b) h,
      M6.Coordinates.encode_polynomial N a ha,
      M6.Coordinates.encode_polynomial N b hb]
  rfl

theorem M6.ActualCounts.boundary_eq_iff : ∀ (N : ℕ) [NeZero N] (a b : M6.ActualCounts.BP), a.degree < (N : WithBot ℕ) → b.degree < (N : WithBot ℕ) → ∀ h h₀ : M6.Physical.Block N, M6.Spaces.boundary N (M6.Coordinates.coefficients N a) (M6.Coordinates.coefficients N b) h = M6.Spaces.boundary N (M6.Coordinates.coefficients N a) (M6.Coordinates.coefficients N b) h₀ ↔ M6.BoundaryFibers.boundary a b (M6.Cyclic.modulus N) (M6.Coordinates.encode N h) = M6.BoundaryFibers.boundary a b (M6.Cyclic.modulus N) (M6.Coordinates.encode N h₀) := by
  intro N inst a b ha hb h h₀
  have hf : Function.Injective (M6.Flatten.flatten N) := by
    intro z w e
    have e' := congrArg (M6.Flatten.unflatten N) e
    simpa only [M6.Flatten.flatten_left] using e'
  rw [← M6.ActualCounts.encoded_boundary N a b ha hb h,
      ← M6.ActualCounts.encoded_boundary N a b ha hb h₀]
  simp only [M6.Spaces.boundary_eval, hf.eq_iff,
    M6.Physical.boundary, Prod.mk.injEq,
    (M6.Coordinates.encode_injective N).eq_iff]
def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N] (a b : M6.ActualCounts.BP), a.degree < (N : WithBot ℕ) → b.degree < (N : WithBot ℕ) → ∀ h₀ : M6.Physical.Block N, Nat.card {h : M6.Physical.Block N // M6.Spaces.boundary N (M6.Coordinates.coefficients N a) (M6.Coordinates.coefficients N b) h = M6.Spaces.boundary N (M6.Coordinates.coefficients N a) (M6.Coordinates.coefficients N b) h₀} = 2^(M6.ActualCounts.f N a b)
