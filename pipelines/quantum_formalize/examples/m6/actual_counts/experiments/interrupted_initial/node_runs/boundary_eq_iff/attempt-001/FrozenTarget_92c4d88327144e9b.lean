import M6ActualCounts
import M6ActualCountsDependencies

theorem M6.ActualCounts.encoded_boundary : ∀ (N : ℕ) [NeZero N] (a b : M6.ActualCounts.BP), a.degree < (N : WithBot ℕ) → b.degree < (N : WithBot ℕ) → ∀ h : M6.Physical.Block N, (M6.Coordinates.encode N (M6.Physical.conv N (M6.Coordinates.coefficients N a) h), M6.Coordinates.encode N (M6.Physical.conv N (M6.Coordinates.coefficients N b) h)) = M6.BoundaryFibers.boundary a b (M6.Cyclic.modulus N) (M6.Coordinates.encode N h) := by
  intro N inst a b ha hb h
  rw [M6.Coordinates.encode_conv N (M6.Coordinates.coefficients N a) h,
      M6.Coordinates.encode_conv N (M6.Coordinates.coefficients N b) h,
      M6.Coordinates.encode_polynomial N a ha,
      M6.Coordinates.encode_polynomial N b hb]
  rfl
def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N] (a b : M6.ActualCounts.BP), a.degree < (N : WithBot ℕ) → b.degree < (N : WithBot ℕ) → ∀ h h₀ : M6.Physical.Block N, M6.Spaces.boundary N (M6.Coordinates.coefficients N a) (M6.Coordinates.coefficients N b) h = M6.Spaces.boundary N (M6.Coordinates.coefficients N a) (M6.Coordinates.coefficients N b) h₀ ↔ M6.BoundaryFibers.boundary a b (M6.Cyclic.modulus N) (M6.Coordinates.encode N h) = M6.BoundaryFibers.boundary a b (M6.Cyclic.modulus N) (M6.Coordinates.encode N h₀)
