import M6ActualCountsDependencies
import M6ActualCounts
open scoped BigOperators
def target_0 : Prop := ∀ (N : ℕ) [NeZero N] (a b : M6.ActualCounts.BP), a.degree < (N : WithBot ℕ) → b.degree < (N : WithBot ℕ) → ∀ h : M6.Physical.Block N, (M6.Coordinates.encode N (M6.Physical.conv N (M6.Coordinates.coefficients N a) h), M6.Coordinates.encode N (M6.Physical.conv N (M6.Coordinates.coefficients N b) h)) = M6.BoundaryFibers.boundary a b (M6.Cyclic.modulus N) (M6.Coordinates.encode N h)
#check target_0
def target_1 : Prop := ∀ (N : ℕ) [NeZero N] (a b : M6.ActualCounts.BP), a.degree < (N : WithBot ℕ) → b.degree < (N : WithBot ℕ) → ∀ h h₀ : M6.Physical.Block N, M6.Spaces.boundary N (M6.Coordinates.coefficients N a) (M6.Coordinates.coefficients N b) h = M6.Spaces.boundary N (M6.Coordinates.coefficients N a) (M6.Coordinates.coefficients N b) h₀ ↔ M6.BoundaryFibers.boundary a b (M6.Cyclic.modulus N) (M6.Coordinates.encode N h) = M6.BoundaryFibers.boundary a b (M6.Cyclic.modulus N) (M6.Coordinates.encode N h₀)
#check target_1
def target_2 : Prop := ∀ (N : ℕ) [NeZero N] (a b : M6.ActualCounts.BP), a.degree < (N : WithBot ℕ) → b.degree < (N : WithBot ℕ) → ∀ h₀ : M6.Physical.Block N, Nat.card {h : M6.Physical.Block N // M6.Spaces.boundary N (M6.Coordinates.coefficients N a) (M6.Coordinates.coefficients N b) h = M6.Spaces.boundary N (M6.Coordinates.coefficients N a) (M6.Coordinates.coefficients N b) h₀} = 2^(M6.ActualCounts.f N a b)
#check target_2
def target_3 : Prop := ∀ (N : ℕ) [NeZero N] (a b : M6.ActualCounts.BP), a.degree < (N : WithBot ℕ) → b.degree < (N : WithBot ℕ) → ∀ h₀ : M6.Physical.Block N, Nat.card {h : M6.Physical.Block N // M6.Spaces.dualBoundary N (M6.Coordinates.coefficients N a) (M6.Coordinates.coefficients N b) h = M6.Spaces.dualBoundary N (M6.Coordinates.coefficients N a) (M6.Coordinates.coefficients N b) h₀} = 2^(M6.ActualCounts.f N a b)
#check target_3
def target_4 : Prop := ∀ (α β : Type) [Fintype α] (L : α → β) (k : ℕ), (∀ a₀ : α, Nat.card {a : α // L a = L a₀} = k) → ∀ w : β → Polynomial ℤ, (∑ a, w (L a)) = Polynomial.C (k : ℤ) * ∑ b ∈ M6.ActualCounts.imageWords L, w b
#check target_4
def target_5 : Prop := ∀ (N : ℕ) [NeZero N] (a b : M6.ActualCounts.BP), a.degree < (N : WithBot ℕ) → b.degree < (N : WithBot ℕ) → ∀ w : M6.Pinned.Vector (2*N) → Polynomial ℤ, (∑ h : M6.Physical.Block N, w (M6.Spaces.boundary N (M6.Coordinates.coefficients N a) (M6.Coordinates.coefficients N b) h)) = Polynomial.C ((2 : ℤ)^(M6.ActualCounts.f N a b)) * ∑ v ∈ M6.Spaces.boundaryWords N (M6.Coordinates.coefficients N a) (M6.Coordinates.coefficients N b), w v
#check target_5
def target_6 : Prop := ∀ (N : ℕ) [NeZero N] (a b : M6.ActualCounts.BP), a.degree < (N : WithBot ℕ) → b.degree < (N : WithBot ℕ) → ∀ w : M6.Pinned.Vector (2*N) → Polynomial ℤ, (∑ h : M6.Physical.Block N, w (M6.Spaces.dualBoundary N (M6.Coordinates.coefficients N a) (M6.Coordinates.coefficients N b) h)) = Polynomial.C ((2 : ℤ)^(M6.ActualCounts.f N a b)) * ∑ v ∈ M6.Character.subspaceWords (M6.Spaces.D N (M6.Coordinates.coefficients N a) (M6.Coordinates.coefficients N b)), w v
#check target_6
def target_7 : Prop := ∀ (N : ℕ) [NeZero N] (a b : M6.ActualCounts.BP), a.degree < (N : WithBot ℕ) → b.degree < (N : WithBot ℕ) → 2^(M6.ActualCounts.f N a b) * (M6.Character.subspaceWords (M6.Spaces.D N (M6.Coordinates.coefficients N a) (M6.Coordinates.coefficients N b))).card = 2^N
#check target_7
def target_8 : Prop := ∀ (N : ℕ) [NeZero N] (a b : M6.ActualCounts.BP), a.degree < (N : WithBot ℕ) → b.degree < (N : WithBot ℕ) → ∀ P : M6.Pinned.Pins (2*N), M6.ActualCounts.boundaryInputSum N a b P = Polynomial.C ((2 : ℤ)^(M6.ActualCounts.f N a b)) * M6.Pinned.enumerator (M6.Spaces.boundaryWords N (M6.Coordinates.coefficients N a) (M6.Coordinates.coefficients N b)) P
#check target_8
def target_9 : Prop := ∀ (N : ℕ) [NeZero N] (a b : M6.ActualCounts.BP), a.degree < (N : WithBot ℕ) → b.degree < (N : WithBot ℕ) → ∀ P : M6.Pinned.Pins (2*N), M6.ActualCounts.signedInputSum N a b P = Polynomial.C ((2 : ℤ)^N) * M6.Pinned.enumerator (M6.Spaces.cycleWords N (M6.Coordinates.coefficients N a) (M6.Coordinates.coefficients N b)) P
#check target_9
