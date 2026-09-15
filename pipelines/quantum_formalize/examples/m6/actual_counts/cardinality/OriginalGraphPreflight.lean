import M6ActualCardinality
import M6ActualCountsAccepted
open scoped BigOperators
#check (∀ (N : ℕ) [NeZero N] (a b : M6.ActualCounts.BP), M6.ActualCounts.f N a b ≤ N)
#check (∀ (N : ℕ) [NeZero N] (a b : M6.ActualCounts.BP), a.degree < (N : WithBot ℕ) → b.degree < (N : WithBot ℕ) → (M6.Spaces.boundaryWords N (M6.Coordinates.coefficients N a) (M6.Coordinates.coefficients N b)).card = 2^(N-(M6.ActualCounts.f N a b)))
#check (∀ (N : ℕ) [NeZero N] (a b : M6.ActualCounts.BP), a.degree < (N : WithBot ℕ) → b.degree < (N : WithBot ℕ) → (M6.Spaces.cycleWords N (M6.Coordinates.coefficients N a) (M6.Coordinates.coefficients N b)).card = 2^(N+(M6.ActualCounts.f N a b)))
#check (∀ (N : ℕ) [NeZero N] (a b : M6.ActualCounts.BP), a.degree < (N : WithBot ℕ) → b.degree < (N : WithBot ℕ) → ((M6.Spaces.logicalWords N (M6.Coordinates.coefficients N a) (M6.Coordinates.coefficients N b)).card : ℤ) = (2 : ℤ)^(N+(M6.ActualCounts.f N a b)) - (2 : ℤ)^(N-(M6.ActualCounts.f N a b)))
#check (∀ (N : ℕ) [NeZero N] (a b : M6.ActualCounts.BP), a.degree < (N : WithBot ℕ) → b.degree < (N : WithBot ℕ) → M6.ActualCounts.f N a b = 0 → M6.Spaces.logicalWords N (M6.Coordinates.coefficients N a) (M6.Coordinates.coefficients N b) = ∅)
#check (∀ (N : ℕ) [NeZero N] (a b : M6.ActualCounts.BP), a.degree < (N : WithBot ℕ) → b.degree < (N : WithBot ℕ) → (M6.Spaces.logicalWords N (M6.Coordinates.coefficients N a) (M6.Coordinates.coefficients N b)).Nonempty ↔ 0 < M6.ActualCounts.f N a b)
#check (∀ (N : ℕ) [NeZero N] (a b : M6.ActualCounts.BP), a.degree < (N : WithBot ℕ) → b.degree < (N : WithBot ℕ) → Module.finrank (ZMod 2) (M6.Spaces.B N (M6.Coordinates.coefficients N a) (M6.Coordinates.coefficients N b)) = N - (M6.ActualCounts.f N a b))
#check (∀ (N : ℕ) [NeZero N] (a b : M6.ActualCounts.BP), a.degree < (N : WithBot ℕ) → b.degree < (N : WithBot ℕ) → Module.finrank (ZMod 2) (M6.Spaces.D N (M6.Coordinates.coefficients N a) (M6.Coordinates.coefficients N b)) = N - (M6.ActualCounts.f N a b))
#check (∀ (N : ℕ) [NeZero N] (a b : M6.ActualCounts.BP), a.degree < (N : WithBot ℕ) → b.degree < (N : WithBot ℕ) → 2 * N - Module.finrank (ZMod 2) (M6.Spaces.B N (M6.Coordinates.coefficients N a) (M6.Coordinates.coefficients N b)) - Module.finrank (ZMod 2) (M6.Spaces.D N (M6.Coordinates.coefficients N a) (M6.Coordinates.coefficients N b)) = 2 * (M6.ActualCounts.f N a b))
