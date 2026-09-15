import M6Spaces
import M6Coordinates
import M6BoundaryFibers
import M6PinnedCharacter
import M6FiberSum
open scoped BigOperators
namespace M6.ActualCounts
abbrev BP := M6.Cyclic.BinaryPolynomial
noncomputable def f (N : ℕ) (a b : BP) : ℕ :=
  (M6.Cyclic.signature a b (M6.Cyclic.modulus N)).natDegree
noncomputable def imageWords {α β : Type} [Fintype α] (L : α → β) : Finset β := by
  classical
  exact Finset.univ.image L
noncomputable def boundaryInputSum (N : ℕ) [NeZero N] (a b : BP) (P : M6.Pinned.Pins (2*N)) : Polynomial ℤ :=
  ∑ h : M6.Physical.Block N,
    M6.Character.pinnedMonomial P
      (M6.Spaces.boundary N (M6.Coordinates.coefficients N a) (M6.Coordinates.coefficients N b) h)
noncomputable def signedInputSum (N : ℕ) [NeZero N] (a b : BP) (P : M6.Pinned.Pins (2*N)) : Polynomial ℤ :=
  ∑ h : M6.Physical.Block N, ∏ i,
    M6.Character.pinnedCharacterFactor P i
      (M6.Spaces.dualBoundary N (M6.Coordinates.coefficients N a) (M6.Coordinates.coefficients N b) h i)
end M6.ActualCounts
