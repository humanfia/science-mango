import M6Coordinates
import M6PinnedCharacter
import M6TransferScatter
import M6Flatten
import M6Normalize
open scoped BigOperators
namespace M6.ActualTransfer
abbrev BP := M6.Cyclic.BinaryPolynomial
noncomputable def span (a b : BP) : ℕ := max a.natDegree b.natDegree
noncomputable def leftIndex (N : ℕ) [NeZero N] (i : ZMod N) : Fin (2*N) :=
  ⟨i.val, by have hi := ZMod.val_lt i; omega⟩
noncomputable def rightIndex (N : ℕ) [NeZero N] (i : ZMod N) : Fin (2*N) :=
  ⟨N+i.val, by have hi := ZMod.val_lt i; omega⟩
noncomputable def window (R : ℕ) (a : BP) : Fin (R+1) → ZMod 2 := fun j => a.coeff j.val
noncomputable def boundaryWeight (R N : ℕ) [NeZero N] (a b : BP) (P : M6.Pinned.Pins (2*N))
    (i : ℕ) (m : M6.Transfer.Memory R) (t : ZMod 2) : Polynomial ℤ :=
  M6.Character.boundaryFactor P (leftIndex N (i : ZMod N)) (M6.Transfer.output (window R a) m t) *
  M6.Character.boundaryFactor P (rightIndex N (i : ZMod N)) (M6.Transfer.output (window R b) m t)
noncomputable def characterWeight (R N : ℕ) [NeZero N] (a b : BP) (P : M6.Pinned.Pins (2*N))
    (i : ℕ) (m : M6.Transfer.Memory R) (t : ZMod 2) : Polynomial ℤ :=
  M6.Character.pinnedCharacterFactor P (rightIndex N (-(i : ZMod N))) (M6.Transfer.output (window R a) m t) *
  M6.Character.pinnedCharacterFactor P (leftIndex N (-(i : ZMod N))) (M6.Transfer.output (window R b) m t)
/-- Actual event-scatter coefficient array evaluator, not dense matrix evaluation. -/
noncomputable def boundaryTrace (N : ℕ) [NeZero N] (a b : BP) (P : M6.Pinned.Pins (2*N)) : Polynomial ℤ :=
  M6.Transfer.scalarTracePolynomial (boundaryWeight (span a b) N a b P) N
noncomputable def characterTrace (N : ℕ) [NeZero N] (a b : BP) (P : M6.Pinned.Pins (2*N)) : Polynomial ℤ :=
  M6.Transfer.scalarTracePolynomial (characterWeight (span a b) N a b P) N
noncomputable def Q (N : ℕ) [NeZero N] (a b : BP) (P : M6.Pinned.Pins (2*N)) : Polynomial ℤ :=
  M6.Normalize.divide ((2 : ℤ)^N) (characterTrace N a b P) -
  M6.Normalize.divide ((2 : ℤ)^(M6.Cyclic.signature a b (M6.Cyclic.modulus N)).natDegree) (boundaryTrace N a b P)
noncomputable def solve (N : ℕ) [NeZero N] (a b : BP) : Option (ℕ × M6.Pinned.Vector (2*N) × ℕ) :=
  M6.Pinned.solve (Q N a b)
end M6.ActualTransfer
