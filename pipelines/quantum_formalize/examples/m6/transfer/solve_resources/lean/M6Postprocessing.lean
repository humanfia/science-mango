import M6ActualTransfer
import M6NormalizeAccepted
namespace M6.ActualTransfer
/-- Literal two arithmetic shifts and one subtraction at an output coefficient. -/
noncomputable def shiftedCoefficient (N : ℕ) [NeZero N] (a b : BP)
    (P : M6.Pinned.Pins (2*N)) (d : ℕ) : ℤ :=
  Int.shiftRight ((characterTrace N a b P).coeff d) N -
  Int.shiftRight ((boundaryTrace N a b P).coeff d)
    (M6.Cyclic.signature a b (M6.Cyclic.modulus N)).natDegree
noncomputable def shiftedOutput (N : ℕ) [NeZero N] (a b : BP)
    (P : M6.Pinned.Pins (2*N)) : Polynomial ℤ :=
  ∑ d : Fin (2*N+1), Polynomial.monomial d.val (shiftedCoefficient N a b P d.val)
noncomputable def shiftedScan (N : ℕ) [NeZero N] (a b : BP)
    (P : M6.Pinned.Pins (2*N)) : Option ℕ :=
  (List.range (2*N+1)).find? (fun d => decide (0 < shiftedCoefficient N a b P d))
end M6.ActualTransfer
