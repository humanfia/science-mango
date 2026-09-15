import M6ActualTransfer
import M6ActualCounts
import M6CSSDistance

namespace M6.Final
abbrev BP := M6.Cyclic.BinaryPolynomial
/-- Exactly the original anchored, equal-support, connected presentation domain. -/
noncomputable def Admissible (N : ℕ) (a b : BP) : Prop :=
  0 < N ∧ a.coeff 0 = 1 ∧ b.coeff 0 = 1 ∧
  a.support.card = b.support.card ∧ M6.ActualTransfer.span a b < N ∧
  Nat.gcd N ((a.support ∪ b.support).gcd id) = 1
noncomputable def BX (N : ℕ) [NeZero N] (a b : BP) :=
  M6.Spaces.boundaryWords N (M6.Coordinates.coefficients N a) (M6.Coordinates.coefficients N b)
noncomputable def CX (N : ℕ) [NeZero N] (a b : BP) :=
  M6.Spaces.cycleWords N (M6.Coordinates.coefficients N a) (M6.Coordinates.coefficients N b)
noncomputable def BZ (N : ℕ) [NeZero N] (a b : BP) :=
  M6.Character.subspaceWords (M6.Spaces.D N (M6.Coordinates.coefficients N a) (M6.Coordinates.coefficients N b))
noncomputable def CZ (N : ℕ) [NeZero N] (a b : BP) :=
  M6.Character.dualWords (M6.Spaces.B N (M6.Coordinates.coefficients N a) (M6.Coordinates.coefficients N b))
noncomputable def quantumDistance (N : ℕ) [NeZero N] (a b : BP) : Option ℕ :=
  M6.CSS.quantumDistance (BX N a b) (CX N a b) (BZ N a b) (CZ N a b)
/-- Actual CSS rank formula, not a definition in terms of the desired signature degree. -/
noncomputable def encodedQubits (N : ℕ) [NeZero N] (a b : BP) : ℕ :=
  2*N - Module.finrank (ZMod 2) (M6.Spaces.B N (M6.Coordinates.coefficients N a) (M6.Coordinates.coefficients N b)) -
    Module.finrank (ZMod 2) (M6.Spaces.D N (M6.Coordinates.coefficients N a) (M6.Coordinates.coefficients N b))
end M6.Final
