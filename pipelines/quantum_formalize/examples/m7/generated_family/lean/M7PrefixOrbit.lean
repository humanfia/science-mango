import M7ResiduePrefixAccepted
import M7RecipeSignatureAccepted
import M7ConnectivityAccepted
import M7CanonicalClassesAccepted
import M7OrbitResidualAccepted

namespace M7.PrefixOrbit
open scoped BigOperators
def Within {N : ℕ} (D W : Finset ℕ) (S : Finset (ZMod N)) : Prop :=
  D ⊆ M7.ResiduePrefix.encode S ∧ M7.ResiduePrefix.encode S ⊆ D ∪ W
def ClassValid {N : ℕ} (w : ℕ) (c : M7.Action.Recipe N) : Prop :=
  c.1.card = w ∧ c.2.card = w ∧ M7.Connectivity.connected c
noncomputable def orbitCount {N : ℕ} [NeZero N] (E : Finset M5.BinaryPolynomial)
    (A B WA WB : Finset ℕ) (c : M7.Action.Recipe N) : ℕ :=
  M7.RecipeSignature.sourceCount c (fun F => F ∈ E) (Within A WA) (Within B WB)
noncomputable def residual {N : ℕ} [NeZero N] (w : ℕ) (E : Finset M5.BinaryPolynomial)
    (A B WA WB : Finset ℕ) (bases : Finset (M7.Action.Recipe N)) : ℤ :=
  M7.PrefixSector.count N w E A B WA WB - ∑ c ∈ bases, (orbitCount E A B WA WB c : ℤ)
end M7.PrefixOrbit
