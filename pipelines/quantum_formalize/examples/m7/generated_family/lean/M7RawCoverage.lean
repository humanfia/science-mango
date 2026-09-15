import M7PrefixOrbit
import M7PrefixBits

namespace M7.RawCoverage
noncomputable def rootCompleted (N w : ℕ) (E : Finset M5.BinaryPolynomial) :=
  M7.ResiduePrefix.completed N w E (M7.PrefixBits.A N []) (M7.PrefixBits.B N [])
    (M7.PrefixBits.WA N []) (M7.PrefixBits.WB N [])
def Queried {N : ℕ} (w : ℕ) (E : Finset M5.BinaryPolynomial) (c : M7.Action.Recipe N) : Prop :=
  M7.PrefixOrbit.ClassValid w c ∧ M7.RecipeSignature.signature c ∈ E
end M7.RawCoverage
