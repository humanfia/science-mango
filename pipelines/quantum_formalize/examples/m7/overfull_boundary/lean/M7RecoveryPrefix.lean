import M7PrefixBits
import M7ResiduePrefix
import M7Action
namespace M7.RecoveryPrefix
noncomputable def completed (N w : ℕ) (E : Finset M5.BinaryPolynomial) (p : List Bool) : Finset (M7.Action.Recipe N) := M7.ResiduePrefix.completed N w E (M7.PrefixBits.A N p) (M7.PrefixBits.B N p) (M7.PrefixBits.WA N p) (M7.PrefixBits.WB N p)
noncomputable def leaf (N : ℕ) (p : List Bool) : M7.Action.Recipe N := M7.ResiduePrefix.decodePair N (M7.PrefixBits.A N p, M7.PrefixBits.B N p)
end M7.RecoveryPrefix
