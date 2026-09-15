import M7PrefixOrbitAccepted
import M7RecoveryPrefixAccepted
import M7DescentTraceAccepted

namespace M7.RecoveryInstance

def GoodBases {N : ℕ} [NeZero N] (w : ℕ) (bases : Finset (M7.Action.Recipe N)) : Prop :=
  (∀ c ∈ bases, M7.PrefixOrbit.ClassValid w c) ∧ M7.CanonicalClasses.Normalized bases

noncomputable def count {N : ℕ} [NeZero N] (w : ℕ) (E : Finset M5.BinaryPolynomial)
    (bases : Finset (M7.Action.Recipe N)) (p : List Bool) : ℤ :=
  M7.PrefixOrbit.residual w E (M7.PrefixBits.A N p) (M7.PrefixBits.B N p)
    (M7.PrefixBits.WA N p) (M7.PrefixBits.WB N p) bases

noncomputable def remaining {N : ℕ} [NeZero N] (w : ℕ) (E : Finset M5.BinaryPolynomial)
    (bases : Finset (M7.Action.Recipe N)) (p : List Bool) : Finset (M7.Action.Recipe N) :=
  M7.OrbitResidual.remaining (M7.RecoveryPrefix.completed N w E p) bases

noncomputable def path {N : ℕ} [NeZero N] (w : ℕ) (E : Finset M5.BinaryPolynomial)
    (bases : Finset (M7.Action.Recipe N)) : List M7.DescentTrace.Step :=
  M7.DescentTrace.trace (count w E bases) [] (M7.PrefixBits.depth N)

noncomputable def word {N : ℕ} [NeZero N] (w : ℕ) (E : Finset M5.BinaryPolynomial)
    (bases : Finset (M7.Action.Recipe N)) : List Bool :=
  M7.DescentTrace.endpoint [] (path w E bases)

noncomputable def recoverLeaf {N : ℕ} [NeZero N] (w : ℕ) (E : Finset M5.BinaryPolynomial)
    (bases : Finset (M7.Action.Recipe N)) : M7.Action.Recipe N :=
  M7.RecoveryPrefix.leaf N (word w E bases)

noncomputable def insertedBases {N : ℕ} [NeZero N] (w : ℕ) (E : Finset M5.BinaryPolynomial)
    (bases : Finset (M7.Action.Recipe N)) : Finset (M7.Action.Recipe N) := by
  classical
  exact insert (M7.CanonicalOuter.canonical (recoverLeaf w E bases)) bases
end M7.RecoveryInstance
