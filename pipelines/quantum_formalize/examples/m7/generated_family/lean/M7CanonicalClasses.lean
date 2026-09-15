import M7CanonicalOuterAccepted
import M7OrbitResidual

namespace M7.CanonicalClasses
def Normalized {N : ℕ} [NeZero N] (bases : Finset (M7.Action.Recipe N)) : Prop :=
  ∀ c ∈ bases, M7.CanonicalOuter.canonical c = c
end M7.CanonicalClasses
