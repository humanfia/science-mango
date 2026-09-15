import M7PrefixBitsAccepted
import M7PrefixOrbitAccepted
import M7RawCoverage


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N] (c : M7.Action.Recipe N) (s t : ZMod N), M7.RecipeSignature.signature (M7.Action.act (M7.Action.translate s t) c) = M7.RecipeSignature.signature c
