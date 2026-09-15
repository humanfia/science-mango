import M7PrefixBitsAccepted
import M7PrefixOrbitAccepted
import M7RawCoverage


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N] (S : Finset (ZMod N)), M7.PrefixOrbit.Within (M7.PrefixBits.A N []) (M7.PrefixBits.WA N []) S ↔ (0 : ZMod N) ∈ S
