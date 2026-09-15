import M7PrefixBitsAccepted
import M7PrefixOrbitAccepted
import M7RawCoverage

def Frozen_translate_supports : Prop :=
 ∀ (N : ℕ) [NeZero N] (c : M7.Action.Recipe N) (s t : ZMod N), M7.Action.act (M7.Action.translate s t) c = (M7.Domain.shift c.1 s, M7.Domain.shift c.2 t)

def Frozen_translate_signature : Prop :=
 ∀ (N : ℕ) [NeZero N] (c : M7.Action.Recipe N) (s t : ZMod N), M7.RecipeSignature.signature (M7.Action.act (M7.Action.translate s t) c) = M7.RecipeSignature.signature c

def Frozen_root_within : Prop :=
 ∀ (N : ℕ) [NeZero N] (S : Finset (ZMod N)), M7.PrefixOrbit.Within (M7.PrefixBits.A N []) (M7.PrefixBits.WA N []) S ↔ (0 : ZMod N) ∈ S

def Frozen_root_membership : Prop :=
 ∀ (N w : ℕ) [NeZero N] (E : Finset M5.BinaryPolynomial) (c : M7.Action.Recipe N), c ∈ M7.RawCoverage.rootCompleted N w E ↔ M7.RawCoverage.Queried w E c ∧ (0 : ZMod N) ∈ c.1 ∧ (0 : ZMod N) ∈ c.2

def Frozen_raw_anchor : Prop :=
 ∀ (N w : ℕ) [NeZero N] (E : Finset M5.BinaryPolynomial) (c : M7.Action.Recipe N), 0 < w → M7.RawCoverage.Queried w E c → ∃ q ∈ c.1, ∃ r ∈ c.2, M7.Action.act (M7.Action.translate (-q) (-r)) c ∈ M7.RawCoverage.rootCompleted N w E

def Frozen_remaining_coverage : Prop :=
 ∀ (N w : ℕ) [NeZero N] (E : Finset M5.BinaryPolynomial) (bases : Finset (M7.Action.Recipe N)), 0 < w → M7.CanonicalClasses.Normalized bases → (∀ b ∈ bases, M7.PrefixOrbit.ClassValid w b) → M7.OrbitResidual.remaining (M7.RawCoverage.rootCompleted N w E) bases = ∅ → ∀ c : M7.Action.Recipe N, M7.RawCoverage.Queried w E c → M7.CanonicalOuter.canonical c ∈ bases ∧ ∃ b ∈ bases, ∃ g : M7.Action.Record N, M7.Action.act g b = c
