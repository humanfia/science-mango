import M7GlobalQueryAccepted
import M7QueryCertificate


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (H N : ℕ) [NeZero N] (bases : M7.GlobalQuery.Family H N) (W P : Finset (M7.GlobalQuery.Index H N)), (M7.QueryCertificate.presentationPass bases W P = true ↔ ∀ x : M7.GlobalQuery.Index H N, x ∈ P ↔ x ∈ W ∧ M7.QueryCertificate.isLeast bases x)
