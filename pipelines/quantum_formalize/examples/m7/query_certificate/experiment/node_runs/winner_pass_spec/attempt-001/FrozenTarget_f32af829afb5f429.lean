import M7GlobalQueryAccepted
import M7QueryCertificate


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (H N : ℕ) [NeZero N] (q : M7.DefaultQuery.Query) (bases : M7.GlobalQuery.Family H N) (W : Finset (M7.GlobalQuery.Index H N)) (dominator : M7.GlobalQuery.Index H N → Option (M7.GlobalQuery.Index H N)), (M7.QueryCertificate.winnerPass q bases W dominator = true ↔ (∀ x ∈ W, M7.GlobalQuery.feasible q bases x ∧ ∀ y : M7.GlobalQuery.Index H N, M7.GlobalQuery.feasible q bases y → ¬ M7.QueryCertificate.strictBetter q bases y x) ∧ (∀ x : M7.GlobalQuery.Index H N, M7.GlobalQuery.feasible q bases x → x ∉ W → ∃ y : M7.GlobalQuery.Index H N, dominator x = some y ∧ y ∈ W ∧ M7.QueryCertificate.strictBetter q bases y x))
