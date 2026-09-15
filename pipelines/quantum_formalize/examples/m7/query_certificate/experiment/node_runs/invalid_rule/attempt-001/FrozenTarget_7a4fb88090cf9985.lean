import M7GlobalQueryAccepted
import M7QueryCertificate


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (H N : ℕ) [NeZero N] (q : M7.DefaultQuery.Query) (bases : M7.GlobalQuery.Family H N) (certificate : M7.QueryCertificate.Certificate H N), (M7.QueryCertificate.check q bases certificate = Except.error M7.DefaultQuery.QueryError.invalidSignature ↔ ¬ M7.DefaultQuery.valid N q) ∧ (M7.DefaultQuery.valid N q → M7.QueryCertificate.check q bases certificate = Except.ok (M7.QueryCertificate.winnerPass q bases certificate.winners certificate.dominator && M7.QueryCertificate.presentationPass bases certificate.winners certificate.presentations))
