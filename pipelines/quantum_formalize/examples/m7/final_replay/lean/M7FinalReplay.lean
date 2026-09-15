import M7FinalSelectorAccepted
import M7GeneratedLabelsAccepted
import M7GenerationReplayAccepted
import M7LabelReplayAccepted
import M7FactorReplayAccepted
import M7QueryCertificateAccepted

namespace M7.FinalReplay
structure Certificate (N w : ℕ) [NeZero N] (q : M7.DefaultQuery.Query) where
  generation : M7.CompactGeneration.Output N
  factors : List (M5.BinaryPolynomial × ℕ)
  labels : Fin (M7.GeneratedFamily.size N w (M7.QuerySectors.effective N q)) → M7.LabelReplay.Certificate N
  query : M7.QueryCertificate.Certificate (M7.GeneratedFamily.size N w (M7.QuerySectors.effective N q)) N
/-- Finite component checks, with explicit alignment of the certified bases and the
    actual deterministic family used by the query indices. No recorded number or hash
    replaces arithmetic recomputation. Query-certificate expansion is explicitly finite. -/
noncomputable def check {N w : ℕ} [NeZero N] (q : M7.DefaultQuery.Query)
    (c : Certificate N w q) : Except M7.DefaultQuery.QueryError Bool := by
  classical
  exact if M7.DefaultQuery.valid N q then
    .ok (M7.GenerationReplay.check w (M7.QuerySectors.effective N q) c.generation &&
      M7.FactorReplay.check (M6.Cyclic.modulus N) c.factors &&
      decide (c.generation.finalBases = (M7.CompactGeneration.generate (N := N) w (M7.QuerySectors.effective N q)).finalBases) &&
      M7.QueryCertificate.allOn Finset.univ (fun i =>
        M7.LabelReplay.check (M7.FinalSelector.family N w q i) (c.labels i)) &&
      match M7.QueryCertificate.check q (M7.FinalSelector.family N w q) c.query with
      | .ok result => result
      | .error _ => false)
    else .error .invalidSignature
end M7.FinalReplay
