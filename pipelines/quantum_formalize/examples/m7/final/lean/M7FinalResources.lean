import M7GeneratedLabelsAccepted
import M7GenerationCallsAccepted
import M7CompactStorageAccepted
import M7ScalarWorkAccepted
import M7StreamingCostAccepted
import M7ObjectiveComparisonAccepted

namespace M7.FinalResources
open scoped BigOperators
noncomputable def distanceWork (N w : ℕ) [NeZero N] (E : Finset M5.BinaryPolynomial) : ℕ :=
  ∑ i : Fin (M7.GeneratedFamily.size N w E),
    M6.ActualTransfer.actualDistanceWork N
      (M7.Supports.polynomial (M7.GeneratedFamily.family N w E i).1)
      (M7.Supports.polynomial (M7.GeneratedFamily.family N w E i).2)
/-- Analysis parameter: maximum signed coordinate word length, not a stored action ledger. -/
noncomputable def objectiveBits {H N : ℕ} [NeZero N] (q : M7.DefaultQuery.Query)
    (bases : M7.GlobalQuery.Family H N) : ℕ := by
  classical
  exact 1 + Finset.univ.sup (fun x : M7.GlobalQuery.Index H N =>
    Finset.univ.sup (fun j : Fin q.objectives.length =>
      (M7.GlobalQuery.objective q bases x j).natAbs.size))
/-- Original signed-word comparison model: up to 2(m+1) comparisons per candidate pair,
    charged by the actual maximum signed word width. Labels/preprocessing/output costs
    are separate. This is not a claim about Lean runtime or arbitrary evaluators. -/
noncomputable def comparisonCharge {H N : ℕ} [NeZero N] (q : M7.DefaultQuery.Query)
    (bases : M7.GlobalQuery.Family H N) : ℕ :=
  (M7.StreamingCost.scanWins q bases).inner * (2*(q.objectives.length+1)) * objectiveBits q bases
end M7.FinalResources
