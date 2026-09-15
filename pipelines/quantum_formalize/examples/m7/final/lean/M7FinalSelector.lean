import M7GeneratedFamilyAccepted
import M7StreamingIndicesAccepted
import M7QuerySectorsAccepted
import M7QueryRebaseAccepted

namespace M7.FinalSelector
noncomputable def family (N w : ℕ) [NeZero N] (q : M7.DefaultQuery.Query) :=
  M7.GeneratedFamily.family N w (M7.QuerySectors.effective N q)
abbrev Index (N w : ℕ) [NeZero N] (q : M7.DefaultQuery.Query) :=
  M7.GlobalQuery.Index (M7.GeneratedFamily.size N w (M7.QuerySectors.effective N q)) N
noncomputable def realize {N w : ℕ} [NeZero N] (q : M7.DefaultQuery.Query) (x : Index N w q) :=
  M7.GlobalQuery.realize (family N w q) x
noncomputable def RawFeasible {N : ℕ} [NeZero N] (w : ℕ) (q : M7.DefaultQuery.Query)
    (c : M7.Action.Recipe N) : Prop :=
  M7.PrefixOrbit.ClassValid w c ∧ M7.DefaultQuery.feasible q c c
noncomputable def RawWinner {N : ℕ} [NeZero N] (w : ℕ) (q : M7.DefaultQuery.Query)
    (c : M7.Action.Recipe N) : Prop :=
  RawFeasible w q c ∧ ∀ d : M7.Action.Recipe N, RawFeasible w q d →
    ¬ M7.Selection.better q.order (M7.DefaultQuery.objective q d) (M7.DefaultQuery.objective q c)
noncomputable def win {N w : ℕ} [NeZero N] (q : M7.DefaultQuery.Query)
    (x : Index N w q) : Bool := M7.StreamingIndices.streamWin q (family N w q) x
noncomputable def present {N w : ℕ} [NeZero N] (q : M7.DefaultQuery.Query)
    (x : Index N w q) : Bool := by
  classical
  exact win q x && decide (M7.ActualPresentation.leastAction (family N w q x.1) (realize q x) = some x.2)
noncomputable def answer {N w : ℕ} [NeZero N] (q : M7.DefaultQuery.Query)
    (x : Index N w q) : Except M7.DefaultQuery.QueryError Bool := by
  classical
  exact if M7.DefaultQuery.valid N q then .ok (present q x) else .error .invalidSignature
end M7.FinalSelector
