import M7GlobalQuery
namespace M7.QueryCertificate
structure Certificate (H N : ℕ) [NeZero N] where
  winners : Finset (M7.GlobalQuery.Index H N)
  presentations : Finset (M7.GlobalQuery.Index H N)
  dominator : M7.GlobalQuery.Index H N → Option (M7.GlobalQuery.Index H N)
noncomputable def allOn {α : Type*} (s : Finset α) (p : α → Bool) : Bool := by
  classical
  exact s.toList.all p
noncomputable def strictBetter {H N : ℕ} [NeZero N] (q : M7.DefaultQuery.Query) (bases : M7.GlobalQuery.Family H N) (y x : M7.GlobalQuery.Index H N) : Prop := M7.Selection.better q.order (M7.GlobalQuery.objective q bases y) (M7.GlobalQuery.objective q bases x)
noncomputable def isLeast {H N : ℕ} [NeZero N] (bases : M7.GlobalQuery.Family H N) (x : M7.GlobalQuery.Index H N) : Prop := M7.ActualPresentation.leastAction (bases x.1) (M7.GlobalQuery.realize bases x) = some x.2
noncomputable def winnerPass {H N : ℕ} [NeZero N] (q : M7.DefaultQuery.Query) (bases : M7.GlobalQuery.Family H N) (W : Finset (M7.GlobalQuery.Index H N)) (dominator : M7.GlobalQuery.Index H N → Option (M7.GlobalQuery.Index H N)) : Bool := by
  classical
  exact allOn W (fun x => decide (M7.GlobalQuery.feasible q bases x) &&
      allOn Finset.univ (fun y => decide (M7.GlobalQuery.feasible q bases y → ¬ strictBetter q bases y x))) &&
    allOn Finset.univ (fun x => if M7.GlobalQuery.feasible q bases x ∧ x ∉ W then
      match dominator x with
      | none => false
      | some y => decide (y ∈ W ∧ strictBetter q bases y x)
      else true)
noncomputable def presentationPass {H N : ℕ} [NeZero N] (bases : M7.GlobalQuery.Family H N) (W P : Finset (M7.GlobalQuery.Index H N)) : Bool := by
  classical
  exact allOn P (fun x => decide (x ∈ W ∧ isLeast bases x)) &&
    allOn W (fun x => decide (isLeast bases x → x ∈ P))
noncomputable def check {H N : ℕ} [NeZero N] (q : M7.DefaultQuery.Query) (bases : M7.GlobalQuery.Family H N) (certificate : Certificate H N) : Except M7.DefaultQuery.QueryError Bool := by
  classical
  exact if M7.DefaultQuery.valid N q then
    .ok (winnerPass q bases certificate.winners certificate.dominator &&
      presentationPass bases certificate.winners certificate.presentations)
    else .error .invalidSignature
/-- Semantic output set used only in theorem targets, never by the checker. -/
noncomputable def allPresentations {H N : ℕ} [NeZero N] (q : M7.DefaultQuery.Query) (bases : M7.GlobalQuery.Family H N) : Finset (M7.GlobalQuery.Index H N) := by
  classical
  exact Finset.univ.filter (M7.GlobalQuery.present q bases)
end M7.QueryCertificate
