import M7StreamingIndicesAccepted
namespace M7.StreamingCost
structure Eval where
  result : Bool
  outer : ℕ
  inner : ℕ
  deriving DecidableEq
/-- Two counters are accumulated with the actual short-circuit recursion. -/
def allFinFrom (n : ℕ) (p : Fin n → Eval) (i : ℕ) : ℕ → Eval
  | 0 => ⟨true, 0, 0⟩
  | fuel + 1 => if hi : i < n then
      let r := p ⟨i, hi⟩
      if r.result then
        let t := allFinFrom n p (i + 1) fuel
        ⟨t.result, r.outer + t.outer, r.inner + t.inner⟩
      else r
    else ⟨true, 0, 0⟩
def allFin (n : ℕ) (p : Fin n → Eval) : Eval := allFinFrom n p 0 n
noncomputable def recordCount (N : ℕ) [NeZero N] : ℕ := 2 * Fintype.card ((ZMod N)ˣ) * N^2
noncomputable def allRecords (N : ℕ) [NeZero N] (p : M7.Action.Record N → Eval) : Eval :=
  allFin (Fintype.card ((ZMod N)ˣ)) (fun u =>
    allFin 2 (fun e => allFin N (fun s => allFin N (fun t =>
      p (M7.StreamingIndices.decodeRecord N u e s t)))))
noncomputable def allIndices (H N : ℕ) [NeZero N] (p : M7.GlobalQuery.Index H N → Eval) : Eval :=
  allFin H (fun h => allRecords N (fun g => p (h,g)))
noncomputable def streamWin {H N : ℕ} [NeZero N] (q : M7.DefaultQuery.Query)
    (bases : M7.GlobalQuery.Family H N) (x : M7.GlobalQuery.Index H N) : Eval := by
  classical
  exact if M7.GlobalQuery.feasible q bases x then
    allIndices H N (fun y => ⟨decide (M7.GlobalQuery.feasible q bases y →
      ¬ M7.Selection.better q.order (M7.GlobalQuery.objective q bases y)
        (M7.GlobalQuery.objective q bases x)), 0, 1⟩)
    else ⟨false, 0, 0⟩
/-- Visit every outer candidate; its winning Boolean is consumed without a ledger.
The counters record one outer visit and its actual short-circuited inner visits. -/
noncomputable def scanWins {H N : ℕ} [NeZero N] (q : M7.DefaultQuery.Query)
    (bases : M7.GlobalQuery.Family H N) : Eval :=
  allIndices H N (fun x => let r := streamWin q bases x; ⟨true, 1, r.inner⟩)
end M7.StreamingCost
