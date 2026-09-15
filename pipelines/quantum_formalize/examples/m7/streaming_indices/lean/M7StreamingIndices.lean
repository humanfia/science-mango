import M7GlobalQueryAccepted

namespace M7.StreamingIndices
/-- Bounded tail recursion; no list or full index collection is constructed. -/
def allFinFrom (n : ℕ) (p : Fin n → Bool) (i : ℕ) : ℕ → Bool
  | 0 => true
  | fuel + 1 => if hi : i < n then
      if p ⟨i, hi⟩ then allFinFrom n p (i + 1) fuel else false
    else true

def allFin (n : ℕ) (p : Fin n → Bool) : Bool := allFinFrom n p 0 n

noncomputable def decodeRecord (N : ℕ) [NeZero N]
    (u : Fin (Fintype.card ((ZMod N)ˣ))) (e : Fin 2) (s t : Fin N) : M7.Action.Record N :=
  { unit := (Fintype.equivFin ((ZMod N)ˣ)).symm u
    exchange := decide (e.val = 1)
    leftShift := (s.val : ZMod N)
    rightShift := (t.val : ZMod N) }

noncomputable def allRecords (N : ℕ) [NeZero N] (p : M7.Action.Record N → Bool) : Bool :=
  allFin (Fintype.card ((ZMod N)ˣ)) (fun u =>
    allFin 2 (fun e => allFin N (fun s => allFin N (fun t => p (decodeRecord N u e s t)))))

noncomputable def allIndices (H N : ℕ) [NeZero N] (p : M7.GlobalQuery.Index H N → Bool) : Bool :=
  allFin H (fun h => allRecords N (fun g => p (h, g)))

noncomputable def streamWin {H N : ℕ} [NeZero N] (q : M7.DefaultQuery.Query)
    (bases : M7.GlobalQuery.Family H N) (x : M7.GlobalQuery.Index H N) : Bool := by
  classical
  exact decide (M7.GlobalQuery.feasible q bases x) &&
    allIndices H N (fun y => decide (M7.GlobalQuery.feasible q bases y →
      ¬ M7.Selection.better q.order (M7.GlobalQuery.objective q bases y)
        (M7.GlobalQuery.objective q bases x)))
end M7.StreamingIndices
