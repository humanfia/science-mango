import M7ClosedSolveAccepted
import M7DefaultQuery
import M7RecipeSignatureAccepted

namespace M7.QualityTable
noncomputable def solveDistance {N : ℕ} [NeZero N] (c : M7.Action.Recipe N) : Option ℕ :=
  (M6.ActualTransfer.solve N (M7.Supports.polynomial c.1) (M7.Supports.polynomial c.2)).map Prod.fst
noncomputable def cache {N : ℕ} [NeZero N] (c : M7.Action.Recipe N) : ℕ × Option ℕ :=
  (2*(M7.DefaultQuery.signature c).natDegree, solveDistance c)
noncomputable def blockScores {N : ℕ} (A : Finset (ZMod N)) : ℕ × ℕ :=
  (M7.DefaultQuery.blockLocality A, M7.DefaultQuery.blockRadius A)
noncomputable def leftTable {N : ℕ} [NeZero N] (c : M7.Action.Recipe N)
    (u : M7.ActualFactorized.Outer N) : Array (ℕ × ℕ) :=
  Array.ofFn (fun i : Fin N => blockScores (M7.ActualFactorized.leftImage c u (i.val : ZMod N)))
noncomputable def rightTable {N : ℕ} [NeZero N] (c : M7.Action.Recipe N)
    (u : M7.ActualFactorized.Outer N) : Array (ℕ × ℕ) :=
  Array.ofFn (fun i : Fin N => blockScores (M7.ActualFactorized.rightImage c u (i.val : ZMod N)))
def read {N : ℕ} (table : Array (ℕ × ℕ)) (i : ZMod N) : ℕ × ℕ :=
  table[i.val]?.getD (0,0)
noncomputable def placedScores {N : ℕ} [NeZero N] (c : M7.Action.Recipe N)
    (g : M7.Action.Record N) : ℕ × ℕ :=
  let l := read (leftTable c (g.unit,g.exchange)) g.leftShift
  let r := read (rightTable c (g.unit,g.exchange)) g.rightShift
  (l.1+r.1, max l.2 r.2)
end M7.QualityTable
