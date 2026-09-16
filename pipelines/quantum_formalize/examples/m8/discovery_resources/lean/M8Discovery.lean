import M8AnchorAccepted
import M8CutoffAccepted
import M8FiniteSearchAccepted

namespace M8.Discovery
structure Choice (N : ℕ) where
  exchange : Bool
  unitIndex : Fin N
  leftAnchor : Fin N
  rightAnchor : Fin N
  deriving DecidableEq, Fintype
abbrev Key (N : ℕ) := Lex (Bool × Lex (Fin N × Lex (Fin N × Fin N)))
def key {N : ℕ} (k : Choice N) : Key N :=
  toLex (k.exchange, toLex (k.unitIndex, toLex (k.leftAnchor,k.rightAnchor)))
noncomputable def unit {N : ℕ} [NeZero N] (k : Choice N) : (ZMod N)ˣ := by
  classical
  exact if h : IsUnit (k.unitIndex.val : ZMod N) then h.unit else 1
noncomputable def action {N : ℕ} [NeZero N] (k : Choice N) : M7.Action.Record N :=
  M8.Anchor.record k.exchange (unit k) (k.leftAnchor.val : ZMod N) (k.rightAnchor.val : ZMod N)
noncomputable def transformed {N : ℕ} [NeZero N] (c : M7.Action.Recipe N) (k : Choice N) :=
  M7.Action.act (action k) c
noncomputable def Good {N : ℕ} [NeZero N] (c : M7.Action.Recipe N) (k : Choice N) : Prop :=
  IsUnit (k.unitIndex.val : ZMod N) ∧
  M8.Anchor.Eligible c k.exchange (k.leftAnchor.val : ZMod N) (k.rightAnchor.val : ZMod N) ∧
  M8.Anchor.span (transformed c k) ≤ M8.Cutoff.limit N
/-- Explicit finite Boolean evaluator: gcd test, anchor membership, then numeric residue span. -/
def test {N : ℕ} [NeZero N] (c : M7.Action.Recipe N) (k : Choice N) : Bool :=
  (Nat.gcd k.unitIndex.val N == 1) &&
  ((M8.Anchor.left c k.exchange).sup (fun i => if i.val == k.leftAnchor.val then 1 else 0) == 1) &&
  ((M8.Anchor.right c k.exchange).sup (fun i => if i.val == k.rightAnchor.val then 1 else 0) == 1) &&
  (decide (max
    ((M8.Anchor.left c k.exchange).sup (fun i => (((k.unitIndex.val : ZMod N)*(i-(k.leftAnchor.val : ZMod N))).val)))
    ((M8.Anchor.right c k.exchange).sup (fun i => (((k.unitIndex.val : ZMod N)*(i-(k.rightAnchor.val : ZMod N))).val)))
      ≤ M8.Cutoff.limit N))
noncomputable def atRight {N : ℕ} [NeZero N] (c : M7.Action.Recipe N) (e : Bool) (t a : Fin N) : Option (Choice N) := by
  classical
  exact ((M8.FiniteSearch.find (fun b : Fin N =>
    let k : Choice N := ⟨e,t,a,b⟩
    if test c k then some k else none)).1).map Prod.snd
noncomputable def atLeft {N : ℕ} [NeZero N] (c : M7.Action.Recipe N) (e : Bool) (t : Fin N) : Option (Choice N) :=
  ((M8.FiniteSearch.find (fun a : Fin N => atRight c e t a)).1).map Prod.snd
noncomputable def atUnit {N : ℕ} [NeZero N] (c : M7.Action.Recipe N) (e : Bool) : Option (Choice N) :=
  ((M8.FiniteSearch.find (fun t : Fin N => atLeft c e t)).1).map Prod.snd
noncomputable def discover {N : ℕ} [NeZero N] (c : M7.Action.Recipe N) : Option (Choice N) :=
  ((M8.FiniteSearch.find (fun e : Fin 2 => atUnit c (decide (e.val = 1)))).1).map Prod.snd
end M8.Discovery
