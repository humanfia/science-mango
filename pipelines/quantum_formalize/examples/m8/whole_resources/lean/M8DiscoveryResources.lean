import M8DiscoveryAccepted
import M8WeightedSearchAccepted

namespace M8.DiscoveryResources
/-- Symbolic binary-operation upper charges, not Lean evaluator time.
The explicit order bounds residue bit width by N+1.  Membership scans charge
comparison and cursor operations, and span scans charge subtraction,
multiplication, reduction and maximum.  Only executed branches are charged.  The 64*(N+1)^2 leaf base covers
standard binary gcd (shift/subtract with decreasing total bit length),
cutoff computation, final max/comparison and Boolean control.  This
convention does not charge schoolbook division quadratically per gcd step.
The separate control charge covers cursor increment, bounds and return. -/
def control (N : ℕ) : ℕ := 8*(N+1)
def memberCharge {N : ℕ} (A : Finset (ZMod N)) : ℕ :=
  A.sum (fun _ => 4*(N+1))
def spanCharge {N : ℕ} (A : Finset (ZMod N)) : ℕ :=
  A.sum (fun _ => 16*(N+1)^2)
def leftTest {N : ℕ} [NeZero N] (c : M7.Action.Recipe N) (k : M8.Discovery.Choice N) : Bool :=
  ((M8.Anchor.left c k.exchange).sup (fun i => if i.val == k.leftAnchor.val then 1 else 0) == 1)
def rightTest {N : ℕ} [NeZero N] (c : M7.Action.Recipe N) (k : M8.Discovery.Choice N) : Bool :=
  ((M8.Anchor.right c k.exchange).sup (fun i => if i.val == k.rightAnchor.val then 1 else 0) == 1)
def leafCharge {N : ℕ} [NeZero N] (c : M7.Action.Recipe N) (k : M8.Discovery.Choice N) : ℕ :=
  64*(N+1)^2 +
  if Nat.gcd k.unitIndex.val N == 1 then
    memberCharge (M8.Anchor.left c k.exchange) +
    if leftTest c k then
      memberCharge (M8.Anchor.right c k.exchange) +
      if rightTest c k then
        spanCharge (M8.Anchor.left c k.exchange) + spanCharge (M8.Anchor.right c k.exchange)
      else 0
    else 0
  else 0
def charged {n : ℕ} {α : Type} (N : ℕ) (r : M8.WeightedSearch.Run n α) :=
  r.work+r.calls*control N
noncomputable def rightRun {N : ℕ} [NeZero N] (c : M7.Action.Recipe N) (e : Bool) (t a : Fin N) :=
  M8.WeightedSearch.find (fun b : Fin N =>
    let k : M8.Discovery.Choice N := ⟨e,t,a,b⟩
    (if M8.Discovery.test c k then some k else none,leafCharge c k))
noncomputable def leftRun {N : ℕ} [NeZero N] (c : M7.Action.Recipe N) (e : Bool) (t : Fin N) :=
  M8.WeightedSearch.find (fun a : Fin N =>
    let r := rightRun c e t a
    (r.selected.map Prod.snd,charged N r))
noncomputable def unitRun {N : ℕ} [NeZero N] (c : M7.Action.Recipe N) (e : Bool) :=
  M8.WeightedSearch.find (fun t : Fin N =>
    let r := leftRun c e t
    (r.selected.map Prod.snd,charged N r))
noncomputable def run {N : ℕ} [NeZero N] (c : M7.Action.Recipe N) :=
  M8.WeightedSearch.find (fun e : Fin 2 =>
    let r := unitRun c (decide (e.val=1))
    (r.selected.map Prod.snd,charged N r))
noncomputable def work {N : ℕ} [NeZero N] (c : M7.Action.Recipe N) := charged N (run c)
end M8.DiscoveryResources
