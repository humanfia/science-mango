import M7ActionAccepted

namespace M8.Anchor
abbrev Recipe (N : ℕ) := M7.Action.Recipe N
def left {N : ℕ} (c : Recipe N) (e : Bool) := if e then c.2 else c.1
def right {N : ℕ} (c : Recipe N) (e : Bool) := if e then c.1 else c.2
def Eligible {N : ℕ} (c : Recipe N) (e : Bool) (a b : ZMod N) : Prop :=
  a ∈ left c e ∧ b ∈ right c e
def record {N : ℕ} [NeZero N] (e : Bool) (u : (ZMod N)ˣ) (a b : ZMod N) : M7.Action.Record N :=
  ⟨u, e, -((u : ZMod N)*a), -((u : ZMod N)*b)⟩
noncomputable def trial {N : ℕ} [NeZero N] (c : Recipe N) (e : Bool) (u : (ZMod N)ˣ) (a b : ZMod N) : Recipe N :=
  M7.Action.act (record e u a b) c
noncomputable def span {N : ℕ} (c : Recipe N) : ℕ :=
  max (c.1.sup ZMod.val) (c.2.sup ZMod.val)
def Anchored {N : ℕ} [NeZero N] (c : Recipe N) : Prop := 0 ∈ c.1 ∧ 0 ∈ c.2
end M8.Anchor
