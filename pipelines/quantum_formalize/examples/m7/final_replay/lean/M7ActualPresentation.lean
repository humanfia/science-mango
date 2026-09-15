import M7Action
import M7Presentation

namespace M7.ActualPresentation
structure UnitKey (N : ℕ) [NeZero N] where
  unit : (ZMod N)ˣ
  deriving DecidableEq, Fintype
instance (N : ℕ) [NeZero N] : LinearOrder (UnitKey N) :=
  LinearOrder.lift' (fun k : UnitKey N => (k.unit : ZMod N).val) (by
    intro a b h
    cases a with | mk a =>
      cases b with | mk b =>
        congr 1
        apply Units.ext
        exact ZMod.val_injective N h)
abbrev Outer (N : ℕ) [NeZero N] := Lex (UnitKey N × Bool)
abbrev Encoded (N : ℕ) [NeZero N] := M7.Presentation.Record (Outer N) (Fin N) (Fin N)
def encode {N : ℕ} [NeZero N] (g : M7.Action.Record N) : Encoded N :=
  M7.Presentation.mk (toLex (⟨g.unit⟩, g.exchange))
    ⟨g.leftShift.val, ZMod.val_lt g.leftShift⟩ ⟨g.rightShift.val, ZMod.val_lt g.rightShift⟩
def decode {N : ℕ} [NeZero N] (a : Encoded N) : M7.Action.Record N :=
  ⟨(ofLex (M7.Presentation.outer a)).1.unit, (ofLex (M7.Presentation.outer a)).2,
   ((M7.Presentation.left a).val : ZMod N), ((M7.Presentation.right a).val : ZMod N)⟩
noncomputable def leftImage {N : ℕ} [NeZero N] (c : M7.Action.Recipe N)
    (k : Outer N) (s : Fin N) : Finset (ZMod N) :=
  (if (ofLex k).2 then c.2 else c.1).image (M7.Action.affine (ofLex k).1.unit (s.val : ZMod N))
noncomputable def rightImage {N : ℕ} [NeZero N] (c : M7.Action.Recipe N)
    (k : Outer N) (t : Fin N) : Finset (ZMod N) :=
  (if (ofLex k).2 then c.1 else c.2).image (M7.Action.affine (ofLex k).1.unit (t.val : ZMod N))
noncomputable def leastAction {N : ℕ} [NeZero N] (c q : M7.Action.Recipe N) : Option (M7.Action.Record N) :=
  (M7.Presentation.targetLeast Finset.univ Finset.univ Finset.univ (leftImage c) (rightImage c) q).map decode
noncomputable def selected {N : ℕ} [NeZero N] {m : ℕ} (c : M7.Action.Recipe N)
    (feasible : M7.Action.Recipe N → Prop) (objective : M7.Action.Recipe N → Fin m → ℤ)
    (mode : M7.Selection.Mode) : Finset (M7.Action.Record N) :=
  M7.Selection.select Finset.univ (fun g => feasible (M7.Action.act g c))
    (fun g => objective (M7.Action.act g c)) mode
noncomputable def present {N : ℕ} [NeZero N] {m : ℕ} (c : M7.Action.Recipe N)
    (feasible : M7.Action.Recipe N → Prop) (objective : M7.Action.Recipe N → Fin m → ℤ)
    (mode : M7.Selection.Mode) (g : M7.Action.Record N) : Prop :=
  g ∈ selected c feasible objective mode ∧ leastAction c (M7.Action.act g c) = some g
end M7.ActualPresentation
