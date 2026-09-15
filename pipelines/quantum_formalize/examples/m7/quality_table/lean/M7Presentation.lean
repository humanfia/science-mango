import M7Selection
import Mathlib.Data.Prod.Lex

namespace M7.Presentation

abbrev Record (κ σ τ : Type*) := Lex (κ × Lex (σ × τ))
def mk {κ σ τ : Type*} (k : κ) (s : σ) (t : τ) : Record κ σ τ := toLex (k, toLex (s,t))
def outer {κ σ τ : Type*} (r : Record κ σ τ) : κ := (ofLex r).1
def left {κ σ τ : Type*} (r : Record κ σ τ) : σ := (ofLex (ofLex r).2).1
def right {κ σ τ : Type*} (r : Record κ σ τ) : τ := (ofLex (ofLex r).2).2

def valid {κ σ τ : Type*} (K : Finset κ) (L : κ → Finset σ) (R : κ → Finset τ)
    (r : Record κ σ τ) : Prop := outer r ∈ K ∧ left r ∈ L (outer r) ∧ right r ∈ R (outer r)

noncomputable def candidates {κ σ τ : Type*} [LinearOrder κ] [LinearOrder σ] [LinearOrder τ]
    (K : Finset κ) (L : κ → Finset σ) (R : κ → Finset τ) : Finset (Record κ σ τ) := by
  classical
  exact K.biUnion (fun k => if h : (L k).Nonempty ∧ (R k).Nonempty then
    {mk k ((L k).min' h.1) ((R k).min' h.2)} else ∅)

noncomputable def leastOf {α : Type*} [LinearOrder α] (S : Finset α) : Option α :=
  if h : S.Nonempty then some (S.min' h) else none

noncomputable def factorLeast {κ σ τ : Type*} [LinearOrder κ] [LinearOrder σ] [LinearOrder τ]
    (K : Finset κ) (L : κ → Finset σ) (R : κ → Finset τ) : Option (Record κ σ τ) :=
  leastOf (candidates K L R)

def realize {κ σ τ X Y : Type*} (l : κ → σ → X) (r : κ → τ → Y)
    (a : Record κ σ τ) : X × Y := (l (outer a) (left a), r (outer a) (right a))

noncomputable def domain {κ σ τ : Type*} (K : Finset κ) (S : Finset σ) (T : Finset τ) : Finset (Record κ σ τ) := by
  classical
  exact K.biUnion (fun k => (S ×ˢ T).image (fun p => mk k p.1 p.2))

noncomputable def targetLeast {κ σ τ X Y : Type*} [LinearOrder κ] [LinearOrder σ] [LinearOrder τ]
    (K : Finset κ) (S : Finset σ) (T : Finset τ) (l : κ → σ → X) (r : κ → τ → Y)
    (q : X × Y) : Option (Record κ σ τ) := by
  classical
  exact factorLeast K (fun k => S.filter (fun s => l k s = q.1))
    (fun k => T.filter (fun t => r k t = q.2))

noncomputable def selected {κ σ τ X Y : Type*} {m : ℕ}
    (K : Finset κ) (S : Finset σ) (T : Finset τ) (l : κ → σ → X) (r : κ → τ → Y)
    (feasible : X × Y → Prop) (objective : X × Y → Fin m → ℤ) (mode : M7.Selection.Mode) :=
  M7.Selection.select (domain K S T) (fun a => feasible (realize l r a))
    (fun a => objective (realize l r a)) mode

noncomputable def present {κ σ τ X Y : Type*} [LinearOrder κ] [LinearOrder σ] [LinearOrder τ] {m : ℕ}
    (K : Finset κ) (S : Finset σ) (T : Finset τ) (l : κ → σ → X) (r : κ → τ → Y)
    (feasible : X × Y → Prop) (objective : X × Y → Fin m → ℤ) (mode : M7.Selection.Mode)
    (a : Record κ σ τ) : Prop :=
  a ∈ selected K S T l r feasible objective mode ∧ targetLeast K S T l r (realize l r a) = some a

end M7.Presentation
