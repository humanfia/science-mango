import M7Presentation
import M7SelectionAccepted

noncomputable def M7.PresentationTarget.record_eta : Prop :=
  ∀ (κ σ τ : Type) (a : M7.Presentation.Record κ σ τ), M7.Presentation.mk (M7.Presentation.outer a) (M7.Presentation.left a) (M7.Presentation.right a) = a

#check M7.PresentationTarget.record_eta

noncomputable def M7.PresentationTarget.record_mono : Prop :=
  ∀ (κ σ τ : Type) [LinearOrder κ] [LinearOrder σ] [LinearOrder τ] (k : κ) (s s1 : σ) (t t1 : τ), s ≤ s1 → t ≤ t1 → M7.Presentation.mk k s t ≤ M7.Presentation.mk k s1 t1

#check M7.PresentationTarget.record_mono

noncomputable def M7.PresentationTarget.candidates_sound : Prop :=
  ∀ (κ σ τ : Type) [LinearOrder κ] [LinearOrder σ] [LinearOrder τ] (K : Finset κ) (L : κ → Finset σ) (R : κ → Finset τ) (a : M7.Presentation.Record κ σ τ), a ∈ M7.Presentation.candidates K L R → M7.Presentation.valid K L R a

#check M7.PresentationTarget.candidates_sound

noncomputable def M7.PresentationTarget.candidate_dominates : Prop :=
  ∀ (κ σ τ : Type) [LinearOrder κ] [LinearOrder σ] [LinearOrder τ] (K : Finset κ) (L : κ → Finset σ) (R : κ → Finset τ) (a : M7.Presentation.Record κ σ τ), M7.Presentation.valid K L R a → ∃ b ∈ M7.Presentation.candidates K L R, b ≤ a

#check M7.PresentationTarget.candidate_dominates

noncomputable def M7.PresentationTarget.leastOf_spec : Prop :=
  ∀ (α : Type) [LinearOrder α] (T : Finset α), (∀ x, M7.Presentation.leastOf T = some x ↔ x ∈ T ∧ ∀ y ∈ T, x ≤ y) ∧ (M7.Presentation.leastOf T = none ↔ T = ∅)

#check M7.PresentationTarget.leastOf_spec

noncomputable def M7.PresentationTarget.factorLeast_spec : Prop :=
  ∀ (κ σ τ : Type) [LinearOrder κ] [LinearOrder σ] [LinearOrder τ] (K : Finset κ) (L : κ → Finset σ) (R : κ → Finset τ) (a : M7.Presentation.Record κ σ τ), M7.Presentation.factorLeast K L R = some a ↔ M7.Presentation.valid K L R a ∧ ∀ b, M7.Presentation.valid K L R b → a ≤ b

#check M7.PresentationTarget.factorLeast_spec

noncomputable def M7.PresentationTarget.factorLeast_none : Prop :=
  ∀ (κ σ τ : Type) [LinearOrder κ] [LinearOrder σ] [LinearOrder τ] (K : Finset κ) (L : κ → Finset σ) (R : κ → Finset τ), M7.Presentation.factorLeast K L R = none ↔ ¬ ∃ a : M7.Presentation.Record κ σ τ, M7.Presentation.valid K L R a

#check M7.PresentationTarget.factorLeast_none

noncomputable def M7.PresentationTarget.domain_membership : Prop :=
  ∀ (κ σ τ : Type) (K : Finset κ) (S : Finset σ) (T : Finset τ) (a : M7.Presentation.Record κ σ τ), a ∈ M7.Presentation.domain K S T ↔ M7.Presentation.outer a ∈ K ∧ M7.Presentation.left a ∈ S ∧ M7.Presentation.right a ∈ T

#check M7.PresentationTarget.domain_membership

noncomputable def M7.PresentationTarget.targetLeast_spec : Prop :=
  ∀ (κ σ τ X Y : Type) [LinearOrder κ] [LinearOrder σ] [LinearOrder τ] (K : Finset κ) (S : Finset σ) (T : Finset τ) (l : κ → σ → X) (r : κ → τ → Y) (q : X × Y), (∀ a : M7.Presentation.Record κ σ τ, M7.Presentation.targetLeast K S T l r q = some a ↔ a ∈ M7.Presentation.domain K S T ∧ M7.Presentation.realize l r a = q ∧ ∀ b ∈ M7.Presentation.domain K S T, M7.Presentation.realize l r b = q → a ≤ b) ∧ (M7.Presentation.targetLeast K S T l r q = none ↔ ¬ ∃ a ∈ M7.Presentation.domain K S T, M7.Presentation.realize l r a = q)

#check M7.PresentationTarget.targetLeast_spec

noncomputable def M7.PresentationTarget.winning_fiber : Prop :=
  ∀ (κ σ τ X Y : Type) [LinearOrder κ] [LinearOrder σ] [LinearOrder τ] (K : Finset κ) (S : Finset σ) (T : Finset τ) (l : κ → σ → X) (r : κ → τ → Y) (m : ℕ) (feasible : X × Y → Prop) (objective : X × Y → Fin m → ℤ) (mode : M7.Selection.Mode) (a b : M7.Presentation.Record κ σ τ), a ∈ M7.Presentation.domain K S T → b ∈ M7.Presentation.domain K S T → M7.Presentation.realize l r a = M7.Presentation.realize l r b → (a ∈ M7.Presentation.selected K S T l r feasible objective mode ↔ b ∈ M7.Presentation.selected K S T l r feasible objective mode)

#check M7.PresentationTarget.winning_fiber

noncomputable def M7.PresentationTarget.presentation_exact : Prop :=
  ∀ (κ σ τ X Y : Type) [LinearOrder κ] [LinearOrder σ] [LinearOrder τ] (K : Finset κ) (S : Finset σ) (T : Finset τ) (l : κ → σ → X) (r : κ → τ → Y) (m : ℕ) (feasible : X × Y → Prop) (objective : X × Y → Fin m → ℤ) (mode : M7.Selection.Mode) (a : M7.Presentation.Record κ σ τ), a ∈ M7.Presentation.selected K S T l r feasible objective mode → ∃! b : M7.Presentation.Record κ σ τ, M7.Presentation.present K S T l r feasible objective mode b ∧ M7.Presentation.realize l r b = M7.Presentation.realize l r a

#check M7.PresentationTarget.presentation_exact

noncomputable def M7.PresentationTarget.presentation_sound : Prop :=
  ∀ (κ σ τ X Y : Type) [LinearOrder κ] [LinearOrder σ] [LinearOrder τ] (K : Finset κ) (S : Finset σ) (T : Finset τ) (l : κ → σ → X) (r : κ → τ → Y) (m : ℕ) (feasible : X × Y → Prop) (objective : X × Y → Fin m → ℤ) (mode : M7.Selection.Mode) (a : M7.Presentation.Record κ σ τ), M7.Presentation.present K S T l r feasible objective mode a → a ∈ M7.Presentation.selected K S T l r feasible objective mode ∧ a ∈ M7.Presentation.domain K S T ∧ ∀ b ∈ M7.Presentation.domain K S T, M7.Presentation.realize l r b = M7.Presentation.realize l r a → a ≤ b

#check M7.PresentationTarget.presentation_sound

