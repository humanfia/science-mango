import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic
open scoped BigOperators
namespace M7.Factorized
noncomputable def count {α : Type} [Fintype α] (P : α → Prop) : ℕ := by
  classical
  exact (Finset.univ.filter P).card
noncomputable def numerator {U S T : Type} [Fintype U] [Fintype S] [Fintype T]
    (sector : U → Prop) (left : U → S → Prop) (right : U → T → Prop) : ℕ := by
  classical
  exact ∑ u, (if sector u then 1 else 0) * count (left u) * count (right u)
noncomputable def records {U S T : Type} [Fintype U] [Fintype S] [Fintype T]
    (sector : U → Prop) (left : U → S → Prop) (right : U → T → Prop) : Finset (U × S × T) := by
  classical
  exact Finset.univ.filter (fun r => sector r.1 ∧ left r.1 r.2.1 ∧ right r.1 r.2.2)
noncomputable def exactTargetNumerator {U S T X Y : Type} [Fintype U] [Fintype S] [Fintype T]
    (leftImage : U → S → X) (rightImage : U → T → Y) (x : X) (y : Y) : ℕ :=
  numerator (fun _ => True) (fun u s => leftImage u s = x) (fun u t => rightImage u t = y)
end M7.Factorized
