import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.List.FinRange
import Mathlib.Tactic

open scoped BigOperators
namespace M6.Pinned

abbrev Vector (m : ℕ) := Fin m → ZMod 2
abbrev Pins (m : ℕ) := Fin m → Option (ZMod 2)

def free (m : ℕ) : Pins m := fun _ => none

def agrees {m : ℕ} (P : Pins m) (v : Vector m) : Prop :=
  ∀ i b, P i = some b → v i = b

noncomputable def weight {m : ℕ} (v : Vector m) : ℕ := by
  classical
  exact (Finset.univ.filter (fun i => v i ≠ 0)).card

noncomputable def enumerator {m : ℕ} (L : Finset (Vector m))
    (P : Pins m) : Polynomial ℤ := by
  classical
  exact ∑ v ∈ L, if agrees P v then Polynomial.X ^ weight v else 0

noncomputable def count {m : ℕ} (L : Finset (Vector m))
    (P : Pins m) (d : ℕ) : ℤ := by
  classical
  exact ((L.filter (fun v => agrees P v ∧ weight v = d)).card : ℤ)

noncomputable def pin {m : ℕ} (P : Pins m) (i : Fin m) (b : ZMod 2) : Pins m :=
  Function.update P i (some b)

def refines {m : ℕ} (P Q : Pins m) : Prop :=
  ∀ i b, P i = some b → Q i = some b

def assigned {m : ℕ} (P : Pins m) : Prop := ∀ i, P i ≠ none

def decode {m : ℕ} (P : Pins m) : Vector m := fun i => (P i).getD 0

noncomputable def distance {m : ℕ} (L : Finset (Vector m)) : Option ℕ := by
  classical
  exact if h : L.Nonempty then some ((L.image weight).min' (h.image weight)) else none

noncomputable def firstPositive (m : ℕ) (Q : Polynomial ℤ) : Option ℕ :=
  (List.range (m+1)).find? (fun d => decide (0 < Q.coeff d))

/-- One tentative zero-pin query, with already assigned coordinates skipped. -/
noncomputable def choose {m : ℕ} (c : Pins m → ℤ) (P : Pins m)
    (i : Fin m) : Pins m × ℕ := by
  classical
  exact match P i with
  | some _ => (P, 0)
  | none => if 0 < c (pin P i 0) then (pin P i 0, 1) else (pin P i 1, 1)

noncomputable def recover {m : ℕ} (c : Pins m → ℤ) (P : Pins m) :
    List (Fin m) → Pins m × ℕ
  | [] => (P, 0)
  | i :: xs =>
      let s := choose c P i
      let t := recover c s.1 xs
      (t.1, s.2 + t.2)

/-- Generic helper property, discharged from exact counts before the final solve theorem. -/
def partitions {m : ℕ} (c : Pins m → ℤ) : Prop :=
  ∀ P i, P i = none → c P = c (pin P i 0) + c (pin P i 1)

/-- Returns distance, minimum witness and number of additional paired coefficient queries. -/
noncomputable def solve {m : ℕ} (Q : Pins m → Polynomial ℤ) :
    Option (ℕ × Vector m × ℕ) :=
  match firstPositive m (Q (free m)) with
  | none => none
  | some d =>
      let result := recover (fun P => (Q P).coeff d) (free m) (List.finRange m)
      some (d, decode result.1, result.2)

end M6.Pinned
