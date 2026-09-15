import M5ConditionalResidueCount
import M5ResidueRecovery
import M5PrefixPartition
import Mathlib.Data.List.OfFn

open scoped BigOperators
namespace M5.ArithmeticResidueRecovery

/-- Generic encoding used solely in the correctness proof. -/
def completionWord {α : Type} (k : ℕ) (u : List α)
    (a : Fin (k - (u.take k).length) → α)
    (b : Fin (k - (u.drop k).length) → α) : List α :=
  (u.take k ++ List.ofFn a) ++ (u.drop k ++ List.ofFn b)

noncomputable def fullWords {α : Type} [Fintype α] (m : ℕ)
    (Valid : List α → Prop) : Finset (List α) := by
  classical
  exact (Finset.univ.image (fun f : Fin m → α => List.ofFn f)).filter Valid

/-- Semantic completion count, used only for the bijection lemma. -/
noncomputable def completionCount {α : Type} [Fintype α] (k : ℕ)
    (u : List α) (Valid : List α → Prop) : ℤ := by
  classical
  exact ((Finset.univ.filter (fun ab :
    (Fin (k - (u.take k).length) → α) × (Fin (k - (u.drop k).length) → α) =>
      Valid (completionWord k u ab.1 ab.2))).card : ℤ)

noncomputable def wordValid {T : ℕ} (w : ℕ) (F : M5.BinaryPolynomial)
    (u : List (Fin T)) : Prop :=
  M5.ConditionalResidueCount.selectedGcd T (u.take (w-1)) (u.drop (w-1)) = 1 ∧
  M5.completeSignature
    (M5.ConditionalResidueCount.selectedPolynomial (u.take (w-1)))
    (M5.ConditionalResidueCount.selectedPolynomial (u.drop (w-1))) T = F

/-- The concrete arithmetic oracle; no semantic enumeration occurs here. -/
noncomputable def oracle (w : ℕ) (F : M5.BinaryPolynomial)
    (u : List (Fin (M5.signaturePeriod F))) : ℤ :=
  M5.ConditionalResidueCount.conditionalA w F (u.take (w-1)) (u.drop (w-1))

noncomputable def recover (w : ℕ) (F : M5.BinaryPolynomial) :
    Option (List (Fin (M5.signaturePeriod F))) × ℕ :=
  M5.ResidueRecovery.recover (oracle w F) [] (2*(w-1))

end M5.ArithmeticResidueRecovery
