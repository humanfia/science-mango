import M5ArithmeticSubsetAccepted
open scoped BigOperators
namespace M5.CompletionBlock
noncomputable def count (P : M5.BinaryPolynomial) (A W : Finset ℕ) (k : ℕ) : ℕ := by
  classical
  exact ((W.powersetCard k).filter (fun U => P ∣ M5.SupportPolynomial.ofSupport (A ∪ U))).card
end M5.CompletionBlock
