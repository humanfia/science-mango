import M5ArithmeticSubsetAccepted

namespace M5.AnchoredCount
noncomputable def count (P : M5.BinaryPolynomial) (W : Finset ℕ) (k : ℕ) : ℕ := by
  classical
  exact ((W.powersetCard k).filter (fun U => P ∣ M5.SupportPolynomial.ofSupport (insert 0 U))).card
end M5.AnchoredCount
