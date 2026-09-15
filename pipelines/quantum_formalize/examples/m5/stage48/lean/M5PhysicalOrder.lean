import M5Checkpoint90
namespace M5.PhysicalOrder
noncomputable def supportPeriod (A B : Finset ℕ) : ℕ :=
  M5.signaturePeriod (EuclideanDomain.gcd (M5.SupportPolynomial.ofSupport A) (M5.SupportPolynomial.ofSupport B))
def realizes (N w : ℕ) (F : M5.BinaryPolynomial) (A B : Finset ℕ) : Prop :=
  0 < N ∧ A.card = w ∧ B.card = w ∧ 0 ∈ A ∧ 0 ∈ B ∧
  (∀ a ∈ A, a < N) ∧ (∀ b ∈ B, b < N) ∧
  M5.Connectivity.supportGcd N A B = 1 ∧
  M5.completeSignature (M5.SupportPolynomial.ofSupport A) (M5.SupportPolynomial.ofSupport B) N = F
end M5.PhysicalOrder
