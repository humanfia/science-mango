import M7PrefixSectorAccepted

namespace M7.PrefixCompleted
def Base (N : ℕ) (A B WA WB : Finset ℕ) : Prop :=
  0 ∈ A ∧ 0 ∈ B ∧ A ⊆ Finset.range N ∧ B ⊆ Finset.range N ∧
  WA ⊆ Finset.range N ∧ WB ⊆ Finset.range N ∧ Disjoint A WA ∧ Disjoint B WB
def Within (A B WA WB : Finset ℕ) (x : Finset ℕ × Finset ℕ) : Prop :=
  A ⊆ x.1 ∧ x.1 ⊆ A ∪ WA ∧ B ⊆ x.2 ∧ x.2 ⊆ B ∪ WB
def Valid (N w : ℕ) (E : Finset M5.BinaryPolynomial) (x : Finset ℕ × Finset ℕ) : Prop :=
  x.1.card = w ∧ x.2.card = w ∧ M5.Connectivity.supportGcd N x.1 x.2 = 1 ∧
  M5.completeSignature (M5.SupportPolynomial.ofSupport x.1) (M5.SupportPolynomial.ofSupport x.2) N ∈ E
noncomputable def completed (N w : ℕ) (E : Finset M5.BinaryPolynomial)
    (A B WA WB : Finset ℕ) : Finset (Finset ℕ × Finset ℕ) := by
  classical
  exact (M7.PrefixSector.completions N w E A B WA WB).image (fun x => (A ∪ x.1, B ∪ x.2))
end M7.PrefixCompleted
