import M5ConditionalCountAccepted

namespace M7.PrefixSector
noncomputable def count (N w : ℕ) (E : Finset M5.BinaryPolynomial)
    (A B WA WB : Finset ℕ) : ℤ :=
  ∑ F ∈ E, M5.ConditionalCount.completionC N w F A B WA WB
noncomputable def completions (N w : ℕ) (E : Finset M5.BinaryPolynomial)
    (A B WA WB : Finset ℕ) : Finset (Finset ℕ × Finset ℕ) := by
  classical
  exact E.biUnion (fun F => M5.ConditionalCount.validCompletions N w F A B WA WB)
def ValidSector (N : ℕ) (E : Finset M5.BinaryPolynomial) : Prop :=
  ∀ F ∈ E, F.Monic ∧ F ∣ M5.cyclicModulus N
end M7.PrefixSector
