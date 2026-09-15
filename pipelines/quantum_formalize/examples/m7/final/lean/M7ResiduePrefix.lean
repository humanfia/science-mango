import M7PrefixCompletedAccepted
import M7SupportsAccepted
import M6Cyclic

namespace M7.ResiduePrefix
noncomputable def decode (N : ℕ) (A : Finset ℕ) : Finset (ZMod N) := A.image (fun i : ℕ => (i : ZMod N))
noncomputable def encode {N : ℕ} (A : Finset (ZMod N)) : Finset ℕ := M7.Supports.natSupport A
noncomputable def decodePair (N : ℕ) (x : Finset ℕ × Finset ℕ) := (decode N x.1, decode N x.2)
noncomputable def encodePair {N : ℕ} (x : Finset (ZMod N) × Finset (ZMod N)) := (encode x.1, encode x.2)
noncomputable def completed (N w : ℕ) (E : Finset M5.BinaryPolynomial)
    (A B WA WB : Finset ℕ) : Finset (Finset (ZMod N) × Finset (ZMod N)) := by
  classical
  exact (M7.PrefixCompleted.completed N w E A B WA WB).image (decodePair N)
end M7.ResiduePrefix
