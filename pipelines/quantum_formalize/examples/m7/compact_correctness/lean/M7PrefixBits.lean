import M7PrefixCompletedAccepted

namespace M7.PrefixBits
/-- Positions 1,...,N-1; the first block precedes the second block. -/
def selected (N offset : ℕ) (p : List Bool) : Finset ℕ :=
  {0} ∪ ((Finset.range (N-1)).filter (fun j => offset+j < p.length ∧ p.getD (offset+j) false = true)).image (fun j => j+1)
def undecided (N offset : ℕ) (p : List Bool) : Finset ℕ :=
  ((Finset.range (N-1)).filter (fun j => p.length ≤ offset+j)).image (fun j => j+1)
def A (N : ℕ) (p : List Bool) := selected N 0 p
def B (N : ℕ) (p : List Bool) := selected N (N-1) p
def WA (N : ℕ) (p : List Bool) := undecided N 0 p
def WB (N : ℕ) (p : List Bool) := undecided N (N-1) p
def depth (N : ℕ) := 2*(N-1)
noncomputable def count (N w : ℕ) (E : Finset M5.BinaryPolynomial) (p : List Bool) : ℤ :=
  M7.PrefixSector.count N w E (A N p) (B N p) (WA N p) (WB N p)
noncomputable def completed (N w : ℕ) (E : Finset M5.BinaryPolynomial) (p : List Bool) :=
  M7.PrefixCompleted.completed N w E (A N p) (B N p) (WA N p) (WB N p)
end M7.PrefixBits
