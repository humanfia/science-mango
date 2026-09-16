import M6FinalDefinitions

namespace M6.Final
open scoped BigOperators
noncomputable def LX (N : ℕ) [NeZero N] (a b : BP) := CX N a b \ BX N a b

noncomputable def CountingCorrect (N : ℕ) [NeZero N] (a b : BP) : Prop :=
 (∀ P : M6.Pinned.Pins (2*N),
  M6.ActualTransfer.boundaryTrace N a b P = Polynomial.C ((2 : ℤ)^(M6.ActualCounts.f N a b)) * M6.Pinned.enumerator (BX N a b) P ∧
  M6.ActualTransfer.characterTrace N a b P = Polynomial.C ((2 : ℤ)^N) * M6.Pinned.enumerator (CX N a b) P ∧
  M6.Normalize.divide ((2 : ℤ)^(M6.ActualCounts.f N a b)) (M6.ActualTransfer.boundaryTrace N a b P) = M6.Pinned.enumerator (BX N a b) P ∧
  M6.Normalize.divide ((2 : ℤ)^N) (M6.ActualTransfer.characterTrace N a b P) = M6.Pinned.enumerator (CX N a b) P ∧
  M6.ActualTransfer.Q N a b P = M6.Pinned.enumerator (LX N a b) P ∧
  (∀ d : ℕ, (M6.ActualTransfer.Q N a b P).coeff d = M6.Pinned.count (LX N a b) P d ∧ 0 ≤ (M6.ActualTransfer.Q N a b P).coeff d) ∧
  (M6.ActualTransfer.Q N a b P).coeff 0 = 0) ∧
 Polynomial.eval 1 (M6.ActualTransfer.Q N a b (M6.Pinned.free (2*N))) = (2 : ℤ)^(N+(M6.ActualCounts.f N a b)) - (2 : ℤ)^(N-(M6.ActualCounts.f N a b))

noncomputable def ParametersCorrect (N : ℕ) [NeZero N] (a b : BP) : Prop :=
 (BX N a b).card = 2^(N-(M6.ActualCounts.f N a b)) ∧ (CX N a b).card = 2^(N+(M6.ActualCounts.f N a b)) ∧
 encodedQubits N a b = 2*(M6.ActualCounts.f N a b) ∧ (M6.ActualCounts.f N a b) ≤ N ∧ ((LX N a b).Nonempty ↔ 0 < (M6.ActualCounts.f N a b))

noncomputable def AnswerCorrect (N : ℕ) [NeZero N] (a b : BP) : Prop :=
 (M6.ActualTransfer.solve N a b = none ↔ (M6.ActualCounts.f N a b) = 0) ∧
 (quantumDistance N a b = none ↔ (M6.ActualCounts.f N a b) = 0) ∧
 (∀ (d : ℕ) (v : M6.Pinned.Vector (2*N)) (k : ℕ), M6.ActualTransfer.solve N a b = some (d,v,k) →
   quantumDistance N a b = some d ∧ v ∈ LX N a b ∧ M6.Pinned.weight v = d ∧
   (M6.Flatten.J N v) ∈ CZ N a b \ BZ N a b ∧ M6.Pinned.weight (M6.Flatten.J N v) = d ∧ k ≤ 2*N) ∧
 (0 < (M6.ActualCounts.f N a b) → ∃ (d : ℕ) (v : M6.Pinned.Vector (2*N)) (k : ℕ), M6.ActualTransfer.solve N a b = some (d,v,k))

noncomputable def ExecutionCorrect (N : ℕ) [NeZero N] (a b : BP) : Prop :=
 (∀ P : M6.Pinned.Pins (2*N),
  M6.Transfer.IndexedArrayGuarantee (M6.ActualTransfer.span a b) N (M6.ActualTransfer.boundaryWeight (M6.ActualTransfer.span a b) N a b P) ∧
  M6.Transfer.IndexedArrayGuarantee (M6.ActualTransfer.span a b) N (M6.ActualTransfer.characterWeight (M6.ActualTransfer.span a b) N a b P) ∧
  M6.ActualTransfer.shiftedOutput N a b P = M6.ActualTransfer.Q N a b P ∧
  M6.ActualTransfer.shiftedScan N a b P = M6.Pinned.firstPositive (2*N) (M6.ActualTransfer.Q N a b P)) ∧
 M6.ActualTransfer.actualDistanceWork N a b ≤ 50000*N^3*4^(M6.ActualTransfer.span a b) ∧
 (∀ (d : ℕ) (v : M6.Pinned.Vector (2*N)) (k : ℕ), M6.ActualTransfer.solve N a b = some (d,v,k) →
  M6.ActualTransfer.actualWitnessWork N a b k ≤ 200000*N^4*4^(M6.ActualTransfer.span a b))

noncomputable def StorageCorrect (N : ℕ) [NeZero N] (a b : BP) : Prop :=
 M6.ActualTransfer.actualSolveStorage N a b ≤ 16384*N^2*2^(M6.ActualTransfer.span a b)

noncomputable def FixedSpanCorrect : Prop :=
 (∀ R : ℕ, Filter.Tendsto (fun N : ℕ => (N : ℝ)^3 * (4 : ℝ)^R / (4 : ℝ)^N) Filter.atTop (nhds 0)) ∧
 (∀ R : ℕ, Filter.Tendsto (fun N : ℕ => (N : ℝ)^4 * (4 : ℝ)^R / (4 : ℝ)^N) Filter.atTop (nhds 0)) ∧
 (∀ k : ℕ, let N := 3*(k+1); Admissible N M6.FixedSpan.recipe M6.FixedSpan.recipe ∧ M6.ActualTransfer.span M6.FixedSpan.recipe M6.FixedSpan.recipe = 2 ∧ M6.ActualCounts.f N M6.FixedSpan.recipe M6.FixedSpan.recipe = 2)

noncomputable def RecipeCorrect : Prop :=
 (∀ (N : ℕ) [NeZero N] (a b : M6.RecipeIsometries.Block N) (r s : ZMod N), Function.Bijective (M6.RecipeIsometries.translate N r s) ∧ ∀ v : M6.Pinned.Vector (2*N), ((M6.RecipeIsometries.translate N r s) v ∈ M6.Spaces.boundaryWords N (M6.RecipeIsometries.shift N r a) (M6.RecipeIsometries.shift N s b) ↔ v ∈ M6.Spaces.boundaryWords N a b) ∧ ((M6.RecipeIsometries.translate N r s) v ∈ M6.Spaces.cycleWords N (M6.RecipeIsometries.shift N r a) (M6.RecipeIsometries.shift N s b) ↔ v ∈ M6.Spaces.cycleWords N a b) ∧ M6.Pinned.weight ((M6.RecipeIsometries.translate N r s) v) = M6.Pinned.weight v) ∧
 (∀ (N : ℕ) [NeZero N] (a b : M6.RecipeIsometries.Block N) (u : (ZMod N)ˣ), Function.Bijective (M6.RecipeIsometries.multiplier N u) ∧ ∀ v : M6.Pinned.Vector (2*N), ((M6.RecipeIsometries.multiplier N u) v ∈ M6.Spaces.boundaryWords N (M6.RecipeIsometries.multiply N u a) (M6.RecipeIsometries.multiply N u b) ↔ v ∈ M6.Spaces.boundaryWords N a b) ∧ ((M6.RecipeIsometries.multiplier N u) v ∈ M6.Spaces.cycleWords N (M6.RecipeIsometries.multiply N u a) (M6.RecipeIsometries.multiply N u b) ↔ v ∈ M6.Spaces.cycleWords N a b) ∧ M6.Pinned.weight ((M6.RecipeIsometries.multiplier N u) v) = M6.Pinned.weight v) ∧
 (∀ (N : ℕ) [NeZero N] (a b : M6.RecipeIsometries.Block N), Function.Bijective (M6.RecipeIsometries.blockExchange N) ∧ ∀ v : M6.Pinned.Vector (2*N), ((M6.RecipeIsometries.blockExchange N) v ∈ M6.Spaces.boundaryWords N (b) (a) ↔ v ∈ M6.Spaces.boundaryWords N a b) ∧ ((M6.RecipeIsometries.blockExchange N) v ∈ M6.Spaces.cycleWords N (b) (a) ↔ v ∈ M6.Spaces.cycleWords N a b) ∧ M6.Pinned.weight ((M6.RecipeIsometries.blockExchange N) v) = M6.Pinned.weight v)

noncomputable def ZeroSpanCorrect : Prop :=
 (∀ (a b : M6.Final.BP), a.coeff 0 = 1 → b.coeff 0 = 1 → M6.ActualTransfer.span a b = 0 → a = 1 ∧ b = 1) ∧
 (∀ N : ℕ, M6.Final.Admissible N 1 1 → N = 1) ∧
 (∀ (N : ℕ) [NeZero N] (i : ℕ) (m n : M6.Transfer.Memory 0), M6.Transfer.edgeMatrix (M6.ActualTransfer.boundaryWeight 0 N 1 1 (M6.Pinned.free (2*N)) i) m n = (1 : Polynomial ℤ) + Polynomial.X^2) ∧
 (∀ (N : ℕ) [NeZero N] (i : ℕ) (m n : M6.Transfer.Memory 0), M6.Transfer.edgeMatrix (M6.ActualTransfer.characterWeight 0 N 1 1 (M6.Pinned.free (2*N)) i) m n = Polynomial.C 2 * ((1 : Polynomial ℤ) + Polynomial.X^2)) ∧
 (∀ (N : ℕ) [NeZero N], M6.ActualTransfer.boundaryTrace N 1 1 (M6.Pinned.free (2*N)) = ((1 : Polynomial ℤ) + Polynomial.X^2)^N) ∧
 (∀ (N : ℕ) [NeZero N], M6.ActualTransfer.characterTrace N 1 1 (M6.Pinned.free (2*N)) = Polynomial.C ((2 : ℤ)^N) * ((1 : Polynomial ℤ) + Polynomial.X^2)^N) ∧
 (∀ (N : ℕ) [NeZero N], M6.ActualTransfer.Q N 1 1 (M6.Pinned.free (2*N)) = 0)

noncomputable def PointwiseCorrect (N : ℕ) [NeZero N] (a b : BP) : Prop :=
 CountingCorrect N a b ∧ ParametersCorrect N a b ∧ AnswerCorrect N a b ∧ ExecutionCorrect N a b ∧ StorageCorrect N a b

noncomputable def OriginalM6 : Prop :=
 (∀ (N : ℕ) [NeZero N] (a b : BP), Admissible N a b → PointwiseCorrect N a b) ∧ FixedSpanCorrect ∧ RecipeCorrect ∧ ZeroSpanCorrect
end M6.Final
