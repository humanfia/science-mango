import M6FixedSpan
def check_0 : Prop := ∀ R : ℕ, Filter.Tendsto (fun N : ℕ => (N : ℝ)^3 * (4 : ℝ)^R / (4 : ℝ)^N) Filter.atTop (nhds 0)
def check_1 : Prop := ∀ R : ℕ, Filter.Tendsto (fun N : ℕ => (N : ℝ)^4 * (4 : ℝ)^R / (4 : ℝ)^N) Filter.atTop (nhds 0)
def check_2 : Prop := M6.FixedSpan.recipe.support = {0,1,2}
def check_3 : Prop := M6.FixedSpan.recipe.Monic ∧ M6.FixedSpan.recipe.natDegree = 2
def check_4 : Prop := ∀ N : ℕ, 3 ∣ N → M6.FixedSpan.recipe ∣ M6.Cyclic.modulus N
def check_5 : Prop := ∀ N : ℕ, 3 ∣ N → M6.Cyclic.signature M6.FixedSpan.recipe M6.FixedSpan.recipe (M6.Cyclic.modulus N) = M6.FixedSpan.recipe
def check_6 : Prop := ∀ k : ℕ, let N := 3*(k+1); 2 < N ∧ M6.FixedSpan.recipe.support.card = 3 ∧ 0 ∈ M6.FixedSpan.recipe.support ∧ Nat.gcd N (M6.FixedSpan.recipe.support.gcd id) = 1 ∧ (M6.Cyclic.signature M6.FixedSpan.recipe M6.FixedSpan.recipe (M6.Cyclic.modulus N)).natDegree = 2
