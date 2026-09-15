import M5FiniteExclusion
#check (∀ (S : Finset M5.BinaryPolynomial) (bad : M5.BinaryPolynomial → Bool), S.powerset.filter (fun H => ∀ p ∈ H, bad p = true) = (S.filter (fun p => bad p = true)).powerset)
#check (∀ S : Finset M5.BinaryPolynomial, (∑ H ∈ S.powerset, (-1 : ℤ)^H.card) = if S = ∅ then 1 else 0)
#check (∀ (S : Finset M5.BinaryPolynomial) (bad : M5.BinaryPolynomial → Bool), M5.FiniteExclusion.exclusionSum S bad = if ∀ p ∈ S, bad p = false then 1 else 0)
