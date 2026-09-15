import M5OrderCount
#check (∀ (N d k : ℕ), (M5.OrderCount.divisorPositions N d).powersetCard k = ((M5.OrderCount.positivePositions N).powersetCard k).filter (fun U => ∀ s ∈ U, d ∣ s))
#check (∀ (P : M5.BinaryPolynomial) (W : Finset ℕ) (k : ℕ), P.Monic → 0 ∉ W → M5.OrderCount.nOne P W k ^ 2 = M5.OrderCount.twoBlockIndicatorSum P W k)
#check (∀ (N w : ℕ) (F : M5.BinaryPolynomial), 0 < N → 0 < w → F.Monic → F ∣ M5.cyclicModulus N → M5.OrderCount.rawC N w F = ∑ U ∈ (M5.OrderCount.positivePositions N).powersetCard (w-1), ∑ V ∈ (M5.OrderCount.positivePositions N).powersetCard (w-1), M5.OrderCount.pairIndicator N F U V)
#check (∀ (N w : ℕ) (F : M5.BinaryPolynomial), 0 < N → 0 < w → F.Monic → F ∣ M5.cyclicModulus N → M5.OrderCount.C N w F = (M5.OrderCount.validPairs N w F).card)
#check (∀ (N w : ℕ) (F : M5.BinaryPolynomial), 0 < N → 0 < w → F.Monic → F ∣ M5.cyclicModulus N → 0 ≤ M5.OrderCount.C N w F)
#check (∀ (N w : ℕ) (F : M5.BinaryPolynomial), 0 < N → 0 < w → F.Monic → F ∣ M5.cyclicModulus N → (0 < M5.OrderCount.C N w F ↔ ∃ A B : Finset ℕ, A ⊆ Finset.range N ∧ B ⊆ Finset.range N ∧ 0 ∈ A ∧ 0 ∈ B ∧ A.card = w ∧ B.card = w ∧ M5.Connectivity.supportGcd N A B = 1 ∧ M5.completeSignature (M5.SupportPolynomial.ofSupport A) (M5.SupportPolynomial.ofSupport B) N = F))
