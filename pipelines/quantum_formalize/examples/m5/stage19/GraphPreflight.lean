import M5PhysicalBridge
#check (∀ (w T d : ℕ) (r : Fin w → Fin T), d ∣ T → ((∀ a ∈ M5.Packing.packedSupport r, d ∣ a) ↔ ∀ i, d ∣ (r i).val))
#check (∀ (w T : ℕ) (r s : Fin w → Fin T), M5.Connectivity.supportGcd T (M5.Packing.packedSupport r) (M5.Packing.packedSupport s) = Nat.gcd T (Nat.gcd (Finset.univ.gcd (fun i : Fin w => (r i).val)) (Finset.univ.gcd (fun i : Fin w => (s i).val))))
#check (∀ A : Finset ℕ, 2 ≤ A.card → 0 ∈ A → ∃ a ∈ A, 0 < a)
#check (∀ (A B : Finset ℕ) (e K : ℕ), 2 ≤ B.card → 0 ∈ B → (∀ b ∈ B, b < K) → 0 < M5.PhysicalBridge.remainingGcd A B e ∧ M5.PhysicalBridge.remainingGcd A B e < K)
#check (∀ (T : ℕ) (A B : Finset ℕ) (e : ℕ), e ∈ A → M5.Connectivity.supportGcd T A B = 1 → Nat.gcd (Nat.gcd T (M5.PhysicalBridge.remainingGcd A B e)) e = 1)
#check (∀ w T e δ k : ℕ, 0 < T → e < w * T → δ < w * T → k < w + δ → e + k * T < M5.packingCutoff w T)
