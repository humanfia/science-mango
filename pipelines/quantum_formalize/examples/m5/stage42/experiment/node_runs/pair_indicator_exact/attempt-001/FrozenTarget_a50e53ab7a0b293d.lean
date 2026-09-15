import M5ConditionalResidueCount

theorem M5.ConditionalResidueCount.prefix_gcd_divisibility : ∀ (T d : ℕ) (p q : List (Fin T)), (d ∣ M5.ConditionalResidueCount.selectedGcd T p q ↔ d ∣ T ∧ (∀ r ∈ p, d ∣ r.val) ∧ (∀ r ∈ q, d ∣ r.val)) := by
  change ∀ (T d : ℕ) (p q : List (Fin T)), _
  intro T d p q
  have hl {α : Type} (f : α → ℕ) (l : List α) (s : ℕ) :
      d ∣ l.foldl (fun g r => Nat.gcd g (f r)) s ↔
        d ∣ s ∧ ∀ r ∈ l, d ∣ f r := by
    induction l generalizing s with
    | nil => simp
    | cons a l ih =>
        simp [List.foldl_cons, ih, Nat.dvd_gcd_iff, and_assoc]
  have hr {α : Type} (f : α → ℕ) (l : List α) (s : ℕ) :
      d ∣ l.foldr (fun r g => Nat.gcd (f r) g) s ↔
        d ∣ s ∧ ∀ r ∈ l, d ∣ f r := by
    induction l with
    | nil => simp
    | cons a l ih =>
        simp [List.foldr_cons, ih, Nat.dvd_gcd_iff, and_assoc,
          and_left_comm, and_comm]
  simp [M5.ConditionalResidueCount.selectedGcd,
    M5.ConditionalResidueCount.prefixGcd, hl, hr,
    Nat.dvd_gcd_iff, and_assoc]
def QuantumHarnessFrozenTarget : Prop :=
  ∀ (T w : ℕ) (F : M5.BinaryPolynomial) (p q : List (Fin T)), ∀ (a : Fin (M5.ConditionalResidueCount.remaining w p) → Fin T) (b : Fin (M5.ConditionalResidueCount.remaining w q) → Fin T), 0 < T → F.Monic → F ∣ M5.cyclicModulus T → M5.ConditionalResidueCount.pairIndicator w F p q a b = M5.ConditionalResidueCount.feasibleIndicator w F p q a b
