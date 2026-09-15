import FrozenTarget_dcc4b8fbbfaf5132
theorem M5.Translation.anchored_difference_gcd : QuantumHarnessFrozenTarget := by
  classical
  intro N inst S U hS hU
  change M5.Translation.differenceGcd S U = M5.Connectivity.supportGcd N (M5.Translation.natSupport S) (M5.Translation.natSupport U)
  have hsub (d : ℕ) (hdN : d ∣ N) (x y : ZMod N)
      (hx : d ∣ x.val) (hy : d ∣ y.val) : d ∣ (x - y).val := by
    have hneg : d ∣ (-y).val := by
      by_cases hy0 : y = 0
      · simp [hy0]
      · letI : NeZero y := ⟨hy0⟩
        rw [ZMod.val_neg_of_ne_zero y]
        exact Nat.dvd_sub' hdN hy
    rw [sub_eq_add_neg, ZMod.val_add]
    have hm : Nat.ModEq N (x.val + (-y).val) ((x.val + (-y).val) % N) := by
      simp [Nat.ModEq]
    exact (hm.dvd_iff hdN).mp (dvd_add hx hneg)
  have hchar (d : ℕ) (A : Finset (ZMod N)) :
      (∀ a ∈ M5.Translation.natSupport (M5.Translation.differences A), d ∣ a) ↔
        (∀ x ∈ A, ∀ y ∈ A, d ∣ (x - y).val) := by
    simp [M5.Translation.natSupport, M5.Translation.differences]
  have hanchor (d : ℕ) (hdN : d ∣ N) (A : Finset (ZMod N)) (hA : 0 ∈ A) :
      (∀ a ∈ M5.Translation.natSupport (M5.Translation.differences A), d ∣ a) ↔
        (∀ a ∈ M5.Translation.natSupport A, d ∣ a) := by
    rw [hchar]
    simp only [M5.Translation.natSupport, Finset.forall_mem_image]
    constructor
    · intro h x hx
      simpa using h x hx 0 hA
    · intro h x hx y hy
      exact hsub d hdN x y (h x hx) (h y hy)
  have hequiv (d : ℕ) :
      d ∣ M5.Translation.differenceGcd S U ↔
        d ∣ M5.Connectivity.supportGcd N (M5.Translation.natSupport S) (M5.Translation.natSupport U) := by
    unfold M5.Translation.differenceGcd
    rw [M5.Connectivity.support_gcd_dvd, M5.Connectivity.support_gcd_dvd]
    constructor
    · rintro ⟨hdN, hdS, hdU⟩
      exact ⟨hdN, (hanchor d hdN S hS).mp hdS, (hanchor d hdN U hU).mp hdU⟩
    · rintro ⟨hdN, hdS, hdU⟩
      exact ⟨hdN, (hanchor d hdN S hS).mpr hdS, (hanchor d hdN U hU).mpr hdU⟩
  apply Nat.dvd_antisymm
  · exact (hequiv _).mp (dvd_refl _)
  · exact (hequiv _).mpr (dvd_refl _)
