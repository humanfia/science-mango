import FrozenTarget_88bf1ceaeb9bc613
theorem M5.Translation.anchored_difference_gcd : QuantumHarnessFrozenTarget := by
  classical
  intro N inst S U hS hU
  have hsub (d : ℕ) (hdN : d ∣ N) (x y : ZMod N)
      (hx : d ∣ x.val) (hy : d ∣ y.val) : d ∣ (x - y).val := by
    have hneg : d ∣ (-y).val := by
      by_cases hy0 : y = 0
      · simp [hy0]
      · rw [ZMod.val_neg_of_ne_zero hy0]
        exact Nat.dvd_sub' hdN hy
    rw [sub_eq_add_neg, ZMod.val_add]
    exact (Nat.dvd_mod_iff hdN).2 (dvd_add hx hneg)
  have hsupport (d : ℕ) (hdN : d ∣ N) (V : Finset (ZMod N))
      (hV : 0 ∈ V) :
      (∀ a ∈ M5.Translation.natSupport (M5.Translation.differences V), d ∣ a) ↔
        (∀ a ∈ M5.Translation.natSupport V, d ∣ a) := by
    constructor
    · intro h a ha
      change a ∈ V.image ZMod.val at ha
      rcases Finset.mem_image.mp ha with ⟨x, hx, rfl⟩
      apply h
      change x.val ∈ (M5.Translation.differences V).image ZMod.val
      apply Finset.mem_image.mpr
      refine ⟨x, ?_, rfl⟩
      simp only [M5.Translation.differences, Finset.mem_biUnion, Finset.mem_image]
      exact ⟨x, hx, 0, hV, sub_zero x⟩
    · intro h a ha
      change a ∈ (M5.Translation.differences V).image ZMod.val at ha
      rcases Finset.mem_image.mp ha with ⟨z, hz, rfl⟩
      simp only [M5.Translation.differences, Finset.mem_biUnion, Finset.mem_image] at hz
      rcases hz with ⟨x, hx, y, hy, rfl⟩
      apply hsub d hdN x y
      · exact h x.val (Finset.mem_image.mpr ⟨x, hx, rfl⟩)
      · exact h y.val (Finset.mem_image.mpr ⟨y, hy, rfl⟩)
  change M5.Connectivity.supportGcd N
      (M5.Translation.natSupport (M5.Translation.differences S))
      (M5.Translation.natSupport (M5.Translation.differences U)) =
    M5.Connectivity.supportGcd N
      (M5.Translation.natSupport S) (M5.Translation.natSupport U)
  have hequiv (d : ℕ) :
      d ∣ M5.Connectivity.supportGcd N
        (M5.Translation.natSupport (M5.Translation.differences S))
        (M5.Translation.natSupport (M5.Translation.differences U)) ↔
      d ∣ M5.Connectivity.supportGcd N
        (M5.Translation.natSupport S) (M5.Translation.natSupport U) := by
    rw [M5.Connectivity.support_gcd_dvd, M5.Connectivity.support_gcd_dvd]
    constructor
    · rintro ⟨hdN, hs, hu⟩
      exact ⟨hdN, (hsupport d hdN S hS).1 hs, (hsupport d hdN U hU).1 hu⟩
    · rintro ⟨hdN, hs, hu⟩
      exact ⟨hdN, (hsupport d hdN S hS).2 hs, (hsupport d hdN U hU).2 hu⟩
  exact Nat.dvd_antisymm ((hequiv _).1 dvd_rfl) ((hequiv _).2 dvd_rfl)
