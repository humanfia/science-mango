import M8MixedFamily

theorem M8.MixedFamily.algebra : M8.MixedFamily.b = M8.MixedFamily.a^2 ∧ M8.MixedFamily.a*M8.MixedFamily.b = 1+Polynomial.X+Polynomial.X^2+Polynomial.X^3 := by
  change (1 + Polynomial.X ^ 2 : Polynomial (ZMod 2)) = (1 + Polynomial.X) ^ 2 ∧
    (1 + Polynomial.X : Polynomial (ZMod 2)) * (1 + Polynomial.X ^ 2) =
      1 + Polynomial.X + Polynomial.X ^ 2 + Polynomial.X ^ 3
  have h : (1 + 1 : Polynomial (ZMod 2)) = 0 := by
    simpa only [map_add, map_one, map_zero] using
      congrArg (fun c : ZMod 2 => Polynomial.C c)
        (show (1 + 1 : ZMod 2) = 0 by decide)
  constructor
  · calc
      (1 + Polynomial.X ^ 2 : Polynomial (ZMod 2)) =
          1 + Polynomial.X ^ 2 + (1 + 1) * Polynomial.X := by rw [h]; simp
      _ = (1 + Polynomial.X) ^ 2 := by ring
  · ring

theorem M8.MixedFamily.literal_polynomials : ∀ (N : ℕ) [NeZero N], 7 ≤ N → M7.Supports.polynomial (M8.MixedFamily.left N) = M8.MixedFamily.a ∧ M7.Supports.polynomial (M8.MixedFamily.right N) = M8.MixedFamily.b := by
  intro N inst hN
  classical
  have hv (k : ℕ) (hk : k < N) : (k : ZMod N).val = k := by
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt hk]
  have h1 : (1 : ZMod N).val = 1 := by
    simpa only [Nat.cast_one] using hv 1 (by omega)
  have h2 : (2 : ZMod N).val = 2 := by
    simpa using hv 2 (by omega)
  have h01 : (0 : ZMod N) ≠ 1 := by
    intro h
    have hh := congrArg ZMod.val h
    simp [h1] at hh
  have h02 : (0 : ZMod N) ≠ 2 := by
    intro h
    have hh := congrArg ZMod.val h
    simp [h2] at hh
  constructor <;>
    simp [M8.MixedFamily.left, M8.MixedFamily.right,
      M8.MixedFamily.a, M8.MixedFamily.b, M7.Supports.polynomial,
      h01, h02, h1, h2] <;>
    ext k <;>
    simp [Polynomial.coeff_X, Polynomial.coeff_X_pow, eq_comm]

theorem M8.MixedFamily.nontrivial : M8.MixedFamily.a ≠ 1 ∧ M8.MixedFamily.a ≠ 0 ∧ (M8.MixedFamily.a*M8.MixedFamily.b).natDegree = 3 := by
  change M8.MixedFamily.a ≠ 1 ∧ M8.MixedFamily.a ≠ 0 ∧ (M8.MixedFamily.a * M8.MixedFamily.b).natDegree = 3
  have ha : M8.MixedFamily.a.natDegree = 1 := by
    unfold M8.MixedFamily.a
    rw [Polynomial.natDegree_add_eq_right_of_natDegree_lt (by simp)]
    simp
  have hb : M8.MixedFamily.b.natDegree = 2 := by
    unfold M8.MixedFamily.b
    rw [Polynomial.natDegree_add_eq_right_of_natDegree_lt (by simp)]
    simp
  have ha1 : M8.MixedFamily.a ≠ 1 := by
    intro h
    rw [h] at ha
    simp at ha
  have ha0 : M8.MixedFamily.a ≠ 0 := by
    intro h
    rw [h] at ha
    simp at ha
  have hb0 : M8.MixedFamily.b ≠ 0 := by
    intro h
    rw [h] at hb
    simp at hb
  refine ⟨ha1, ha0, ?_⟩
  rw [Polynomial.natDegree_mul ha0 hb0, ha, hb]

theorem M8.MixedFamily.span_cutoff : ∀ (N : ℕ) [NeZero N], 7 ≤ N → M8.Anchor.span (M8.MixedFamily.recipe N) ≤ M8.Cutoff.limit N := by
  change ∀ (N : ℕ) [NeZero N], 7 ≤ N → M8.Anchor.span (M8.MixedFamily.recipe N) ≤ M8.Cutoff.limit N
  intro N inst hN
  have hval (k : ℕ) (hk : k ≤ 2) : (k : ZMod N).val ≤ 2 := by
    rw [ZMod.val_natCast]
    exact (Nat.mod_le k N).trans hk
  have hspan : M8.Anchor.span (M8.MixedFamily.recipe N) ≤ 2 := by
    apply (M8.Anchor.span_le N (M8.MixedFamily.recipe N) 2).mpr
    change (∀ i ∈ ({0, 1} : Finset (ZMod N)), i.val ≤ 2) ∧
      (∀ i ∈ ({0, 2} : Finset (ZMod N)), i.val ≤ 2)
    constructor
    · intro i hi
      simp only [Finset.mem_insert, Finset.mem_singleton] at hi
      rcases hi with rfl | rfl
      · simpa only [Nat.cast_zero] using hval 0 (by omega)
      · simpa only [Nat.cast_one] using hval 1 (by omega)
    · intro i hi
      simp only [Finset.mem_insert, Finset.mem_singleton] at hi
      rcases hi with rfl | rfl
      · simpa only [Nat.cast_zero] using hval 0 (by omega)
      · simpa using hval 2 (by omega)
  apply hspan.trans
  rw [M8.Cutoff.bit_length_limit, Nat.log2_eq_log_two]
  apply le_min
  · omega
  · have hlog := Nat.log_mono_right (b := 2) (show 4 ≤ N + 1 by omega)
    norm_num at hlog
    exact hlog

theorem M8.MixedFamily.support_data : ∀ (N : ℕ) [NeZero N], 7 ≤ N → (M8.MixedFamily.left N).card = 2 ∧ (M8.MixedFamily.right N).card = 2 ∧ (0 : ZMod N) ∈ M8.MixedFamily.left N ∧ (0 : ZMod N) ∈ M8.MixedFamily.right N ∧ (1 : ZMod N) ∈ M8.MixedFamily.left N := by
  intro N inst hN
  have hsmall : ∀ k : ℕ, 0 < k → k < N → (k : ZMod N) ≠ 0 := by
    intro k hk hkN he
    have hv := congrArg ZMod.val he
    rw [ZMod.val_natCast, ZMod.val_zero, Nat.mod_eq_of_lt hkN] at hv
    omega
  have h01 : (0 : ZMod N) ≠ 1 := by
    simpa using Ne.symm (hsmall 1 (by omega) (by omega))
  have h02 : (0 : ZMod N) ≠ 2 := by
    simpa using Ne.symm (hsmall 2 (by omega) (by omega))
  simp [M8.MixedFamily.left, M8.MixedFamily.right, h01, h02]

theorem M8.MixedFamily.full_direction : ∀ (N : ℕ) [NeZero N], 7 ≤ N → M8.CoverageFoundation.FullDirection (M8.MixedFamily.left N) := by
  intro N inst hN
  classical
  apply M8.CoverageFoundation.consecutive_full N (M8.MixedFamily.left N) 0
  · simp [M8.MixedFamily.left]
  · simp [M8.MixedFamily.left]

theorem M8.MixedFamily.signature : ∀ (N : ℕ) [NeZero N], 7 ≤ N → M7.RecipeSignature.signature (M8.MixedFamily.recipe N) = M8.MixedFamily.a := by
  intro N inst hN
  have hp := M8.MixedFamily.literal_polynomials N hN
  have hab : M8.MixedFamily.a ∣ M8.MixedFamily.b := by
    rw [M8.MixedFamily.algebra.1]
    exact dvd_pow_self _ (by decide : 2 ≠ 0)
  have hn : -(1 : Polynomial (ZMod 2)) = 1 := by
    have h := congrArg (fun c : ZMod 2 => Polynomial.C c)
      (show -(1 : ZMod 2) = 1 by decide)
    simpa only [Polynomial.C_neg, Polynomial.C_1] using h
  have ham : M8.MixedFamily.a ∣ M6.Cyclic.modulus N := by
    simpa [M8.MixedFamily.a, M6.Cyclic.modulus, sub_eq_add_neg, hn, add_comm] using
      (sub_dvd_pow_sub_pow (Polynomial.X : Polynomial (ZMod 2)) 1 N)
  change EuclideanDomain.gcd
    (EuclideanDomain.gcd (M7.Supports.polynomial (M8.MixedFamily.left N))
      (M7.Supports.polynomial (M8.MixedFamily.right N))) (M6.Cyclic.modulus N) = M8.MixedFamily.a
  rw [hp.1,hp.2,EuclideanDomain.gcd_eq_left.mpr hab]
  exact EuclideanDomain.gcd_eq_left.mpr ham

theorem M8.MixedFamily.valid : ∀ (N : ℕ) [NeZero N], 7 ≤ N → M8.PhysicalBridge.Valid 2 (M8.MixedFamily.recipe N) := by
  intro N inst hN
  classical
  obtain ⟨hL, hR, h0L, h0R, h1L⟩ := M8.MixedFamily.support_data N hN
  have hf := M8.MixedFamily.full_direction N hN
  change AddSubgroup.closure (M7.Connectivity.differences (M8.MixedFamily.left N)) = ⊤ at hf
  have hc : M7.Connectivity.connected (M8.MixedFamily.recipe N) := by
    change AddSubgroup.closure (M7.Connectivity.differences (M8.MixedFamily.left N) ∪ M7.Connectivity.differences (M8.MixedFamily.right N)) = ⊤
    apply top_unique
    calc
      ⊤ = AddSubgroup.closure (M7.Connectivity.differences (M8.MixedFamily.left N)) := hf.symm
      _ ≤ AddSubgroup.closure (M7.Connectivity.differences (M8.MixedFamily.left N) ∪ M7.Connectivity.differences (M8.MixedFamily.right N)) := AddSubgroup.closure_mono Set.subset_union_left
  simp_all [M8.PhysicalBridge.Valid, M8.MixedFamily.recipe]
#print axioms M8.MixedFamily.algebra
#print axioms M8.MixedFamily.literal_polynomials
#print axioms M8.MixedFamily.nontrivial
#print axioms M8.MixedFamily.signature
#print axioms M8.MixedFamily.span_cutoff
#print axioms M8.MixedFamily.support_data
#print axioms M8.MixedFamily.full_direction
#print axioms M8.MixedFamily.valid
