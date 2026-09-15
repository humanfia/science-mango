import M7CompactStorage

theorem M7.CompactStorage.emission_valid : ∀ (N : ℕ) [NeZero N] (w : ℕ) (E : Finset M5.BinaryPolynomial) (bases : Finset (M7.Action.Recipe N)), M7.CompactStorage.Valid (M7.CompactGeneration.emission w E bases) := by
  intro N inst w E bases
  unfold M7.CompactStorage.Valid
  repeat' apply And.intro
  all_goals first
    | exact (M7.CompactGeneration.emission_action N w E bases).1
    | exact (M7.CompactGeneration.emission_stabilizer N w E bases).2
    | rfl

theorem M7.CompactStorage.field_bounds : ∀ (N : ℕ) [NeZero N] (c : M7.Action.Recipe N), (M7.RecipeSignature.signature c).natDegree ≤ N ∧ M7.ActualOrbit.stabilizerCount c < 2^(1+3*N) := by
  change ∀ (N : ℕ) [NeZero N] (c : M7.Action.Recipe N), _
  intro N inst c
  classical
  constructor
  · have hd := (M7.RecipeSignature.signature_properties N c).2
    have hn := (M7.SignatureTau.modulus_monic N).ne_zero
    refine (Polynomial.natDegree_le_of_dvd hd hn).trans ?_
    change (Polynomial.X ^ N + 1 : M6.Cyclic.BinaryPolynomial).natDegree ≤ N
    simpa using (Polynomial.natDegree_add_le
      (Polynomial.X ^ N : M6.Cyclic.BinaryPolynomial) 1)
  · have hcard : M7.ActualOrbit.stabilizerCount c ≤ Fintype.card (M7.Action.Record N) := by
      change (M7.ActualOrbit.fullStabilizer c).card ≤ Fintype.card (M7.Action.Record N)
      exact Finset.card_le_univ _
    have hb : Fintype.card (M7.Action.Record N) ≤ 2 * N ^ 3 := by
      calc
        Fintype.card (M7.Action.Record N) = Nat.totient N * 2 * N * N := M7.Action.record_card N
        _ ≤ N * 2 * N * N := by
          gcongr <;> exact Nat.totient_le N
        _ = 2 * N ^ 3 := by ring
    have hp : ∀ n : ℕ, n < 2 ^ n := by
      intro n
      induction n with
      | zero => norm_num
      | succ n ih =>
          rw [pow_succ]
          have hpos : 0 < (2 : ℕ) ^ n := by positivity
          omega
    have hc : N ^ 3 < (2 ^ N) ^ 3 := by
      have h := hp N
      gcongr
    calc
      M7.ActualOrbit.stabilizerCount c ≤ 2 * N ^ 3 := hcard.trans hb
      _ < 2 * (2 ^ N) ^ 3 := by omega
      _ = 2 ^ (1 + 3 * N) := by
        simp [← pow_mul, pow_add, Nat.mul_comm]

theorem M7.CompactStorage.polynomial_injective : ∀ (N : ℕ) (F G : M5.BinaryPolynomial), F.natDegree ≤ N → G.natDegree ≤ N → M7.CompactStorage.polynomialBits N F = M7.CompactStorage.polynomialBits N G → F = G := by
  change ∀ (N : ℕ) (F G : M5.BinaryPolynomial), F.natDegree ≤ N → G.natDegree ≤ N → M7.CompactStorage.polynomialBits N F = M7.CompactStorage.polynomialBits N G → F = G
  intro N F G hF hG hbits
  have hinj : ∀ a b : ZMod 2, decide (a = 1) = decide (b = 1) → a = b := by
    decide
  apply Polynomial.ext
  intro i
  by_cases hi : i ≤ N
  · have h := congrFun hbits (⟨i, by omega⟩ : Fin (N + 1))
    change decide (F.coeff i = 1) = decide (G.coeff i = 1) at h
    exact hinj (F.coeff i) (G.coeff i) h
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (show F.natDegree < i by omega),
      Polynomial.coeff_eq_zero_of_natDegree_lt (show G.natDegree < i by omega)]

theorem M7.CompactStorage.storage_bounds : ∀ (N H : ℕ) [NeZero N], M7.CompactStorage.coreBits N = 12*N+4 ∧ M7.CompactStorage.coreBits N ≤ 16*N ∧ M7.CompactStorage.tableBits N = Nat.totient N*(N+1) ∧ M7.CompactStorage.storedCoreBits N H ≤ 16*H*N ∧ M7.CompactStorage.storedWithTablesBits N H ≤ 16*H*N + 2*H*Nat.totient N*N := by
  intro N H inst
  have hN : 0 < N := NeZero.pos N
  have hcore : M7.CompactStorage.coreBits N = 12 * N + 4 := by
    unfold M7.CompactStorage.coreBits
    ring
  have hbound : M7.CompactStorage.coreBits N ≤ 16 * N := by
    rw [hcore]
    omega
  have htable : M7.CompactStorage.tableBits N = Nat.totient N * (N + 1) := by
    simp [M7.CompactStorage.tableBits, ZMod.card_units_eq_totient]
  have hwidth : N + 1 ≤ 2 * N := by omega
  have hstored := Nat.mul_le_mul_left H hbound
  have htstored := Nat.mul_le_mul_left (H * Nat.totient N) hwidth
  refine ⟨hcore, hbound, htable, ?_, ?_⟩
  · unfold M7.CompactStorage.storedCoreBits
    nlinarith [hstored]
  · simp only [M7.CompactStorage.storedWithTablesBits, M7.CompactStorage.storedCoreBits, htable]
    nlinarith [hstored, htstored]

theorem M7.CompactStorage.support_value_injective : ∀ (N : ℕ) [NeZero N], Function.Injective (@M7.CompactStorage.supportBits N) ∧ Function.Injective (@M7.CompactStorage.valueBits N) := by
  classical
  change ∀ (N : ℕ) [NeZero N], Function.Injective (@M7.CompactStorage.supportBits N) ∧ Function.Injective (@M7.CompactStorage.valueBits N)
  intro N inst
  constructor
  · intro A B h
    apply Finset.ext
    intro x
    have hx := congrFun h (⟨x.val, ZMod.val_lt x⟩ : Fin N)
    have hx' := congrArg (fun b : Bool => b = true) hx
    simpa [M7.CompactStorage.supportBits, ZMod.natCast_zmod_val] using hx'
  · intro x y h
    have hx := congrFun h (⟨x.val, ZMod.val_lt x⟩ : Fin N)
    simpa [M7.CompactStorage.valueBits, ZMod.natCast_zmod_val, eq_comm] using hx

theorem M7.CompactStorage.encode_core : ∀ (N : ℕ) [NeZero N] (e f : M7.CompactGeneration.Emission N), M7.CompactStorage.Valid e → M7.CompactStorage.Valid f → M7.CompactStorage.encode e = M7.CompactStorage.encode f → M7.CompactStorage.coreView e = M7.CompactStorage.coreView f := by
  change ∀ (N : ℕ) [NeZero N] (e f : M7.CompactGeneration.Emission N), _
  intro N inst e f he hf h
  classical
  obtain ⟨hs, hv⟩ := M7.CompactStorage.support_value_injective N
  simp only [M7.CompactStorage.encode, M7.CompactStorage.Code.mk.injEq] at h
  have hl : e.leaf = f.leaf := by
    apply Prod.ext <;> apply hs <;> tauto
  have hr : e.representative = f.representative := by
    apply Prod.ext <;> apply hs <;> tauto
  have hu : e.action.unit = f.action.unit := by
    apply Units.ext
    apply hv
    tauto
  have hx : e.action.exchange = f.action.exchange := by tauto
  have ha : e.action.leftShift = f.action.leftShift := by
    apply hv
    tauto
  have hb : e.action.rightShift = f.action.rightShift := by
    apply hv
    tauto
  have hg : e.action = f.action := by
    cases hea : e.action
    cases hfa : f.action
    simp_all
  unfold M7.CompactStorage.Valid at he hf
  simp_all [M7.CompactStorage.coreView]

theorem M7.CompactStorage.unit_table_recovery : ∀ (N : ℕ) [NeZero N] (e : M7.CompactGeneration.Emission N) (u : (ZMod N)ˣ) (F : M5.BinaryPolynomial), F.natDegree ≤ N → (M7.CompactStorage.unitTable e u = M7.CompactStorage.polynomialBits N F ↔ M7.RecipeSignature.signature (M7.Action.act (⟨u,false,0,0⟩ : M7.Action.Record N) e.representative) = F) := by
  intro N inst e u F hF
  change M7.CompactStorage.polynomialBits N (M7.RecipeSignature.signature (M7.Action.act (⟨u, false, 0, 0⟩ : M7.Action.Record N) e.representative)) = M7.CompactStorage.polynomialBits N F ↔ _
  constructor
  · intro h
    exact M7.CompactStorage.polynomial_injective N _ F
      (M7.CompactStorage.field_bounds N (M7.Action.act (⟨u, false, 0, 0⟩ : M7.Action.Record N) e.representative)).1 hF h
  · intro h
    exact congrArg (M7.CompactStorage.polynomialBits N) h
#print axioms M7.CompactStorage.emission_valid
#print axioms M7.CompactStorage.field_bounds
#print axioms M7.CompactStorage.polynomial_injective
#print axioms M7.CompactStorage.storage_bounds
#print axioms M7.CompactStorage.support_value_injective
#print axioms M7.CompactStorage.encode_core
#print axioms M7.CompactStorage.unit_table_recovery
