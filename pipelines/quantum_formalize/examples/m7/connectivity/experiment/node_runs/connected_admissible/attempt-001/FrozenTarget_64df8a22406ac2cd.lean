import M7Connectivity

theorem M7.Connectivity.anchored_closure : ∀ (N : ℕ) [NeZero N] (A B : Finset (ZMod N)), (0 : ZMod N) ∈ A → (0 : ZMod N) ∈ B → AddSubgroup.closure (M7.Connectivity.differences A ∪ M7.Connectivity.differences B) = AddSubgroup.closure ((A : Set (ZMod N)) ∪ (B : Set (ZMod N))) := by
  intro N inst A B hA hB
  apply le_antisymm
  · apply (AddSubgroup.closure_le _).2
    intro x hx
    rcases hx with hx | hx
    · rcases hx with ⟨a, ha, b, hb, h⟩
      subst x
      exact (AddSubgroup.closure ((A : Set (ZMod N)) ∪ (B : Set (ZMod N)))).sub_mem
        (AddSubgroup.subset_closure (Or.inl ha))
        (AddSubgroup.subset_closure (Or.inl hb))
    · rcases hx with ⟨a, ha, b, hb, h⟩
      subst x
      exact (AddSubgroup.closure ((A : Set (ZMod N)) ∪ (B : Set (ZMod N)))).sub_mem
        (AddSubgroup.subset_closure (Or.inr ha))
        (AddSubgroup.subset_closure (Or.inr hb))
  · apply (AddSubgroup.closure_le _).2
    intro x hx
    apply AddSubgroup.subset_closure
    rcases hx with hx | hx
    · left
      refine ⟨x, hx, 0, hA, ?_⟩
      simp
    · right
      refine ⟨x, hx, 0, hB, ?_⟩
      simp

theorem M7.Connectivity.gcd_mem : ∀ (N : ℕ) [NeZero N] (H : AddSubgroup (ZMod N)) (S : Finset ℕ), (∀ a ∈ S, (a : ZMod N) ∈ H) → ((S.gcd id : ℕ) : ZMod N) ∈ H := by
  change ∀ (N : ℕ) [NeZero N] (H : AddSubgroup (ZMod N)) (S : Finset ℕ), (∀ a ∈ S, (a : ZMod N) ∈ H) → ((S.gcd id : ℕ) : ZMod N) ∈ H
  intro N inst H S
  induction S using Finset.induction_on with
  | empty =>
      intro h
      simpa using H.zero_mem
  | @insert a S ha ih =>
      intro h
      have haH : (a : ZMod N) ∈ H := h a (Finset.mem_insert_self a S)
      have hSH : ((S.gcd id : ℕ) : ZMod N) ∈ H :=
        ih (fun b hb => h b (Finset.mem_insert_of_mem hb))
      rw [Finset.gcd_insert]
      change ((Nat.gcd a (S.gcd id) : ℕ) : ZMod N) ∈ H
      have hbez := congrArg (fun z : ℤ => (z : ZMod N))
        (Nat.gcd_eq_gcd_ab a (S.gcd id))
      simp only [Int.cast_add, Int.cast_mul, Int.cast_natCast] at hbez
      rw [hbez]
      simpa only [zsmul_eq_mul, mul_comm] using
        H.add_mem (H.zsmul_mem haH (Nat.gcdA a (S.gcd id)))
          (H.zsmul_mem hSH (Nat.gcdB a (S.gcd id)))

theorem M7.Connectivity.nat_support_image : ∀ (N : ℕ) [NeZero N] (A B : Finset (ZMod N)), (fun a : ℕ => (a : ZMod N)) '' ((M7.Supports.natSupport A ∪ M7.Supports.natSupport B : Finset ℕ) : Set ℕ) = (A : Set (ZMod N)) ∪ (B : Set (ZMod N)) := by
  intro N inst A B
  classical
  ext x
  change (∃ n : ℕ, n ∈ (A.image ZMod.val ∪ B.image ZMod.val) ∧ (n : ZMod N) = x) ↔ (x ∈ A ∨ x ∈ B)
  constructor
  · rintro ⟨n, hn, rfl⟩
    rcases Finset.mem_union.mp hn with hn | hn
    · rcases Finset.mem_image.mp hn with ⟨a, ha, rfl⟩
      exact Or.inl (by simpa only [ZMod.natCast_zmod_val] using ha)
    · rcases Finset.mem_image.mp hn with ⟨b, hb, rfl⟩
      exact Or.inr (by simpa only [ZMod.natCast_zmod_val] using hb)
  · intro hx
    refine ⟨x.val, ?_, ZMod.natCast_zmod_val x⟩
    rcases hx with hx | hx
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_image.mpr ⟨x, hx, rfl⟩))
    · exact Finset.mem_union.mpr (Or.inr (Finset.mem_image.mpr ⟨x, hx, rfl⟩))

theorem M7.Connectivity.scalar_mem : ∀ (N : ℕ) [NeZero N] (H : AddSubgroup (ZMod N)) (a r : ZMod N), a ∈ H → r*a ∈ H := by
  change ∀ (N : ℕ) [NeZero N] (H : AddSubgroup (ZMod N)) (a r : ZMod N), a ∈ H → r * a ∈ H
  intro N inst H a r ha
  simpa only [nsmul_eq_mul, ZMod.natCast_zmod_val] using H.nsmul_mem ha r.val

theorem M7.Connectivity.one_mem_top : ∀ (N : ℕ) [NeZero N] (H : AddSubgroup (ZMod N)), (1 : ZMod N) ∈ H ↔ H = ⊤ := by
  change ∀ (N : ℕ) [NeZero N] (H : AddSubgroup (ZMod N)), (1 : ZMod N) ∈ H ↔ H = ⊤
  intro N inst H
  constructor
  · intro h
    apply le_antisymm le_top
    intro x hx
    simpa only [mul_one] using M7.Connectivity.scalar_mem N H 1 x h
  · intro h
    rw [h]
    trivial

theorem M7.Connectivity.finite_generation_gcd : ∀ (N : ℕ) [NeZero N] (S : Finset ℕ), AddSubgroup.closure ((fun a : ℕ => (a : ZMod N)) '' (S : Set ℕ)) = ⊤ ↔ Nat.gcd N (S.gcd id) = 1 := by
  change ∀ (N : ℕ) [NeZero N] (S : Finset ℕ), AddSubgroup.closure ((fun a : ℕ => (a : ZMod N)) '' (S : Set ℕ)) = ⊤ ↔ Nat.gcd N (S.gcd id) = 1
  intro N inst S
  let H : AddSubgroup (ZMod N) := AddSubgroup.closure ((fun a : ℕ => (a : ZMod N)) '' (S : Set ℕ))
  let g : ZMod N := (S.gcd id : ℕ)
  have hg : g ∈ H := M7.Connectivity.gcd_mem N H S (fun a ha => AddSubgroup.subset_closure ⟨a, ha, rfl⟩)
  change H = ⊤ ↔ Nat.gcd N (S.gcd id) = 1
  constructor
  · intro htop
    let K : AddSubgroup (ZMod N) :=
      { carrier := {x | ∃ r : ZMod N, r * g = x}
        zero_mem' := ⟨0, zero_mul g⟩
        add_mem' := by
          intro x y hx hy
          rcases hx with ⟨r, hr⟩
          rcases hy with ⟨s, hs⟩
          exact ⟨r + s, by rw [add_mul, hr, hs]⟩
        neg_mem' := by
          intro x hx
          rcases hx with ⟨r, hr⟩
          exact ⟨-r, by rw [neg_mul, hr]⟩ }
    have hHK : H ≤ K := by
      change AddSubgroup.closure ((fun a : ℕ => (a : ZMod N)) '' (S : Set ℕ)) ≤ K
      apply (AddSubgroup.closure_le K).2
      rintro x ⟨a, ha, rfl⟩
      have hd : S.gcd id ∣ a := Finset.gcd_dvd ha
      rcases hd with ⟨b, hb⟩
      change ∃ r : ZMod N, r * g = (a : ZMod N)
      refine ⟨(b : ZMod N), ?_⟩
      dsimp [g]
      rw [hb, Nat.cast_mul, mul_comm]
    have h1 : (1 : ZMod N) ∈ H := (M7.Connectivity.one_mem_top N H).2 htop
    obtain ⟨r, hr⟩ := hHK h1
    have hu : IsUnit g := ⟨⟨g, r, by rw [mul_comm]; exact hr, hr⟩, rfl⟩
    have hc := (ZMod.isUnit_iff_coprime (S.gcd id) N).1 hu
    simpa only [Nat.coprime_iff_gcd_eq_one, Nat.gcd_comm] using hc
  · intro h
    have hc : (S.gcd id).Coprime N := by
      rw [Nat.coprime_iff_gcd_eq_one, Nat.gcd_comm]
      exact h
    have hu : IsUnit g := (ZMod.isUnit_iff_coprime (S.gcd id) N).2 hc
    rcases hu with ⟨u, hu⟩
    apply (M7.Connectivity.one_mem_top N H).1
    have hm := M7.Connectivity.scalar_mem N H g (↑(u⁻¹) : ZMod N) hg
    rw [← hu] at hm
    simpa using hm

theorem M7.Connectivity.anchored_gcd : ∀ (N : ℕ) [NeZero N] (A B : Finset (ZMod N)), (0 : ZMod N) ∈ A → (0 : ZMod N) ∈ B → (M7.Connectivity.connected (A,B) ↔ M7.Domain.connectivityGcd A B = 1) := by
  change ∀ (N : ℕ) [NeZero N] (A B : Finset (ZMod N)), (0 : ZMod N) ∈ A → (0 : ZMod N) ∈ B → (M7.Connectivity.connected (A, B) ↔ M7.Domain.connectivityGcd A B = 1)
  intro N inst A B hA hB
  change AddSubgroup.closure (M7.Connectivity.differences A ∪ M7.Connectivity.differences B) = ⊤ ↔ Nat.gcd N ((M7.Supports.natSupport A ∪ M7.Supports.natSupport B).gcd id) = 1
  rw [M7.Connectivity.anchored_closure N A B hA hB, ← M7.Connectivity.nat_support_image N A B]
  exact M7.Connectivity.finite_generation_gcd N (M7.Supports.natSupport A ∪ M7.Supports.natSupport B)
def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N w : ℕ) [NeZero N] (c : M7.Connectivity.Recipe N), c.1.card = w → c.2.card = w → (0 : ZMod N) ∈ c.1 → (0 : ZMod N) ∈ c.2 → M7.Connectivity.connected c → M6.Final.Admissible N (M7.Supports.polynomial c.1) (M7.Supports.polynomial c.2)
