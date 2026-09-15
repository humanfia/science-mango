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

theorem M7.Connectivity.closure_equiv_top : ∀ (N : ℕ) [NeZero N] (e : ZMod N ≃+ ZMod N) (S : Set (ZMod N)), AddSubgroup.closure (e '' S) = ⊤ ↔ AddSubgroup.closure S = ⊤ := by
  change ∀ (N : ℕ) [NeZero N] (e : ZMod N ≃+ ZMod N) (S : Set (ZMod N)), AddSubgroup.closure (e '' S) = ⊤ ↔ AddSubgroup.closure S = ⊤
  intro N inst e S
  constructor
  · intro h
    have hle : AddSubgroup.closure (e '' S) ≤
        (AddSubgroup.closure S).comap e.symm.toAddMonoidHom := by
      apply (AddSubgroup.closure_le _).mpr
      rintro y ⟨x, hx, rfl⟩
      change e.symm (e x) ∈ AddSubgroup.closure S
      simpa using (AddSubgroup.subset_closure hx)
    apply top_unique
    intro x hx
    have hm : e x ∈ AddSubgroup.closure (e '' S) := by
      rw [h]
      trivial
    have hm' := hle hm
    change e.symm (e x) ∈ AddSubgroup.closure S at hm'
    simpa using hm'
  · intro h
    have hle : AddSubgroup.closure S ≤
        (AddSubgroup.closure (e '' S)).comap e.toAddMonoidHom := by
      apply (AddSubgroup.closure_le _).mpr
      intro x hx
      change e x ∈ AddSubgroup.closure (e '' S)
      exact AddSubgroup.subset_closure ⟨x, hx, rfl⟩
    apply top_unique
    intro x hx
    have hm : e.symm x ∈ AddSubgroup.closure S := by
      rw [h]
      trivial
    have hm' := hle hm
    change e (e.symm x) ∈ AddSubgroup.closure (e '' S) at hm'
    simpa using hm'

theorem M7.Connectivity.difference_affine : ∀ (N : ℕ) [NeZero N] (A : Finset (ZMod N)) (u : (ZMod N)ˣ) (s : ZMod N), M7.Connectivity.differences (A.image (M7.Action.affine u s)) = (fun x : ZMod N => (u : ZMod N)*x) '' M7.Connectivity.differences A := by
  intro N inst A u s
  classical
  apply Set.ext
  intro x
  simp only [M7.Connectivity.differences, Set.mem_setOf_eq, Set.mem_image,
    Finset.mem_image]
  constructor
  · rintro ⟨a, ⟨a₀, ha₀, rfl⟩, b, ⟨b₀, hb₀, rfl⟩, hx⟩
    refine ⟨a₀ - b₀, ⟨a₀, ha₀, b₀, hb₀, rfl⟩, ?_⟩
    first
    | simpa [M7.Action.affine, mul_sub] using hx
    | simpa [M7.Action.affine, mul_sub] using hx.symm
  · rintro ⟨y, ⟨a, ha, b, hb, rfl⟩, hx⟩
    refine ⟨M7.Action.affine u s a, ⟨a, ha, rfl⟩,
      M7.Action.affine u s b, ⟨b, hb, rfl⟩, ?_⟩
    first
    | simpa [M7.Action.affine, mul_sub] using hx
    | simpa [M7.Action.affine, mul_sub] using hx.symm

theorem M7.Connectivity.difference_shift : ∀ (N : ℕ) [NeZero N] (A : Finset (ZMod N)) (s : ZMod N), M7.Connectivity.differences (M7.Domain.shift A s) = M7.Connectivity.differences A := by
  change ∀ (N : ℕ) [NeZero N] (A : Finset (ZMod N)) (s : ZMod N), M7.Connectivity.differences (M7.Domain.shift A s) = M7.Connectivity.differences A
  intro N inst A s
  classical
  ext x
  change (∃ a ∈ M7.Domain.shift A s, ∃ b ∈ M7.Domain.shift A s, x = a - b) ↔ (∃ a ∈ A, ∃ b ∈ A, x = a - b)
  constructor
  · rintro ⟨a, ha, b, hb, h⟩
    have ha' : a + -s ∈ A := by simpa [M7.Domain.shift] using ha
    have hb' : b + -s ∈ A := by simpa [M7.Domain.shift] using hb
    refine ⟨a + -s, ha', b + -s, hb', ?_⟩
    calc
      x = a - b := h
      _ = (a + -s) - (b + -s) := by ring
  · rintro ⟨a, ha, b, hb, h⟩
    have ha' : a + s ∈ M7.Domain.shift A s := by simpa [M7.Domain.shift] using ha
    have hb' : b + s ∈ M7.Domain.shift A s := by simpa [M7.Domain.shift] using hb
    refine ⟨a + s, ha', b + s, hb', ?_⟩
    calc
      x = a - b := h
      _ = (a + s) - (b + s) := by ring

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

theorem M7.Connectivity.scalar_mem : ∀ (N : ℕ) [NeZero N] (H : AddSubgroup (ZMod N)) (a r : ZMod N), a ∈ H → r*a ∈ H := by
  change ∀ (N : ℕ) [NeZero N] (H : AddSubgroup (ZMod N)) (a r : ZMod N), a ∈ H → r * a ∈ H
  intro N inst H a r ha
  simpa only [nsmul_eq_mul, ZMod.natCast_zmod_val] using H.nsmul_mem ha r.val

theorem M7.Connectivity.connected_action : ∀ (N : ℕ) [NeZero N] (g : M7.Action.Record N) (c : M7.Connectivity.Recipe N), M7.Connectivity.connected (M7.Action.act g c) ↔ M7.Connectivity.connected c := by
  change ∀ (N : ℕ) [NeZero N] (g : M7.Action.Record N) (c : M7.Connectivity.Recipe N), M7.Connectivity.connected (M7.Action.act g c) ↔ M7.Connectivity.connected c
  intro N inst g c
  classical
  have h (S : Set (ZMod N)) :
      AddSubgroup.closure ((fun x : ZMod N => (g.unit : ZMod N) * x) '' S) = ⊤ ↔
        AddSubgroup.closure S = ⊤ := by
    exact M7.Connectivity.closure_equiv_top N (M7.Connectivity.unitEquiv g.unit) S
  cases he : g.exchange <;>
    simpa [M7.Connectivity.connected, M7.Action.act, he,
      M7.Connectivity.difference_affine, Set.image_union, Set.union_comm] using
      h (M7.Connectivity.differences c.1 ∪ M7.Connectivity.differences c.2)

theorem M7.Connectivity.connected_shift : ∀ (N : ℕ) [NeZero N] (c : M7.Connectivity.Recipe N) (s t : ZMod N), M7.Connectivity.connected (M7.Domain.shift c.1 s, M7.Domain.shift c.2 t) ↔ M7.Connectivity.connected c := by
  change ∀ (N : ℕ) [NeZero N] (c : M7.Connectivity.Recipe N) (s t : ZMod N), M7.Connectivity.connected (M7.Domain.shift c.1 s, M7.Domain.shift c.2 t) ↔ M7.Connectivity.connected c
  intro N inst c s t
  simp only [M7.Connectivity.connected, M7.Connectivity.difference_shift]

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
#print axioms M7.Connectivity.anchored_closure
#print axioms M7.Connectivity.closure_equiv_top
#print axioms M7.Connectivity.difference_affine
#print axioms M7.Connectivity.connected_action
#print axioms M7.Connectivity.difference_shift
#print axioms M7.Connectivity.connected_shift
#print axioms M7.Connectivity.gcd_mem
#print axioms M7.Connectivity.scalar_mem
#print axioms M7.Connectivity.one_mem_top
#print axioms M7.Connectivity.finite_generation_gcd
