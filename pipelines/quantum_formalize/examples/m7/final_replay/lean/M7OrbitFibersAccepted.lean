import M7OrbitFibers

theorem M7.OrbitFibers.action_partition : ∀ (G : Type) [Group G] [Fintype G] (X : Type) [MulAction G X] (c : X), ∀ (P : X → Prop) (test : X → Bool), M7.OrbitFibers.actionCount G c P = M7.OrbitFibers.actionCount G c (fun y => P y ∧ test y = false) + M7.OrbitFibers.actionCount G c (fun y => P y ∧ test y = true) := by
  classical
  intro G _ _ X _ c P test
  have partition {α : Type} (s : Finset α) (Q : α → Prop) (b : α → Bool) :
      (s.filter Q).card =
        (s.filter (fun a => Q a ∧ b a = false)).card +
        (s.filter (fun a => Q a ∧ b a = true)).card := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert a s ha ih =>
      by_cases hQ : Q a <;> cases hb : b a <;>
        simp_all [Finset.filter_insert, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  simpa [M7.OrbitFibers.actionCount] using
    partition (Finset.univ : Finset G) (fun g => P (g • c)) (fun g => test (g • c))

theorem M7.OrbitFibers.fiber_equiv : ∀ (G : Type) [Group G] [Fintype G] (X : Type) [MulAction G X] (c : X), ∀ g₀ : G, Nonempty ({h : G // h • c = c} ≃ {g : G // g • c = g₀ • c}) := by
  let QuantumHarnessFrozenTarget : Prop := (
    ∀ (G : Type) [Group G] [Fintype G] (X : Type) [MulAction G X] (c : X), ∀ g₀ : G, Nonempty ({h : G // h • c = c} ≃ {g : G // g • c = g₀ • c})
  )
  change QuantumHarnessFrozenTarget
  unfold QuantumHarnessFrozenTarget
  intro G _ _ X _ c g₀
  refine ⟨{
    toFun := fun h => ⟨g₀ * h.val, ?_⟩
    invFun := fun g => ⟨g₀⁻¹ * g.val, ?_⟩
    left_inv := ?_
    right_inv := ?_
  }⟩
  · rw [mul_smul, h.property]
  · rw [mul_smul, g.property]
    simp
  · intro h
    apply Subtype.ext
    change g₀⁻¹ * (g₀ * h.val) = h.val
    simp
  · intro g
    apply Subtype.ext
    change g₀ * (g₀⁻¹ * g.val) = g.val
    simp

theorem M7.OrbitFibers.orbit_partition : ∀ (G : Type) [Group G] [Fintype G] (X : Type) [MulAction G X] (c : X), ∀ (P : X → Prop) (test : X → Bool), M7.OrbitFibers.orbitCount G c P = M7.OrbitFibers.orbitCount G c (fun y => P y ∧ test y = false) + M7.OrbitFibers.orbitCount G c (fun y => P y ∧ test y = true) := by
  classical
  intro G _ _ X _ c P test
  unfold M7.OrbitFibers.orbitCount
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro y hy
  have hb : ∀ b : Bool, b ≠ false → b = true := by decide
  by_cases hp : P y
  · by_cases ht : test y = false
    · simp [hp, ht]
    · have ht' : test y = true := hb (test y) ht
      simp [hp, ht']
  · simp [hp]

theorem M7.OrbitFibers.stabilizer_positive : ∀ (G : Type) [Group G] [Fintype G] (X : Type) [MulAction G X] (c : X), 0 < M7.OrbitFibers.stabilizerCount G c := by
  let QuantumHarnessFrozenTarget : Prop := (
    ∀ (G : Type) [Group G] [Fintype G] (X : Type) [MulAction G X] (c : X), 0 < M7.OrbitFibers.stabilizerCount G c
  )
  change QuantumHarnessFrozenTarget
  unfold QuantumHarnessFrozenTarget
  intro G _ _ X _ c
  classical
  unfold M7.OrbitFibers.stabilizerCount
  apply Finset.card_pos.mpr
  refine ⟨(1 : G), ?_⟩
  apply Finset.mem_filter.mpr
  exact ⟨Finset.mem_univ _, one_smul G c⟩

theorem M7.OrbitFibers.fiber_count : ∀ (G : Type) [Group G] [Fintype G] (X : Type) [MulAction G X] (c : X), ∀ y ∈ M7.OrbitFibers.orbit G c, M7.OrbitFibers.fiberCount G c y = M7.OrbitFibers.stabilizerCount G c := by
  let QuantumHarnessFrozenTarget : Prop := (
    ∀ (G : Type) [Group G] [Fintype G] (X : Type) [MulAction G X] (c : X), ∀ y ∈ M7.OrbitFibers.orbit G c, M7.OrbitFibers.fiberCount G c y = M7.OrbitFibers.stabilizerCount G c
  )
  change QuantumHarnessFrozenTarget
  unfold QuantumHarnessFrozenTarget
  intro G _ _ X _ c y hy
  classical
  unfold M7.OrbitFibers.orbit at hy
  obtain ⟨g₀, _, rfl⟩ := Finset.mem_image.mp hy
  obtain ⟨e⟩ := M7.OrbitFibers.fiber_equiv G X c g₀
  unfold M7.OrbitFibers.fiberCount M7.OrbitFibers.stabilizerCount
  refine Finset.card_bij
    (fun g hg => (e.symm ⟨g, (Finset.mem_filter.mp hg).2⟩).val) ?_ ?_ ?_
  · intro g hg
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (e.symm ⟨g, (Finset.mem_filter.mp hg).2⟩).property⟩
  · intro a ha b hb hab
    have h : e.symm ⟨a, (Finset.mem_filter.mp ha).2⟩ =
        e.symm ⟨b, (Finset.mem_filter.mp hb).2⟩ := Subtype.ext hab
    exact congrArg Subtype.val (e.symm.injective h)
  · intro h hh
    let h' : {h : G // h • c = c} := ⟨h, (Finset.mem_filter.mp hh).2⟩
    have hg : (e h').val ∈ Finset.univ.filter (fun g : G => g • c = g₀ • c) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, (e h').property⟩
    refine ⟨(e h').val, hg, ?_⟩
    change (e.symm (e h')).val = h
    exact congrArg Subtype.val (e.symm_apply_apply h')

theorem M7.OrbitFibers.action_count_product : ∀ (G : Type) [Group G] [Fintype G] (X : Type) [MulAction G X] (c : X), ∀ P : X → Prop, M7.OrbitFibers.actionCount G c P = M7.OrbitFibers.orbitCount G c P * M7.OrbitFibers.stabilizerCount G c := by
  let QuantumHarnessFrozenTarget : Prop := (
    ∀ (G : Type) [Group G] [Fintype G] (X : Type) [MulAction G X] (c : X), ∀ P : X → Prop, M7.OrbitFibers.actionCount G c P = M7.OrbitFibers.orbitCount G c P * M7.OrbitFibers.stabilizerCount G c
  )
  change QuantumHarnessFrozenTarget
  unfold QuantumHarnessFrozenTarget
  intro G _ _ X _ c P
  classical
  unfold M7.OrbitFibers.actionCount M7.OrbitFibers.orbitCount
  calc
    _ = ∑ y ∈ (M7.OrbitFibers.orbit G c).filter P,
        ((Finset.univ.filter (fun g : G => P (g • c))).filter
          (fun g => g • c = y)).card := by
      apply Finset.card_eq_sum_card_fiberwise
      intro g hg
      apply Finset.mem_filter.mpr
      refine ⟨?_, (Finset.mem_filter.mp hg).2⟩
      unfold M7.OrbitFibers.orbit
      exact Finset.mem_image.mpr ⟨g, Finset.mem_univ g, rfl⟩
    _ = ∑ y ∈ (M7.OrbitFibers.orbit G c).filter P,
        M7.OrbitFibers.stabilizerCount G c := by
      apply Finset.sum_congr rfl
      intro y hy
      obtain ⟨hyorbit, hPy⟩ := Finset.mem_filter.mp hy
      have hf :
          (Finset.univ.filter (fun g : G => P (g • c))).filter
              (fun g => g • c = y) =
            Finset.univ.filter (fun g : G => g • c = y) := by
        ext g
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · intro h
          exact h.2
        · intro h
          exact ⟨by simpa only [h] using hPy, h⟩
      rw [hf]
      change M7.OrbitFibers.fiberCount G c y =
        M7.OrbitFibers.stabilizerCount G c
      exact M7.OrbitFibers.fiber_count G X c y hyorbit
    _ = _ := by simp

theorem M7.OrbitFibers.orbit_count_div : ∀ (G : Type) [Group G] [Fintype G] (X : Type) [MulAction G X] (c : X), ∀ P : X → Prop, M7.OrbitFibers.actionCount G c P / M7.OrbitFibers.stabilizerCount G c = M7.OrbitFibers.orbitCount G c P ∧ M7.OrbitFibers.stabilizerCount G c ∣ M7.OrbitFibers.actionCount G c P := by
  let QuantumHarnessFrozenTarget : Prop := (
    ∀ (G : Type) [Group G] [Fintype G] (X : Type) [MulAction G X] (c : X), ∀ P : X → Prop, M7.OrbitFibers.actionCount G c P / M7.OrbitFibers.stabilizerCount G c = M7.OrbitFibers.orbitCount G c P ∧ M7.OrbitFibers.stabilizerCount G c ∣ M7.OrbitFibers.actionCount G c P
  )
  change QuantumHarnessFrozenTarget
  unfold QuantumHarnessFrozenTarget
  intro G _ _ X _ c P
  rw [M7.OrbitFibers.action_count_product G X c P]
  constructor
  · exact Nat.mul_div_cancel _ (M7.OrbitFibers.stabilizer_positive G X c)
  · exact ⟨M7.OrbitFibers.orbitCount G c P, Nat.mul_comm _ _⟩
#print axioms M7.OrbitFibers.action_partition
#print axioms M7.OrbitFibers.fiber_equiv
#print axioms M7.OrbitFibers.fiber_count
#print axioms M7.OrbitFibers.action_count_product
#print axioms M7.OrbitFibers.orbit_partition
#print axioms M7.OrbitFibers.stabilizer_positive
#print axioms M7.OrbitFibers.orbit_count_div
