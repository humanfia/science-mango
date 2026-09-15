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
#print axioms M7.OrbitFibers.action_partition
#print axioms M7.OrbitFibers.fiber_equiv
#print axioms M7.OrbitFibers.orbit_partition
#print axioms M7.OrbitFibers.stabilizer_positive
