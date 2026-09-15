import M7OrbitFibers

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
def QuantumHarnessFrozenTarget : Prop :=
  ∀ (G : Type) [Group G] [Fintype G] (X : Type) [MulAction G X] (c : X), ∀ P : X → Prop, M7.OrbitFibers.actionCount G c P / M7.OrbitFibers.stabilizerCount G c = M7.OrbitFibers.orbitCount G c P ∧ M7.OrbitFibers.stabilizerCount G c ∣ M7.OrbitFibers.actionCount G c P
