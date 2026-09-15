import M7Connectivity

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
def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N] (g : M7.Action.Record N) (c : M7.Connectivity.Recipe N), M7.Connectivity.connected (M7.Action.act g c) ↔ M7.Connectivity.connected c
