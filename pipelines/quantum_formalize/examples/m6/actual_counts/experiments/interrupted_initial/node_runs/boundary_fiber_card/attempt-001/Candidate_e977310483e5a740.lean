import FrozenTarget_e977310483e5a740
theorem M6.ActualCounts.boundary_fiber_card : QuantumHarnessFrozenTarget := by
  intro N inst a b ha hb h₀
  classical
  let S := {h : M6.Physical.Block N //
    M6.Spaces.boundary N (M6.Coordinates.coefficients N a) (M6.Coordinates.coefficients N b) h =
    M6.Spaces.boundary N (M6.Coordinates.coefficients N a) (M6.Coordinates.coefficients N b) h₀}
  let T := {h : AdjoinRoot (M6.Cyclic.modulus N) //
    M6.BoundaryFibers.boundary a b (M6.Cyclic.modulus N) h =
    M6.BoundaryFibers.boundary a b (M6.Cyclic.modulus N) (M6.Coordinates.encode N h₀)}
  let g : S → T := fun h =>
    ⟨M6.Coordinates.encode N h.val,
      (M6.ActualCounts.boundary_eq_iff N a b ha hb h.val h₀).mp h.property⟩
  have hg : Function.Bijective g := by
    constructor
    · intro x y hxy
      apply Subtype.ext
      apply M6.Coordinates.encode_injective N
      exact congrArg Subtype.val hxy
    · intro y
      obtain ⟨h, hh⟩ := M6.Coordinates.encode_surjective N y.val
      have hp : M6.Spaces.boundary N (M6.Coordinates.coefficients N a) (M6.Coordinates.coefficients N b) h =
          M6.Spaces.boundary N (M6.Coordinates.coefficients N a) (M6.Coordinates.coefficients N b) h₀ := by
        apply (M6.ActualCounts.boundary_eq_iff N a b ha hb h h₀).mpr
        rw [hh]
        exact y.property
      refine ⟨⟨h, hp⟩, ?_⟩
      apply Subtype.ext
      exact hh
  have hc : Nat.card S = Nat.card T :=
    Nat.card_congr (Equiv.ofBijective g hg)
  change Nat.card S = 2 ^ (M6.ActualCounts.f N a b)
  refine hc.trans ?_
  exact M6.BoundaryFibers.fiber_card a b (M6.Cyclic.modulus N)
    (M6.Coordinates.modulus_monic_degree N).1.ne_zero
    (M6.Coordinates.encode N h₀)
