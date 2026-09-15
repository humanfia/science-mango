import M6ActualCounts
import M6ActualCountsDependencies

theorem M6.ActualCounts.encoded_boundary : ∀ (N : ℕ) [NeZero N] (a b : M6.ActualCounts.BP), a.degree < (N : WithBot ℕ) → b.degree < (N : WithBot ℕ) → ∀ h : M6.Physical.Block N, (M6.Coordinates.encode N (M6.Physical.conv N (M6.Coordinates.coefficients N a) h), M6.Coordinates.encode N (M6.Physical.conv N (M6.Coordinates.coefficients N b) h)) = M6.BoundaryFibers.boundary a b (M6.Cyclic.modulus N) (M6.Coordinates.encode N h) := by
  intro N inst a b ha hb h
  rw [M6.Coordinates.encode_conv N (M6.Coordinates.coefficients N a) h,
      M6.Coordinates.encode_conv N (M6.Coordinates.coefficients N b) h,
      M6.Coordinates.encode_polynomial N a ha,
      M6.Coordinates.encode_polynomial N b hb]
  rfl

theorem M6.ActualCounts.finite_image_weighted_sum : ∀ (α β : Type) [Fintype α] (L : α → β) (k : ℕ), (∀ a₀ : α, Nat.card {a : α // L a = L a₀} = k) → ∀ w : β → Polynomial ℤ, (∑ a, w (L a)) = Polynomial.C (k : ℤ) * ∑ b ∈ M6.ActualCounts.imageWords L, w b := by
  classical
  intro α β _ L k hk w
  let L' : α → ↥(M6.ActualCounts.imageWords L) := fun a =>
    ⟨L a, by simp [M6.ActualCounts.imageWords]⟩
  have hu : M6.FiberSum.UniformFibers L' k := by
    intro b
    obtain ⟨a₀, ha₀⟩ : ∃ a₀ : α, L a₀ = b.val := by
      simpa [M6.ActualCounts.imageWords] using b.property
    have hb : (Finset.univ.filter (fun a : α => L a = b.val)).card = k := by
      simpa [ha₀, Nat.card_eq_fintype_card, Fintype.card_subtype] using hk a₀
    have hf : M6.FiberSum.fiber L' b =
        Finset.univ.filter (fun a : α => L a = b.val) := by
      ext a
      simp only [M6.FiberSum.fiber, Finset.mem_filter, Finset.mem_univ, true_and]
      change (L' a = b ↔ L a = b.val)
      exact Subtype.ext_iff
    change (M6.FiberSum.fiber L' b).card = k
    rw [hf]
    exact hb
  have hs := M6.FiberSum.uniform_weighted_sum α
    ↥(M6.ActualCounts.imageWords L) L' k hu (fun b => w b.val)
  change (∑ a, w (L a)) = Polynomial.C (k : ℤ) *
    (∑ b : ↥(M6.ActualCounts.imageWords L), w b.val) at hs
  rw [Finset.sum_coe_sort] at hs
  exact hs

theorem M6.ActualCounts.boundary_eq_iff : ∀ (N : ℕ) [NeZero N] (a b : M6.ActualCounts.BP), a.degree < (N : WithBot ℕ) → b.degree < (N : WithBot ℕ) → ∀ h h₀ : M6.Physical.Block N, M6.Spaces.boundary N (M6.Coordinates.coefficients N a) (M6.Coordinates.coefficients N b) h = M6.Spaces.boundary N (M6.Coordinates.coefficients N a) (M6.Coordinates.coefficients N b) h₀ ↔ M6.BoundaryFibers.boundary a b (M6.Cyclic.modulus N) (M6.Coordinates.encode N h) = M6.BoundaryFibers.boundary a b (M6.Cyclic.modulus N) (M6.Coordinates.encode N h₀) := by
  intro N inst a b ha hb h h₀
  have hf : Function.Injective (M6.Flatten.flatten N) := by
    intro z w e
    have e' := congrArg (M6.Flatten.unflatten N) e
    simpa only [M6.Flatten.flatten_left] using e'
  rw [← M6.ActualCounts.encoded_boundary N a b ha hb h,
      ← M6.ActualCounts.encoded_boundary N a b ha hb h₀]
  simp only [M6.Spaces.boundary_eval, hf.eq_iff,
    M6.Physical.boundary, Prod.mk.injEq,
    (M6.Coordinates.encode_injective N).eq_iff]

theorem M6.ActualCounts.boundary_fiber_card : ∀ (N : ℕ) [NeZero N] (a b : M6.ActualCounts.BP), a.degree < (N : WithBot ℕ) → b.degree < (N : WithBot ℕ) → ∀ h₀ : M6.Physical.Block N, Nat.card {h : M6.Physical.Block N // M6.Spaces.boundary N (M6.Coordinates.coefficients N a) (M6.Coordinates.coefficients N b) h = M6.Spaces.boundary N (M6.Coordinates.coefficients N a) (M6.Coordinates.coefficients N b) h₀} = 2^(M6.ActualCounts.f N a b) := by
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
def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N] (a b : M6.ActualCounts.BP), a.degree < (N : WithBot ℕ) → b.degree < (N : WithBot ℕ) → ∀ w : M6.Pinned.Vector (2*N) → Polynomial ℤ, (∑ h : M6.Physical.Block N, w (M6.Spaces.boundary N (M6.Coordinates.coefficients N a) (M6.Coordinates.coefficients N b) h)) = Polynomial.C ((2 : ℤ)^(M6.ActualCounts.f N a b)) * ∑ v ∈ M6.Spaces.boundaryWords N (M6.Coordinates.coefficients N a) (M6.Coordinates.coefficients N b), w v
