import M8CoverageFoundation

theorem M8.CoverageFoundation.affine_full : ∀ (N : ℕ) [NeZero N], ∀ (A : Finset (ZMod N)) (u : (ZMod N)ˣ) (s : ZMod N), M8.CoverageFoundation.FullDirection (A.image (M7.Action.affine u s)) ↔ M8.CoverageFoundation.FullDirection A := by
  intro N inst A u s
  simpa [M8.CoverageFoundation.FullDirection, M8.CoverageFoundation.direction,
    M7.Connectivity.connected, M7.Action.act] using
    (M7.Connectivity.connected_action N (⟨u, false, s, s⟩ : M7.Action.Record N) (A, A))

theorem M8.CoverageFoundation.consecutive_full : ∀ (N : ℕ) [NeZero N], ∀ (A : Finset (ZMod N)) (a : ZMod N), a ∈ A → a+1 ∈ A → M8.CoverageFoundation.FullDirection A := by
  intro N inst A a ha ha1
  change AddSubgroup.closure (M7.Connectivity.differences A) = ⊤
  apply (M7.Connectivity.one_mem_top N _).mp
  apply AddSubgroup.subset_closure
  unfold M7.Connectivity.differences
  refine ⟨a + 1, ha1, a, ha, ?_⟩
  simp [add_comm]

theorem M8.CoverageFoundation.proper_multiples : ∀ (N : ℕ) [NeZero N], ∀ q : ℕ, 2 ≤ q → q ∣ N → AddSubgroup.zmultiples (q : ZMod N) ≠ ⊤ := by
  change ∀ (N : ℕ) [NeZero N], ∀ q : ℕ, 2 ≤ q → q ∣ N → AddSubgroup.zmultiples (q : ZMod N) ≠ ⊤
  intro N inst q hq hdiv htop
  have hg : Nat.gcd N q = 1 := by
    have h := (M7.Connectivity.finite_generation_gcd N ({q} : Finset ℕ)).mp (by
      simpa [AddSubgroup.zmultiples_eq_closure] using htop)
    simpa using h
  have hd : q ∣ Nat.gcd N q := Nat.dvd_gcd hdiv (dvd_refl q)
  rw [hg] at hd
  have hl : q ≤ 1 := Nat.le_of_dvd (by decide) hd
  omega
#print axioms M8.CoverageFoundation.affine_full
#print axioms M8.CoverageFoundation.consecutive_full
#print axioms M8.CoverageFoundation.proper_multiples
