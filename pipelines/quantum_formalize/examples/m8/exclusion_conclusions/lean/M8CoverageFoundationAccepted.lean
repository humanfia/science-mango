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

theorem M8.CoverageFoundation.coset_direction : ∀ (N : ℕ) [NeZero N], ∀ (A : Finset (ZMod N)) (H : AddSubgroup (ZMod N)), M8.CoverageFoundation.InCoset A H → M8.CoverageFoundation.direction A ≤ H := by
  intro N inst A H hA
  rcases hA with ⟨a, ha⟩
  change AddSubgroup.closure (M7.Connectivity.differences A) ≤ H
  apply (AddSubgroup.closure_le H).2
  intro z hz
  rcases hz with ⟨x, hx, y, hy, rfl⟩
  change x - y ∈ H
  have he : x - y = (x - a) - (y - a) := by abel
  rw [he]
  exact H.sub_mem (ha x hx) (ha y hy)

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

theorem M8.CoverageFoundation.no_separated : ∀ (N : ℕ) [NeZero N], ∀ c : M7.Action.Recipe N, (M8.CoverageFoundation.FullDirection c.1 ∨ M8.CoverageFoundation.FullDirection c.2) → ¬ M8.CoverageFoundation.Separated c := by
  change ∀ (N : ℕ) [NeZero N], ∀ c : M7.Action.Recipe N, (M8.CoverageFoundation.FullDirection c.1 ∨ M8.CoverageFoundation.FullDirection c.2) → ¬ M8.CoverageFoundation.Separated c
  intro N inst c hfull hsep
  rcases hsep with ⟨m, q, hm, hq, hN, hcop, hA, hB⟩
  rcases hfull with hAfull | hBfull
  · have hdiv : q ∣ N := ⟨m, by simpa [Nat.mul_comm] using hN⟩
    have hle := M8.CoverageFoundation.coset_direction N c.1 (AddSubgroup.zmultiples (q : ZMod N)) hA
    change M8.CoverageFoundation.direction c.1 = ⊤ at hAfull
    rw [hAfull] at hle
    exact M8.CoverageFoundation.proper_multiples N q hq hdiv (le_antisymm le_top hle)
  · have hdiv : m ∣ N := ⟨q, hN⟩
    have hle := M8.CoverageFoundation.coset_direction N c.2 (AddSubgroup.zmultiples (m : ZMod N)) hB
    change M8.CoverageFoundation.direction c.2 = ⊤ at hBfull
    rw [hBfull] at hle
    exact M8.CoverageFoundation.proper_multiples N m hm hdiv (le_antisymm le_top hle)

theorem M8.CoverageFoundation.orbit_no_separated : ∀ (N : ℕ) [NeZero N], ∀ (c : M7.Action.Recipe N) (g : M7.Action.Record N), (M8.CoverageFoundation.FullDirection c.1 ∨ M8.CoverageFoundation.FullDirection c.2) → ¬ M8.CoverageFoundation.Separated (M7.Action.act g c) := by
  change ∀ (N : ℕ) [NeZero N], ∀ (c : M7.Action.Recipe N) (g : M7.Action.Record N), (M8.CoverageFoundation.FullDirection c.1 ∨ M8.CoverageFoundation.FullDirection c.2) → ¬ M8.CoverageFoundation.Separated (M7.Action.act g c)
  intro N inst c g hfull
  apply M8.CoverageFoundation.no_separated N (M7.Action.act g c)
  rcases g with ⟨u, exchange, s, t⟩
  cases exchange <;>
    simpa [M7.Action.act, M8.CoverageFoundation.affine_full, or_comm] using hfull
#print axioms M8.CoverageFoundation.affine_full
#print axioms M8.CoverageFoundation.consecutive_full
#print axioms M8.CoverageFoundation.coset_direction
#print axioms M8.CoverageFoundation.proper_multiples
#print axioms M8.CoverageFoundation.no_separated
#print axioms M8.CoverageFoundation.orbit_no_separated
