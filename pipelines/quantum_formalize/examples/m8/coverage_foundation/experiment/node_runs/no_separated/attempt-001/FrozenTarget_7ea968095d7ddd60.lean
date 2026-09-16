import M8CoverageFoundation

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
def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N], ∀ c : M7.Action.Recipe N, (M8.CoverageFoundation.FullDirection c.1 ∨ M8.CoverageFoundation.FullDirection c.2) → ¬ M8.CoverageFoundation.Separated c
