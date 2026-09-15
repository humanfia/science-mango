import FrozenTarget_fdcf580d4ec89c34
theorem M7.Connectivity.finite_generation_gcd : QuantumHarnessFrozenTarget := by
  change ∀ (N : ℕ) [NeZero N] (S : Finset ℕ), AddSubgroup.closure ((fun a : ℕ => (a : ZMod N)) '' (S : Set ℕ)) = ⊤ ↔ Nat.gcd N (S.gcd id) = 1
  intro N inst S
  let g : ℕ := S.gcd id
  let H : AddSubgroup (ZMod N) := AddSubgroup.closure ((fun a : ℕ => (a : ZMod N)) '' (S : Set ℕ))
  change H = ⊤ ↔ Nat.gcd N g = 1
  have hg : (g : ZMod N) ∈ H := by
    apply M7.Connectivity.gcd_mem N H S
    intro a ha
    exact AddSubgroup.subset_closure ⟨a, ha, rfl⟩
  constructor
  · intro htop
    let K : AddSubgroup (ZMod N) :=
      { carrier := {x | ∃ r : ZMod N, (g : ZMod N) * r = x}
        zero_mem' := ⟨0, mul_zero _⟩
        add_mem' := by
          rintro x y ⟨r, hr⟩ ⟨s, hs⟩
          exact ⟨r + s, by rw [mul_add, hr, hs]⟩
        neg_mem' := by
          rintro x ⟨r, hr⟩
          exact ⟨-r, by rw [mul_neg, hr]⟩ }
    have hle : H ≤ K := by
      apply AddSubgroup.closure_le.mpr
      rintro x ⟨a, ha, rfl⟩
      have hd : g ∣ a := by
        dsimp [g]
        first
        | exact Finset.gcd_dvd ha
        | exact Finset.gcd_dvd (f := id) ha
        | exact Finset.gcd_dvd id ha
      obtain ⟨k, hk⟩ := hd
      refine ⟨(k : ZMod N), ?_⟩
      simpa only [Nat.cast_mul] using congrArg (fun t : ℕ => (t : ZMod N)) hk.symm
    have h1 : (1 : ZMod N) ∈ K := hle ((M7.Connectivity.one_mem_top N H).mpr htop)
    obtain ⟨r, hr⟩ := h1
    have hu : IsUnit (g : ZMod N) := by
      refine ⟨⟨(g : ZMod N), r, hr, ?_⟩, rfl⟩
      rw [mul_comm]
      exact hr
    have hc := (ZMod.isUnit_iff_coprime g N).mp hu
    simpa only [Nat.coprime_iff_gcd_eq_one, Nat.gcd_comm] using hc
  · intro h
    have hc : g.Coprime N := by
      rw [Nat.coprime_iff_gcd_eq_one, Nat.gcd_comm]
      exact h
    obtain ⟨u, hu⟩ := (ZMod.isUnit_iff_coprime g N).mpr hc
    apply (M7.Connectivity.one_mem_top N H).mp
    have hm := M7.Connectivity.scalar_mem N H (g : ZMod N) (↑(u⁻¹) : ZMod N) hg
    simpa [← hu] using hm
