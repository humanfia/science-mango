import FrozenTarget_1a357cb2e2049c17
theorem M8.Diagonal.weight_zero : QuantumHarnessFrozenTarget := by
  classical
  intro N inst a
  change (Finset.univ.filter (fun i : ZMod N => a i ≠ 0)).card = 0 ↔ a = 0
  constructor
  · intro h
    have hempty := Finset.card_eq_zero.mp h
    funext i
    change a i = 0
    by_contra hi
    have hmem : i ∈ Finset.univ.filter (fun j : ZMod N => a j ≠ 0) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩
    simp [hempty] at hmem
  · rintro rfl
    simp
