import FrozenTarget_adcd1f2a3b77dc51
theorem M8.ExclusionGeometry.pair_span : QuantumHarnessFrozenTarget := by
  intro N inst h B hN hB
  rcases hB with ⟨x, hx, hxh⟩
  by_cases hhx : h ≤ x.val
  · exact hhx.trans (Finset.le_sup (f := ZMod.val) hx)
  · have hsum : x.val + h < N := by omega
    have hhN : h < N := by omega
    have hv : (x + (h : ZMod N)).val = x.val + h := by
      rw [ZMod.val_add, ZMod.val_natCast, Nat.mod_eq_of_lt hhN,
        Nat.mod_eq_of_lt hsum]
    have hbound : (x + (h : ZMod N)).val ≤ B.sup ZMod.val :=
      Finset.le_sup (f := ZMod.val) hxh
    rw [hv] at hbound
    omega
