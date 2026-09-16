import FrozenTarget_4bfd5a374a8865df
theorem M8.Discovery.test_spec : QuantumHarnessFrozenTarget := by
    classical
    intro N _ c k
    have hv (i : ZMod N) (a : Fin N) : i.val = a.val ↔ i = (a.val : ZMod N) := by
      constructor
      · intro h
        rw [← ZMod.natCast_zmod_val i, h]
      · intro h
        subst i
        simp [ZMod.val_natCast, Nat.mod_eq_of_lt a.isLt]
    have hs (s : Finset (ZMod N)) (a : ZMod N) :
        s.sup (fun i => if i = a then (1 : ℕ) else 0) =
          if a ∈ s then 1 else 0 := by
      induction s using Finset.induction_on with
      | empty => simp
      | @insert i s hi ih =>
        by_cases hia : i = a <;> by_cases ha : a ∈ s <;>
          simp_all [Finset.sup_insert, eq_comm]
    have hg : Nat.gcd k.unitIndex.val N = 1 ↔
        IsUnit (k.unitIndex.val : ZMod N) := by
      simpa [Nat.Coprime, ZMod.val_natCast,
        Nat.mod_eq_of_lt k.unitIndex.isLt] using
        (ZMod.isUnit_iff_coprime k.unitIndex.val N).symm
    by_cases hu : IsUnit (k.unitIndex.val : ZMod N)
    · have hc : (M8.Discovery.unit k : ZMod N) = (k.unitIndex.val : ZMod N) := by
        simpa only [M8.Discovery.unit, dif_pos hu] using hu.unit_spec
      have ht : M8.Anchor.span (M8.Discovery.transformed c k) =
          max
            ((M8.Anchor.left c k.exchange).sup (fun i =>
              (((k.unitIndex.val : ZMod N) * (i - (k.leftAnchor.val : ZMod N))).val)))
            ((M8.Anchor.right c k.exchange).sup (fun i =>
              (((k.unitIndex.val : ZMod N) * (i - (k.rightAnchor.val : ZMod N))).val))) := by
        change M8.Anchor.span (M8.Anchor.trial c k.exchange
          (M8.Discovery.unit k) (k.leftAnchor.val : ZMod N)
          (k.rightAnchor.val : ZMod N)) = _
        rw [M8.Anchor.trial_formula]
        simp [M8.Anchor.span, Finset.sup_image, Function.comp_def, hc]
      simp [M8.Discovery.test, M8.Discovery.Good, M8.Anchor.Eligible,
        hv, hs, hg, hu, ht, and_assoc]
    · simp [M8.Discovery.test, M8.Discovery.Good, hg, hu]
