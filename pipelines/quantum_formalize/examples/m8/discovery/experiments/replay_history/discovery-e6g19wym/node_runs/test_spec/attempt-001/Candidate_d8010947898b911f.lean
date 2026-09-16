import FrozenTarget_d8010947898b911f
theorem M8.Discovery.test_spec : QuantumHarnessFrozenTarget := by
    classical
    change ∀ (N : ℕ) [NeZero N] (c : M7.Action.Recipe N), ∀ k : M8.Discovery.Choice N, M8.Discovery.test c k = true ↔ M8.Discovery.Good c k
    intro N inst c k
    have hv (i : ZMod N) (a : Fin N) : i.val = a.val ↔ i = (a.val : ZMod N) := by
      constructor
      · intro h
        calc
          i = (i.val : ZMod N) := (ZMod.natCast_zmod_val i).symm
          _ = (a.val : ZMod N) := congrArg (fun n : ℕ => (n : ZMod N)) h
      · intro h
        subst i
        simp [ZMod.val_natCast, Nat.mod_eq_of_lt a.isLt]
    have hm (s : Finset (ZMod N)) (a : Fin N) :
        s.sup (fun i => if i.val == a.val then (1 : ℕ) else 0) = 1 ↔
          (a.val : ZMod N) ∈ s := by
      have hs : s.sup (fun i => if i.val == a.val then (1 : ℕ) else 0) =
          if (a.val : ZMod N) ∈ s then 1 else 0 := by
        induction s using Finset.induction_on with
        | empty => simp
        | @insert i s hi ih =>
          by_cases hia : i = (a.val : ZMod N)
          · by_cases ha : (a.val : ZMod N) ∈ s <;>
              simp [Finset.sup_insert, ih, hv, hia, ha]
          · by_cases ha : (a.val : ZMod N) ∈ s <;>
              simp [Finset.sup_insert, ih, hv, hia, ha, eq_comm]
      rw [hs]
      split_ifs <;> simp_all
    have hg : Nat.gcd k.unitIndex.val N = 1 ↔ IsUnit (k.unitIndex.val : ZMod N) := by
      first
      | simpa only [Nat.coprime_iff_gcd_eq_one] using
          (ZMod.isUnit_iff_coprime k.unitIndex.val N).symm
      | simpa [ZMod.val_natCast, Nat.mod_eq_of_lt k.unitIndex.isLt,
          Nat.coprime_iff_gcd_eq_one] using
          (ZMod.isUnit_iff_val_coprime (k.unitIndex.val : ZMod N)).symm
    unfold M8.Discovery.test
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
    rw [hg, hm, hm]
    by_cases hu : IsUnit (k.unitIndex.val : ZMod N)
    · have huval : (M8.Discovery.unit k : ZMod N) = (k.unitIndex.val : ZMod N) := by
        simp [M8.Discovery.unit, hu, IsUnit.unit_spec]
      have hs : M8.Anchor.span (M8.Discovery.transformed c k) =
          max
            ((M8.Anchor.left c k.exchange).sup (fun i =>
              ((k.unitIndex.val : ZMod N) * (i - (k.leftAnchor.val : ZMod N))).val))
            ((M8.Anchor.right c k.exchange).sup (fun i =>
              ((k.unitIndex.val : ZMod N) * (i - (k.rightAnchor.val : ZMod N))).val)) := by
        change M8.Anchor.span (M8.Anchor.trial c k.exchange (M8.Discovery.unit k)
          (k.leftAnchor.val : ZMod N) (k.rightAnchor.val : ZMod N)) = _
        rw [M8.Anchor.trial_formula]
        simp [M8.Anchor.span, Finset.sup_image, huval, Function.comp_def]
      simp [M8.Discovery.Good, M8.Anchor.Eligible, hu, hs, and_assoc]
    · simp [M8.Discovery.Good, hu]
