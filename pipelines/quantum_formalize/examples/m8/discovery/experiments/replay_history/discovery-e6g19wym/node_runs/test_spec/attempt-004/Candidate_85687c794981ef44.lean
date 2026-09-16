import FrozenTarget_85687c794981ef44
theorem M8.Discovery.test_spec : QuantumHarnessFrozenTarget := by
  intro N inst c k
  classical
  have hv (i : ZMod N) (a : Fin N) : i.val = a.val ↔ i = (a.val : ZMod N) := by
    constructor
    · intro h
      rw [← ZMod.natCast_zmod_val i, h]
    · intro h
      rw [h, ZMod.val_natCast, Nat.mod_eq_of_lt a.isLt]
  have hs (s : Finset (ZMod N)) (a : ZMod N) :
      s.sup (fun i => if i = a then (1 : ℕ) else 0) = if a ∈ s then 1 else 0 := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih =>
      by_cases hia : i = a
      · subst i
        by_cases ha : a ∈ s <;> simp_all
      · by_cases ha : a ∈ s <;> simp_all
  have hm (s : Finset (ZMod N)) (a : Fin N) :
      s.sup (fun i => if i.val = a.val then (1 : ℕ) else 0) = 1 ↔
        (a.val : ZMod N) ∈ s := by
    simp only [hv]
    rw [hs]
    split_ifs <;> simp_all
  have hg : Nat.gcd k.unitIndex.val N = 1 ↔ IsUnit (k.unitIndex.val : ZMod N) := by
    rw [ZMod.isUnit_iff_coprime, Nat.coprime_iff_gcd_eq_one]
  simp only [M8.Discovery.test, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
  rw [hg, hm, hm]
  unfold M8.Discovery.Good
  by_cases hu : IsUnit (k.unitIndex.val : ZMod N)
  · have hunit : (M8.Discovery.unit k : ZMod N) = (k.unitIndex.val : ZMod N) := by
      simp [M8.Discovery.unit, hu, IsUnit.unit_spec]
    have hspan : M8.Anchor.span (M8.Discovery.transformed c k) =
        max
          ((M8.Anchor.left c k.exchange).sup (fun i =>
            ((k.unitIndex.val : ZMod N) * (i - (k.leftAnchor.val : ZMod N))).val))
          ((M8.Anchor.right c k.exchange).sup (fun i =>
            ((k.unitIndex.val : ZMod N) * (i - (k.rightAnchor.val : ZMod N))).val)) := by
      change M8.Anchor.span (M8.Anchor.trial c k.exchange (M8.Discovery.unit k)
        (k.leftAnchor.val : ZMod N) (k.rightAnchor.val : ZMod N)) = _
      rw [M8.Anchor.trial_formula]
      simp [M8.Anchor.span, Finset.sup_image, Function.comp_def, hunit]
    rw [hspan]
    simp [hu, M8.Anchor.Eligible, and_assoc]
  · simp [hu]
