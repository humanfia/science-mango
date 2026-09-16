import FrozenTarget_7d3f2d844faea270
theorem M8.Discovery.test_spec : QuantumHarnessFrozenTarget := by
  classical
  intro N inst c k
  have hv : ∀ (i : ZMod N) (a : Fin N), i.val = a.val ↔ i = (a.val : ZMod N) := by
    intro i a
    constructor
    · intro h
      calc
        i = (i.val : ZMod N) := (ZMod.natCast_zmod_val i).symm
        _ = (a.val : ZMod N) := congrArg (fun n : ℕ => (n : ZMod N)) h
    · intro h
      subst i
      simp [ZMod.val_natCast, Nat.mod_eq_of_lt a.isLt]
  have hind : ∀ (s : Finset (ZMod N)) (a : ZMod N),
      s.sup (fun i => if i = a then (1 : ℕ) else 0) = if a ∈ s then 1 else 0 := by
    intro s a
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih =>
      by_cases hia : i = a
      · subst i
        simp [Finset.sup_insert, ih]
      · by_cases ha : a ∈ s
        · simp [Finset.sup_insert, ih, hia, ha]
        · simp [Finset.sup_insert, ih, hia, ha, Ne.symm hia]
  have hm : ∀ (s : Finset (ZMod N)) (a : Fin N),
      (s.sup (fun i => if i.val == a.val then (1 : ℕ) else 0) = 1) ↔
        (a.val : ZMod N) ∈ s := by
    intro s a
    simp only [beq_iff_eq, hv]
    rw [hind]
    by_cases h : (a.val : ZMod N) ∈ s <;> simp [h]
  have hg : Nat.gcd k.unitIndex.val N = 1 ↔ IsUnit (k.unitIndex.val : ZMod N) := by
    rw [ZMod.isUnit_iff_coprime, Nat.coprime_iff_gcd_eq_one]
  change M8.Discovery.test c k = true ↔ M8.Discovery.Good c k
  simp only [M8.Discovery.test, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
  rw [hg]
  have hm' : ∀ (s : Finset (ZMod N)) (a : Fin N),
      (s.sup (fun i => if i.val = a.val then (1 : ℕ) else 0) = 1) ↔
        (a.val : ZMod N) ∈ s := by
    intro s a
    simpa only [beq_iff_eq] using hm s a
  rw [hm', hm']
  by_cases hu : IsUnit (k.unitIndex.val : ZMod N)
  · have huval : (M8.Discovery.unit k : ZMod N) = (k.unitIndex.val : ZMod N) := by
      simpa only [M8.Discovery.unit, dif_pos hu] using hu.unit_spec
    have hf : M8.Discovery.transformed c k =
        ((M8.Anchor.left c k.exchange).image (fun i => (k.unitIndex.val : ZMod N) * (i - (k.leftAnchor.val : ZMod N))),
         (M8.Anchor.right c k.exchange).image (fun i => (k.unitIndex.val : ZMod N) * (i - (k.rightAnchor.val : ZMod N)))) := by
      change M8.Anchor.trial c k.exchange (M8.Discovery.unit k)
        (k.leftAnchor.val : ZMod N) (k.rightAnchor.val : ZMod N) = _
      rw [M8.Anchor.trial_formula, huval]
    simp only [M8.Discovery.Good, M8.Anchor.Eligible, hf, M8.Anchor.span,
      Finset.sup_image, Function.comp_def]
    tauto
  · simp [M8.Discovery.Good, hu]
