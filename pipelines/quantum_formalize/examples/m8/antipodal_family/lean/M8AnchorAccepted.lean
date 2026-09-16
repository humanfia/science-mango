import M8Anchor

theorem M8.Anchor.anchored : ∀ (N : ℕ) [NeZero N] (c : M8.Anchor.Recipe N) (e : Bool) (u : (ZMod N)ˣ) (a b : ZMod N), M8.Anchor.Eligible c e a b → M8.Anchor.Anchored (M8.Anchor.trial c e u a b) := by
  intro N _ c e u a b h
  cases e <;> simp only [M8.Anchor.Eligible, M8.Anchor.left, M8.Anchor.right, Bool.false_eq_true, if_false, if_true] at h
  all_goals
    rcases h with ⟨ha, hb⟩
    dsimp [M8.Anchor.Anchored, M8.Anchor.trial, M8.Anchor.record, M7.Action.act]
    constructor
  all_goals
    first
    | exact Finset.mem_image.mpr ⟨a, ha, by simp [M7.Action.affine]⟩
    | exact Finset.mem_image.mpr ⟨b, hb, by simp [M7.Action.affine]⟩

theorem M8.Anchor.inverse_trial : ∀ (N : ℕ) [NeZero N] (c : M8.Anchor.Recipe N) (e : Bool) (u : (ZMod N)ˣ) (a b : ZMod N), M7.Action.act (M7.Action.inverse (M8.Anchor.record e u a b)) (M8.Anchor.trial c e u a b) = c := by
  intro N inst c e u a b
  exact M7.Action.act_inverse N (M8.Anchor.record e u a b) c

theorem M8.Anchor.record_injective : ∀ (N : ℕ) [NeZero N] (e : Bool) (u : (ZMod N)ˣ) (a b a1 b1 : ZMod N), M8.Anchor.record e u a b = M8.Anchor.record e u a1 b1 → a = a1 ∧ b = b1 := by
  intro N _ e u a b a1 b1 h
  have ha := congrArg M7.Action.Record.leftShift h
  have hb := congrArg M7.Action.Record.rightShift h
  change -((u : ZMod N) * a) = -((u : ZMod N) * a1) at ha
  change -((u : ZMod N) * b) = -((u : ZMod N) * b1) at hb
  constructor
  · have h' := congrArg (fun x : ZMod N => (↑(u⁻¹) : ZMod N) * (-x)) ha
    simpa [← mul_assoc] using h'
  · have h' := congrArg (fun x : ZMod N => (↑(u⁻¹) : ZMod N) * (-x)) hb
    simpa [← mul_assoc] using h'

theorem M8.Anchor.span_le : ∀ (N : ℕ) [NeZero N] (c : M8.Anchor.Recipe N) (L : ℕ), M8.Anchor.span c ≤ L ↔ (∀ i ∈ c.1, i.val ≤ L) ∧ (∀ i ∈ c.2, i.val ≤ L) := by
  intro N inst c L
  simp only [M8.Anchor.span, max_le_iff, Finset.sup_le_iff]

theorem M8.Anchor.span_lt_order : ∀ (N : ℕ) [NeZero N] (c : M8.Anchor.Recipe N), M8.Anchor.span c < N := by
  change ∀ (N : ℕ) [NeZero N] (c : M8.Anchor.Recipe N), M8.Anchor.span c < N
  intro N inst c
  have hN : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  unfold M8.Anchor.span
  apply max_lt_iff.mpr
  constructor
  all_goals
    apply (Finset.sup_lt_iff hN).mpr
    intro a ha
    exact ZMod.val_lt a

theorem M8.Anchor.translation_reconstruction : ∀ (N : ℕ) [NeZero N] (c : M8.Anchor.Recipe N) (g : M7.Action.Record N), M8.Anchor.Anchored (M7.Action.act g c) → ∃ a b : ZMod N, M8.Anchor.Eligible c g.exchange a b ∧ M8.Anchor.record g.exchange g.unit a b = g := by
  intro N inst c g h
  classical
  rcases g with ⟨u, e, s, t⟩
  cases e <;> simp [M8.Anchor.Anchored, M7.Action.act, M7.Action.affine, Finset.mem_image] at h
  all_goals
    rcases h with ⟨⟨a, ha, hsa⟩, ⟨b, hb, htb⟩⟩
    have hs : -((u : ZMod N) * a) = s := by
      linear_combination -hsa
    have ht : -((u : ZMod N) * b) = t := by
      linear_combination -htb
    refine ⟨a, b, ?_, ?_⟩
    · exact ⟨ha, hb⟩
    · simp [M8.Anchor.record, hs, ht]

theorem M8.Anchor.trial_formula : ∀ (N : ℕ) [NeZero N] (c : M8.Anchor.Recipe N) (e : Bool) (u : (ZMod N)ˣ) (a b : ZMod N), M8.Anchor.trial c e u a b = ((M8.Anchor.left c e).image (fun i => (u : ZMod N)*(i-a)), (M8.Anchor.right c e).image (fun i => (u : ZMod N)*(i-b))) := by
  intro N inst c e u a b
  cases e <;> simp [M8.Anchor.trial, M8.Anchor.record, M8.Anchor.left, M8.Anchor.right, M7.Action.act] <;> constructor <;> congr 1 <;> funext i <;> dsimp [M7.Action.affine] <;> ring

theorem M8.Anchor.passing_presentations : ∀ (N : ℕ) [NeZero N] (c : M8.Anchor.Recipe N) (L : ℕ), (∃ (e : Bool) (u : (ZMod N)ˣ) (a b : ZMod N), M8.Anchor.Eligible c e a b ∧ M8.Anchor.span (M8.Anchor.trial c e u a b) ≤ L) ↔ ∃ g : M7.Action.Record N, M8.Anchor.Anchored (M7.Action.act g c) ∧ M8.Anchor.span (M7.Action.act g c) ≤ L := by
  intro N inst c L
  constructor
  · rintro ⟨e, u, a, b, hEligible, hSpan⟩
    refine ⟨M8.Anchor.record e u a b, ?_, hSpan⟩
    exact M8.Anchor.anchored N c e u a b hEligible
  · rintro ⟨g, hAnchored, hSpan⟩
    rcases M8.Anchor.translation_reconstruction N c g hAnchored with ⟨a, b, hEligible, hRecord⟩
    refine ⟨g.exchange, g.unit, a, b, hEligible, ?_⟩
    simpa only [M8.Anchor.trial, hRecord] using hSpan
#print axioms M8.Anchor.anchored
#print axioms M8.Anchor.inverse_trial
#print axioms M8.Anchor.record_injective
#print axioms M8.Anchor.span_le
#print axioms M8.Anchor.span_lt_order
#print axioms M8.Anchor.translation_reconstruction
#print axioms M8.Anchor.passing_presentations
#print axioms M8.Anchor.trial_formula
