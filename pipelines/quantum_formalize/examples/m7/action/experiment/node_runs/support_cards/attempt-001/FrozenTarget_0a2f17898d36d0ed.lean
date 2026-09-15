import M7Action

theorem M7.Action.affine_bijective : ∀ (N : ℕ) [NeZero N], ∀ (u : (ZMod N)ˣ) (s : ZMod N), Function.Bijective (M7.Action.affine u s) := by
  change ∀ (N : ℕ) [NeZero N] (u : (ZMod N)ˣ) (s : ZMod N), Function.Bijective (M7.Action.affine u s)
  intro N inst u s
  constructor
  · intro a b h
    change (u : ZMod N) * a + s = (u : ZMod N) * b + s at h
    have h' := congrArg (fun x : ZMod N => (↑(u⁻¹) : ZMod N) * x) (add_right_cancel h)
    simpa [← mul_assoc] using h'
  · intro y
    refine ⟨(↑(u⁻¹) : ZMod N) * (y - s), ?_⟩
    simp [M7.Action.affine, ← mul_assoc]
def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N], ∀ (g : M7.Action.Record N) (c : M7.Action.Recipe N), (M7.Action.act g c).1.card = (if g.exchange then c.2.card else c.1.card) ∧ (M7.Action.act g c).2.card = (if g.exchange then c.1.card else c.2.card)
