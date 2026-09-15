import M7Action

theorem M7.Action.act_compose : ∀ (N : ℕ) [NeZero N], ∀ (g h : M7.Action.Record N) (c : M7.Action.Recipe N), M7.Action.act (M7.Action.compose g h) c = M7.Action.act g (M7.Action.act h c) := by
  intro N inst g h c
  classical
  have ha (u v : (ZMod N)ˣ) (a s : ZMod N) :
      M7.Action.affine (u * v) ((u : ZMod N) * a + s) =
        fun x => M7.Action.affine u s (M7.Action.affine v a x) := by
    funext x
    simp only [M7.Action.affine, Units.val_mul]
    ring
  rcases g with ⟨u, e, s, t⟩
  rcases h with ⟨v, f, a, b⟩
  cases e <;> cases f <;>
    simp [M7.Action.act, M7.Action.compose, ha, Finset.image_image, Function.comp_def]

theorem M7.Action.act_identity : ∀ (N : ℕ) [NeZero N], ∀ c : M7.Action.Recipe N, M7.Action.act (M7.Action.identity N) c = c := by
  change ∀ (N : ℕ) [NeZero N], ∀ c : M7.Action.Recipe N, M7.Action.act (M7.Action.identity N) c = c
  intro N inst c
  have h : M7.Action.affine (1 : (ZMod N)ˣ) (0 : ZMod N) = id := by
    funext i
    simp [M7.Action.affine]
  rcases c with ⟨s, t⟩
  simp [M7.Action.act, M7.Action.identity, h]

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

theorem M7.Action.associative : ∀ (N : ℕ) [NeZero N], ∀ g h k : M7.Action.Record N, M7.Action.compose (M7.Action.compose g h) k = M7.Action.compose g (M7.Action.compose h k) := by
  change ∀ (N : ℕ) [NeZero N], ∀ g h k : M7.Action.Record N, M7.Action.compose (M7.Action.compose g h) k = M7.Action.compose g (M7.Action.compose h k)
  intro N inst g h k
  rcases g with ⟨u, e, a, b⟩
  rcases h with ⟨v, f, c, d⟩
  rcases k with ⟨w, q, s, t⟩
  cases e <;> cases f <;> cases q <;>
    simp [M7.Action.compose, mul_add, mul_assoc, add_assoc]

theorem M7.Action.left_identity : ∀ (N : ℕ) [NeZero N], ∀ g : M7.Action.Record N, M7.Action.compose (M7.Action.identity N) g = g := by
  change ∀ (N : ℕ) [NeZero N], ∀ g : M7.Action.Record N, M7.Action.compose (M7.Action.identity N) g = g
  intro N inst g
  rcases g with ⟨u, e, l, r⟩
  cases e <;> simp [M7.Action.compose, M7.Action.identity]

theorem M7.Action.left_inverse : ∀ (N : ℕ) [NeZero N], ∀ g : M7.Action.Record N, M7.Action.compose (M7.Action.inverse g) g = M7.Action.identity N := by
  change ∀ (N : ℕ) [NeZero N], ∀ g : M7.Action.Record N, M7.Action.compose (M7.Action.inverse g) g = M7.Action.identity N
  intro N inst g
  rcases g with ⟨u, e, s, t⟩
  cases e <;> simp [M7.Action.compose, M7.Action.inverse, M7.Action.identity]

theorem M7.Action.normal_form : ∀ (N : ℕ) [NeZero N], ∀ g : M7.Action.Record N, M7.Action.compose (M7.Action.translate g.leftShift g.rightShift) (M7.Action.compose (M7.Action.multiplier g.unit) (if g.exchange then M7.Action.exchange N else M7.Action.identity N)) = g := by
  let QuantumHarnessFrozenTarget : Prop := (
    ∀ (N : ℕ) [NeZero N], ∀ g : M7.Action.Record N, M7.Action.compose (M7.Action.translate g.leftShift g.rightShift) (M7.Action.compose (M7.Action.multiplier g.unit) (if g.exchange then M7.Action.exchange N else M7.Action.identity N)) = g
  )
  change QuantumHarnessFrozenTarget
  unfold QuantumHarnessFrozenTarget
  intro N inst g
  rcases g with ⟨u, b, s, t⟩
  cases b <;> simp [M7.Action.compose, M7.Action.translate, M7.Action.multiplier, M7.Action.exchange, M7.Action.identity]

theorem M7.Action.record_card : ∀ (N : ℕ) [NeZero N], Fintype.card (M7.Action.Record N) = Nat.totient N * 2 * N * N := by
  change ∀ (N : ℕ) [NeZero N], Fintype.card (M7.Action.Record N) = Nat.totient N * 2 * N * N
  intro N hN
  let e : M7.Action.Record N ≃ (ZMod N)ˣ × Bool × ZMod N × ZMod N :=
    { toFun := fun g => (g.unit, g.exchange, g.leftShift, g.rightShift)
      invFun := fun p => ⟨p.1, p.2.1, p.2.2.1, p.2.2.2⟩
      left_inv := by intro g; cases g; rfl
      right_inv := by intro p; rcases p with ⟨u, b, s, t⟩; rfl }
  rw [Fintype.card_congr e]
  simp [Fintype.card_prod, ZMod.card_units_eq_totient, ZMod.card, Nat.mul_assoc]

theorem M7.Action.right_identity : ∀ (N : ℕ) [NeZero N], ∀ g : M7.Action.Record N, M7.Action.compose g (M7.Action.identity N) = g := by
  intro N inst g
  change M7.Action.compose g (M7.Action.identity N) = g
  rcases g with ⟨u, b, s, t⟩
  cases b <;> simp [M7.Action.compose, M7.Action.identity]

theorem M7.Action.right_inverse : ∀ (N : ℕ) [NeZero N], ∀ g : M7.Action.Record N, M7.Action.compose g (M7.Action.inverse g) = M7.Action.identity N := by
  change ∀ (N : ℕ) [NeZero N], ∀ g : M7.Action.Record N, M7.Action.compose g (M7.Action.inverse g) = M7.Action.identity N
  intro N inst g
  rcases g with ⟨u, e, s, t⟩
  cases e <;> simp [M7.Action.compose, M7.Action.inverse, M7.Action.identity, mul_neg, ← mul_assoc]

theorem M7.Action.act_inverse : ∀ (N : ℕ) [NeZero N], ∀ (g : M7.Action.Record N) (c : M7.Action.Recipe N), M7.Action.act (M7.Action.inverse g) (M7.Action.act g c) = c := by
  change ∀ (N : ℕ) [NeZero N], ∀ (g : M7.Action.Record N) (c : M7.Action.Recipe N), M7.Action.act (M7.Action.inverse g) (M7.Action.act g c) = c
  intro N inst g c
  rw [← M7.Action.act_compose N (M7.Action.inverse g) g c,
    M7.Action.left_inverse N g, M7.Action.act_identity N c]

theorem M7.Action.order_one_records : Fintype.card (M7.Action.Record 1) = 2 := by
  change Fintype.card (M7.Action.Record 1) = 2
  simpa using (M7.Action.record_card 1)

theorem M7.Action.support_cards : ∀ (N : ℕ) [NeZero N], ∀ (g : M7.Action.Record N) (c : M7.Action.Recipe N), (M7.Action.act g c).1.card = (if g.exchange then c.2.card else c.1.card) ∧ (M7.Action.act g c).2.card = (if g.exchange then c.1.card else c.2.card) := by
  change ∀ (N : ℕ) [NeZero N] (g : M7.Action.Record N) (c : M7.Action.Recipe N), (M7.Action.act g c).1.card = (if g.exchange then c.2.card else c.1.card) ∧ (M7.Action.act g c).2.card = (if g.exchange then c.1.card else c.2.card)
  intro N inst g c
  classical
  dsimp only [M7.Action.act]
  rw [Finset.card_image_of_injective _ (M7.Action.affine_bijective N g.unit g.leftShift).injective,
      Finset.card_image_of_injective _ (M7.Action.affine_bijective N g.unit g.rightShift).injective]
  cases g.exchange <;> simp
#print axioms M7.Action.act_compose
#print axioms M7.Action.act_identity
#print axioms M7.Action.affine_bijective
#print axioms M7.Action.associative
#print axioms M7.Action.left_identity
#print axioms M7.Action.left_inverse
#print axioms M7.Action.act_inverse
#print axioms M7.Action.normal_form
#print axioms M7.Action.record_card
#print axioms M7.Action.order_one_records
#print axioms M7.Action.right_identity
#print axioms M7.Action.right_inverse
#print axioms M7.Action.support_cards
