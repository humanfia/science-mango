import M8ExclusionGeometry

theorem M8.ExclusionGeometry.card_sup : ∀ (N : ℕ) [NeZero N], ∀ B : Finset (ZMod N), B.card ≤ B.sup ZMod.val + 1 := by
  change ∀ (N : ℕ) [NeZero N], ∀ B : Finset (ZMod N), B.card ≤ B.sup ZMod.val + 1
  intro N inst B
  classical
  have hinj : Function.Injective (ZMod.val : ZMod N → ℕ) := by
    intro a b h
    have hc := congrArg (fun k : ℕ => (k : ZMod N)) h
    simpa using hc
  have hsub : B.image ZMod.val ⊆ Finset.range (B.sup ZMod.val + 1) := by
    intro k hk
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hk
    apply Finset.mem_range.mpr
    exact Nat.lt_succ_of_le (Finset.le_sup hx)
  calc
    B.card = (B.image ZMod.val).card := (Finset.card_image_of_injective B hinj).symm
    _ ≤ (Finset.range (B.sup ZMod.val + 1)).card := Finset.card_le_card hsub
    _ = B.sup ZMod.val + 1 := Finset.card_range _

theorem M8.ExclusionGeometry.pair_span : ∀ (N : ℕ) [NeZero N], ∀ (h : ℕ) (B : Finset (ZMod N)), N = 2*h → M8.ExclusionGeometry.Antipodal h B → h ≤ B.sup ZMod.val := by
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

theorem M8.ExclusionGeometry.unit_half : ∀ (N : ℕ) [NeZero N], ∀ (h : ℕ) (u : (ZMod N)ˣ), N = 2*h → (u : ZMod N) * (h : ZMod N) = (h : ZMod N) := by
  change ∀ (N : ℕ) [NeZero N], ∀ (h : ℕ) (u : (ZMod N)ˣ), N = 2 * h → (u : ZMod N) * (h : ZMod N) = (h : ZMod N)
  intro N _ h u hN
  have hc := ZMod.val_coe_unit_coprime u
  have hc2 : Nat.Coprime (u : ZMod N).val 2 :=
    hc.of_dvd_right ⟨h, hN⟩
  have ho : Odd (u : ZMod N).val := Nat.coprime_two_right.mp hc2
  obtain ⟨k, hk⟩ := ho
  have hk' : (u : ZMod N).val = 2 * k + 1 := by omega
  have hu : (u : ZMod N) = 2 * (k : ZMod N) + 1 := by
    simpa using congrArg (fun n : ℕ => (n : ZMod N)) hk'
  have hz : (2 : ZMod N) * (h : ZMod N) = 0 := by
    have he := congrArg (fun n : ℕ => (n : ZMod N)) hN
    simpa using he.symm
  rw [hu]
  calc
    (2 * (k : ZMod N) + 1) * (h : ZMod N) =
        (k : ZMod N) * (2 * (h : ZMod N)) + (h : ZMod N) := by ring
    _ = (h : ZMod N) := by rw [hz]; simp

theorem M8.ExclusionGeometry.pair_affine : ∀ (N : ℕ) [NeZero N], ∀ (h : ℕ) (B : Finset (ZMod N)) (u : (ZMod N)ˣ) (s : ZMod N), N = 2*h → M8.ExclusionGeometry.Antipodal h B → M8.ExclusionGeometry.Antipodal h (B.image (M7.Action.affine u s)) := by
  change ∀ (N : ℕ) [NeZero N], ∀ (h : ℕ) (B : Finset (ZMod N)) (u : (ZMod N)ˣ) (s : ZMod N), N = 2 * h → M8.ExclusionGeometry.Antipodal h B → M8.ExclusionGeometry.Antipodal h (B.image (M7.Action.affine u s))
  intro N _ h B u s hN hB
  classical
  rcases hB with ⟨x, hx, hxh⟩
  refine ⟨M7.Action.affine u s x, Finset.mem_image.mpr ⟨x, hx, rfl⟩, ?_⟩
  apply Finset.mem_image.mpr
  refine ⟨x + (h : ZMod N), hxh, ?_⟩
  simp [M7.Action.affine, mul_add, M8.ExclusionGeometry.unit_half N h u hN, add_assoc, add_comm, add_left_comm]

theorem M8.ExclusionGeometry.weight_orbit_span : ∀ (N : ℕ) [NeZero N], ∀ (w : ℕ) (c : M7.Action.Recipe N) (g : M7.Action.Record N), c.1.card = w → c.2.card = w → w ≤ M8.Anchor.span (M7.Action.act g c) + 1 := by
  change ∀ (N : ℕ) [NeZero N], ∀ (w : ℕ) (c : M7.Action.Recipe N) (g : M7.Action.Record N), c.1.card = w → c.2.card = w → w ≤ M8.Anchor.span (M7.Action.act g c) + 1
  intro N inst w c g h₁ h₂
  classical
  have hc : (M7.Action.act g c).1.card = w := by
    simpa [h₁, h₂] using (M7.Action.support_cards N g c).1
  have hs : (M7.Action.act g c).1.sup ZMod.val ≤ M8.Anchor.span (M7.Action.act g c) := by
    apply Finset.sup_le
    intro i hi
    exact ((M8.Anchor.span_le N (M7.Action.act g c) (M8.Anchor.span (M7.Action.act g c))).mp le_rfl).1 i hi
  calc
    w = (M7.Action.act g c).1.card := hc.symm
    _ ≤ (M7.Action.act g c).1.sup ZMod.val + 1 := M8.ExclusionGeometry.card_sup N _
    _ ≤ M8.Anchor.span (M7.Action.act g c) + 1 := Nat.add_le_add_right hs 1

theorem M8.ExclusionGeometry.orbit_pair : ∀ (N : ℕ) [NeZero N], ∀ (h : ℕ) (c : M7.Action.Recipe N) (g : M7.Action.Record N), N = 2*h → (M8.ExclusionGeometry.Antipodal h c.1 ∨ M8.ExclusionGeometry.Antipodal h c.2) → (M8.ExclusionGeometry.Antipodal h (M7.Action.act g c).1 ∨ M8.ExclusionGeometry.Antipodal h (M7.Action.act g c).2) := by
  change ∀ (N : ℕ) [NeZero N], ∀ (h : ℕ) (c : M7.Action.Recipe N) (g : M7.Action.Record N), N = 2 * h → (M8.ExclusionGeometry.Antipodal h c.1 ∨ M8.ExclusionGeometry.Antipodal h c.2) → (M8.ExclusionGeometry.Antipodal h (M7.Action.act g c).1 ∨ M8.ExclusionGeometry.Antipodal h (M7.Action.act g c).2)
  intro N _ h c g hN hc
  classical
  cases he : g.exchange <;> rcases hc with hc | hc <;>
    simp [M7.Action.act, he] <;>
    first
    | exact Or.inl (M8.ExclusionGeometry.pair_affine N h _ g.unit g.leftShift hN hc)
    | exact Or.inr (M8.ExclusionGeometry.pair_affine N h _ g.unit g.rightShift hN hc)

theorem M8.ExclusionGeometry.weight_exclusion : ∀ (N : ℕ) [NeZero N], ∀ (w L : ℕ) (c : M7.Action.Recipe N), c.1.card = w → c.2.card = w → L+1 < w → ∀ g : M7.Action.Record N, L < M8.Anchor.span (M7.Action.act g c) := by
  change ∀ (N : ℕ) [NeZero N], ∀ (w L : ℕ) (c : M7.Action.Recipe N), c.1.card = w → c.2.card = w → L + 1 < w → ∀ g : M7.Action.Record N, L < M8.Anchor.span (M7.Action.act g c)
  intro N inst w L c h₁ h₂ hL g
  have hs := M8.ExclusionGeometry.weight_orbit_span N w c g h₁ h₂
  omega

theorem M8.ExclusionGeometry.orbit_span : ∀ (N : ℕ) [NeZero N], ∀ (h : ℕ) (c : M7.Action.Recipe N) (g : M7.Action.Record N), N = 2*h → (M8.ExclusionGeometry.Antipodal h c.1 ∨ M8.ExclusionGeometry.Antipodal h c.2) → h ≤ M8.Anchor.span (M7.Action.act g c) := by
  change ∀ (N : ℕ) [NeZero N], ∀ (h : ℕ) (c : M7.Action.Recipe N) (g : M7.Action.Record N), N = 2 * h → (M8.ExclusionGeometry.Antipodal h c.1 ∨ M8.ExclusionGeometry.Antipodal h c.2) → h ≤ M8.Anchor.span (M7.Action.act g c)
  intro N _ h c g hN hc
  have hb := (M8.Anchor.span_le N (M7.Action.act g c) (M8.Anchor.span (M7.Action.act g c))).mp (le_refl _)
  rcases M8.ExclusionGeometry.orbit_pair N h c g hN hc with hl | hr
  · exact (M8.ExclusionGeometry.pair_span N h _ hN hl).trans (Finset.sup_le hb.1)
  · exact (M8.ExclusionGeometry.pair_span N h _ hN hr).trans (Finset.sup_le hb.2)

theorem M8.ExclusionGeometry.antipodal_exclusion : ∀ (N : ℕ) [NeZero N], ∀ (h L : ℕ) (c : M7.Action.Recipe N), N = 2*h → (M8.ExclusionGeometry.Antipodal h c.1 ∨ M8.ExclusionGeometry.Antipodal h c.2) → L < h → ∀ g : M7.Action.Record N, L < M8.Anchor.span (M7.Action.act g c) := by
  change ∀ (N : ℕ) [NeZero N], ∀ (h L : ℕ) (c : M7.Action.Recipe N), N = 2 * h → (M8.ExclusionGeometry.Antipodal h c.1 ∨ M8.ExclusionGeometry.Antipodal h c.2) → L < h → ∀ g : M7.Action.Record N, L < M8.Anchor.span (M7.Action.act g c)
  intro N _ h L c hN hc hL g
  exact lt_of_lt_of_le hL (M8.ExclusionGeometry.orbit_span N h c g hN hc)
#print axioms M8.ExclusionGeometry.card_sup
#print axioms M8.ExclusionGeometry.pair_span
#print axioms M8.ExclusionGeometry.unit_half
#print axioms M8.ExclusionGeometry.pair_affine
#print axioms M8.ExclusionGeometry.orbit_pair
#print axioms M8.ExclusionGeometry.orbit_span
#print axioms M8.ExclusionGeometry.antipodal_exclusion
#print axioms M8.ExclusionGeometry.weight_orbit_span
#print axioms M8.ExclusionGeometry.weight_exclusion
