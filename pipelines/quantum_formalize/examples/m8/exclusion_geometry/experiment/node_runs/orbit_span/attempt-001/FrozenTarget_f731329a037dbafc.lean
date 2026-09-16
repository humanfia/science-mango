import M8ExclusionGeometry

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

theorem M8.ExclusionGeometry.orbit_pair : ∀ (N : ℕ) [NeZero N], ∀ (h : ℕ) (c : M7.Action.Recipe N) (g : M7.Action.Record N), N = 2*h → (M8.ExclusionGeometry.Antipodal h c.1 ∨ M8.ExclusionGeometry.Antipodal h c.2) → (M8.ExclusionGeometry.Antipodal h (M7.Action.act g c).1 ∨ M8.ExclusionGeometry.Antipodal h (M7.Action.act g c).2) := by
  change ∀ (N : ℕ) [NeZero N], ∀ (h : ℕ) (c : M7.Action.Recipe N) (g : M7.Action.Record N), N = 2 * h → (M8.ExclusionGeometry.Antipodal h c.1 ∨ M8.ExclusionGeometry.Antipodal h c.2) → (M8.ExclusionGeometry.Antipodal h (M7.Action.act g c).1 ∨ M8.ExclusionGeometry.Antipodal h (M7.Action.act g c).2)
  intro N _ h c g hN hc
  classical
  cases he : g.exchange <;> rcases hc with hc | hc <;>
    simp [M7.Action.act, he] <;>
    first
    | exact Or.inl (M8.ExclusionGeometry.pair_affine N h _ g.unit g.leftShift hN hc)
    | exact Or.inr (M8.ExclusionGeometry.pair_affine N h _ g.unit g.rightShift hN hc)
def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N], ∀ (h : ℕ) (c : M7.Action.Recipe N) (g : M7.Action.Record N), N = 2*h → (M8.ExclusionGeometry.Antipodal h c.1 ∨ M8.ExclusionGeometry.Antipodal h c.2) → h ≤ M8.Anchor.span (M7.Action.act g c)
