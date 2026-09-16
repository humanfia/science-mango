import FrozenTarget_da36cddb794134e6
theorem M8.ExclusionGeometry.unit_half : QuantumHarnessFrozenTarget := by
  change ∀ (N : ℕ) [NeZero N], ∀ (h : ℕ) (u : (ZMod N)ˣ), N = 2 * h → (u : ZMod N) * (h : ZMod N) = (h : ZMod N)
  intro N inst h u hn
  have hc : Nat.Coprime (u : ZMod N).val N := by
    first
    | exact ZMod.val_coe_unit_coprime u
    | exact (ZMod.val_coe_unit_coprime u).symm
    | exact?
  have hc2 : Nat.Coprime (u : ZMod N).val 2 :=
    hc.of_dvd_right ⟨h, hn⟩
  have ho : Odd (u : ZMod N).val := Nat.coprime_two_right.mp hc2
  obtain ⟨k, hk⟩ := ho
  have hv : (u : ZMod N).val = 2 * k + 1 := by omega
  have hu : (u : ZMod N) = 2 * (k : ZMod N) + 1 := by
    calc
      (u : ZMod N) = ((u : ZMod N).val : ZMod N) := (ZMod.natCast_zmod_val _).symm
      _ = 2 * (k : ZMod N) + 1 := by
        rw [hv]
        simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
  have hz : (2 : ZMod N) * (h : ZMod N) = 0 := by
    have hzN : (N : ZMod N) = 0 := by simp
    rw [hn] at hzN
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using hzN
  rw [hu]
  calc
    (2 * (k : ZMod N) + 1) * (h : ZMod N) = (k : ZMod N) * (2 * (h : ZMod N)) + (h : ZMod N) := by ring
    _ = (h : ZMod N) := by rw [hz]; simp
