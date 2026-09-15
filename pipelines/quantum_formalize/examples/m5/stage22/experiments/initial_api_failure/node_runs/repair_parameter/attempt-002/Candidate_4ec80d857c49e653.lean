import FrozenTarget_4ec80d857c49e653
theorem M5.BoundedConstruction.repair_parameter : QuantumHarnessFrozenTarget := by
  intro w T r s e hT he hδpos hδlt hgcd
  let δ := M5.PhysicalBridge.remainingGcd (M5.Packing.packedSupport r) (M5.Packing.packedSupport s) e
  have hrange : ∀ a ∈ M5.Packing.packedSupport r, a < w * T := by
    intro a ha
    first
    | solve_by_elim [M5.Packing.packed_support_range]
    | aesop (add safe forward M5.Packing.packed_support_range)
    | solve_by_elim [M5.packed_support_range]
    | aesop (add safe forward M5.packed_support_range)
  have hrepair : ∃ k : ℕ, w ≤ k ∧ k < w + δ ∧ Nat.gcd δ (e + k * T) = 1 := by
    first
    | solve_by_elim [M5.bounded_connectivity_repair]
    | solve_by_elim [M5.PhysicalBridge.bounded_connectivity_repair]
    | solve_by_elim [M5.BoundedConstruction.bounded_connectivity_repair]
    | solve_by_elim [bounded_connectivity_repair]
  obtain ⟨k, hwk, hk, hcop⟩ := hrepair
  refine ⟨k, hwk, ?_, ?_, hcop⟩
  · intro hmem
    have hlt := hrange (e + k * T) hmem
    have hmul := Nat.mul_le_mul_right T hwk
    omega
  · have heBound := hrange e he
    have hδBound : δ < w * T := hδlt
    first
    | solve_by_elim [M5.repaired_exponent_cutoff]
    | solve_by_elim [M5.BoundedConstruction.repaired_exponent_cutoff]
    | solve_by_elim [M5.Packing.repaired_exponent_cutoff]
    | solve_by_elim [repaired_exponent_cutoff]
    | unfold M5.packingCutoff
      nlinarith [Nat.mul_le_mul_right T (Nat.le_of_lt hk), Nat.mul_le_mul_right T (Nat.le_of_lt hδBound)]
