import M6EuclidAccepted
import M6EuclidStorage

theorem M6.EuclidStorage.control_encoding : ∀ (width v : ℕ), v ≤ 32*width → v < 2 ^ (M6.EuclidStorage.registerBits width) := by
  change ∀ (width v : ℕ), v ≤ 32 * width → v < 2 ^ (M6.EuclidStorage.registerBits width)
  intro width v hv
  have h : width < 2 ^ width := Nat.lt_two_pow_self
  change v < 2 ^ (width + 5)
  rw [pow_add]
  norm_num
  omega
def QuantumHarnessFrozenTarget : Prop :=
  ∀ (width : ℕ) (s : M6.EuclidStorage.Slots) (fuel c e t : ℕ), M6.EuclidStorage.slotsFit width s → fuel ≤ 32*width → c ≤ 32*width → e ≤ 32*width → t ≤ 32*width → ∀ v ∈ M6.EuclidStorage.controlValues s fuel c e t, v < 2 ^ (M6.EuclidStorage.registerBits width)
