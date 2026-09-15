import M7PrefixOrbit

theorem M7.PrefixOrbit.gcd_bridge : ∀ (N : ℕ) [NeZero N], ∀ y : M7.Action.Recipe N, M7.Domain.connectivityGcd y.1 y.2 = M5.Connectivity.supportGcd N (M7.ResiduePrefix.encode y.1) (M7.ResiduePrefix.encode y.2) := by
  intro N _ y
  rw [M7.ResiduePrefix.gcd_union]
  rfl

theorem M7.PrefixOrbit.prefix_anchors : ∀ (N : ℕ) [NeZero N], ∀ (A B WA WB : Finset ℕ) (y : M7.Action.Recipe N), M7.PrefixCompleted.Base N A B WA WB → M7.PrefixOrbit.Within A WA y.1 → M7.PrefixOrbit.Within B WB y.2 → (0 : ZMod N) ∈ y.1 ∧ (0 : ZMod N) ∈ y.2 := by
  intro N inst A B WA WB y hbase hA hB
  classical
  have hzero : 0 ∈ A ∧ 0 ∈ B := by
    unfold M7.PrefixCompleted.Base at hbase
    tauto
  have hleft : 0 ∈ M7.ResiduePrefix.encode y.1 := hA.1 hzero.1
  have hright : 0 ∈ M7.ResiduePrefix.encode y.2 := hB.1 hzero.2
  constructor
  · rw [← M7.ResiduePrefix.residue_roundtrip N y.1]
    unfold M7.ResiduePrefix.decode
    exact Finset.mem_image.mpr ⟨0, hleft, by simp⟩
  · rw [← M7.ResiduePrefix.residue_roundtrip N y.2]
    unfold M7.ResiduePrefix.decode
    exact Finset.mem_image.mpr ⟨0, hright, by simp⟩
def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N], ∀ (w : ℕ) (E : Finset M5.BinaryPolynomial) (A B WA WB : Finset ℕ), M7.PrefixCompleted.Base N A B WA WB → ∀ y : M7.Action.Recipe N, y ∈ M7.ResiduePrefix.completed N w E A B WA WB ↔ M7.PrefixOrbit.ClassValid w y ∧ M7.RecipeSignature.signature y ∈ E ∧ M7.PrefixOrbit.Within A WA y.1 ∧ M7.PrefixOrbit.Within B WB y.2
