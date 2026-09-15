import FrozenTarget_39ef1fb580d41d99
theorem M7.PrefixOrbit.prefix_anchors : QuantumHarnessFrozenTarget := by
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
