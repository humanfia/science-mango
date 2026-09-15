import FrozenTarget_35de671534d0ac15
theorem M7.CompactGeneration.stop : QuantumHarnessFrozenTarget := by
  by
    unfold QuantumHarnessFrozenTarget
    intro N inst w E bases fuel root hroot
    have h : ¬ 0 < root := not_lt.mpr hroot
    cases fuel <;> simp [M7.CompactGeneration.run, h]
