import FrozenTarget_55394beecd619774
theorem M6.CSS.common_quantum_distance : QuantumHarnessFrozenTarget := by
  unfold QuantumHarnessFrozenTarget
  intro m BX CX BZ CZ J hBX hBZ hBCX hBCZ hJ hw hmem
  have hd := M6.CSS.involution_distance m (M6.CSS.logical BX CX)
    (M6.CSS.logical BZ CZ) J hJ hw hmem
  rw [M6.CSS.css_distance_min m BX CX BZ CZ hBX hBZ hBCX hBCZ, ← hd]
  cases M6.Pinned.distance (M6.CSS.logical BX CX) <;>
    simp [M6.CSS.minDistance]
