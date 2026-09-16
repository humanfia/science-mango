import FrozenTarget_6749d4ee1f672876
theorem M8.WholeResources.elementary_bounds : QuantumHarnessFrozenTarget := by
  intro N inst
  have hfold (l : List ℕ) (w k : ℕ) :
      l.foldl (fun acc _ => acc + k) w = w + l.length * k := by
    induction l generalizing w with
    | nil => simp
    | cons x xs ih =>
      simp only [List.foldl_cons, List.length_cons, ih]
      ring
  have hp := M8.BankLayout.payload_bound N
  simp only [M8.WholeResources.setupWork, M8.WholeResources.inputScanWork,
    M8.WholeResources.connectivityScanWork, M8.WholeResources.transformWork,
    M8.WholeResources.undoWork, hfold, List.length_range, zero_add]
  refine ⟨?_, ?_, ?_⟩ <;>
    nlinarith [Nat.zero_le (N^3), Nat.zero_le (N^2)]
