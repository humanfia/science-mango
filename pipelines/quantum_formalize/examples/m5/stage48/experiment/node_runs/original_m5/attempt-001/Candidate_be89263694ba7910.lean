import FrozenTarget_be89263694ba7910
theorem M5.Final.original_m5 : QuantumHarnessFrozenTarget := by
  change ∀ (w : ℕ) (F : M5.BinaryPolynomial), 0 < w → F.Monic → F.coeff 0 = 1 → M5.Final.OriginalM5Spec w F
  intro w F hw hmonic hcoeff
  unfold M5.Final.OriginalM5Spec
  exact ⟨M5.Final.core w F hw hmonic hcoeff,
    M5.Final.actual_order_recovery w F hw hmonic hcoeff,
    fun _ => M5.Final.actual_residue_recovery w F hw hmonic hcoeff⟩
