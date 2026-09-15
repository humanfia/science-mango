import M5BoundedConstructionReady

theorem M5.BoundedConstruction.packed_repair_hypotheses : ∀ (w T : ℕ) (r s : Fin w → Fin T), 2 ≤ w → 0 < T → M5.BoundedConstruction.anchoredTuple r → M5.BoundedConstruction.anchoredTuple s → M5.BoundedConstruction.tupleSupportGcd r s = 1 → ∃ e ∈ (M5.Packing.packedSupport r), 0 < e ∧ 0 < (M5.PhysicalBridge.remainingGcd (M5.Packing.packedSupport r) (M5.Packing.packedSupport s) e) ∧ (M5.PhysicalBridge.remainingGcd (M5.Packing.packedSupport r) (M5.Packing.packedSupport s) e) < w * T ∧ Nat.gcd (Nat.gcd T (M5.PhysicalBridge.remainingGcd (M5.Packing.packedSupport r) (M5.Packing.packedSupport s) e)) e = 1 := by
  intro w T r s hw hT hr hs hg
  have hw0 : 0 < w := by omega
  have hr0 : 0 ∈ M5.Packing.packedSupport r :=
    M5.Packing.packed_support_anchor w T r hw0 (hr ⟨0, hw0⟩ rfl)
  have hs0 : 0 ∈ M5.Packing.packedSupport s :=
    M5.Packing.packed_support_anchor w T s hw0 (hs ⟨0, hw0⟩ rfl)
  have hrc : 2 ≤ (M5.Packing.packedSupport r).card := by
    rw [M5.Packing.packed_support_card w T r]
    exact hw
  have hsc : 2 ≤ (M5.Packing.packedSupport s).card := by
    rw [M5.Packing.packed_support_card w T s]
    exact hw
  obtain ⟨e, he, hepos⟩ :=
    M5.PhysicalBridge.positive_member (M5.Packing.packedSupport r) hrc hr0
  obtain ⟨hpos, hlt⟩ :=
    M5.PhysicalBridge.remaining_gcd_bounds
      (M5.Packing.packedSupport r) (M5.Packing.packedSupport s) e (w * T)
      hsc hs0 (fun b hb => M5.Packing.packed_support_range w T s b hb)
  refine ⟨e, he, hepos, hpos, hlt, ?_⟩
  apply M5.PhysicalBridge.remaining_gcd_feasible T
    (M5.Packing.packedSupport r) (M5.Packing.packedSupport s) e he
  rw [M5.PhysicalBridge.packed_combined_gcd w T r s]
  simpa only [M5.BoundedConstruction.tupleSupportGcd] using hg

theorem M5.BoundedConstruction.repaired_support_properties : ∀ (w T : ℕ) (r s : Fin w → Fin T), 2 ≤ w → 0 < T → M5.BoundedConstruction.anchoredTuple r → M5.BoundedConstruction.anchoredTuple s → ∀ e k : ℕ, e ∈ (M5.Packing.packedSupport r) → 0 < e → e + k * T ∉ (M5.Packing.packedSupport r) → e + k * T < M5.packingCutoff w T → Nat.gcd (M5.PhysicalBridge.remainingGcd (M5.Packing.packedSupport r) (M5.Packing.packedSupport s) e) (e + k * T) = 1 → (M5.RepairSupport.repaired (M5.Packing.packedSupport r) e (e + k * T)).card = w ∧ 0 ∈ (M5.RepairSupport.repaired (M5.Packing.packedSupport r) e (e + k * T)) ∧ (∀ a ∈ (M5.RepairSupport.repaired (M5.Packing.packedSupport r) e (e + k * T)), a < M5.packingCutoff w T) ∧ M5.RepairSupport.combinedGcd (M5.RepairSupport.repaired (M5.Packing.packedSupport r) e (e + k * T)) (M5.Packing.packedSupport s) = 1 := by
  intro w T r s hw hT hr hs e k he hepos hnew hcut hgcd
  have hw0 : 0 < w := by omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (M5.RepairSupport.replacement_card
      (M5.Packing.packedSupport r) e (e + k * T) he hnew).trans
      (M5.Packing.packed_support_card w T r)
  · exact M5.RepairSupport.replacement_anchor
      (M5.Packing.packedSupport r) e (e + k * T)
      (by omega)
      (M5.Packing.packed_support_anchor w T r hw0 (hr ⟨0, hw0⟩ rfl))
  · apply M5.RepairSupport.replacement_range
      (M5.Packing.packedSupport r) e (e + k * T) (M5.packingCutoff w T)
    · intro a ha
      have harange := M5.Packing.packed_support_range w T r a ha
      simpa using M5.PhysicalBridge.repaired_exponent_cutoff
        w T a 0 0 hT harange (Nat.mul_pos hw0 hT) (by omega)
    · exact hcut
  · apply M5.RepairSupport.replacement_connected
      (M5.Packing.packedSupport r) (M5.Packing.packedSupport s) e (e + k * T)
    simpa only [M5.PhysicalBridge.remainingGcd] using hgcd
def QuantumHarnessFrozenTarget : Prop :=
  ∀ (w T : ℕ) (r s : Fin w → Fin T), 2 ≤ w → 0 < T → M5.BoundedConstruction.anchoredTuple r → M5.BoundedConstruction.anchoredTuple s → M5.BoundedConstruction.tupleSupportGcd r s = 1 → ∃ A : Finset ℕ, A.card = w ∧ (M5.Packing.packedSupport s).card = w ∧ 0 ∈ A ∧ 0 ∈ (M5.Packing.packedSupport s) ∧ (∀ a ∈ A, a < M5.packingCutoff w T) ∧ (∀ b ∈ (M5.Packing.packedSupport s), b < w * T) ∧ M5.RepairSupport.combinedGcd A (M5.Packing.packedSupport s) = 1 ∧ M5.completeSignature (M5.SupportPolynomial.ofSupport A) (M5.SupportPolynomial.ofSupport (M5.Packing.packedSupport s)) T = M5.completeSignature (M5.SupportPolynomial.ofResidueTuple r) (M5.SupportPolynomial.ofResidueTuple s) T
