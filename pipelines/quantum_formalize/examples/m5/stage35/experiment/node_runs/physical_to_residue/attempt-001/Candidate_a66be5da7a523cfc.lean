import FrozenTarget_a66be5da7a523cfc
theorem M5.ResidueNecessity.physical_to_residue : QuantumHarnessFrozenTarget := by
  classical
  change ∀ (N w T : ℕ) (F : M5.BinaryPolynomial) (A B : Finset ℕ), 0 < w → 0 < T → T ∣ N → F ∣ M5.cyclicModulus T → M5.PhysicalOrder.realizes N w F A B → ∃ r s : Fin w → Fin T, M5.BoundedConstruction.anchoredTuple r ∧ M5.BoundedConstruction.anchoredTuple s ∧ M5.BoundedConstruction.tupleSupportGcd r s = 1 ∧ M5.completeSignature (M5.SupportPolynomial.ofResidueTuple r) (M5.SupportPolynomial.ofResidueTuple s) T = F
  intro N w T F A B hw hT hTN hFT hphys
  unfold M5.PhysicalOrder.realizes at hphys
  have hAc : A.card = w := by tauto
  have hBc : B.card = w := by tauto
  have hAz : 0 ∈ A := by tauto
  have hBz : 0 ∈ B := by tauto
  have hconn : M5.Connectivity.supportGcd N A B = 1 := by tauto
  have hsig : M5.completeSignature (M5.SupportPolynomial.ofSupport A) (M5.SupportPolynomial.ofSupport B) N = F := by tauto
  obtain ⟨u, hu, huA, hu0⟩ := M5.ResidueNecessity.anchored_enumeration A w hw hAc hAz
  obtain ⟨v, hv, hvB, hv0⟩ := M5.ResidueNecessity.anchored_enumeration B w hw hBc hBz
  refine ⟨M5.ResidueNecessity.reduceTuple T hT u, M5.ResidueNecessity.reduceTuple T hT v, ?_, ?_, ?_, ?_⟩
  · change ∀ i : Fin w, i.val = 0 → u i % T = 0
    intro i hi
    rw [hu0 i hi, Nat.zero_mod]
  · change ∀ i : Fin w, i.val = 0 → v i % T = 0
    intro i hi
    rw [hv0 i hi, Nat.zero_mod]
  · apply M5.ResidueNecessity.reduced_connectivity w N T hT u v hTN
    simpa only [huA, hvB] using hconn
  · have hpu := M5.ResidueNecessity.reduced_polynomial w T hT u hu
    have hpv := M5.ResidueNecessity.reduced_polynomial w T hT v hv
    rw [huA] at hpu
    rw [hvB] at hpv
    have hc := M5.SignatureCongruence.complete_signature_congruence
      (M5.SupportPolynomial.ofSupport A) (M5.SupportPolynomial.ofSupport B)
      (M5.SupportPolynomial.ofResidueTuple (M5.ResidueNecessity.reduceTuple T hT u))
      (M5.SupportPolynomial.ofResidueTuple (M5.ResidueNecessity.reduceTuple T hT v))
      T hpu hpv
    exact hc.symm.trans (M5.ResidueNecessity.signature_restriction
      (M5.SupportPolynomial.ofSupport A) (M5.SupportPolynomial.ofSupport B)
      F N T hTN hFT hsig)
