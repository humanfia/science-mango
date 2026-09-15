import FrozenTarget_2262d1dc90bacfa5
theorem M5.SignatureCongruence.packed_complete_signature : QuantumHarnessFrozenTarget := by
  change ∀ (w T : ℕ) (r s : Fin w → Fin T), M5.completeSignature (M5.SupportPolynomial.ofSupport (M5.Packing.packedSupport r)) (M5.SupportPolynomial.ofSupport (M5.Packing.packedSupport s)) T = M5.completeSignature (M5.SupportPolynomial.ofResidueTuple r) (M5.SupportPolynomial.ofResidueTuple s) T
  intro w T r s
  apply M5.SignatureCongruence.complete_signature_congruence
  · apply M5.SupportPolynomial.packed_polynomial_residue
  · apply M5.SupportPolynomial.packed_polynomial_residue
