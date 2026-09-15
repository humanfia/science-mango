import M6TransferPartialResourcesReady


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (R N : ℕ) (W : ℕ → M6.Transfer.Memory R → M6.Transfer.Bit → Polynomial ℤ) (k : ℕ) (d : Fin (2*N+1)), (∀ j m t, M6.Transfer.polynomialMass (W j m t) ≤ 4) → (∀ j m t, (W j m t).natDegree ≤ 2) → ((((Finset.univ : Finset (M6.Transfer.Memory R)).toList.take k).map (fun start => M6.Transfer.scalarLayers (N:=N) W start N (start,d))).sum).natAbs ≤ 2^R * 8^N
