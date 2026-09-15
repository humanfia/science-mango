import M6TransferScatter


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (R N : ℕ) (W : M6.Transfer.Memory R → M6.Transfer.Bit → Polynomial ℤ) (input initial : M6.Transfer.CoefficientArray R N) (l : List (M6.Transfer.ScatterEvent R N)) (addr : M6.Transfer.CoefficientAddress R N), (l.foldl (M6.Transfer.scatterUpdate W input) initial) addr = initial addr + (l.map (fun e => if M6.Transfer.eventDestination e = some addr then M6.Transfer.eventTerm W input e else 0)).sum
