import M6TransferScatter
namespace M6.Transfer
noncomputable def arrayMass {R N : ℕ} (input : CoefficientArray R N) : ℕ :=
  ∑ addr : CoefficientAddress R N, (input addr).natAbs
noncomputable def eventMass {R N : ℕ} (W : Memory R → Bit → Polynomial ℤ)
    (input : CoefficientArray R N) : ℕ :=
  ∑ e : ScatterEvent R N, (eventTerm W input e).natAbs
end M6.Transfer
