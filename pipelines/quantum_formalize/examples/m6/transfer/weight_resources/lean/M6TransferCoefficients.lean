import M6TransferTrace
namespace M6.Transfer
noncomputable def polynomialMass (p : Polynomial ℤ) : ℕ := p.sum (fun _ c => c.natAbs)
noncomputable def rowMass {R : ℕ} (v : Memory R → Polynomial ℤ) : ℕ :=
  ∑ m : Memory R, polynomialMass (v m)
end M6.Transfer
