import ArchonPhysics.ReducedModeTransform

/-!
# Finite normal-mode interaction coefficients

For a fixed positive mass realization and the already selected deterministic
normal-mode basis, this module expands physical bond differences in real modal
coordinates.  The order-`n` interaction tensor is the finite bond sum of
products of bond-mode coefficients.  Mathlib's `Fintype.sum_pow` then gives an
exact ordered-index expansion of the real polynomial
`sum_j (D q j)^n`.

No coefficient is asserted to be nonzero or resonant.  No measurable choice
of eigenbasis, eigenvalue ordering, or random tensor is asserted.
-/

namespace ArchonPhysics.ModeCoupling

open ArchonPhysics
open HarmonicModes
open ReducedModeTransform

noncomputable section

/--
The weighted difference matrix is physical forward difference after inverse
square-root mass weighting.
-/
theorem weightedDifference_mulVec_eq_forwardDifference {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (x : WeightedConfiguration N) :
    Matrix.mulVec (massWeightedDifferenceMatrix m) (WithLp.ofLp x) =
      Lattice.forwardDifference
        (Lattice.inverseSqrtMassAction m (WithLp.ofLp x)) := by
  unfold massWeightedDifferenceMatrix
  rw [← Matrix.mulVec_mulVec, differenceMatrix_mulVec]
  congr 1
  ext i
  simp [Matrix.mulVec_diagonal, Lattice.inverseSqrtMassAction]

/-- Contribution of normal mode `k` to physical bond `j`. -/
def bondModeCoefficient {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (j k : Lattice.Site N) : Real :=
  Matrix.mulVec (massWeightedDifferenceMatrix m)
    ⇑(normalModeBasis m k) j

/-- The coefficient is the physical forward difference of one reconstructed mode. -/
theorem bondModeCoefficient_eq_forwardDifference {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (j k : Lattice.Site N) :
    bondModeCoefficient m j k =
      Lattice.forwardDifference
        (Lattice.inverseSqrtMassAction m ⇑(normalModeBasis m k)) j := by
  exact congrFun
    (weightedDifference_mulVec_eq_forwardDifference m (normalModeBasis m k)) j

/-- Physical site displacement reconstructed from real modal amplitudes. -/
def physicalReconstruction {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (amplitude : WeightedConfiguration N) :
    Lattice.Configuration N :=
  Lattice.inverseSqrtMassAction m
    (WithLp.ofLp (reconstruct m amplitude))

/-- Every reconstructed physical bond difference is the finite modal sum. -/
theorem forwardDifference_physicalReconstruction {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (amplitude : WeightedConfiguration N)
    (j : Lattice.Site N) :
    Lattice.forwardDifference (physicalReconstruction m amplitude) j =
      ∑ k, amplitude k * bondModeCoefficient m j k := by
  unfold physicalReconstruction
  rw [← congrFun
    (weightedDifference_mulVec_eq_forwardDifference m (reconstruct m amplitude)) j]
  have hreconstruct :
      reconstruct m amplitude =
        ∑ k, amplitude k • normalModeBasis m k := by
    change (normalModeBasis m).repr.symm amplitude =
      ∑ k, amplitude k • normalModeBasis m k
    exact (normalModeBasis m).sum_repr_symm amplitude |>.symm
  rw [hreconstruct]
  change ((massWeightedDifferenceMatrix m).mulVecLin
    (WithLp.ofLp (∑ k, amplitude k • normalModeBasis m k))) j = _
  simp only [WithLp.ofLp_sum, WithLp.ofLp_smul, map_sum, map_smul,
    Matrix.mulVecLin_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    bondModeCoefficient]

/--
The order-`n` finite interaction tensor.  Its indices are ordered only to make
the exact `Fintype.sum_pow` expansion transparent; symmetry is proved below.
-/
def interactionTensor {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (n : Nat)
    (modes : Fin n → Lattice.Site N) : Real :=
  ∑ j, ∏ r, bondModeCoefficient m j (modes r)

/-- The interaction tensor is invariant under every permutation of its `Fin n` slots. -/
theorem interactionTensor_perm {N n : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (modes : Fin n → Lattice.Site N)
    (sigma : Equiv.Perm (Fin n)) :
    interactionTensor m n (modes ∘ sigma) = interactionTensor m n modes := by
  unfold interactionTensor
  apply Finset.sum_congr rfl
  intro j hj
  change (∏ r, bondModeCoefficient m j (modes (sigma r))) =
    ∏ r, bondModeCoefficient m j (modes r)
  exact Equiv.prod_comp sigma (fun r => bondModeCoefficient m j (modes r))

/--
Exact finite real-coordinate expansion of the order-`n` physical bond
polynomial after inverse normal-mode reconstruction.
-/
theorem sum_forwardDifference_pow_eq_interactionTensor {N n : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (amplitude : WeightedConfiguration N) :
    ∑ j, (Lattice.forwardDifference (physicalReconstruction m amplitude) j) ^ n =
      ∑ modes : Fin n → Lattice.Site N,
        interactionTensor m n modes * ∏ r, amplitude (modes r) := by
  simp_rw [forwardDifference_physicalReconstruction]
  calc
    ∑ j, (∑ k, amplitude k * bondModeCoefficient m j k) ^ n =
        ∑ j, ∑ modes : Fin n → Lattice.Site N,
          ∏ r, amplitude (modes r) * bondModeCoefficient m j (modes r) := by
      apply Finset.sum_congr rfl
      intro j hj
      exact Fintype.sum_pow
        (fun k => amplitude k * bondModeCoefficient m j k) n
    _ = ∑ j, ∑ modes : Fin n → Lattice.Site N,
        (∏ r, amplitude (modes r)) *
          ∏ r, bondModeCoefficient m j (modes r) := by
      apply Finset.sum_congr rfl
      intro j hj
      apply Finset.sum_congr rfl
      intro modes hmodes
      exact Finset.prod_mul_distrib
    _ = ∑ modes : Fin n → Lattice.Site N, ∑ j,
        (∏ r, amplitude (modes r)) *
          ∏ r, bondModeCoefficient m j (modes r) := by
      rw [Finset.sum_comm]
    _ = ∑ modes : Fin n → Lattice.Site N, ∑ j,
        (∏ r, bondModeCoefficient m j (modes r)) *
          ∏ r, amplitude (modes r) := by
      apply Finset.sum_congr rfl
      intro modes hmodes
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ = ∑ modes : Fin n → Lattice.Site N,
        interactionTensor m n modes * ∏ r, amplitude (modes r) := by
      apply Finset.sum_congr rfl
      intro modes hmodes
      unfold interactionTensor
      rw [Finset.sum_mul]

end

end ArchonPhysics.ModeCoupling
