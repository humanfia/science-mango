import ArchonPhysics.MassWeightedHamiltonianDynamics
import ArchonPhysics.RandomMassOrderedProjectorBridge

/-!
# Measurable ordered harmonic-mode energies

For mass-weighted position and momentum coordinates

`X = sqrt(M) q`, `Y = M^(-1/2) p`,

the physical harmonic energy of the ordered mode `k` is

`(‖P_k Y‖^2 + lambda_k * ‖P_k X‖^2) / 2`.

The Lagrange projector is totalized, so this observable is globally defined
and measurable without choosing eigenvectors.  Exact spectral decompositions
are used only under the already proved simple-spectrum hypothesis.
-/

open scoped Matrix

namespace ArchonPhysics.MeasurableOrderedHarmonicEnergy

open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.OrderedSingleModeProjector
open ArchonPhysics.OrderedSpectrumContinuity
open ArchonPhysics.RandomMassOrderedProjectorBridge
open ArchonPhysics.SpectralBandEnergyObservable

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Basis-free physical harmonic energy carried by one ordered mode. -/
def orderedHarmonicModeEnergy
    (A : HermitianMatrix ι) (k : Fin (Fintype.card ι))
    (position momentum : ι → Real) : Real :=
  (orderedModeEnergy A k momentum +
      orderedEigenvalue A k * orderedModeEnergy A k position) / 2

/-- The observable is nonnegative for a nonnegative ordered eigenvalue. -/
theorem orderedHarmonicModeEnergy_nonneg
    (A : HermitianMatrix ι) (k : Fin (Fintype.card ι))
    (position momentum : ι → Real)
    (hk : 0 ≤ orderedEigenvalue A k) :
    0 ≤ orderedHarmonicModeEnergy A k position momentum := by
  unfold orderedHarmonicModeEnergy
  exact div_nonneg
    (add_nonneg (orderedModeEnergy_nonneg A k momentum)
      (mul_nonneg hk (orderedModeEnergy_nonneg A k position)))
    (by norm_num)

/-- Global measurability in a measurable matrix and two measurable states. -/
theorem measurable_orderedHarmonicModeEnergy
    {Omega : Type*} [MeasurableSpace Omega]
    (sample : Omega → HermitianMatrix ι) (hsample : Measurable sample)
    (position momentum : Omega → ι → Real)
    (hposition : Measurable position) (hmomentum : Measurable momentum)
    (k : Fin (Fintype.card ι)) :
    Measurable fun omega =>
      orderedHarmonicModeEnergy (sample omega) k
        (position omega) (momentum omega) := by
  unfold orderedHarmonicModeEnergy
  exact ((measurable_orderedModeEnergy sample hsample momentum hmomentum k).add
    (((continuous_orderedEigenvalue k).measurable.comp hsample).mul
      (measurable_orderedModeEnergy sample hsample position hposition k))).div_const 2

/-- Weighted projector resolution of the Hermitian matrix. -/
theorem sum_eigenvalue_smul_orderedModeProjector
    (A : HermitianMatrix ι) (hsimple : SimpleOrderedSpectrum A) :
    (∑ k : Fin (Fintype.card ι),
        orderedEigenvalue A k • orderedModeProjector A k) = matrixVal A := by
  calc
    (∑ k : Fin (Fintype.card ι),
        orderedEigenvalue A k • orderedModeProjector A k) =
        ∑ k : Fin (Fintype.card ι), matrixVal A * orderedModeProjector A k := by
          apply Finset.sum_congr rfl
          intro k _hk
          exact (matrixVal_mul_orderedModeProjector A hsimple k).symm
    _ = matrixVal A *
        (∑ k : Fin (Fintype.card ι), orderedModeProjector A k) := by
          rw [Finset.mul_sum]
    _ = matrixVal A := by
          rw [orderedModeProjector_sum_eq_one A hsimple, mul_one]

/-- The position parts of the ordered energies sum to the harmonic quadratic
form. -/
theorem sum_eigenvalue_mul_orderedModeEnergy
    (A : HermitianMatrix ι) (hsimple : SimpleOrderedSpectrum A)
    (position : ι → Real) :
    (∑ k : Fin (Fintype.card ι),
        orderedEigenvalue A k * orderedModeEnergy A k position) =
      position ⬝ᵥ (matrixVal A *ᵥ position) := by
  simp_rw [orderedModeEnergy_eq_quadraticForm A hsimple]
  calc
    (∑ k : Fin (Fintype.card ι),
        orderedEigenvalue A k *
          (position ⬝ᵥ orderedModeProjectedState A k position)) =
        ∑ k : Fin (Fintype.card ι),
          position ⬝ᵥ
            ((orderedEigenvalue A k • orderedModeProjector A k) *ᵥ position) := by
              apply Finset.sum_congr rfl
              intro k _hk
              rw [Matrix.smul_mulVec, dotProduct_smul]
              rfl
    _ = position ⬝ᵥ
        (∑ k : Fin (Fintype.card ι),
          (orderedEigenvalue A k • orderedModeProjector A k) *ᵥ position) := by
            simpa using
              (dotProduct_sum position Finset.univ
                (fun k : Fin (Fintype.card ι) =>
                  (orderedEigenvalue A k • orderedModeProjector A k) *ᵥ position)).symm
    _ = position ⬝ᵥ
        ((∑ k : Fin (Fintype.card ι),
          orderedEigenvalue A k • orderedModeProjector A k) *ᵥ position) := by
            rw [Matrix.sum_mulVec]
    _ = position ⬝ᵥ (matrixVal A *ᵥ position) := by
            rw [sum_eigenvalue_smul_orderedModeProjector A hsimple]

/-- Exact total harmonic-energy decomposition across the ordered modes. -/
theorem sum_orderedHarmonicModeEnergy
    (A : HermitianMatrix ι) (hsimple : SimpleOrderedSpectrum A)
    (position momentum : ι → Real) :
    (∑ k : Fin (Fintype.card ι),
        orderedHarmonicModeEnergy A k position momentum) =
      (coordinateEnergy momentum +
        position ⬝ᵥ (matrixVal A *ᵥ position)) / 2 := by
  unfold orderedHarmonicModeEnergy
  rw [← Finset.sum_div, Finset.sum_add_distrib]
  rw [orderedModeEnergy_sum_eq_coordinateEnergy A hsimple momentum,
    sum_eigenvalue_mul_orderedModeEnergy A hsimple position]

end

end ArchonPhysics.MeasurableOrderedHarmonicEnergy
