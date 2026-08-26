import ArchonPhysics.MeasurableOrderedEigenframe
import ArchonPhysics.MeasurableOrderedHarmonicEnergy

/-!
# Reconstruction from the explicit signed ordered eigenframe

The measurable signed eigenvectors form an orthonormal frame whenever the
ordered spectrum is simple.  This module proves the exact finite algebra
needed to reconstruct a site-coordinate state from scalar mode coordinates.
Every ordered projector extracts precisely its supplied scalar coefficient,
and the basis-free ordered harmonic energy reduces to the usual scalar modal
energy.  A separate theorem provides global measurability even on the
totalized degenerate set.
-/

open scoped Matrix

namespace ArchonPhysics.SignedEigenframeModeAssembly

open ArchonPhysics.MeasurableOrderedEigenframe
open ArchonPhysics.MeasurableOrderedHarmonicEnergy
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.OrderedSingleModeProjector
open ArchonPhysics.SpectralBandEnergyObservable

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Reconstruct a real site-coordinate vector from ordered scalar
coefficients and the explicit signed frame. -/
def signedFrameReconstruction
    (A : HermitianMatrix ι)
    (coefficient : Fin (Fintype.card ι) → Real) : ι → Real :=
  ∑ k, coefficient k • signedOrderedEigenvector A k

/-- Reconstruction is globally measurable in a measurable matrix sample and
measurable scalar coefficient vector. -/
theorem measurable_signedFrameReconstruction
    {Omega : Type*} [MeasurableSpace Omega]
    (sample : Omega → HermitianMatrix ι) (hsample : Measurable sample)
    (coefficient : Omega → Fin (Fintype.card ι) → Real)
    (hcoefficient : Measurable coefficient) :
    Measurable fun omega =>
      signedFrameReconstruction (sample omega) (coefficient omega) := by
  apply measurable_pi_lambda
  intro i
  unfold signedFrameReconstruction
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  apply Finset.measurable_sum
  intro k _hk
  exact (hcoefficient.eval.mul
    (measurable_signedOrderedEigenvector_apply sample hsample k i))

/-- Distinct explicit signed eigenvectors are orthogonal on a simple
spectrum. -/
theorem signedOrderedEigenvector_dot_eq_zero
    (A : HermitianMatrix ι) (hsimple : SimpleOrderedSpectrum A)
    {k l : Fin (Fintype.card ι)} (hkl : k ≠ l) :
    signedOrderedEigenvector A k ⬝ᵥ signedOrderedEigenvector A l = 0 := by
  let vk := signedOrderedEigenvector A k
  let vl := signedOrderedEigenvector A l
  have hprod := orderedModeProjector_mul_eq_zero A hsimple hkl
  rw [← signedOrderedEigenvector_outerProduct A hsimple k,
    ← signedOrderedEigenvector_outerProduct A hsimple l,
    Matrix.vecMulVec_mul_vecMulVec] at hprod
  have htrace := congrArg Matrix.trace hprod
  rw [Matrix.trace_vecMulVec] at htrace
  simp only [Matrix.trace_zero] at htrace
  change vk ⬝ᵥ (vk ⬝ᵥ vl) • vl = 0 at htrace
  rw [dotProduct_smul] at htrace
  change (vk ⬝ᵥ vl) * (vk ⬝ᵥ vl) = 0 at htrace
  exact mul_self_eq_zero.mp htrace

/-- Kronecker orthonormality of the explicit signed frame. -/
theorem signedOrderedEigenvector_dot
    (A : HermitianMatrix ι) (hsimple : SimpleOrderedSpectrum A)
    (k l : Fin (Fintype.card ι)) :
    signedOrderedEigenvector A k ⬝ᵥ signedOrderedEigenvector A l =
      if k = l then 1 else 0 := by
  by_cases hkl : k = l
  · subst l
    simpa using signedOrderedEigenvector_dot_self A hsimple k
  · simp [hkl, signedOrderedEigenvector_dot_eq_zero A hsimple hkl]

/-- Taking the signed-frame dot product of a reconstruction extracts exactly
the supplied scalar coefficient. -/
theorem signedOrderedEigenvector_dot_reconstruction
    (A : HermitianMatrix ι) (hsimple : SimpleOrderedSpectrum A)
    (coefficient : Fin (Fintype.card ι) → Real)
    (k : Fin (Fintype.card ι)) :
    signedOrderedEigenvector A k ⬝ᵥ
        signedFrameReconstruction A coefficient = coefficient k := by
  classical
  unfold signedFrameReconstruction
  rw [dotProduct_sum]
  calc
    (∑ l, signedOrderedEigenvector A k ⬝ᵥ
        coefficient l • signedOrderedEigenvector A l) =
        ∑ l, coefficient l *
          (signedOrderedEigenvector A k ⬝ᵥ
            signedOrderedEigenvector A l) := by
      apply Finset.sum_congr rfl
      intro l _hl
      rw [dotProduct_smul]
      rfl
    _ = coefficient k := by
      simp [signedOrderedEigenvector_dot A hsimple]

/-- The ordered rank-one projector extracts its corresponding reconstructed
frame component. -/
theorem orderedModeProjector_mulVec_reconstruction
    (A : HermitianMatrix ι) (hsimple : SimpleOrderedSpectrum A)
    (coefficient : Fin (Fintype.card ι) → Real)
    (k : Fin (Fintype.card ι)) :
    orderedModeProjector A k *ᵥ signedFrameReconstruction A coefficient =
      coefficient k • signedOrderedEigenvector A k := by
  rw [← signedOrderedEigenvector_outerProduct A hsimple k,
    Matrix.vecMulVec_mulVec,
    signedOrderedEigenvector_dot_reconstruction A hsimple coefficient k]
  exact op_smul_eq_smul _ _

/-- The basis-free coordinate energy of one projected reconstruction is the
square of its scalar coefficient. -/
theorem orderedModeEnergy_reconstruction
    (A : HermitianMatrix ι) (hsimple : SimpleOrderedSpectrum A)
    (coefficient : Fin (Fintype.card ι) → Real)
    (k : Fin (Fintype.card ι)) :
    orderedModeEnergy A k (signedFrameReconstruction A coefficient) =
      (coefficient k) ^ 2 := by
  unfold orderedModeEnergy orderedModeProjectedState coordinateEnergy
  rw [orderedModeProjector_mulVec_reconstruction A hsimple coefficient k,
    smul_dotProduct, dotProduct_smul,
    signedOrderedEigenvector_dot_self A hsimple k]
  simp [pow_two]

/-- Two scalar coefficient vectors reconstruct to exactly the usual physical
harmonic mode energy in the corresponding ordered mode. -/
theorem orderedHarmonicModeEnergy_reconstruction
    (A : HermitianMatrix ι) (hsimple : SimpleOrderedSpectrum A)
    (positionCoefficient momentumCoefficient :
      Fin (Fintype.card ι) → Real)
    (k : Fin (Fintype.card ι)) :
    orderedHarmonicModeEnergy A k
        (signedFrameReconstruction A positionCoefficient)
        (signedFrameReconstruction A momentumCoefficient) =
      HarmonicModes.modalEnergy (orderedEigenvalue A k)
        (positionCoefficient k) (momentumCoefficient k) := by
  unfold orderedHarmonicModeEnergy HarmonicModes.modalEnergy
  rw [orderedModeEnergy_reconstruction A hsimple momentumCoefficient k,
    orderedModeEnergy_reconstruction A hsimple positionCoefficient k]

end

end ArchonPhysics.SignedEigenframeModeAssembly
