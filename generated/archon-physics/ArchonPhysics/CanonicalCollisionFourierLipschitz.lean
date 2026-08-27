import ArchonPhysics.CanonicalCollisionFourierPerSiteLimit
import ArchonPhysics.CanonicalCollisionPerSiteMeasureFourier

/-!
# Uniform Lipschitz control of the canonical collision Fourier transform

The frozen collision mismatch has common compact support, and the
site-normalized collision mass has a volume-independent ceiling on the
probability-one simple-spectrum event.  This module packages those two facts
as one common `LipschitzWith` constant for the genuine finite-volume Fourier
transforms.  No convergence statement is made here.
-/

namespace ArchonPhysics.CanonicalCollisionFourierLipschitz

open ArchonPhysics
open ArchonPhysics.CanonicalCollisionFourierPerSiteLimit
open ArchonPhysics.CanonicalCollisionPerSiteMeasureFourier
open ArchonPhysics.CanonicalComplexSpectralPolynomialMomentAllVolume
open ArchonPhysics.FrozenUniformCollisionCompactSupport
open ArchonPhysics.MeasurableOrderedModeCoupling.Harmonic
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.OrderedSingleModeProjector
open Filter MeasureTheory

noncomputable section

variable {Omega : Type*} [MeasurableSpace Omega]

/-- Common Lipschitz constant: support radius times per-site mass ceiling. -/
def canonicalCollisionFourierLipschitzConstant : NNReal :=
  ⟨3 * collisionFrequencyCeiling * canonicalCollisionPerSiteMassCeiling,
    mul_nonneg
      (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))
      canonicalCollisionPerSiteMassCeiling_nonneg⟩

/-- At one simple finite volume, the genuine per-site Fourier integral is
Lipschitz with the common frozen constant. -/
theorem canonicalCollisionPerSiteFourierIntegral_lipschitzWith_of_simple
    (ensemble : IIDMassPhaseEnsemble Omega)
    (sign : Fin 3 -> InteractionSign)
    (n : Nat) (omega : Omega)
    (hsimple : SimpleOrderedSpectrum
      (harmonicHermitian
        (ensemble.restrictPositiveMass (N := n + 2) omega))) :
    LipschitzWith canonicalCollisionFourierLipschitzConstant
      (fun time : Real =>
        canonicalCollisionPerSiteFourierIntegral
          ensemble sign time n omega) := by
  apply LipschitzWith.of_dist_le_mul
  intro time time'
  rw [dist_eq_norm, Real.dist_eq]
  have hbound :=
    norm_canonicalCollisionPerSiteFourierIntegral_sub_le
      ensemble sign time time' n omega hsimple
  calc
    ‖canonicalCollisionPerSiteFourierIntegral ensemble sign time n omega -
        canonicalCollisionPerSiteFourierIntegral
          ensemble sign time' n omega‖ <=
        |time - time'| * (3 * collisionFrequencyCeiling) *
          canonicalCollisionPerSiteMassCeiling := hbound
    _ = (canonicalCollisionFourierLipschitzConstant : Real) *
        |time - time'| := by
      change |time - time'| * (3 * collisionFrequencyCeiling) *
          canonicalCollisionPerSiteMassCeiling =
        (3 * collisionFrequencyCeiling *
          canonicalCollisionPerSiteMassCeiling) * |time - time'|
      ring

/-- The exact finite sum per site is the preceding Fourier integral, so it
inherits the same common Lipschitz constant. -/
theorem canonicalCollisionFourierPerSite_lipschitzWith_of_simple
    (ensemble : IIDMassPhaseEnsemble Omega)
    (sign : Fin 3 -> InteractionSign)
    (n : Nat) (omega : Omega)
    (hsimple : SimpleOrderedSpectrum
      (harmonicHermitian
        (ensemble.restrictPositiveMass (N := n + 2) omega))) :
    LipschitzWith canonicalCollisionFourierLipschitzConstant
      (fun time : Real =>
        canonicalCollisionFourierPerSite ensemble sign time n omega) := by
  have h :=
    canonicalCollisionPerSiteFourierIntegral_lipschitzWith_of_simple
      ensemble sign n omega hsimple
  convert h using 1
  funext time
  exact (canonicalCollisionPerSiteFourierIntegral_eq_fourierSum_div
    ensemble sign time n omega).symm

/-- One probability-one event supplies the common Lipschitz bound at every
canonical volume `N = n + 2`. -/
theorem canonicalCollisionFourierPerSite_lipschitzWith_ae
    (ensemble : IIDMassPhaseEnsemble Omega)
    (sign : Fin 3 -> InteractionSign) :
    ∀ᵐ omega ∂ensemble.probability, forall n : Nat,
      LipschitzWith canonicalCollisionFourierLipschitzConstant
        (fun time : Real =>
          canonicalCollisionFourierPerSite ensemble sign time n omega) := by
  filter_upwards
    [canonicalPositiveVolumes_simpleOrderedSpectrum_ae ensemble] with
      omega hsimple
  intro n
  apply canonicalCollisionFourierPerSite_lipschitzWith_of_simple
  simpa [Nat.add_assoc] using hsimple (n + 1) (by omega)

end

end ArchonPhysics.CanonicalCollisionFourierLipschitz
