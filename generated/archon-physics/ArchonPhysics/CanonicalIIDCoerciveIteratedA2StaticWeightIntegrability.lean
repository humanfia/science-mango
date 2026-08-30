import ArchonPhysics.CanonicalIIDCoerciveIteratedA2ExpectationFourierDecay
import ArchonPhysics.PhyslibFPUTA1AnnealedMismatchSmallBall

/-!
# Integrability of the finite-volume actual iterated-A2 static weight

This file supplies the deterministic estimate which is needed before a
weighted mismatch law can be constructed.  If every modal radius is bounded
by `R` and every squared harmonic frequency is at most five, one complete
iterated quadratic tree satisfies the explicit bound

`norm staticWeight <= 4 * |kappa|^2 * R^3`.

For an `IIDMassPhaseEnsemble`, the spectral-band premise is already a theorem.
Thus a measurable actual static weight is integrable under the ensemble
probability law with the same ceiling.  The measurability premise is kept
transparent: the legacy physical coefficient uses the signs of Mathlib's
eigenvector basis, whereas the repository's unconditional measurable spectral
API is sign-invariant (or uses a separately constructed signed frame).  A
measurable radius profile alone therefore does not currently imply
measurability of this legacy signed coefficient.

No thermodynamic limit, Fourier-density regularity, or kinetic closure is
asserted here.
-/

namespace ArchonPhysics
namespace CanonicalIIDCoerciveIteratedA2StaticWeightIntegrability

open ArchonPhysics
open ArchonPhysics.CanonicalIIDCoerciveIteratedA2ExpectationFourierDecay
open ArchonPhysics.CubicVertexInfraredBound
open ArchonPhysics.FreeFPUTDuhamelResonanceBridge
open ArchonPhysics.FreeFPUTTensorPhaseExpansion
open ArchonPhysics.HarmonicModes
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.ModeCoupling
open ArchonPhysics.PhyslibFPUTA1AnnealedMismatchSmallBall
open ArchonPhysics.PhyslibFPUTAfterSecondPicardEnergyEnvelope
open ArchonPhysics.PhyslibFPUTFirstPicardCoordinateCharacterFamily
open ArchonPhysics.PhyslibFPUTFirstPicardDecomposition
open ArchonPhysics.PhyslibFPUTIteratedQuadraticSecondPicardCharacterFamily
open ArchonPhysics.RandomEnsemble
open ArchonPhysics.UniformRandomMassHarmonicSpectrumBound
open MeasureTheory

noncomputable section

/-! ## Deterministic finite-volume coefficient ceilings -/

/-- The raw three-leg tensor is at most five times its first frequency on the
common iid spectral band.  This is the cancellation which removes the
apparent acoustic singularity in the reconstructed inner coordinate. -/
theorem abs_interactionTensor_three_le_five_mul_firstFrequency
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N)
    (hfrequency : forall mode, modeFrequencySq m mode <= 5)
    (modes : Fin 3 -> Lattice.Site N) :
    |interactionTensor m 3 modes| <= 5 * modeFrequency m (modes 0) := by
  let w0 := modeFrequency m (modes 0)
  let w1 := modeFrequency m (modes 1)
  let w2 := modeFrequency m (modes 2)
  let d := interactionTensor m 3 modes
  have hw0 : 0 <= w0 := modeFrequency_nonneg m (modes 0)
  have hw0sq : w0 ^ 2 = modeFrequencySq m (modes 0) := by
    simp [w0, modeFrequency_sq]
  have hw1sq : w1 ^ 2 <= 5 := by
    simpa [w1, modeFrequency_sq] using hfrequency (modes 1)
  have hw2sq : w2 ^ 2 <= 5 := by
    simpa [w2, modeFrequency_sq] using hfrequency (modes 2)
  have hdsq : d ^ 2 <= w0 ^ 2 * w1 ^ 2 * w2 ^ 2 := by
    simpa [d, w0, w1, w2, modeFrequency_sq] using
      interactionTensor_three_sq_le m modes
  have htarget : |d| ^ 2 <= (5 * w0) ^ 2 := by
    rw [sq_abs]
    calc
      d ^ 2 <= w0 ^ 2 * w1 ^ 2 * w2 ^ 2 := hdsq
      _ <= w0 ^ 2 * 5 * 5 := by gcongr
      _ = (5 * w0) ^ 2 := by ring
  have hnonneg : 0 <= 5 * w0 := by positivity
  simpa [d, w0] using
    ((sq_le_sq₀ (abs_nonneg d) hnonneg).mp htarget)

/-- After the exact real-coordinate reconstruction scale is included, one
inner first-Picard branch is uniformly bounded.  In particular, no inverse
small-frequency factor remains. -/
theorem norm_firstPicardCoordinateBranchStaticCoefficient_le
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa R : Real) (hR : 0 <= R)
    (hfrequency : forall mode, modeFrequencySq m mode <= 5)
    (radius : Lattice.Site N -> Real)
    (hradius : forall mode, |radius mode| <= R)
    (innerObserved : Lattice.Site N)
    (entry : QuadraticFirstPicardCoordinateCharacterTerm N) :
    ‖firstPicardCoordinateBranchStaticCoefficient
        m kappa radius innerObserved entry‖ <= |kappa| * R ^ 2 := by
  let w := modeFrequency m innerObserved
  by_cases hwpos : 0 < w
  · have hsqrtPos : 0 < Real.sqrt (2 * w) := Real.sqrt_pos.2 (by positivity)
    have hcoupling :
        ‖physlibQuadraticCoupling m kappa 1 innerObserved‖ =
          |kappa| / Real.sqrt (2 * w) := by
      simpa [physlibQuadraticCoupling, w] using
        (norm_forcedModeSource hwpos (-(kappa * 1)))
    let d := interactionTensor m 3 (Fin.cons innerObserved entry.1.1)
    have hd : |d| <= 5 * w := by
      simpa [d, w] using
        abs_interactionTensor_three_le_five_mul_firstFrequency m hfrequency
          (Fin.cons innerObserved entry.1.1)
    have hr0 := hradius (entry.1.1 0)
    have hr1 := hradius (entry.1.1 1)
    have hr0half : |radius (entry.1.1 0) / 2| <= R / 2 := by
      rw [abs_div, abs_of_pos (by norm_num : (0 : Real) < 2)]
      exact div_le_div_of_nonneg_right hr0 (by norm_num)
    have hr1half : |radius (entry.1.1 1) / 2| <= R / 2 := by
      rw [abs_div, abs_of_pos (by norm_num : (0 : Real) < 2)]
      exact div_le_div_of_nonneg_right hr1 (by norm_num)
    have hscaleNonneg :
        0 <= physlibQuadraticFirstPicardCoordinateScale m innerObserved / 2 := by
      unfold physlibQuadraticFirstPicardCoordinateScale
      positivity
    unfold firstPicardCoordinateBranchStaticCoefficient
    rw [if_pos (by simpa [w] using hwpos)]
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hscaleNonneg]
    split_ifs with hbranch
    · unfold freeQuadraticDuhamelCoefficient quadraticPhaseCoefficient
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      rw [hcoupling]
      change
        (Real.sqrt (2 * w) / w / 2) *
            (|kappa| / Real.sqrt (2 * w) *
              (|d| * |radius (entry.1.1 0) / 2| *
                |radius (entry.1.1 1) / 2|)) <=
          |kappa| * R ^ 2
      calc
        _ <= (Real.sqrt (2 * w) / w / 2) *
            (|kappa| / Real.sqrt (2 * w) *
              ((5 * w) * (R / 2) * (R / 2))) := by gcongr
        _ = (5 / 8 : Real) * |kappa| * R ^ 2 := by
          field_simp [ne_of_gt hwpos, ne_of_gt hsqrtPos]
          ring
        _ <= |kappa| * R ^ 2 := by
          have hx : 0 <= |kappa| * R ^ 2 := by positivity
          nlinarith
    · have hstar :
          ‖starRingEnd Complex
            (freeQuadraticDuhamelCoefficient
              (physlibQuadraticCoupling m kappa 1 innerObserved)
              m innerObserved radius entry.1)‖ =
            ‖freeQuadraticDuhamelCoefficient
              (physlibQuadraticCoupling m kappa 1 innerObserved)
              m innerObserved radius entry.1‖ := by
          change ‖star (freeQuadraticDuhamelCoefficient
            (physlibQuadraticCoupling m kappa 1 innerObserved)
            m innerObserved radius entry.1)‖ = _
          exact norm_star _
      rw [hstar]
      unfold freeQuadraticDuhamelCoefficient quadraticPhaseCoefficient
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      rw [hcoupling]
      change
        (Real.sqrt (2 * w) / w / 2) *
            (|kappa| / Real.sqrt (2 * w) *
              (|d| * |radius (entry.1.1 0) / 2| *
                |radius (entry.1.1 1) / 2|)) <=
          |kappa| * R ^ 2
      calc
        _ <= (Real.sqrt (2 * w) / w / 2) *
            (|kappa| / Real.sqrt (2 * w) *
              ((5 * w) * (R / 2) * (R / 2))) := by gcongr
        _ = (5 / 8 : Real) * |kappa| * R ^ 2 := by
          field_simp [ne_of_gt hwpos, ne_of_gt hsqrtPos]
          ring
        _ <= |kappa| * R ^ 2 := by
          have hx : 0 <= |kappa| * R ^ 2 := by positivity
          nlinarith
  · unfold firstPicardCoordinateBranchStaticCoefficient
    rw [if_neg (by simpa [w] using hwpos)]
    simp only [norm_zero]
    exact mul_nonneg (abs_nonneg kappa) (sq_nonneg R)

/-- The outer coupling times its raw tensor has a uniform `8 * |kappa|`
ceiling.  This is a direct specialization of the established A1 bound with
both auxiliary radii equal to two. -/
theorem norm_outerCoupling_mul_interactionTensor_le_eight_absKappa
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa : Real)
    (hfrequency : forall mode, modeFrequencySq m mode <= 5)
    (observed : Lattice.Site N)
    (modes : Fin 2 -> Lattice.Site N) :
    ‖physlibIteratedQuadraticOuterCoupling m kappa observed *
        (interactionTensor m 3 (Fin.cons observed modes) : Complex)‖ <=
      8 * |kappa| := by
  let term : QuadraticPhaseTerm N := (modes, (0, 0))
  have hbound := physlibA1StaticCoefficient_le_two_absKappa_radiusSq
    m kappa 2 (by norm_num) hfrequency (fun _ => 2)
      (fun _ => by norm_num) observed term
  have hbound' :
      ‖physlibIteratedQuadraticOuterCoupling m kappa observed *
          (interactionTensor m 3 (Fin.cons observed modes) : Complex)‖ <=
        2 * |kappa| * 2 ^ 2 := by
    simpa [term, freeQuadraticDuhamelCoefficient, quadraticPhaseCoefficient,
      physlibQuadraticCoupling, physlibIteratedQuadraticOuterCoupling] using hbound
  nlinarith [abs_nonneg kappa]

/-- Explicit deterministic finite-volume norm ceiling for one complete
iterated-A2 static tree. -/
theorem norm_iteratedQuadraticSecondPicardStaticCoefficient_le
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa R : Real) (hR : 0 <= R)
    (hfrequency : forall mode, modeFrequencySq m mode <= 5)
    (radius : Lattice.Site N -> Real)
    (hradius : forall mode, |radius mode| <= R)
    (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N) :
    ‖iteratedQuadraticSecondPicardStaticCoefficient
        m kappa radius observed term‖ <=
      4 * |kappa| ^ 2 * R ^ 3 := by
  by_cases hwpos : 0 < modeFrequency m observed
  · have houter := norm_outerCoupling_mul_interactionTensor_le_eight_absKappa
      m kappa hfrequency observed (iteratedQuadraticOuterModes term)
    have hinner := norm_firstPicardCoordinateBranchStaticCoefficient_le
      m kappa R hR hfrequency radius hradius
        (iteratedQuadraticFirstPicardMode term)
        (iteratedQuadraticInnerEntry term)
    have hfree := hradius (iteratedQuadraticFreeMode term)
    have hfreeHalf : |radius (iteratedQuadraticFreeMode term) / 2| <= R / 2 := by
      rw [abs_div, abs_of_pos (by norm_num : (0 : Real) < 2)]
      exact div_le_div_of_nonneg_right hfree (by norm_num)
    unfold iteratedQuadraticSecondPicardStaticCoefficient
    rw [if_pos hwpos]
    change
      ‖(physlibIteratedQuadraticOuterCoupling m kappa observed *
          (interactionTensor m 3
            (Fin.cons observed (iteratedQuadraticOuterModes term)) : Complex)) *
        ((radius (iteratedQuadraticFreeMode term) / 2 : Real) : Complex) *
        firstPicardCoordinateBranchStaticCoefficient m kappa radius
          (iteratedQuadraticFirstPicardMode term)
          (iteratedQuadraticInnerEntry term)‖ <= _
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    calc
      _ <= (8 * |kappa|) * (R / 2) * (|kappa| * R ^ 2) := by
        gcongr
      _ = 4 * |kappa| ^ 2 * R ^ 3 := by ring
  · unfold iteratedQuadraticSecondPicardStaticCoefficient
    rw [if_neg hwpos]
    simp only [norm_zero]
    exact mul_nonneg
      (mul_nonneg (by positivity : 0 <= (4 : Real)) (sq_nonneg |kappa|))
      (pow_nonneg hR 3)

/-! ## Actual iid-weight integrability -/

variable {Omega : Type*} [MeasurableSpace Omega]

/-- Pointwise actual iid specialization of the deterministic ceiling. -/
theorem norm_actualIteratedA2StaticWeightSample_le
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N]
    (kappa R : Real) (hR : 0 <= R)
    (radius : Omega -> Lattice.Site N -> Real)
    (hradius : forall sample mode, |radius sample mode| <= R)
    (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N)
    (sample : Omega) :
    ‖actualIteratedA2StaticWeightSample ensemble kappa radius observed term
        sample‖ <=
      4 * |kappa| ^ 2 * R ^ 3 := by
  exact norm_iteratedQuadraticSecondPicardStaticCoefficient_le
    (ensemble.restrictPositiveMass (N := N) sample) kappa R hR
      (iid_modeFrequencySq_le_five ensemble sample) (radius sample)
      (hradius sample) observed term

/-- A bounded measurable actual static weight is integrable under the iid
probability law, with a completely explicit norm ceiling. -/
theorem integrable_actualIteratedA2StaticWeightSample
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N]
    (kappa R : Real) (hR : 0 <= R)
    (radius : Omega -> Lattice.Site N -> Real)
    (hradius : forall sample mode, |radius sample mode| <= R)
    (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N)
    (hweight : Measurable
      (actualIteratedA2StaticWeightSample ensemble kappa radius observed term)) :
    Integrable
      (actualIteratedA2StaticWeightSample ensemble kappa radius observed term)
      ensemble.probability := by
  let _ : IsProbabilityMeasure ensemble.probability :=
    ⟨ensemble.probability_univ⟩
  exact Integrable.of_bound hweight.aestronglyMeasurable
    (4 * |kappa| ^ 2 * R ^ 3)
    (ae_of_all _ fun sample =>
      norm_actualIteratedA2StaticWeightSample_le ensemble kappa R hR radius
        hradius observed term sample)

end

end CanonicalIIDCoerciveIteratedA2StaticWeightIntegrability
end ArchonPhysics
