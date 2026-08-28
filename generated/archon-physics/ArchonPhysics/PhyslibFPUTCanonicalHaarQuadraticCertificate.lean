import ArchonPhysics.PhyslibFPUTCanonicalQLevelQuadratic
import ArchonPhysics.PhyslibFPUTCrossOrbitEnergyQuadratic
import ArchonPhysics.PhyslibFPUTEnergyProfileCollisionLipschitz

/-!
# Constructed quadratic certificate for the canonical finite-time Haar field

For positive block time, the exact q-level closure identifies the canonical
Haar collision with a finite sum of quadratic signed-flux terms and the
exceptional cross-orbit coherent term.  The latter agrees, on nonnegative
energies, with the zero-charge polynomial constructed in the companion
module.  Consequently no model-specific quadratic representation is left as
an assumed structure field: this file constructs the certificate itself.
-/

namespace ArchonPhysics.PhyslibFPUTCanonicalHaarQuadraticCertificate

open ArchonPhysics
open ArchonPhysics.FreeFPUTObservedChildGlobalFeedbackClosure
open ArchonPhysics.FreeFPUTObservedChildQLevelGainLossClosure
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.PhyslibFPUTCanonicalQLevelQuadratic
open ArchonPhysics.PhyslibFPUTCanonicalQuadraticClosure
open ArchonPhysics.PhyslibFPUTCrossOrbitEnergyQuadratic
open ArchonPhysics.PhyslibFPUTEnergyProfileCollisionLipschitz
open ArchonPhysics.PhyslibFPUTEnergyProfileKineticShadowing
open ArchonPhysics.PhyslibFPUTFirstPicardDecomposition
open ArchonPhysics.PhyslibFPUTSecondOrderQLevelUnifiedClosure
open ArchonPhysics.PhyslibFPUTSecondOrderUnifiedDegenerateClosure

noncomputable section

/-- The polynomial field used to construct one output row of the canonical
Haar quadratic kernel.  It contains every exact q-level summand, including
the zero-charge polynomial proxy for cross-orbit coherence. -/
def canonicalHaarEnergyQuadraticPolynomial
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa time : Real)
    (observed : PositiveFrequencyMode m)
    (energy : PositiveEnergyProfile m) : Real :=
  modeFrequency m observed *
    (qLevelResolvedSecondOrderSignedFluxMain m kappa time
          (extendPositiveEnergyProfile m energy) observed +
      allEqualOrbitGainSum m kappa time
          (extendPositiveEnergyProfile m energy) observed +
      repeatedAwayFixedPointCorrection m kappa time
          (extendPositiveEnergyProfile m energy) observed +
      observedChildPlacementCorrection m kappa time
          (extendPositiveEnergyProfile m energy) observed +
      allEqualChannelFiveCorrection m kappa time
          (extendPositiveEnergyProfile m energy) observed +
      secondOrderCounterrotatingRemainder m kappa time
          (extendPositiveEnergyProfile m energy) observed +
      zeroChargeCrossOrbitEnergyPolynomial
        (physlibQuadraticCoupling m kappa 1 observed) m observed time energy)

/-- Every output row of the displayed polynomial field has a constructed
finite quadratic kernel on the complete positive-frequency profile. -/
theorem isPositiveEnergyQuadratic_canonicalHaarEnergyQuadraticPolynomial
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa time : Real)
    (observed : PositiveFrequencyMode m) :
    IsPositiveEnergyQuadratic m
      (canonicalHaarEnergyQuadraticPolynomial m kappa time observed) := by
  unfold canonicalHaarEnergyQuadraticPolynomial
  exact ((isPositiveEnergyQuadratic_qLevelClosureWithoutCross
      m kappa time observed).add
    (isPositiveEnergyQuadratic_zeroChargeCrossOrbitEnergyPolynomial
      (physlibQuadraticCoupling m kappa 1 observed) m observed time)).const_mul
        (modeFrequency m observed)

/-- Extension of coordinatewise nonnegativity from positive-frequency modes
to the complete modal site type. -/
theorem extendPositiveEnergyProfile_nonneg
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N)
    (energy : PositiveEnergyProfile m)
    (henergy : ∀ mode, 0 ≤ energy mode) :
    ∀ site, 0 ≤ extendPositiveEnergyProfile m energy site := by
  intro site
  by_cases hsite : 0 < modeFrequency m site
  · simpa [extendPositiveEnergyProfile, hsite] using henergy ⟨site, hsite⟩
  · simp [extendPositiveEnergyProfile, hsite]

/-- On nonnegative physical profiles, the canonical Haar collision is exactly
the constructed polynomial field. -/
theorem canonicalHaarEnergyCollision_eq_quadraticPolynomial
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa beta : Real)
    {time : Real} (htime : 0 < time)
    (energy : PositiveEnergyProfile m)
    (henergy : ∀ mode, 0 ≤ energy mode)
    (observed : PositiveFrequencyMode m) :
    canonicalHaarEnergyCollision m kappa beta time energy observed =
      canonicalHaarEnergyQuadraticPolynomial m kappa time observed energy := by
  have hfull := extendPositiveEnergyProfile_nonneg m energy henergy
  rw [canonicalHaarEnergyCollision_apply,
    normalizedSecondOrderHaarBroadening_eq_qLevelUnifiedClosure
      m kappa beta (extendPositiveEnergyProfile m energy) observed
        htime observed.property hfull]
  unfold canonicalHaarEnergyQuadraticPolynomial
  congr 1
  unfold secondOrderCrossOrbitRemainder
  rw [freeQuadraticCrossSwapOrbitCoherentRemainder_re_eq_energyPolynomial
    (physlibQuadraticCoupling m kappa 1 observed) m observed energy time henergy]

/-- For every positive block time, the canonical finite-time Haar energy
collision carries an actual finite quadratic-kernel certificate.  No abstract
representation hypothesis is an input to this constructor. -/
def canonicalHaarQuadraticKernelCertificate
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa beta : Real)
    {time : Real} (htime : 0 < time) :
    CanonicalHaarQuadraticKernelCertificate m kappa beta time := by
  classical
  choose rowKernel hrowKernel using
    (fun observed : PositiveFrequencyMode m ↦
      isPositiveEnergyQuadratic_canonicalHaarEnergyQuadraticPolynomial
        m kappa time observed)
  refine
    { kernel := fun observed first second ↦
        rowKernel observed first second
      represents_nonnegative := ?_ }
  intro energy henergy
  funext observed
  rw [canonicalHaarEnergyCollision_eq_quadraticPolynomial
    m kappa beta htime energy henergy observed]
  simpa only [finiteQuadraticCollisionField] using
    hrowKernel observed energy

end

end ArchonPhysics.PhyslibFPUTCanonicalHaarQuadraticCertificate
