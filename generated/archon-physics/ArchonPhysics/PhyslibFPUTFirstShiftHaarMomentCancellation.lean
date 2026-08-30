import ArchonPhysics.PhyslibFPUTActualOneBlockKineticLittleO
import ArchonPhysics.PhyslibFPUTReferenceBlockKineticResidual

/-!
# First-shift Haar moment cancellation for the physical FPUT chain

For a canonical Haar initial phase, the free amplitude `A0` has one phase
leg and the quadratic first-Picard amplitude `A1` has two.  Their charges
therefore cannot match.  This module records two consequences at the first
Hamiltonian time shift.

* The canonical two-step Haar reference moment has derivative zero with
  respect to the coupling at `g = 0`.  This is the exact first-variation
  cancellation, not a triangle estimate.
* For a genuine frozen finite-volume Physlib FPUT Hamiltonian trajectory,
  the endpoint quadratic modal moment differs from that two-step reference
  by an explicit `|g|^3` envelope.

The collision contribution `g^2 T Q_T` belongs to the reference endpoint and
is deliberately retained.  Thus the second statement is the discrepancy
needed by shifted-block telescoping; it is not the raw increment from time
zero.  No conclusion that the shifted full phase law is Haar is made here.
-/

namespace ArchonPhysics.PhyslibFPUTFirstShiftHaarMomentCancellation

open MeasureTheory
open Set
open UnitAddTorus
open ArchonPhysics
open ArchonPhysics.CoerciveHamiltonianPhyslib
open ArchonPhysics.DuhamelTwoStepMomentAlgebra
open ArchonPhysics.FiniteSecondOrderCharacterFamilyExpansion
open ArchonPhysics.FreeFPUTA0DirectCubicBridge
open ArchonPhysics.FreeFPUTTensorPhaseExpansion
open ArchonPhysics.MassWeightedHamiltonianDynamics
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.PhyslibFPUTActualHaarPostSecondPicardDecomposition
open ArchonPhysics.PhyslibFPUTActualHaarSecondOrderEnergyDrift
open ArchonPhysics.PhyslibFPUTActualOneBlockKineticLittleO
open ArchonPhysics.PhyslibFPUTCubicHistoryLipschitzRemainder
open ArchonPhysics.PhyslibFPUTMomentKineticEulerShadowing
open ArchonPhysics.PhyslibFPUTCompleteSecondPicardCharacterFamily
open ArchonPhysics.PhyslibFPUTSecondOrderHaarCharacterExpansion
open ArchonPhysics.PhyslibFPUTRenormalizedHaarMomentDefect
open ArchonPhysics.PhyslibFPUTReferenceBlockKineticResidual
open ArchonPhysics.PhyslibFPUTSecondPicardHistoryBridge
open ArchonPhysics.PhyslibHamiltonDuhamel
open ArchonPhysics.PhyslibHamiltonDerivativeBridge
open ArchonPhysics.QuadraticTensorHistoryExpansion
open ArchonPhysics.RandomPhaseMoments

noncomputable section

/-- Exact first-variation cancellation in the coupling.  The canonical Haar
charge expansion contains powers `g^0`, `g^2`, `g^3`, and `g^4`, but no
`g^1` term.  The collision coefficient at order two is retained exactly. -/
theorem physlibReferenceTwoStepHaarMoment_sub_initial_eq_no_firstOrder
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa beta : Real)
    (radius : Lattice.Site N -> Real) (time : Real)
    (observed : Lattice.Site N) (g : Real)
    (homega : 0 < modeFrequency m observed) :
    physlibReferenceTwoStepHaarMoment
          m kappa beta g radius time observed -
        physlibReferenceInitialHaarMoment m radius observed =
      g ^ 2 * physlibHaarFiniteTimeKineticCoefficient
          m kappa beta radius time observed +
        g ^ 3 * equalChargeFamilyInterference
          (physlibQuadraticFirstPicardCharacterCoefficient
            m kappa radius time observed)
          quadraticPhaseCharge
          (completeSecondPicardCoefficient
            m kappa beta radius observed time)
          completeSecondPicardCharge +
        g ^ 4 * sameChargeFamilySquare
          (completeSecondPicardCoefficient
            m kappa beta radius observed time)
          completeSecondPicardCharge := by
  have h := physlibReferenceBlock_sub_kineticCoefficient_eq_highOrder
    m kappa beta g radius time observed homega
  linarith

/-- At the first time shift, the genuine Hamiltonian Haar quadratic moment
is cubically close to the canonical two-step Picard Haar reference endpoint.

The hypotheses are the physical finite-volume energy-window hypotheses used
by the proved two-time Duhamel remainder estimate.  In particular, no RPA,
restart, coupling, or diagram-remainder certificate is an input. -/
theorem abs_actualHaarModalMoment_firstShift_sub_twoStepReference_le_abs_cube
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N)
    {mUpper kappa beta g H T : Real}
    (hmUpper0 : 0 <= mUpper) (hmassUpper : forall i, m.mass i <= mUpper)
    (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (observed : Lattice.Site N)
    (p q : UnitAddTorus (Lattice.Site N) -> Time -> HilbertConfiguration N)
    (hp : forall phase, Differentiable Real (p phase))
    (hq : forall phase, Differentiable Real (q phase))
    (hHamilton : forall phase,
      SatisfiesHamiltonEquations m kappa beta g (p phase) (q phase))
    (radius : Lattice.Site N -> Real)
    (homega : 0 < modeFrequency m observed)
    (hinitial : forall phase mode,
      physlibModeAmplitude m mode (p phase) (q phase) 0 =
        canonicalFreeComplexInitialAmplitude
          radius (modeFrequency m) phase mode)
    (hT : 0 <= T)
    (hgauge : forall phase s, s ∈ Icc 0 T -> ∑ i, m.mass i *
      asConfiguration ((realReparametrize (q phase)) s) i = 0)
    (henergy : forall phase s, s ∈ Icc 0 T ->
      CoerciveLatticeEnergy.hamiltonian m kappa beta g
        (asConfiguration ((realReparametrize (p phase)) s))
        (asConfiguration ((realReparametrize (q phase)) s)) <= H)
    (hzeroHistory : forall phase s, s ∈ Icc 0 T -> forall mode,
      modeFrequency m mode = 0 ->
        physlibModalHistoryDefect m (q phase) radius phase s mode = 0)
    (hmeasurable : Measurable
      (actualPostSecondPicardEnergyCorrection
        m kappa beta g observed q radius T)) :
    |actualHaarModalMoment m observed p q T -
        physlibReferenceTwoStepHaarMoment
          m kappa beta g radius T observed| <=
      |g| ^ 3 *
        physlibHaarCubicLipschitzEnergyCorrectionUnitEnvelope
          m mUpper kappa beta g H radius T observed := by
  let C := physlibHaarCubicLipschitzEnergyCorrectionEnvelope
    m mUpper kappa beta g H radius T observed
  have hdecomposition :=
    integral_actualPhaseModalNormSq_eq_matchedCharge_add_boundedCorrection
      m kappa beta g observed p q hp hq hHamilton radius homega
        (fun phase => hinitial phase observed) T hmeasurable
        (C := C) (fun phase => by
          apply abs_actualPostSecondPicardEnergyCorrection_le
            m kappa beta g observed q radius T phase homega
          exact
            norm_afterSecondPicardRemainderCoefficient_le_cubicLipschitzEnergyWindow
              m hmUpper0 hmassUpper hbeta observed (p phase) (q phase)
                (hp phase) (hq phase) (hHamilton phase) radius phase
                  (hinitial phase) homega hT (hgauge phase)
                    (henergy phase) (hzeroHistory phase))
  rcases hdecomposition with ⟨hactual, hcorrection⟩
  have href := physlibReferenceTwoStepHaarMoment_eq_matchedCharge
    m kappa beta g radius T observed homega
  dsimp only [C] at hcorrection
  rw [physlibHaarCubicLipschitzEnergyCorrectionEnvelope_abs_cube_factor] at hcorrection
  unfold actualHaarModalMoment
  rw [hactual, href]
  simpa only [add_sub_cancel_left] using hcorrection

end

end ArchonPhysics.PhyslibFPUTFirstShiftHaarMomentCancellation
