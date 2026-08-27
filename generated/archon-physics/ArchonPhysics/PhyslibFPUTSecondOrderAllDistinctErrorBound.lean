import ArchonPhysics.FreeFPUTCrossOrbitRealDecay
import ArchonPhysics.PhyslibFPUTSecondOrderAllDistinctSignedFluxFormula

/-!
# Quantitative error bound for the all-distinct second-order formula

After subtracting the closed all-distinct signed flux and the two explicit
mode-degenerate remainders, the exact finite-volume second-order Haar formula
contains only the real cross-swap-orbit coherent remainder.  Its existing
fixed-volume estimate therefore gives an explicit inverse-time error bound.

The coefficient on the right is intentionally retained.  No uniformity in
the lattice size is asserted here.
-/

namespace ArchonPhysics.PhyslibFPUTSecondOrderAllDistinctErrorBound

open MeasureTheory
open UnitAddTorus
open ArchonPhysics
open ArchonPhysics.DuhamelTwoStepMomentAlgebra
open ArchonPhysics.FreeFPUTA0DirectCubicBridge
open ArchonPhysics.FreeFPUTAllDistinctRepresentativeSignedGainLoss
open ArchonPhysics.FreeFPUTCrossOrbitRealDecay
open ArchonPhysics.FreeFPUTCrossOrbitZeroChargeBridge
open ArchonPhysics.FreeFPUTPositiveInnerFeedbackPartition
open ArchonPhysics.FreeFPUTPositiveRepresentativeGainPartition
open ArchonPhysics.FreeFPUTSwapOrbitCollisionCorrection
open ArchonPhysics.FreeFPUTTensorPhaseExpansion
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.NormalizedModeCoupling
open ArchonPhysics.PhyslibFPUTFirstPicardDecomposition
open ArchonPhysics.PhyslibFPUTIteratedQuadraticSecondPicardCharacterFamily
open ArchonPhysics.PhyslibFPUTSecondOrderAllDistinctSignedFluxFormula
open ArchonPhysics.PhyslibFPUTSecondPicardHistoryBridge
open ArchonPhysics.RandomPhaseMoments

noncomputable section

/-- Once the signed-flux main term and both positive mode-degenerate
remainders are removed, the original normalized second-order Haar coefficient
has an explicit fixed-volume `O(T⁻¹)` bound. -/
theorem abs_secondOrderBroadening_sub_resolvedTerms_le_inverseTime
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa beta : Real)
    (energy : Lattice.Site N → Real) (observed : Lattice.Site N)
    {time : Real} (htime : 0 < time)
    (homega : 0 < modeFrequency m observed)
    (henergy : ∀ mode, 0 ≤ energy mode) :
    |(1 / time) *
        (∫ phase : UnitAddTorus (Lattice.Site N),
          twoStepSecondCoefficient
            (canonicalFreeComplexInitialAmplitude
              (phaseEnergyRadius energy (modeFrequency m))
              (modeFrequency m) phase observed)
            (physlibQuadraticFirstPicardCoefficient m kappa
              (phaseEnergyRadius energy (modeFrequency m)) phase time observed)
            (physlibFPUTSecondPicardCoefficient m kappa beta observed
              (phaseEnergyRadius energy (modeFrequency m)) phase time)
          ∂finitePhaseHaarLaw (Lattice.Site N)) -
        allDistinctRepresentativeSignedFluxSum
          m kappa time energy observed -
        positiveNonAllDistinctRepresentativeA1GainRemainder
          m kappa time energy observed -
        positiveInnerNonAllDistinctFeedbackRemainder m kappa time
          (phaseEnergyRadius energy (modeFrequency m)) observed| ≤
      ‖freeQuadraticZeroChargeCrossOrbitCoefficient
        (physlibQuadraticCoupling m kappa 1 observed) m observed
        (phaseEnergyRadius energy (modeFrequency m))‖ *
        (4 / (modeFrequency m observed ^ 2 * time)) := by
  rw [secondOrderBroadening_eq_allDistinctSignedFlux_add_remainders
    m kappa beta energy observed htime homega henergy]
  have hcross :=
    abs_re_freeQuadraticCrossSwapOrbitCoherentRemainder_le_inverseTime
      (physlibQuadraticCoupling m kappa 1 observed) m observed
      (phaseEnergyRadius energy (modeFrequency m)) (modeFrequency m)
      homega htime
  convert hcross using 1
  ring_nf

end

end ArchonPhysics.PhyslibFPUTSecondOrderAllDistinctErrorBound
