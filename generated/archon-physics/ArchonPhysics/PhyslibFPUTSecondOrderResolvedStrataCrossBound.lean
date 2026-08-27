import ArchonPhysics.FreeFPUTCrossOrbitCoefficientVolumeBound
import ArchonPhysics.FreeFPUTNonAllDistinctFeedbackTreePartition
import ArchonPhysics.PhyslibFPUTSecondOrderDegenerateGainStrataFormula
import ArchonPhysics.PhyslibHamiltonianFirstLayerBridge

/-!
# Physical cross bound after resolving all degenerate second-order strata

The exact normalized second-order Haar formula already separates the
all-distinct signed flux, five degenerate A1 gain strata, four intrinsic
degenerate feedback strata, and the real cross-swap-orbit coherence term.
After subtracting the first ten displayed contributions, only that cross
term remains.  The physical energy-volume estimate therefore controls the
absolute error by an explicit `O(N^2 / T)` bound.

The Physlib coupling in the exact formula is rewritten using the proved
Hamiltonian coupling identity; it is not identified definitionally.  The
quartic parameter `beta` remains in the original Haar coefficient but drops
out of this second-order cross bound.  No gain or feedback stratum is claimed
small here: all nine are subtracted exactly.
-/

namespace ArchonPhysics.PhyslibFPUTSecondOrderResolvedStrataCrossBound

open MeasureTheory
open UnitAddTorus
open ArchonPhysics
open ArchonPhysics.DuhamelTwoStepMomentAlgebra
open ArchonPhysics.FreeFPUTA0DirectCubicBridge
open ArchonPhysics.FreeFPUTAllDistinctRepresentativeSignedGainLoss
open ArchonPhysics.FreeFPUTCrossOrbitCoefficientVolumeBound
open ArchonPhysics.FreeFPUTEnergyCollisionWeightBridge
open ArchonPhysics.FreeFPUTNonAllDistinctFeedbackTreePartition
open ArchonPhysics.FreeFPUTPositiveDegenerateRepresentativeA1Partition
open ArchonPhysics.FreeFPUTSwapOrbitCollisionCorrection
open ArchonPhysics.FreeFPUTTensorPhaseExpansion
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.PhyslibFPUTFirstPicardDecomposition
open ArchonPhysics.PhyslibFPUTIteratedQuadraticSecondPicardCharacterFamily
open ArchonPhysics.PhyslibFPUTSecondOrderDegenerateGainStrataFormula
open ArchonPhysics.PhyslibFPUTSecondPicardHistoryBridge
open ArchonPhysics.PhyslibHamiltonianFirstLayerBridge
open ArchonPhysics.RandomPhaseMoments

noncomputable section

/-- The five mutually exclusive positive degenerate A1 gain strata. -/
def fiveDegenerateGainStrataSum
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa time : Real)
    (energy : Lattice.Site N → Real) (observed : Lattice.Site N) : Real :=
  positiveRepeatedChildSameSignRepresentativeA1Gain
      m kappa time energy observed +
    positiveRepeatedChildOppositeSignRepresentativeA1Gain
      m kappa time energy observed +
    positiveObservedOnlyAtChildZeroRepresentativeA1Gain
      m kappa time energy observed +
    positiveObservedOnlyAtChildOneRepresentativeA1Gain
      m kappa time energy observed +
    positiveObservedAtBothChildrenRepresentativeA1Gain
      m kappa time energy observed

/-- The four mutually exclusive intrinsic non-all-distinct feedback strata. -/
def fourDegenerateFeedbackStrataSum
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa time : Real)
    (radius : Lattice.Site N → Real) (observed : Lattice.Site N) : Real :=
  positiveInnerCarrierFreeRepeatedAwayFeedbackRemainder
      m kappa time radius observed +
    positiveInnerObservedOnlyAtCarrierFeedbackRemainder
      m kappa time radius observed +
    positiveInnerObservedOnlyAtFreeFeedbackRemainder
      m kappa time radius observed +
    positiveInnerObservedAtCarrierAndFreeFeedbackRemainder
      m kappa time radius observed

/-- The original normalized second-order Physlib Haar coefficient. -/
def normalizedSecondOrderHaarBroadening
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa beta : Real)
    (energy : Lattice.Site N → Real) (observed : Lattice.Site N)
    (time : Real) : Real :=
  (1 / time) *
    (∫ phase : UnitAddTorus (Lattice.Site N),
      twoStepSecondCoefficient
        (canonicalFreeComplexInitialAmplitude
          (phaseEnergyRadius energy (modeFrequency m))
          (modeFrequency m) phase observed)
        (physlibQuadraticFirstPicardCoefficient m kappa
          (phaseEnergyRadius energy (modeFrequency m)) phase time observed)
        (physlibFPUTSecondPicardCoefficient m kappa beta observed
          (phaseEnergyRadius energy (modeFrequency m)) phase time)
      ∂finitePhaseHaarLaw (Lattice.Site N))

/-- Exact resolved-strata identity before estimating cross coherence. -/
theorem normalizedSecondOrderHaarBroadening_eq_resolvedStrata_add_cross
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa beta : Real)
    (energy : Lattice.Site N → Real) (observed : Lattice.Site N)
    {time : Real} (htime : 0 < time)
    (homega : 0 < modeFrequency m observed)
    (henergy : ∀ mode, 0 ≤ energy mode) :
    normalizedSecondOrderHaarBroadening
        m kappa beta energy observed time =
      allDistinctRepresentativeSignedFluxSum m kappa time energy observed +
        fiveDegenerateGainStrataSum m kappa time energy observed +
        fourDegenerateFeedbackStrataSum m kappa time
          (phaseEnergyRadius energy (modeFrequency m)) observed +
        (freeQuadraticCrossSwapOrbitCoherentRemainder
          (physlibQuadraticCoupling m kappa 1 observed) m observed
          (phaseEnergyRadius energy (modeFrequency m)) (modeFrequency m)
          time).re := by
  unfold normalizedSecondOrderHaarBroadening fiveDegenerateGainStrataSum
    fourDegenerateFeedbackStrataSum
  rw [secondOrderBroadening_eq_signedFlux_add_fiveDegenerateGainStrata
    m kappa beta energy observed htime homega henergy]
  rw [positiveInnerNonAllDistinctFeedbackRemainder_eq_four_strata]
  ring

/-- After subtracting the signed flux, all five gain strata, and all four
feedback strata, the remaining absolute error is controlled by the proved
physical cross bound. -/
theorem abs_normalizedSecondOrderHaarBroadening_sub_resolvedStrata_le
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa beta : Real)
    (energy : Lattice.Site N → Real) (observed : Lattice.Site N)
    (energyBound : Real) (henergyBoundNonneg : 0 ≤ energyBound)
    (henergy : ∀ mode, 0 ≤ energy mode)
    (henergyBound : ∀ mode, energy mode ≤ energyBound)
    {time : Real} (htime : 0 < time)
    (homega : 0 < modeFrequency m observed) :
    |normalizedSecondOrderHaarBroadening
        m kappa beta energy observed time -
      allDistinctRepresentativeSignedFluxSum m kappa time energy observed -
      fiveDegenerateGainStrataSum m kappa time energy observed -
      fourDegenerateFeedbackStrataSum m kappa time
        (phaseEnergyRadius energy (modeFrequency m)) observed| ≤
      2 * (N : Real) ^ 2 * kappa ^ 2 * energyBound ^ 2 /
        (modeFrequency m observed * time) := by
  have hresolved :=
    normalizedSecondOrderHaarBroadening_eq_resolvedStrata_add_cross
      m kappa beta energy observed htime homega henergy
  have hcross := abs_re_physical_crossOrbit_le_energy_volume
    kappa 1 m observed energy energyBound henergyBoundNonneg
    henergy henergyBound homega htime
  rw [physlibQuadraticCoupling_eq_physicalQuadraticCoupling
    m kappa 1 observed] at hresolved
  rw [hresolved]
  ring_nf at hcross ⊢
  exact hcross

end

end ArchonPhysics.PhyslibFPUTSecondOrderResolvedStrataCrossBound
