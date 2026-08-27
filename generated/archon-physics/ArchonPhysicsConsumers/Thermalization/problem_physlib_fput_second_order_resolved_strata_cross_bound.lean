import ArchonPhysics.PhyslibFPUTSecondOrderResolvedStrataCrossBound

/-!
# Consumer gate: physical cross bound after all resolved F2 strata
-/

namespace ArchonPhysicsConsumers.Thermalization

open ArchonPhysics
open ArchonPhysics.FreeFPUTAllDistinctRepresentativeSignedGainLoss
open ArchonPhysics.FreeFPUTEnergyCollisionWeightBridge
open ArchonPhysics.FreeFPUTTensorPhaseExpansion
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.PhyslibFPUTSecondOrderResolvedStrataCrossBound

noncomputable section

/-- The original normalized second-order Haar coefficient, after subtracting
the all-distinct signed flux, all five degenerate gain strata, and all four
degenerate feedback strata, obeys the explicit physical cross bound. -/
theorem problem_abs_secondOrderHaar_sub_allResolvedStrata_le
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
        (modeFrequency m observed * time) :=
  abs_normalizedSecondOrderHaarBroadening_sub_resolvedStrata_le
    m kappa beta energy observed energyBound henergyBoundNonneg
    henergy henergyBound htime homega

#print axioms problem_abs_secondOrderHaar_sub_allResolvedStrata_le

end

end ArchonPhysicsConsumers.Thermalization
