import ArchonPhysics.FreeFPUTAllDistinctCounterrotatingSignedFluxDecay

namespace ArchonPhysicsConsumers.Thermalization

open ArchonPhysics
open ArchonPhysics.FreeFPUTAllDistinctCounterrotatingSignedFluxDecay
open ArchonPhysics.FreeFPUTAllDistinctRepresentativeSignedGainLoss
open ArchonPhysics.FreeFPUTEnergyCollisionWeightBridge
open ArchonPhysics.ModalPhaseMismatch

noncomputable section

/-- Consumer-facing exact all-distinct sign-sector partition. -/
theorem problem_allDistinctSignedFlux_eq_noncounterrotating_add_counterrotating
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa time : Real)
    (energy : Lattice.Site N → Real) (observed : Lattice.Site N) :
    allDistinctRepresentativeSignedFluxSum
        m kappa time energy observed =
      allDistinctNoncounterrotatingSignedFluxSum
          m kappa time energy observed +
        allDistinctCounterrotatingSignedFluxSum
          m kappa time energy observed :=
  allDistinctRepresentativeSignedFluxSum_eq_noncounterrotating_add_counterrotating
    m kappa time energy observed

/-- Consumer-facing inverse-time bound for the complete all-plus branch. -/
theorem problem_abs_allDistinctCounterrotatingSignedFluxSum_le_inverseTime
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa : Real)
    (energy : Lattice.Site N → Real) (observed : Lattice.Site N)
    {time : Real} (htime : 0 < time)
    (homega : 0 < modeFrequency m observed)
    (henergy : ∀ mode, 0 ≤ energy mode) :
    |allDistinctCounterrotatingSignedFluxSum
        m kappa time energy observed| ≤
      allDistinctCounterrotatingStaticFluxMass
          m kappa energy observed *
        ((2 / modeFrequency m observed) ^ 2 / time) :=
  abs_allDistinctCounterrotatingSignedFluxSum_le_inverseTime
    m kappa energy observed htime homega henergy

#print axioms
  problem_allDistinctSignedFlux_eq_noncounterrotating_add_counterrotating
#print axioms
  problem_abs_allDistinctCounterrotatingSignedFluxSum_le_inverseTime

end

end ArchonPhysicsConsumers.Thermalization
