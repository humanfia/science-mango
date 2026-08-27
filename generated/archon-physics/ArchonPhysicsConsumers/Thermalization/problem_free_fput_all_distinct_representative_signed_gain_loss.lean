import ArchonPhysics.FreeFPUTAllDistinctRepresentativeSignedGainLoss

/-!
# Consumer gate: representative-level all-distinct signed gain--loss

This consumer restates the exact finite representative sum while preserving
the boundary that the connected contribution is still a nested sum of local
eight-tree images.
-/

namespace ArchonPhysicsConsumers.Thermalization

open ArchonPhysics
open ArchonPhysics.FreeFPUTAllDistinctRepresentativeSignedGainLoss
open ArchonPhysics.FreeFPUTCollisionMismatchBridge
open ArchonPhysics.FreeFPUTEnergyCollisionWeightBridge
open ArchonPhysics.MicroscopicFiniteTimeCollisionPolynomial
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.SignedThreeWaveCollisionFlux

noncomputable section

theorem problem_allDistinctRepresentativeSignedGainLossSum_eq_gain_add_feedback
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa time : Real)
    (energy : Lattice.Site N → Real) (observed : Lattice.Site N) :
    allDistinctRepresentativeSignedGainLossSum
        m kappa time energy observed =
      allDistinctRepresentativeA1GainSum
          m kappa time energy observed +
        allDistinctRepresentativeConnectedFeedbackSum
          m kappa time energy observed :=
  allDistinctRepresentativeSignedGainLossSum_eq_gain_add_feedback
    m kappa time energy observed

theorem problem_allDistinctRepresentativeSignedGainLossSum_eq_signedFluxSum
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa time : Real)
    (energy : Lattice.Site N → Real) (observed : Lattice.Site N)
    (hEnergy : ∀ mode, 0 ≤ energy mode) :
    allDistinctRepresentativeSignedGainLossSum
        m kappa time energy observed =
      allDistinctRepresentativeSignedFluxSum
        m kappa time energy observed :=
  allDistinctRepresentativeSignedGainLossSum_eq_signedFluxSum
    m kappa time energy observed hEnergy

theorem problem_allDistinctRepresentativeGain_add_feedback_eq_signedFluxSum
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa time : Real)
    (energy : Lattice.Site N → Real) (observed : Lattice.Site N)
    (hEnergy : ∀ mode, 0 ≤ energy mode) :
    allDistinctRepresentativeA1GainSum
        m kappa time energy observed +
      allDistinctRepresentativeConnectedFeedbackSum
        m kappa time energy observed =
      allDistinctRepresentativeSignedFluxSum
        m kappa time energy observed :=
  allDistinctRepresentativeGain_add_feedback_eq_signedFluxSum
    m kappa time energy observed hEnergy

#print axioms
  problem_allDistinctRepresentativeSignedGainLossSum_eq_gain_add_feedback
#print axioms
  problem_allDistinctRepresentativeSignedGainLossSum_eq_signedFluxSum
#print axioms
  problem_allDistinctRepresentativeGain_add_feedback_eq_signedFluxSum

end

end ArchonPhysicsConsumers.Thermalization
