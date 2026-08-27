import ArchonPhysics.FreeFPUTRepeatedChildOppositeSignCorrection

/-!
# Consumer: equal-child, opposite-sign local FPUT stratum

These contracts expose the exact local eight-tree calculation.  The final
outside-orbit witness is essential: zero charge allows coherent partners
beyond the input-swap orbit, so this consumer does not silently promote the
local identity to a complete coherent-fiber theorem.
-/

namespace ArchonPhysicsConsumers.Thermalization

open ArchonPhysics
open ArchonPhysics.FreeFPUTAllDistinctConnectedReturnFiber
open ArchonPhysics.FreeFPUTCollisionMismatchBridge
open ArchonPhysics.FreeFPUTEnergyCollisionWeightBridge
open ArchonPhysics.FreeFPUTQuadraticTermSwapSymmetry
open ArchonPhysics.FreeFPUTRepeatedChildOppositeSignCorrection
open ArchonPhysics.FreeFPUTTensorPhaseExpansion
open ArchonPhysics.MicroscopicFiniteTimeCollisionPolynomial
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.NormalizedModeCoupling
open ArchonPhysics.SignedThreeWaveCollisionFlux

noncomputable section

/-- Opposite signs leave a two-element input-swap orbit. -/
theorem problem_repeatedChildOppositeSign_swapOrbit_card
    {N : Nat} [NeZero N] (q : QuadraticPhaseTerm N)
    (hRepeated : RepeatedChildOppositeSign q) :
    (quadraticSwapOrbit q).card = 2 :=
  card_quadraticSwapOrbit_eq_two_of_repeatedChildOppositeSign q hRepeated

/-- The same-mode, opposite-sign quadratic phase charge is zero. -/
theorem problem_repeatedChildOppositeSign_charge_zero
    {N : Nat} [NeZero N] (q : QuadraticPhaseTerm N)
    (hRepeated : RepeatedChildOppositeSign q) :
    quadraticPhaseCharge q = 0 :=
  quadraticPhaseCharge_eq_zero_of_repeatedChildOppositeSign q hRepeated

/-- All eight literal connected trees remain distinct. -/
theorem problem_repeatedChildOppositeSign_connectedImage_card
    {N : Nat} [NeZero N] (observed : Lattice.Site N)
    (q : QuadraticPhaseTerm N)
    (hSeparated : ObservedSeparatedRepeatedChildOppositeSign observed q) :
    (allDistinctConnectedReturnImage observed q).card = 8 :=
  card_allDistinctConnectedReturnImage_of_repeatedChildOppositeSign
    observed q hSeparated

/-- The two four-tree feedback families cancel. -/
theorem problem_repeatedChildOppositeSign_feedback_zero
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa time : Real)
    (energy : Lattice.Site N → Real) (observed : Lattice.Site N)
    (q : QuadraticPhaseTerm N)
    (hSeparated : ObservedSeparatedRepeatedChildOppositeSign observed q)
    (hEnergy : ∀ mode, 0 ≤ energy mode)
    (hPositive : PositiveModeTuple m (quadraticCollisionModes observed q)) :
    repeatedChildOppositeSignConnectedReturnFeedbackSum
        m kappa time energy observed q = 0 :=
  repeatedChildOppositeSignConnectedReturnFeedbackSum_eq_zero
    m kappa time energy observed q hSeparated hEnergy hPositive

/-- The local A1 gain and connected feedback equal four signed collision
brackets, with zero repeated-mode correction. -/
theorem problem_repeatedChildOppositeSign_local_gain_feedback
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa time : Real)
    (energy : Lattice.Site N → Real) (observed : Lattice.Site N)
    (q : QuadraticPhaseTerm N)
    (hSeparated : ObservedSeparatedRepeatedChildOppositeSign observed q)
    (hEnergy : ∀ mode, 0 ≤ energy mode)
    (hPositive : PositiveModeTuple m (quadraticCollisionModes observed q)) :
    repeatedChildOppositeSignLocalGainFeedback
        m kappa time energy observed q =
      4 * finiteTimeCollisionKernel m kappa
          (quadraticCollisionSign q) time
          (quadraticCollisionModes observed q) *
        quadraticSignedCollisionFlux q
          (modeAction energy (modeFrequency m)) observed :=
  repeatedChildOppositeSignLocalGainFeedback_eq_four_signedFlux
    m kappa time energy observed q hSeparated hEnergy hPositive

/-- An explicit charge-matched term outside the swap orbit records the
remaining zero-charge cross-orbit coherence boundary. -/
theorem problem_repeatedChildOppositeSign_crossOrbit_witness
    {N : Nat} [NeZero N] (observed : Lattice.Site N)
    (q : QuadraticPhaseTerm N)
    (hSeparated : ObservedSeparatedRepeatedChildOppositeSign observed q) :
    quadraticPhaseCharge (canonicalOppositeSignTermAt observed) =
        quadraticPhaseCharge q ∧
      canonicalOppositeSignTermAt observed ∉ quadraticSwapOrbit q :=
  ⟨canonicalOppositeSignTermAt_observed_charge_eq observed q hSeparated.1,
    canonicalOppositeSignTermAt_observed_not_mem_swapOrbit
      observed q hSeparated⟩

#print axioms problem_repeatedChildOppositeSign_swapOrbit_card
#print axioms problem_repeatedChildOppositeSign_charge_zero
#print axioms problem_repeatedChildOppositeSign_connectedImage_card
#print axioms problem_repeatedChildOppositeSign_feedback_zero
#print axioms problem_repeatedChildOppositeSign_local_gain_feedback
#print axioms problem_repeatedChildOppositeSign_crossOrbit_witness

end

end ArchonPhysicsConsumers.Thermalization
