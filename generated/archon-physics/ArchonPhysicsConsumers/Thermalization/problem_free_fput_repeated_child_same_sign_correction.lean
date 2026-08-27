import ArchonPhysics.FreeFPUTRepeatedChildSameSignCorrection

/-!
# Consumer: repeated-child same-sign FPUT correction

This consumer checks the exact fixed-swap-orbit and four-tree multiplicities
on the equal-child/equal-sign boundary stratum.  The final theorem exposes,
rather than removes, the repeated-mode correction to the signed flux.
-/

namespace ArchonPhysicsConsumers.Thermalization

open ArchonPhysics
open ArchonPhysics.FreeFPUTAllDistinctConnectedReturnFiber
open ArchonPhysics.FreeFPUTCollisionMismatchBridge
open ArchonPhysics.FreeFPUTEnergyCollisionWeightBridge
open ArchonPhysics.FreeFPUTQuadraticTermSwapSymmetry
open ArchonPhysics.FreeFPUTRepeatedChildSameSignCorrection
open ArchonPhysics.FreeFPUTTensorPhaseExpansion
open ArchonPhysics.MicroscopicFiniteTimeCollisionPolynomial
open ArchonPhysics.MatchedIteratedQuadraticCanonicalReturnChannel
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.NormalizedModeCoupling
open ArchonPhysics.SignedThreeWaveCollisionFlux

noncomputable section

/-- The repeated child is one canonical swap-orbit entry. -/
theorem problem_repeatedChildSameSign_swapOrbit_card
    {N : Nat} [NeZero N] (q : QuadraticPhaseTerm N)
    (hRepeated : RepeatedChildSameSign q) :
    (quadraticSwapOrbit q).card = 1 :=
  card_quadraticSwapOrbit_eq_one_of_repeatedChildSameSign q hRepeated

/-- This fixed orbit is nonzero-charge, so equal-charge coherence has no
partner outside the singleton swap orbit. -/
theorem problem_repeatedChildSameSign_sameCharge_mem_swapOrbit
    {N : Nat} [NeZero N] (q right : QuadraticPhaseTerm N)
    (hRepeated : RepeatedChildSameSign q)
    (hCharge : quadraticPhaseCharge q = quadraticPhaseCharge right) :
    right ∈ quadraticSwapOrbit q :=
  mem_quadraticSwapOrbit_of_charge_eq_repeatedChildSameSign
    q right hRepeated hCharge

/-- The nominal eight-index constructor image contains four literal trees
on this boundary stratum. -/
theorem problem_repeatedChildSameSign_connectedImage_card
    {N : Nat} [NeZero N] (observed : Lattice.Site N)
    (q : QuadraticPhaseTerm N)
    (hSeparated : ObservedSeparatedRepeatedChildSameSign observed q) :
    (allDistinctConnectedReturnImage observed q).card = 4 := by
  rw [allDistinctConnectedReturnImage_eq_repeatedChildImage
      observed q hSeparated.1,
    card_repeatedChildConnectedReturnImage observed q hSeparated]

/-- The canonical first-match selector keeps every four-placement tree out
of the two tadpole labels. -/
theorem problem_repeatedChildSameSign_canonical_not_tadpole
    {N : Nat} [NeZero N] (observed : Lattice.Site N)
    (q : QuadraticPhaseTerm N) (index : RepeatedChildConnectedReturnIndex)
    (hSeparated : ObservedSeparatedRepeatedChildSameSign observed q) :
    canonicalReturnChannel observed
          (repeatedChildConnectedReturnMap observed q index) ≠
        .freeObservedInnerZeroCancelsInnerOne ∧
      canonicalReturnChannel observed
          (repeatedChildConnectedReturnMap observed q index) ≠
        .freeObservedInnerOneCancelsInnerZero :=
  repeatedChildConnectedReturnMap_canonical_not_tadpole
    observed q index hSeparated

/-- Exact repeated-child gain--feedback correction contract. -/
theorem problem_repeatedChildSameSign_gainFeedback_correction
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa time : Real)
    (energy : Lattice.Site N → Real) (observed : Lattice.Site N)
    (q : QuadraticPhaseTerm N)
    (hSeparated : ObservedSeparatedRepeatedChildSameSign observed q)
    (hEnergy : ∀ mode, 0 ≤ energy mode)
    (hPositive : PositiveModeTuple m (quadraticCollisionModes observed q)) :
    repeatedChildSameSignLocalGainFeedback
        m kappa time energy observed q =
      finiteTimeCollisionKernel m kappa
          (quadraticCollisionSign q) time
          (quadraticCollisionModes observed q) *
        quadraticSignedCollisionFlux q
          (modeAction energy (modeFrequency m)) observed +
      2 * finiteTimeCollisionKernel m kappa
          (quadraticCollisionSign q) time
          (quadraticCollisionModes observed q) *
        (quadraticInputInteractionSign q 0).coefficient *
        modeAction energy (modeFrequency m) observed *
        modeAction energy (modeFrequency m) (q.1 0) :=
  repeatedChildSameSignLocalGainFeedback_eq_signedFlux_add_correction
    m kappa time energy observed q hSeparated hEnergy hPositive

#print axioms problem_repeatedChildSameSign_swapOrbit_card
#print axioms problem_repeatedChildSameSign_sameCharge_mem_swapOrbit
#print axioms problem_repeatedChildSameSign_connectedImage_card
#print axioms problem_repeatedChildSameSign_canonical_not_tadpole
#print axioms problem_repeatedChildSameSign_gainFeedback_correction

end

end ArchonPhysicsConsumers.Thermalization
