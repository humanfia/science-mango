import ArchonPhysics.PhyslibFPUTCanonicalQuadraticClosure

/-!
# Quadratic representability of the explicit FPUT q-level closure

Every q-level gain, loss, placement correction, and counterrotating term is a
finite linear combination of products of two modal actions.  This file turns
that displayed algebra into actual finite quadratic kernels on the positive
energy profile.  The exceptional cross-swap-orbit coherent remainder is
treated separately in the next module.
-/

namespace ArchonPhysics.PhyslibFPUTCanonicalQLevelQuadratic

open ArchonPhysics
open ArchonPhysics.FreeFPUTAllDistinctCounterrotatingSignedFluxDecay
open ArchonPhysics.FreeFPUTCollisionMismatchBridge
open ArchonPhysics.FreeFPUTEnergyCollisionWeightBridge
open ArchonPhysics.FreeFPUTObservedChildGlobalFeedbackClosure
open ArchonPhysics.FreeFPUTObservedChildQLevelGainLossClosure
open ArchonPhysics.FreeFPUTQuadraticTermSwapSymmetry
open ArchonPhysics.FreeFPUTRepeatedAwayGlobalFeedbackReindex
open ArchonPhysics.FreeFPUTTensorPhaseExpansion
open ArchonPhysics.MicroscopicFiniteTimeCollisionPolynomial
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.PhyslibFPUTIteratedQuadraticSecondPicardCharacterFamily
open ArchonPhysics.PhyslibFPUTCanonicalQuadraticClosure
open ArchonPhysics.PhyslibFPUTEnergyProfileKineticShadowing
open ArchonPhysics.PhyslibFPUTSecondOrderQLevelUnifiedClosure
open ArchonPhysics.PhyslibFPUTSecondOrderUnifiedDegenerateClosure

noncomputable section

theorem isPositiveEnergyQuadratic_const_modeActionProduct
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (constant : Real)
    (first second : Lattice.Site N) :
    IsPositiveEnergyQuadratic m (fun energy ↦
      constant *
        (modeAction (extendPositiveEnergyProfile m energy) (modeFrequency m) first *
          modeAction (extendPositiveEnergyProfile m energy) (modeFrequency m) second)) :=
  (isPositiveEnergyQuadratic_modeActionProduct m first second).const_mul constant

theorem isPositiveEnergyQuadratic_allDistinctRepresentativeSignedFluxTerm
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa time : Real)
    (observed : Lattice.Site N) (q : QuadraticPhaseTerm N) :
    IsPositiveEnergyQuadratic m (fun energy ↦
      allDistinctRepresentativeSignedFluxTerm m kappa time
        (extendPositiveEnergyProfile m energy) observed q) := by
  unfold allDistinctRepresentativeSignedFluxTerm
  exact (isPositiveEnergyQuadratic_quadraticSignedCollisionFlux
    m observed q).const_mul
      (4 * finiteTimeCollisionKernel m kappa
        (quadraticCollisionSign q) time
        (quadraticCollisionModes observed q))

theorem isPositiveEnergyQuadratic_allDistinctNoncounterrotatingSignedFluxSum
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa time : Real)
    (observed : Lattice.Site N) :
    IsPositiveEnergyQuadratic m (fun energy ↦
      allDistinctNoncounterrotatingSignedFluxSum m kappa time
        (extendPositiveEnergyProfile m energy) observed) := by
  unfold allDistinctNoncounterrotatingSignedFluxSum
  exact isPositiveEnergyQuadratic_finsetSum
    (positiveAllDistinctNoncounterrotatingRepresentatives m observed)
    (fun q energy ↦ allDistinctRepresentativeSignedFluxTerm m kappa time
      (extendPositiveEnergyProfile m energy) observed q)
    (fun q hq ↦
      isPositiveEnergyQuadratic_allDistinctRepresentativeSignedFluxTerm
        m kappa time observed q)

theorem isPositiveEnergyQuadratic_allDistinctCounterrotatingSignedFluxSum
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa time : Real)
    (observed : Lattice.Site N) :
    IsPositiveEnergyQuadratic m (fun energy ↦
      allDistinctCounterrotatingSignedFluxSum m kappa time
        (extendPositiveEnergyProfile m energy) observed) := by
  unfold allDistinctCounterrotatingSignedFluxSum
  exact isPositiveEnergyQuadratic_finsetSum
    (positiveAllDistinctCounterrotatingRepresentatives m observed)
    (fun q energy ↦ allDistinctRepresentativeSignedFluxTerm m kappa time
      (extendPositiveEnergyProfile m energy) observed q)
    (fun q hq ↦
      isPositiveEnergyQuadratic_allDistinctRepresentativeSignedFluxTerm
        m kappa time observed q)

theorem isPositiveEnergyQuadratic_repeatedAwaySignedFluxMain
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa time : Real)
    (observed : Lattice.Site N) :
    IsPositiveEnergyQuadratic m (fun energy ↦
      repeatedAwaySignedFluxMain m kappa time
        (extendPositiveEnergyProfile m energy) observed) := by
  unfold repeatedAwaySignedFluxMain repeatedChildOppositeSignFourSignedFlux
  apply IsPositiveEnergyQuadratic.add
  · apply isPositiveEnergyQuadratic_finsetSum
    intro q hq
    exact (isPositiveEnergyQuadratic_quadraticSignedCollisionFlux
      m observed q).const_mul
        (finiteTimeCollisionKernel m kappa
          (quadraticCollisionSign q) time
          (quadraticCollisionModes observed q))
  · apply isPositiveEnergyQuadratic_finsetSum
    intro q hq
    exact (isPositiveEnergyQuadratic_quadraticSignedCollisionFlux
      m observed q).const_mul
        (4 * finiteTimeCollisionKernel m kappa
          (quadraticCollisionSign q) time
          (quadraticCollisionModes observed q))

theorem isPositiveEnergyQuadratic_repeatedAwayFixedPointCorrection
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa time : Real)
    (observed : Lattice.Site N) :
    IsPositiveEnergyQuadratic m (fun energy ↦
      repeatedAwayFixedPointCorrection m kappa time
        (extendPositiveEnergyProfile m energy) observed) := by
  unfold repeatedAwayFixedPointCorrection
  apply isPositiveEnergyQuadratic_finsetSum
  intro q hq
  simpa only [mul_assoc] using
    (isPositiveEnergyQuadratic_const_modeActionProduct m
      (2 * finiteTimeCollisionKernel m kappa
          (quadraticCollisionSign q) time
          (quadraticCollisionModes observed q) *
        (quadraticInputInteractionSign q 0).coefficient)
      observed (q.1 0))

theorem isPositiveEnergyQuadratic_observedChildFourSignedFluxSum
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa time : Real)
    (observed : Lattice.Site N) :
    IsPositiveEnergyQuadratic m (fun energy ↦
      observedChildFourSignedFluxSum m kappa time
        (extendPositiveEnergyProfile m energy) observed) := by
  unfold observedChildFourSignedFluxSum observedChildFourSignedFluxKernel
  apply isPositiveEnergyQuadratic_sum
  intro selector
  exact (isPositiveEnergyQuadratic_quadraticSignedCollisionFlux
    m observed selector.q).const_mul
      (4 * finiteTimeCollisionKernel m kappa
        (quadraticCollisionSign selector.q) time
        (quadraticCollisionModes observed selector.q))

theorem isPositiveEnergyQuadratic_observedChildOtherInputLossKernel
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa time : Real)
    (observed : Lattice.Site N)
    (selector : PositiveObservedChildSelector N m observed) :
    IsPositiveEnergyQuadratic m (fun energy ↦
      observedChildOtherInputLossKernel m kappa time
        (extendPositiveEnergyProfile m energy) observed selector) := by
  unfold observedChildOtherInputLossKernel
  simpa only [mul_assoc] using
    (isPositiveEnergyQuadratic_const_modeActionProduct m
      ((quadraticInputInteractionSign selector.q
          (otherQuadraticSlot selector.observedSlot)).coefficient *
        finiteTimeCollisionKernel m kappa
          (quadraticCollisionSign selector.q) time
          (quadraticCollisionModes observed selector.q))
      observed observed)

theorem isPositiveEnergyQuadratic_observedChildPlacementCorrection
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa time : Real)
    (observed : Lattice.Site N) :
    IsPositiveEnergyQuadratic m (fun energy ↦
      observedChildPlacementCorrection m kappa time
        (extendPositiveEnergyProfile m energy) observed) := by
  unfold observedChildPlacementCorrection
  apply IsPositiveEnergyQuadratic.sub
  · apply isPositiveEnergyQuadratic_sum
    intro selector
    exact (isPositiveEnergyQuadratic_observedChildOtherInputLossKernel
      m kappa time observed selector.1).const_mul 2
  · apply isPositiveEnergyQuadratic_sum
    intro selector
    exact (isPositiveEnergyQuadratic_observedChildOtherInputLossKernel
      m kappa time observed selector).const_mul 4

theorem isPositiveEnergyQuadratic_allEqualOrbitGainSum
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa time : Real)
    (observed : Lattice.Site N) :
    IsPositiveEnergyQuadratic m (fun energy ↦
      allEqualOrbitGainSum m kappa time
        (extendPositiveEnergyProfile m energy) observed) := by
  unfold allEqualOrbitGainSum
  apply isPositiveEnergyQuadratic_finsetSum
  intro q hq
  simpa only [pow_two, mul_assoc] using
    (isPositiveEnergyQuadratic_const_modeActionProduct m
      (((quadraticSwapOrbit q).card : Real) *
        ((quadraticSwapOrbit q).card : Real) *
        finiteTimeCollisionKernel m kappa
          (quadraticCollisionSign q) time
          (quadraticCollisionModes observed q))
      observed observed)

theorem isPositiveEnergyQuadratic_allEqualChannelFiveCorrection
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa time : Real)
    (observed : Lattice.Site N) :
    IsPositiveEnergyQuadratic m (fun energy ↦
      allEqualChannelFiveCorrection m kappa time
        (extendPositiveEnergyProfile m energy) observed) := by
  unfold allEqualChannelFiveCorrection
  apply isPositiveEnergyQuadratic_finsetSum
  intro parameter hparameter
  simpa only [pow_two, mul_assoc] using
    (isPositiveEnergyQuadratic_const_modeActionProduct m
      ((quadraticInputInteractionSign parameter.1
          parameter.2.1).coefficient *
        finiteTimeCollisionKernel m kappa
          (quadraticCollisionSign parameter.1) time
          (quadraticCollisionModes observed parameter.1))
      observed observed)

theorem isPositiveEnergyQuadratic_qLevelResolvedSecondOrderSignedFluxMain
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa time : Real)
    (observed : Lattice.Site N) :
    IsPositiveEnergyQuadratic m (fun energy ↦
      qLevelResolvedSecondOrderSignedFluxMain m kappa time
        (extendPositiveEnergyProfile m energy) observed) := by
  unfold qLevelResolvedSecondOrderSignedFluxMain
  simpa only [add_assoc] using
    ((isPositiveEnergyQuadratic_allDistinctNoncounterrotatingSignedFluxSum
      m kappa time observed).add
      ((isPositiveEnergyQuadratic_repeatedAwaySignedFluxMain
        m kappa time observed).add
        (isPositiveEnergyQuadratic_observedChildFourSignedFluxSum
          m kappa time observed)))

/- Every term in the exact q-level closure except cross-orbit coherence is
now backed by a constructed finite quadratic kernel. -/
theorem isPositiveEnergyQuadratic_qLevelClosureWithoutCross
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa time : Real)
    (observed : Lattice.Site N) :
    IsPositiveEnergyQuadratic m (fun energy ↦
      qLevelResolvedSecondOrderSignedFluxMain m kappa time
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
          (extendPositiveEnergyProfile m energy) observed) := by
  exact (((((isPositiveEnergyQuadratic_qLevelResolvedSecondOrderSignedFluxMain
      m kappa time observed).add
      (isPositiveEnergyQuadratic_allEqualOrbitGainSum
        m kappa time observed)).add
      (isPositiveEnergyQuadratic_repeatedAwayFixedPointCorrection
        m kappa time observed)).add
      (isPositiveEnergyQuadratic_observedChildPlacementCorrection
        m kappa time observed)).add
      (isPositiveEnergyQuadratic_allEqualChannelFiveCorrection
        m kappa time observed)).add
      (isPositiveEnergyQuadratic_allDistinctCounterrotatingSignedFluxSum
        m kappa time observed)

end

end ArchonPhysics.PhyslibFPUTCanonicalQLevelQuadratic
