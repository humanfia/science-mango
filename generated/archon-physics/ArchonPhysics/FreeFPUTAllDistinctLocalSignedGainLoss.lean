import ArchonPhysics.FreeFPUTAllDistinctConnectedReturnFiber
import ArchonPhysics.SignedThreeWaveCollisionFlux

/-!
# Local all-distinct signed gain--loss identity

For one fixed ordered quadratic phase term, this module adds its coherent
input-swap-orbit first-Picard gain to the feedback over the literal eight-tree
connected-return image.  Pairwise distinctness makes the swap orbit have two
elements, so the gain and the two signed feedback channels combine into four
copies of the signed three-wave collision bracket.

This is an identity for the explicit local image only.  It neither identifies
that image with the complete positive connected representative fiber nor
removes coherent, tadpole, zero-charge, or counterrotating remainders outside
the image.
-/

namespace ArchonPhysics.FreeFPUTAllDistinctLocalSignedGainLoss

open ArchonPhysics
open ArchonPhysics.FiniteTimeResonanceWeight
open ArchonPhysics.FreeFPUTA0IteratedQuadraticFeedbackIdentity
open ArchonPhysics.FreeFPUTAllDistinctConnectedReturnFiber
open ArchonPhysics.FreeFPUTCanonicalConnectedReturnTree
open ArchonPhysics.FreeFPUTCollisionMismatchBridge
open ArchonPhysics.FreeFPUTEnergyCollisionWeightBridge
open ArchonPhysics.FreeFPUTQuadraticTermSwapSymmetry
open ArchonPhysics.FreeFPUTTensorPhaseExpansion
open ArchonPhysics.MicroscopicFiniteTimeCollisionPolynomial
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.NormalizedModeCoupling
open ArchonPhysics.PhyslibFPUTIteratedQuadraticSecondPicardCharacterFamily
open ArchonPhysics.PhyslibFPUTSecondOrderExplicitReturnFeedback
open ArchonPhysics.SignedThreeWaveCollisionFlux
open ArchonPhysics.ThreeWaveCollisionAlgebra

noncomputable section

/-- The coherent first-Picard gain attached to one input-swap orbit. -/
def allDistinctLocalA1Gain
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa time : Real)
    (energy : Lattice.Site N → Real) (observed : Lattice.Site N)
    (q : QuadraticPhaseTerm N) : Real :=
  ((quadraticSwapOrbit q).card : Real) ^ 2 *
    finiteTimeCollisionKernel m kappa
      (quadraticCollisionSign q) time
      (quadraticCollisionModes observed q) *
    ∏ r : Fin 2, modeAction energy (modeFrequency m) (q.1 r)

/-- Physical feedback summed over the literal eight-tree local image. -/
def allDistinctConnectedReturnTreeFeedbackSum
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa time : Real)
    (energy : Lattice.Site N → Real) (observed : Lattice.Site N)
    (q : QuadraticPhaseTerm N) : Real :=
  ∑ term ∈ allDistinctConnectedReturnImage observed q,
    compactIteratedQuadraticStaticFeedbackWeight m kappa
        (phaseEnergyRadius energy (modeFrequency m)) observed term.1 *
      finiteTimeResonanceWeight
        (iteratedQuadraticInnerMismatch m term.1) time

/-- Sum of the local coherent A1 gain and the explicit connected-return
feedback. -/
def allDistinctLocalSignedGainLoss
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa time : Real)
    (energy : Lattice.Site N → Real) (observed : Lattice.Site N)
    (q : QuadraticPhaseTerm N) : Real :=
  allDistinctLocalA1Gain m kappa time energy observed q +
    allDistinctConnectedReturnTreeFeedbackSum
      m kappa time energy observed q

/-- Distinct input modes force the ordered quadratic term's swap orbit to
have two elements. -/
theorem card_quadraticSwapOrbit_eq_two_of_observedQuadraticAllDistinct
    {N : Nat} [NeZero N] (observed : Lattice.Site N)
    (q : QuadraticPhaseTerm N)
    (hDistinct : ObservedQuadraticAllDistinct observed q) :
    (quadraticSwapOrbit q).card = 2 := by
  apply card_quadraticSwapOrbit_eq_two_of_ne
  intro hfixed
  have hmodes : q.1 0 = q.1 1 :=
    ((swapQuadraticPhaseTerm_eq_self_iff q).mp hfixed).1
  exact hDistinct.1 hmodes

/-- The local eight-tree feedback is the two signed observed-input terms,
each with multiplicity four. -/
theorem allDistinctConnectedReturnTreeFeedbackSum_eq
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa time : Real)
    (energy : Lattice.Site N → Real) (observed : Lattice.Site N)
    (q : QuadraticPhaseTerm N)
    (hDistinct : ObservedQuadraticAllDistinct observed q)
    (hEnergy : ∀ mode, 0 ≤ energy mode)
    (hPositive : PositiveModeTuple m (quadraticCollisionModes observed q)) :
    allDistinctConnectedReturnTreeFeedbackSum
        m kappa time energy observed q =
      4 * finiteTimeCollisionKernel m kappa
            (quadraticCollisionSign q) time
            (quadraticCollisionModes observed q) *
        ((quadraticCollisionSign q (Fin.succ (0 : Fin 2))).coefficient *
            modeAction energy (modeFrequency m) observed *
            modeAction energy (modeFrequency m) (q.1 1) +
          (quadraticCollisionSign q (Fin.succ (1 : Fin 2))).coefficient *
            modeAction energy (modeFrequency m) observed *
            modeAction energy (modeFrequency m) (q.1 0)) := by
  unfold allDistinctConnectedReturnTreeFeedbackSum
  exact sum_allDistinctConnectedReturnImage_feedback_eq
    m kappa time energy observed q hDistinct hEnergy hPositive

/-- Exact closure of the local coherent gain and the literal eight-tree
feedback into the signed three-wave bracket. -/
theorem allDistinctLocalSignedGainLoss_eq_signedCollisionFlux
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa time : Real)
    (energy : Lattice.Site N → Real) (observed : Lattice.Site N)
    (q : QuadraticPhaseTerm N)
    (hDistinct : ObservedQuadraticAllDistinct observed q)
    (hEnergy : ∀ mode, 0 ≤ energy mode)
    (hPositive : PositiveModeTuple m (quadraticCollisionModes observed q)) :
    allDistinctLocalSignedGainLoss m kappa time energy observed q =
      4 * finiteTimeCollisionKernel m kappa
            (quadraticCollisionSign q) time
            (quadraticCollisionModes observed q) *
        quadraticSignedCollisionFlux q
          (modeAction energy (modeFrequency m)) observed := by
  unfold allDistinctLocalSignedGainLoss allDistinctLocalA1Gain
  rw [card_quadraticSwapOrbit_eq_two_of_observedQuadraticAllDistinct
      observed q hDistinct,
    allDistinctConnectedReturnTreeFeedbackSum_eq
      m kappa time energy observed q hDistinct hEnergy hPositive]
  simp only [Nat.cast_ofNat, Fin.prod_univ_two,
    quadraticSignedCollisionFlux, signedThreeWaveCollisionFlux,
    quadraticCollisionSign_succ]
  ring

/-- In the phase--phase sector, the local signed bracket is the standard
`ThreeWaveCollisionAlgebra.collisionFlux`. -/
theorem allDistinctLocalSignedGainLoss_eq_collisionFlux_of_phase_phase
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa time : Real)
    (energy : Lattice.Site N → Real) (observed : Lattice.Site N)
    (q : QuadraticPhaseTerm N)
    (hDistinct : ObservedQuadraticAllDistinct observed q)
    (hEnergy : ∀ mode, 0 ≤ energy mode)
    (hPositive : PositiveModeTuple m (quadraticCollisionModes observed q))
    (hzero : binaryPhaseSign q.2.1 = .phase)
    (hone : binaryPhaseSign q.2.2 = .phase) :
    allDistinctLocalSignedGainLoss m kappa time energy observed q =
      4 * finiteTimeCollisionKernel m kappa
            (quadraticCollisionSign q) time
            (quadraticCollisionModes observed q) *
        collisionFlux
          (modeAction energy (modeFrequency m) observed)
          (modeAction energy (modeFrequency m) (q.1 0))
          (modeAction energy (modeFrequency m) (q.1 1)) := by
  rw [allDistinctLocalSignedGainLoss_eq_signedCollisionFlux
      m kappa time energy observed q hDistinct hEnergy hPositive,
    quadraticSignedCollisionFlux_eq_collisionFlux_of_phase_phase
      q (modeAction energy (modeFrequency m)) observed hzero hone]

end

end ArchonPhysics.FreeFPUTAllDistinctLocalSignedGainLoss
