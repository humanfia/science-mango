import ArchonPhysics.PhyslibFPUTIteratedA2PairFiberCompactSmallBall

/-!
# Consumer: compact actual iterated-A2 pair-fiber atlases

This consumer records the precise replacement for global fiber injectivity.
On a supplied compact regular set with actual vertical Jacobian at least
`j₀ > 0`, finitely many local inverse charts dominate the pushed-forward
one-mass law.  Restoring the full law adds exactly `massCoordinateLaw Kᶜ`.

A finite family of ordinary mismatch channels is handled by a union bound;
no independence assumption is used.  Charge-matched total channels cannot
satisfy a positive-Jacobian ordinary certificate on a nonempty compact set,
so they remain in the explicitly retained resonant/feedback sector.
-/

namespace ArchonPhysicsConsumers.Thermalization

open ArchonPhysics
open ArchonPhysics.CanonicalIIDCoerciveIteratedA2ExpectationFourierDecay
open ArchonPhysics.FreeFPUTA0DirectCubicBridge
open ArchonPhysics.PhyslibFPUTIteratedA2PairFiberCompactSmallBall
open ArchonPhysics.PhyslibFPUTIteratedA2PairFiberTransversalityAtlas
open ArchonPhysics.PhyslibFPUTIteratedQuadraticSecondPicardCharacterFamily
open ArchonPhysics.RandomEnsemble
open MeasureTheory Set
open scoped ENNReal

noncomputable section

/-- Consumer form of the actual compact-atlas endpoint. -/
theorem problem_physlibIteratedA2_pairFiberCompact_smallBall
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    {site₁ site₂ : Lattice.Site N} (hsite : site₁ ≠ site₂)
    (channel : IteratedA2MismatchChannel) (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N)
    (first : Real) (K : Set Real) (hK : IsCompact K)
    (hKregular : ∀ second ∈ K,
      (first, second) ∈ physlibIteratedA2PairMismatchDifferentiabilitySource
        fixed site₁ site₂ channel observed term)
    {j₀ : Real} (hj₀ : 0 < j₀)
    (hjac : ∀ second ∈ K, j₀ ≤
      |physlibIteratedA2PairMismatchVerticalJacobian
        fixed site₁ site₂ channel observed term (first, second)|) :
    ∃ atlasCard : Nat,
      Measure.map
          (fun second => physlibIteratedA2PairMismatchChart
            fixed site₁ site₂ channel observed term (first, second))
          (massCoordinateLaw.restrict K) ≤
        ((atlasCard : ENNReal) *
          ((5 / 2 : ENNReal) * (ENNReal.ofReal j₀)⁻¹)) •
            (volume : Measure Real) ∧
      ∀ delta : Real,
        Measure.map
            (fun second => physlibIteratedA2PairMismatchChart
              fixed site₁ site₂ channel observed term (first, second))
            massCoordinateLaw (Ioo (-delta) delta) ≤
          ((atlasCard : ENNReal) *
            ((5 / 2 : ENNReal) * (ENNReal.ofReal j₀)⁻¹)) *
              ENNReal.ofReal (2 * delta) + massCoordinateLaw Kᶜ := by
  exact exists_atlasCard_physlibIteratedA2PairFiberCompact_smallBall
    fixed hsite channel observed term first K hK hKregular hj₀ hjac

/-- Consumer form of the finite ordinary-channel union estimate. -/
theorem problem_physlibIteratedA2_fixedOrderOrdinaryNearEvent_le
    {Ordinary : Type*} [Fintype Ordinary]
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    {site₁ site₂ : Lattice.Site N} (hsite : site₁ ≠ site₂)
    (observed : Lattice.Site N)
    (channel : Ordinary → IteratedA2MismatchChannel)
    (term : Ordinary → IteratedQuadraticSecondPicardCharacterTerm N)
    (first : Real) (K : Ordinary → Set Real)
    (hK : ∀ j, IsCompact (K j))
    (hKregular : ∀ j second, second ∈ K j →
      (first, second) ∈ physlibIteratedA2PairMismatchDifferentiabilitySource
        fixed site₁ site₂ (channel j) observed (term j))
    (j₀ : Ordinary → Real) (hj₀ : ∀ j, 0 < j₀ j)
    (hjac : ∀ j second, second ∈ K j → j₀ j ≤
      |physlibIteratedA2PairMismatchVerticalJacobian
        fixed site₁ site₂ (channel j) observed (term j)
          (first, second)|) :
    ∃ atlasCard : Ordinary → Nat, ∀ delta : Real,
      massCoordinateLaw
          (physlibIteratedA2FixedOrderOrdinaryNearEvent
            fixed site₁ site₂ observed channel term first delta) ≤
        (∑ j, (atlasCard j : ENNReal) *
          ((5 / 2 : ENNReal) * (ENNReal.ofReal (j₀ j))⁻¹)) *
            ENNReal.ofReal (2 * delta) +
          massCoordinateLaw
            (physlibIteratedA2FixedOrderOrdinaryCompactBadEvent K) := by
  exact exists_atlasCard_physlibIteratedA2FixedOrderOrdinaryNearEvent_le
    fixed hsite observed channel term first K hK hKregular j₀ hj₀ hjac

/-- Consumer audit that a charge-matched total channel is forced into the
retained sector by the exact zero-Jacobian identity. -/
theorem problem_physlibIteratedA2_chargeMatchedTotal_retained
    {J : Type*} [Fintype J] [DecidableEq J]
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (site₁ site₂ observed : Lattice.Site N) (first : Real)
    (ordinary : Finset J)
    (channel : J → IteratedA2MismatchChannel)
    (term : J → IteratedQuadraticSecondPicardCharacterTerm N)
    (K : J → Set Real) (hKnonempty : ∀ j ∈ ordinary, (K j).Nonempty)
    (j₀ : J → Real) (hj₀ : ∀ j ∈ ordinary, 0 < j₀ j)
    (hjac : ∀ j ∈ ordinary, ∀ second ∈ K j, j₀ j ≤
      |physlibIteratedA2PairMismatchVerticalJacobian
        fixed site₁ site₂ (channel j) observed (term j) (first, second)|)
    {j : J} (hchannel : channel j = .total)
    (hcharge : freeInitialPhaseCharge observed 0 =
      iteratedQuadraticSecondPicardCharge (term j)) :
    j ∈ physlibIteratedA2FixedOrderRetainedSector ordinary := by
  exact chargeMatchedTotal_mem_physlibIteratedA2FixedOrderRetainedSector
    fixed site₁ site₂ observed first ordinary channel term K hKnonempty
      j₀ hj₀ hjac hchannel hcharge

#print axioms
  ArchonPhysics.PhyslibFPUTIteratedA2PairFiberCompactSmallBall.exists_atlasCard_physlibIteratedA2PairFiberCompact_smallBall
#print axioms
  ArchonPhysics.PhyslibFPUTIteratedA2PairFiberCompactSmallBall.exists_atlasCard_physlibIteratedA2FixedOrderOrdinaryNearEvent_le
#print axioms
  ArchonPhysics.PhyslibFPUTIteratedA2PairFiberCompactSmallBall.chargeMatchedTotal_mem_physlibIteratedA2FixedOrderRetainedSector
#print axioms problem_physlibIteratedA2_pairFiberCompact_smallBall
#print axioms problem_physlibIteratedA2_fixedOrderOrdinaryNearEvent_le
#print axioms problem_physlibIteratedA2_chargeMatchedTotal_retained

end

end ArchonPhysicsConsumers.Thermalization
