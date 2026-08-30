import ArchonPhysics.PhyslibFPUTIteratedA2PairFiberTransversalityAtlas

/-!
# Consumer: actual iterated-A2 pair-fiber transversality

This consumer checks both sides of the physical atlas.  Regular noncritical
outer, inner, total, and twisted mismatch fibers have genuine local
one-mass inverse charts derived from actual simple ordered eigenfrequencies.
Charge-matched return trees, however, have identically zero total mismatch
and Jacobian and are therefore retained as a resonant/feedback block.

The positivity source is a conservative tree-level finite-mode superset.
No probability bound for the measurable bad set, uniform-in-volume
Jacobian estimate, RPA, or kinetic limit is asserted.
-/

namespace ArchonPhysicsConsumers.Thermalization

open ArchonPhysics
open ArchonPhysics.CanonicalIIDCoerciveIteratedA2ExpectationFourierDecay
open ArchonPhysics.FreeFPUTA0DirectCubicBridge
open ArchonPhysics.PhyslibFPUTIteratedQuadraticSecondPicardCharacterFamily
open ArchonPhysics.PhyslibFPUTIteratedA2PairFiberTransversalityAtlas
open ArchonPhysics.RandomEnsemble
open MeasureTheory Set

noncomputable section

/-- Consumer form of the exact charge-matched total-channel obstruction. -/
theorem consumer_iteratedA2_chargeMatchedTotal_is_resonant
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (site₁ site₂ observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N)
    (hcharge : freeInitialPhaseCharge observed 0 =
      iteratedQuadraticSecondPicardCharge term)
    (pair : Real × Real) (first : Real) :
    physlibIteratedA2PairMismatchChart fixed site₁ site₂ .total observed term
        pair = 0 ∧
      physlibIteratedA2PairMismatchVerticalJacobian
          fixed site₁ site₂ .total observed term pair = 0 ∧
      ¬ InjOn
        (fun second => physlibIteratedA2PairMismatchChart fixed site₁ site₂
          .total observed term (first, second)) massSupport := by
  exact ⟨
    physlibIteratedA2TotalPairMismatchChart_eq_zero_of_chargeMatched
      fixed site₁ site₂ observed term hcharge pair,
    physlibIteratedA2TotalPairMismatchVerticalJacobian_eq_zero_of_chargeMatched
      fixed site₁ site₂ observed term hcharge pair,
    not_injOn_physlibIteratedA2ChargeMatchedTotalPairFiber_massSupport
      fixed site₁ site₂ observed term hcharge first⟩

/-- Consumer form of the genuine local inverse-chart conclusion. -/
theorem consumer_iteratedA2_regularNoncritical_has_localInjectivePatch
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    {site₁ site₂ : Lattice.Site N} (hsite : site₁ ≠ site₂)
    (channel : IteratedA2MismatchChannel) (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N)
    {pair : Real × Real}
    (hregular : pair ∈
      physlibIteratedA2PairMismatchDifferentiabilitySource
        fixed site₁ site₂ channel observed term)
    (hjac : physlibIteratedA2PairMismatchVerticalJacobian
      fixed site₁ site₂ channel observed term pair ≠ 0) :
    ∃ patch : Set Real,
      pair.2 ∈ patch ∧ IsOpen patch ∧ MeasurableSet patch ∧
      patch ⊆ massSupport ∧
      InjOn
        (fun second => physlibIteratedA2PairMismatchChart
          fixed site₁ site₂ channel observed term (pair.1, second)) patch := by
  exact exists_physlibIteratedA2PairFiber_localInjectivePatch
    fixed hsite channel observed term hregular hjac

/-- Consumer form of the measurable quantitative good/bad hierarchy. -/
theorem consumer_iteratedA2_good_bad_levels_measurable
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (site₁ site₂ : Lattice.Site N) (channel : IteratedA2MismatchChannel)
    (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N)
    (first : Real) (n : Nat) :
    MeasurableSet (physlibIteratedA2PairFiberGoodLevel
        fixed site₁ site₂ channel observed term first n) ∧
      MeasurableSet (physlibIteratedA2PairFiberBadLevel
        fixed site₁ site₂ channel observed term first n) := by
  exact ⟨
    measurableSet_physlibIteratedA2PairFiberGoodLevel
      fixed site₁ site₂ channel observed term first n,
    measurableSet_physlibIteratedA2PairFiberBadLevel
      fixed site₁ site₂ channel observed term first n⟩

#print axioms
  physlibIteratedA2TotalPairMismatchChart_eq_zero_of_chargeMatched
#print axioms
  physlibIteratedA2TotalPairMismatchVerticalJacobian_eq_zero_of_chargeMatched
#print axioms
  hasStrictFDerivAt_physlibIteratedA2PairMismatchChart
#print axioms
  exists_physlibIteratedA2PairFiber_localInjectivePatch
#print axioms
  mem_physlibIteratedA2PairFiberBadLevel_iff
#print axioms consumer_iteratedA2_chargeMatchedTotal_is_resonant
#print axioms consumer_iteratedA2_regularNoncritical_has_localInjectivePatch
#print axioms consumer_iteratedA2_good_bad_levels_measurable

end

end ArchonPhysicsConsumers.Thermalization
