import ArchonPhysics.PhyslibFPUTA1OrderedHistoryPrefixCompactSmallBall

/-!
# Thermalization consumer: arbitrary ordered-history A1 prefix atlases

This consumer checks the exact finite-order endpoint.  A list of actual local
A1 mismatch charts sharing one retained mass fiber has root-prefix cumulative
charts equal to the corresponding prefix phase sums.  Each such prefix is an
actual member of the full ordered-history denominator enumeration, and its
derivative is the sum of the actual vertical Jacobians in that prefix.

Independent compact sets and independent positive noncancellation thresholds
produce one compact-atlas certificate per prefix.  This does not cover the
additional shifted intervals in the full `2^r - 1` denominator list, choose a
common fiber for a branching garden, or assert re-Haar/Markov/recollision
closure.
-/

namespace ArchonPhysicsConsumers.Thermalization

open scoped BigOperators

open ArchonPhysics
open ArchonPhysics.FreeFPUTDuhamelResonanceBridge
open ArchonPhysics.FreeFPUTOrderedHistoryDenominatorEnumeration
open ArchonPhysics.FreeFPUTTensorPhaseExpansion
open ArchonPhysics.PhyslibFPUTA1OrderedHistoryPrefixCompactSmallBall
open ArchonPhysics.PhyslibFPUTA1PairFiberTransversalityAtlas
open ArchonPhysics.PhyslibFPUTArbitraryGardenCompactSmallBall
open Set

noncomputable section

theorem problem_physlibA1OrderedHistory_prefix_list_exact
    {order N : Nat} [NeZero N]
    (fixed : Lattice.PositiveMassConfig N)
    (site₁ site₂ observed : Lattice.Site N)
    (term : Fin order → QuadraticPhaseTerm N)
    (pair : Real × Real) :
    physlibA1OrderedHistoryPrefixCumulativeChartList
        fixed site₁ site₂ observed term pair =
      orderedHistoryPrefixCumulativePhases
        (physlibA1OrderedHistoryLocalPhaseList
          fixed site₁ site₂ observed term pair) :=
  physlibA1OrderedHistoryPrefixCumulativeChartList_eq_cumulativePhases
    fixed site₁ site₂ observed term pair

theorem problem_physlibA1OrderedHistory_prefix_mem_denominators
    {order N : Nat} [NeZero N]
    (fixed : Lattice.PositiveMassConfig N)
    (site₁ site₂ observed : Lattice.Site N)
    (term : Fin order → QuadraticPhaseTerm N) (j : Fin order)
    (pair : Real × Real) :
    physlibA1OrderedHistoryPrefixCumulativePairMismatchChart
        fixed site₁ site₂ observed term j pair ∈
      orderedHistoryDenominators
        (physlibA1OrderedHistoryLocalPhaseList
          fixed site₁ site₂ observed term pair) :=
  physlibA1OrderedHistoryPrefixCumulativeChart_mem_denominators
    fixed site₁ site₂ observed term j pair

theorem problem_deriv_physlibA1OrderedHistory_prefix_eq_sum
    {order N : Nat} [NeZero N]
    (fixed : Lattice.PositiveMassConfig N)
    {site₁ site₂ : Lattice.Site N} (hsite : site₁ ≠ site₂)
    (observed : Lattice.Site N)
    (term : Fin order → QuadraticPhaseTerm N) (j : Fin order)
    {pair : Real × Real}
    (hregular : pair ∈
      physlibA1OrderedHistoryPrefixDifferentiabilitySource
        fixed site₁ site₂ observed term j) :
    deriv (fun second =>
        physlibA1OrderedHistoryPrefixCumulativePairMismatchChart
          fixed site₁ site₂ observed term j (pair.1, second)) pair.2 =
      ∑ i ∈ physlibA1OrderedHistoryPrefixActive j,
        physlibA1PairMismatchVerticalJacobian
          fixed site₁ site₂ observed (term i) pair :=
  deriv_physlibA1OrderedHistoryPrefixCumulativePairMismatchFiber_eq_sum
    fixed hsite observed term j hregular

theorem problem_exists_physlibA1OrderedHistory_prefix_certificates
    {order N : Nat} [NeZero N]
    (fixed : Lattice.PositiveMassConfig N)
    {site₁ site₂ : Lattice.Site N} (hsite : site₁ ≠ site₂)
    (observed : Lattice.Site N)
    (term : Fin order → QuadraticPhaseTerm N) (first : Real)
    (K : Fin order → Set Real) (hK : ∀ j, IsCompact (K j))
    (hregular : ∀ j second, second ∈ K j →
      (first, second) ∈
        physlibA1OrderedHistoryPrefixDifferentiabilitySource
          fixed site₁ site₂ observed term j)
    (j0 : Fin order → Real) (hj0 : ∀ j, 0 < j0 j)
    (hjac : ∀ j second, second ∈ K j → j0 j ≤
      |physlibA1OrderedHistoryPrefixVerticalJacobian
        fixed site₁ site₂ observed term j (first, second)|) :
    ∃ certificate : ∀ j : Fin order,
        OrdinaryGardenCoordinateCompactAtlas
          (fun second =>
            physlibA1OrderedHistoryPrefixCumulativePairMismatchChart
              fixed site₁ site₂ observed term j (first, second)),
      (∀ j, (certificate j).compactSet = K j) ∧
      (∀ j, (certificate j).jacLower = j0 j) :=
  exists_physlibA1OrderedHistoryPrefixCompactAtlasCertificates
    fixed hsite observed term first K hK hregular j0 hj0 hjac

#print axioms sum_take_succ_mem_orderedHistoryDenominators
#print axioms mem_orderedHistoryDenominators_of_mem_prefixCumulativePhases
#print axioms orderedHistoryDenominators_three_ne_prefixCumulativePhases
#print axioms physlibA1OrderedHistoryPrefixCumulativeChartList_eq_cumulativePhases
#print axioms physlibA1OrderedHistoryPrefixCumulativeChart_mem_denominators
#print axioms deriv_physlibA1OrderedHistoryPrefixCumulativePairMismatchFiber_eq_sum
#print axioms exists_physlibA1OrderedHistoryPrefixCompactAtlasCertificates
#print axioms problem_physlibA1OrderedHistory_prefix_list_exact
#print axioms problem_physlibA1OrderedHistory_prefix_mem_denominators
#print axioms problem_deriv_physlibA1OrderedHistory_prefix_eq_sum
#print axioms problem_exists_physlibA1OrderedHistory_prefix_certificates

end

end ArchonPhysicsConsumers.Thermalization
