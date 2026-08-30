import ArchonPhysics.PhyslibFPUTA1OrderedHistoryIntervalCompactSmallBall

/-!
# Thermalization consumer: every linear ordered-history interval denominator

This consumer checks the complete linear endpoint.  Every occurrence in
`orderedHistoryDenominators` is represented by a nonempty contiguous interval,
and for actual A1 local phases on one explicitly common retained mass pair it
is exactly the cumulative chart of that interval.  The interval derivative is
the sum of its actual vertical Jacobians, and independent compact/Jacobian
hypotheses produce a certificate family over all intervals.

The result does not select or prove a common fiber across different branches
of a garden.  Such a branching compatibility selector remains separate, as do
re-Haar, Markov, RPA, and recollision-decay inputs.
-/

namespace ArchonPhysicsConsumers.Thermalization

open scoped BigOperators

open ArchonPhysics
open ArchonPhysics.FreeFPUTDuhamelResonanceBridge
open ArchonPhysics.FreeFPUTOrderedHistoryDenominatorEnumeration
open ArchonPhysics.FreeFPUTTensorPhaseExpansion
open ArchonPhysics.PhyslibFPUTA1AnnealedMismatchSmallBall
open ArchonPhysics.PhyslibFPUTA1PairFiberTransversalityAtlas
open ArchonPhysics.PhyslibFPUTA1OrderedHistoryIntervalCompactSmallBall
open ArchonPhysics.PhyslibFPUTArbitraryGardenCompactSmallBall
open Set

noncomputable section

theorem problem_exists_interval_eq_orderedHistoryDenominator
    (phases : List Real) {delta : Real}
    (hdelta : delta ∈ orderedHistoryDenominators phases) :
    ∃ interval : OrderedHistoryInterval phases.length,
      delta = (interval.block phases).sum :=
  exists_interval_eq_orderedHistoryDenominator phases hdelta

theorem problem_exists_intervalChart_eq_actual_orderedHistoryDenominator
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (site₁ site₂ observed : Lattice.Site N)
    (term : List (QuadraticPhaseTerm N)) (pair : Real × Real)
    {delta : Real}
    (hdelta : delta ∈ orderedHistoryDenominators
      (physlibA1OrderedHistoryListLocalPhaseList
        fixed site₁ site₂ observed term pair)) :
    ∃ interval : OrderedHistoryInterval term.length,
      delta = physlibA1OrderedHistoryIntervalPairMismatchChart
        fixed site₁ site₂ observed term interval pair :=
  exists_intervalChart_eq_physlibA1OrderedHistoryDenominator
    fixed site₁ site₂ observed term pair hdelta

theorem problem_deriv_actual_orderedHistoryInterval_eq_sum
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    {site₁ site₂ : Lattice.Site N} (hsite : site₁ ≠ site₂)
    (observed : Lattice.Site N)
    (term : List (QuadraticPhaseTerm N))
    (interval : OrderedHistoryInterval term.length)
    {pair : Real × Real}
    (hregular : pair ∈
      physlibA1OrderedHistoryIntervalDifferentiabilitySource
        fixed site₁ site₂ observed term interval) :
    deriv (fun second =>
        physlibA1OrderedHistoryIntervalPairMismatchChart
          fixed site₁ site₂ observed term interval (pair.1, second)) pair.2 =
      ∑ i : Fin
          (physlibA1OrderedHistoryIntervalTermList term interval).length,
        physlibA1PairMismatchVerticalJacobian
          fixed site₁ site₂ observed
            (physlibA1OrderedHistoryIntervalTermFamily term interval i) pair :=
  deriv_physlibA1OrderedHistoryIntervalPairMismatchFiber_eq_sum
    fixed hsite observed term interval hregular

theorem problem_exists_actual_orderedHistoryInterval_certificates
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    {site₁ site₂ : Lattice.Site N} (hsite : site₁ ≠ site₂)
    (observed : Lattice.Site N)
    (term : List (QuadraticPhaseTerm N)) (first : Real)
    (K : OrderedHistoryInterval term.length → Set Real)
    (hK : ∀ interval, IsCompact (K interval))
    (hregular : ∀ interval second, second ∈ K interval →
      (first, second) ∈
        physlibA1OrderedHistoryIntervalDifferentiabilitySource
          fixed site₁ site₂ observed term interval)
    (j0 : OrderedHistoryInterval term.length → Real)
    (hj0 : ∀ interval, 0 < j0 interval)
    (hjac : ∀ interval second, second ∈ K interval →
      j0 interval ≤
        |physlibA1OrderedHistoryIntervalVerticalJacobian
          fixed site₁ site₂ observed term interval (first, second)|) :
    ∃ certificate : ∀ interval : OrderedHistoryInterval term.length,
        OrdinaryGardenCoordinateCompactAtlas
          (fun second =>
            physlibA1OrderedHistoryIntervalPairMismatchChart
              fixed site₁ site₂ observed term interval (first, second)),
      (∀ interval, (certificate interval).compactSet = K interval) ∧
      (∀ interval, (certificate interval).jacLower = j0 interval) :=
  exists_physlibA1OrderedHistoryIntervalCompactAtlasCertificates
    fixed hsite observed term first K hK hregular j0 hj0 hjac

#print axioms orderedHistoryDenominator_isContiguousIntervalSum
#print axioms exists_interval_eq_orderedHistoryDenominator
#print axioms physlibA1OrderedHistoryIntervalPairMismatchChart_eq_block_sum
#print axioms exists_intervalChart_eq_physlibA1OrderedHistoryDenominator
#print axioms deriv_physlibA1OrderedHistoryIntervalPairMismatchFiber_eq_sum
#print axioms exists_physlibA1OrderedHistoryIntervalCompactAtlasCertificates
#print axioms problem_exists_interval_eq_orderedHistoryDenominator
#print axioms problem_exists_intervalChart_eq_actual_orderedHistoryDenominator
#print axioms problem_deriv_actual_orderedHistoryInterval_eq_sum
#print axioms problem_exists_actual_orderedHistoryInterval_certificates

end

end ArchonPhysicsConsumers.Thermalization
