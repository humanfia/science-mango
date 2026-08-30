import ArchonPhysics.PhyslibFPUTA1CumulativePairFiberCompactSmallBall

/-!
# Consumer: actual cumulative A1 pair-fiber transversality

This consumer checks the first genuine cumulative-denominator adapter.  A
finite family of local actual A1 mismatch charts shares one retained mass
coordinate; its derivative is the sum of their actual vertical Jacobians.
The inverse-function and compact-atlas conclusions assume a lower bound on
the absolute value of that total sum, so cancellation between local terms is
kept visible.

For order two the exact denominator list consists of two existing single-A1
coordinates and one cumulative coordinate.  Their three compact sets and
three Jacobian thresholds are independent hypotheses.  In particular this
consumer proves no uniform lower bound on the full iid mass support and uses
no phase independence, re-Haar, high-order RPA, Markov approximation, or
recollision decay.
-/

namespace ArchonPhysicsConsumers.Thermalization

open scoped BigOperators ENNReal

open ArchonPhysics
open ArchonPhysics.FreeFPUTDuhamelResonanceBridge
open ArchonPhysics.FreeFPUTOrderedHistoryDenominatorEnumeration
open ArchonPhysics.FreeFPUTTensorPhaseExpansion
open ArchonPhysics.PhyslibFPUTA1AnnealedMismatchSmallBall
open ArchonPhysics.PhyslibFPUTA1CumulativePairFiberCompactSmallBall
open ArchonPhysics.PhyslibFPUTA1PairFiberTransversalityAtlas
open Function MeasureTheory Set

noncomputable section

/-- Consumer form of the actual total-Jacobian derivative identity. -/
theorem problem_physlibA1CumulativePairFiber_deriv_eq_sum
    {Index : Type*} [DecidableEq Index]
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    {site₁ site₂ : Lattice.Site N} (hsite : site₁ ≠ site₂)
    (observed : Lattice.Site N)
    (term : Index → QuadraticPhaseTerm N) (active : Finset Index)
    {pair : Real × Real}
    (hregular : pair ∈
      physlibA1CumulativePairMismatchDifferentiabilitySource
        fixed site₁ site₂ observed term active) :
    deriv (fun second => physlibA1CumulativePairMismatchChart
        fixed site₁ site₂ observed term active (pair.1, second)) pair.2 =
      ∑ i ∈ active,
        physlibA1PairMismatchVerticalJacobian
          fixed site₁ site₂ observed (term i) pair := by
  exact deriv_physlibA1CumulativePairMismatchFiber_eq_sum
    fixed hsite observed term active hregular

/-- Consumer form of the exact order-two local/local/cumulative identity. -/
theorem problem_physlibA1OrderTwo_denominators_exact
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (site₁ site₂ observed : Lattice.Site N)
    (termOne termTwo : QuadraticPhaseTerm N) (pair : Real × Real) :
    orderedHistoryDenominators
        [physlibA1PairMismatchChart
          fixed site₁ site₂ observed termOne pair,
         physlibA1PairMismatchChart
          fixed site₁ site₂ observed termTwo pair] =
      [physlibA1PairMismatchChart
          fixed site₁ site₂ observed termOne pair,
       physlibA1PairMismatchChart
          fixed site₁ site₂ observed termTwo pair,
       physlibA1CumulativePairMismatchChart
          fixed site₁ site₂ observed
            (physlibA1OrderTwoTermFamily termOne termTwo)
            Finset.univ pair] := by
  exact physlibA1OrderTwoDenominators_eq_local_local_cumulative
    fixed site₁ site₂ observed termOne termTwo pair

#print axioms
  ArchonPhysics.PhyslibFPUTA1CumulativePairFiberCompactSmallBall.hasStrictDerivAt_physlibA1CumulativePairMismatchFiber
#print axioms
  ArchonPhysics.PhyslibFPUTA1CumulativePairFiberCompactSmallBall.deriv_physlibA1CumulativePairMismatchFiber_eq_sum
#print axioms
  ArchonPhysics.PhyslibFPUTA1CumulativePairFiberCompactSmallBall.exists_physlibA1CumulativePairFiber_localInjectivePatch
#print axioms
  ArchonPhysics.PhyslibFPUTA1CumulativePairFiberCompactSmallBall.exists_atlasCard_physlibA1CumulativePairFiberCompact_smallBall
#print axioms
  ArchonPhysics.PhyslibFPUTA1CumulativePairFiberCompactSmallBall.exists_ordinaryGardenCoordinateCompactAtlas_of_physlibA1Cumulative
#print axioms
  ArchonPhysics.PhyslibFPUTA1CumulativePairFiberCompactSmallBall.physlibA1OrderTwoDenominators_eq_local_local_cumulative
#print axioms
  ArchonPhysics.PhyslibFPUTA1CumulativePairFiberCompactSmallBall.exists_physlibA1OrderTwoCompactAtlasCertificates
#print axioms problem_physlibA1CumulativePairFiber_deriv_eq_sum
#print axioms problem_physlibA1OrderTwo_denominators_exact

end

end ArchonPhysicsConsumers.Thermalization
