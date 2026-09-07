import Family8Grounding.Family8NormalizedCrossingSourceTauShadingV2
import Mathlib.Tactic

/-!
# Source-produced frozen assembly at an actual normalized crossing

This is the one-step composition of the source-to-`tau` shading producer with
the literal normalized-crossing frozen adapter.  Starting from nonzero mass
of the original shading on the actual source-to-`tau` active set, it builds
the full lower-scale shading, the exact coarse partition, and the
polylogarithmic same-data assembly.

All mass, density, and average-multiplicity conclusions refer to the literal
constructed shadings.  No almost-cover, cover-cost, `lotsOfUinW`, retention,
or target-average callback occurs in the theorem.
-/

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8NormalizedCrossingSourceTauFrozenAssemblyV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8KatzTaoFrostmanPropertiesV1
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainCoherentIntervalProducerV1
open Family8NormalizedCFDividingWitnessFiniteSelectionV4.CoherentStickyMultiscaleCover
open Family8ComparableMultiplicityBucketsV1
open Family8FrozenComparableActualAverageMassDensityV1
open Family8StickyScaleCoverFrozenComparableAdapterV2
open Family8NormalizedCrossingFrozenComparableAdapterV3
open Family8NormalizedCrossingSourceTauShadingV2

noncomputable section

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000
set_option linter.unusedSectionVars false

local instance family8SourceTauAssemblyPropDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

variable {delta : NNReal} {iota : Type}
  [Fintype iota] [DecidableEq iota]
  {depth : Nat}

/-- The full callback-free assembly chain for a buffered interval selected by
the normalized first-crossing machinery.  The sole nondegeneracy premise is
nonzero source shading mass on the actual source-to-`tau` active set. -/
theorem exists_frozenComparableAssembly_of_sourceTauActiveMass
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible)
    (C : CoherentStickyMultiscaleCover D.family)
    (S : FiniteScaleSequence delta depth)
    (epsilon : Real) (hepsilon : 0 ≤ epsilon)
    (m : Fin depth) (rho : NNReal)
    (hbuffered : S.IsBuffered epsilon m rho)
    (r : Real) (hr : 0 < r)
    (hsourceTau :
      (IndexedShadingRefinement.restrictTo D.shading
        (sourceTauCover D C S m).activeFine).shading.shadingMass ≠ 0) :
    let Y := sourceTauFullShading D C S m
    let U := bufferedIntervalCover D hD C S epsilon hepsilon m rho hbuffered
    let hsource :
        (IndexedShadingRefinement.restrictTo Y U.activeFine).shading.shadingMass ≠
          0 :=
      sourceTauFullShading_restrictedMass_ne_zero
        D hD C S epsilon hepsilon m rho hbuffered hsourceTau
    ∃ A : Family8FrozenNeighborhoodAssemblyV1.Assembly
        (sourceMassCoarseTubePartition U
          (actualDatum_tau_le_of_isBuffered
            D hD S hepsilon m rho hbuffered) Y hsource).asConvexFactorization
          Y r,
      A.loss = frozenComparableLoss (bufferedLowerIndex D C S m)
        (Fin U.coarseCard) ∧
      A.fiberLabel ∈ Finset.range
        (Nat.log 2 (Fintype.card (bufferedLowerIndex D C S m)) + 2) ∧
      A.outerLabel ∈
        Finset.range (Nat.log 2 (Fintype.card (Fin U.coarseCard)) + 2) ∧
      (Assembly.sourceActiveFineShading
          (sourceMassCoarseTubePartition U
            (actualDatum_tau_le_of_isBuffered
              D hD S hepsilon m rho hbuffered) Y hsource).asConvexFactorization
          Y).shadingMass ≤
        (frozenComparableLoss (bufferedLowerIndex D C S m)
          (Fin U.coarseCard) : ENNReal) *
          (Assembly.actualRefinementShading A).shadingMass ∧
      (Assembly.sourceActiveFineShading
          (sourceMassCoarseTubePartition U
            (actualDatum_tau_le_of_isBuffered
              D hD S hepsilon m rho hbuffered) Y hsource).asConvexFactorization
          Y).shadingDensity /
          (frozenComparableLoss (bufferedLowerIndex D C S m)
            (Fin U.coarseCard) : ENNReal) ≤
        (Assembly.actualRefinementShading A).shadingDensity ∧
      ∃ k ∈ U.activeCoarse,
        0 < volume (Assembly.finalFiberShading A k).shadedUnion ∧
        (comparableBase A.fiberLabel : ENNReal) ≤
          (Assembly.finalFiberShading A k).averageMultiplicity ∧
        (Assembly.finalFiberShading A k).averageMultiplicity ≤
          (2 * comparableBase A.fiberLabel : Nat) ∧
        (comparableBase A.outerLabel : ENNReal) ≤
          A.frozenCoarse.averageMultiplicity ∧
        A.frozenCoarse.averageMultiplicity ≤
          (2 * comparableBase A.outerLabel : Nat) ∧
        (Assembly.actualRefinementShading A).averageMultiplicity ≤
          4 * (A.frozenCoarse.averageMultiplicity *
            (Assembly.finalFiberShading A k).averageMultiplicity) := by
  dsimp only
  exact exists_frozenComparableAssembly_of_actualBufferedInterval
    D hD C S epsilon hepsilon m rho hbuffered
    (sourceTauFullShading D C S m) r hr
    (sourceTauFullShading_restrictedMass_ne_zero
      D hD C S epsilon hepsilon m rho hbuffered hsourceTau)

#print axioms exists_frozenComparableAssembly_of_sourceTauActiveMass

end

end Family8NormalizedCrossingSourceTauFrozenAssemblyV1
