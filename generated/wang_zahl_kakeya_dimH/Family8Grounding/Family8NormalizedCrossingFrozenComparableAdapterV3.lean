import Family8Grounding.Family8StickyScaleCoverFrozenComparableAdapterV2
import Family8Grounding.Family8NormalizedCFDividingWitnessFiniteSelectionV6
import Mathlib.Tactic

/-!
# Literal normalized-crossing cover to frozen polylogarithmic assembly

The normalized first-crossing theorem returns the literal coherent interval
cover at scales `tau_m <= rho`.  This file removes the remaining type seam:
that very cover is converted to its actual coarse partition and passed to the
frozen comparable-multiplicity producer.

The only extra datum is a shading on the actual lower-scale family and the
necessary assertion that its restriction to the cover's active fine indices
has nonzero mass.  The normalized selector does not contain any shading, and
an admissible empty datum is possible, so this nondegeneracy cannot be
derived from the crossing certificate alone.  No almost-cover,
`lotsOfUinW`, cover-cost, or desired retention inequality is assumed.
-/

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8NormalizedCrossingFrozenComparableAdapterV3

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8KatzTaoFrostmanPropertiesV1
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDeltaMaxFiniteChainV2
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainCoherentIntervalProducerV1
open Family8NormalizedCFDividingWitnessFiniteSelectionV4.CoherentStickyMultiscaleCover
open Family8ComparableMultiplicityBucketsV1
open Family8FrozenComparableActualAverageMassDensityV1
open Family8StickyScaleCoverFrozenComparableAdapterV2

noncomputable section

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000
set_option linter.unusedSectionVars false

local instance family8CrossingFrozenPropDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

variable {delta : NNReal} {iota : Type}
  [Fintype iota] [DecidableEq iota]
  {depth : Nat}

/-- The actual index type at the lower endpoint of a selected interval. -/
abbrev bufferedLowerIndex
    (D : ActualTubeDatum delta iota)
    (C : CoherentStickyMultiscaleCover D.family)
    (S : FiniteScaleSequence delta depth) (m : Fin depth) : Type :=
  Fin ((C.base.cover (S.tau m) (S.delta_le_tau m)
    (CoherentStickyMultiscaleCover.tau_le_one S m)).coarseCard)

/-- The literal tube family chosen at the lower endpoint `tau_m`. -/
def bufferedLowerFamily
    (D : ActualTubeDatum delta iota)
    (C : CoherentStickyMultiscaleCover D.family)
    (S : FiniteScaleSequence delta depth) (m : Fin depth) :
    UniformTubeFamily (S.tau m) (bufferedLowerIndex D C S m) :=
  (C.base.cover (S.tau m) (S.delta_le_tau m)
    (CoherentStickyMultiscaleCover.tau_le_one S m)).coarse

/-- The exact interval cover occurring in the normalized crossing theorem,
with its lower family exposed under a stable name. -/
def bufferedIntervalCover
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible)
    (C : CoherentStickyMultiscaleCover D.family)
    (S : FiniteScaleSequence delta depth)
    (epsilon : Real) (hepsilon : 0 ≤ epsilon)
    (m : Fin depth) (rho : NNReal)
    (hbuffered : S.IsBuffered epsilon m rho) :
    StickyScaleCover (bufferedLowerFamily D C S m) rho :=
  C.intervalScaleCover (S.tau m) rho (S.delta_le_tau m)
    (actualDatum_tau_le_of_isBuffered D hD S hepsilon m rho hbuffered)
    (buffered_le_one S hepsilon m rho hbuffered)

/-- A literal buffered interval selected by the normalized first-crossing
machinery feeds directly into the actual same-data frozen assembly.  Thus the
selector-to-partition and partition-to-polylog type seams are completely
closed; the displayed nonzero source mass is the sole missing datum not
carried by the selector itself. -/
theorem exists_frozenComparableAssembly_of_actualBufferedInterval
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible)
    (C : CoherentStickyMultiscaleCover D.family)
    (S : FiniteScaleSequence delta depth)
    (epsilon : Real) (hepsilon : 0 ≤ epsilon)
    (m : Fin depth) (rho : NNReal)
    (hbuffered : S.IsBuffered epsilon m rho)
    (Y : Shading (bufferedLowerFamily D C S m).bodyFamily)
    (r : Real) (hr : 0 < r)
    (hsource :
      (IndexedShadingRefinement.restrictTo Y
        (bufferedIntervalCover D hD C S epsilon hepsilon m rho hbuffered).activeFine).shading.shadingMass ≠
          0) :
    let U := bufferedIntervalCover D hD C S epsilon hepsilon m rho hbuffered
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
  exact exists_frozenComparableAssembly_of_stickyScaleCover
    (bufferedIntervalCover D hD C S epsilon hepsilon m rho hbuffered)
    (actualDatum_tau_le_of_isBuffered D hD S hepsilon m rho hbuffered)
    Y r hr hsource

#print axioms bufferedLowerFamily
#print axioms bufferedIntervalCover
#print axioms exists_frozenComparableAssembly_of_actualBufferedInterval

end

end Family8NormalizedCrossingFrozenComparableAdapterV3
