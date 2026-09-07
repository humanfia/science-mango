import Family8Grounding.Family8CanonicalBufferedTauActiveKatzTaoEveryScaleV3
import Family8Grounding.Family8StickyActiveRestrictedCoarseKatzTaoV1
import Family8Grounding.Family8FrozenCoarseB2FrostmanActualDatumV1
import Family8Grounding.Family8B2NormalizedConflictKatzTaoCapV3
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8CanonicalBufferedTauActiveFrozenOuterConflictCapV5

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8KatzTaoFrostmanPropertiesV1
open Family8GeneralizedKatzTaoMultiplicityV1
open Family8FiniteRandomRigidMotionB2FreshGreedyV1
open Family8B2NormalizedConflictKatzTaoCapV3
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainCoherentIntervalProducerV1
open FamilyStickyScaleChainIdentifiedFrostmanDividingWitnessV4
open Family8IdentifiedDividingWitnessCanonicalBufferedCoverV5.Witness
open Family8IdentifiedDividingWitnessCanonicalTauCoarseDatumV3.Witness
open Family8StickyScaleCoverActiveFineRestrictionV2.ScaleCover
open Family8StickyActiveRestrictedCoarseKatzTaoV1
open Family8FrozenComparableActualAverageMassDensityV1.Assembly
open Family8FrozenCoarseB2FrostmanActualDatumV1
open Family8CanonicalBufferedTauActiveKatzTaoEveryScaleV3.Witness

noncomputable section

/-!
# Exact conflict cap on the canonical frozen-coarse datum

The frozen datum has exactly the reindexed active-parent family.  Every-scale
Katz--Tao control therefore supplies the literal normalized conflict cap on
the same partition and the same frozen assembly, with no degree callback.
-/

namespace Witness

variable {delta : NNReal} {iota : Type}
  [Fintype iota] [DecidableEq iota]
  {depth N : Nat} {stoppingEpsilon : Real}
  {stoppingEta : Nat -> Real}

theorem canonicalBufferedTauActive_frozenCoarse_normalizedConflict_card_le
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible)
    (Cmulti : CoherentStickyMultiscaleCover D.family)
    (Sseq : FiniteScaleSequence delta depth)
    (W : IdentifiedFrostmanDividingWitness D.family Cmulti N
      stoppingEpsilon stoppingEta Sseq)
    (hstopping : 0 <= stoppingEpsilon)
    (hstoppingHalf : stoppingEpsilon <= 1 / 2)
    (hbufferedSixteenth :
      canonicalBufferedRadius W <= (1 / 16 : NNReal))
    (Pcoarse : CoarseTubePartition
      (activeFineRestrictedFamily
        (canonicalBufferedTauActiveCover D hD Cmulti Sseq W
          hstopping hstoppingHalf))
      (activeFineRestrictedScaleCover
        (canonicalBufferedTauActiveCover D hD Cmulti Sseq W
          hstopping hstoppingHalf)).coarse)
    (Y : Shading
      (activeFineRestrictedFamily
        (canonicalBufferedTauActiveCover D hD Cmulti Sseq W
          hstopping hstoppingHalf)).bodyFamily)
    {r : Real}
    (A : Family8FrozenNeighborhoodAssemblyV1.Assembly
      Pcoarse.asConvexFactorization Y r)
    {CKT : ENNReal} (hCKTfinite : CKT ≠ ∞)
    (hKTEvery : Cmulti.base.IsKatzTaoAtEveryScale CKT) :
    forall k,
      (normalizedConflictIndices
        (frozenCoarseActualDatum Pcoarse Y A) k).card <=
          normalizedConflictKatzTaoNatCap
            (canonicalBufferedRadius W) (128 * CKT) := by
  let U := canonicalBufferedTauActiveCover
    D hD Cmulti Sseq W hstopping hstoppingHalf
  have hrhoPos : 0 < canonicalBufferedRadius W :=
    canonicalBufferedRadius_pos W hD.delta_pos hstopping
  have hsixteenHalf : (1 / 16 : NNReal) <= (2 : NNReal)⁻¹ := by
    change (1 : Real) / 16 <= (2 : Real)⁻¹
    norm_num
  have hrhoHalf : canonicalBufferedRadius W <= (2 : NNReal)⁻¹ :=
    hbufferedSixteenth.trans hsixteenHalf
  have hKTU : U.IsKatzTaoAtScale CKT :=
    canonicalBufferedTauActiveCover_isKatzTaoAtScale_of_everyScale
      D hD Cmulti Sseq W hstopping hstoppingHalf hKTEvery
  have hKTcoarse : IsKatzTao CKT
      (activeFineRestrictedScaleCover U).coarse.bodyFamily :=
    activeFineRestrictedScaleCover_coarse_isKatzTao U hKTU
  have hKTdatum : IsKatzTao CKT
      (frozenCoarseActualDatum Pcoarse Y A).family.bodyFamily := by
    simpa only [frozenCoarseActualDatum_family, U] using hKTcoarse
  intro k
  exact normalizedConflictIndices_card_le_sourceKatzTaoNatCap
    (frozenCoarseActualDatum Pcoarse Y A) hrhoPos hrhoHalf
      hCKTfinite hKTdatum k

#print axioms
  canonicalBufferedTauActive_frozenCoarse_normalizedConflict_card_le

end Witness
end
end Family8CanonicalBufferedTauActiveFrozenOuterConflictCapV5
