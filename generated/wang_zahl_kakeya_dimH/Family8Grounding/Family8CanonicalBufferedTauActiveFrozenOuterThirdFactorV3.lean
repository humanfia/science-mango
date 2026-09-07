import Family8Grounding.Family8CanonicalBufferedTauActiveFrozenOuterThirdFactorV2
import Family8Grounding.Family8CanonicalBufferedTauActiveKatzTaoEveryScaleV3
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8CanonicalBufferedTauActiveFrozenOuterThirdFactorV3

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8KatzTaoFrostmanPropertiesV1
open Family8GeneralizedKatzTaoMultiplicityV1
open Family8FiniteRandomRigidMotionB2FreshGreedyV1
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainCoherentIntervalProducerV1
open FamilyStickyScaleChainIdentifiedFrostmanDividingWitnessV4
open Family8IdentifiedDividingWitnessCanonicalBufferedCoverV5.Witness
open Family8IdentifiedDividingWitnessCanonicalTauCoarseDatumV3.Witness
open Family8StickyScaleCoverActiveFineRestrictionV2.ScaleCover
open Family8FrozenComparableActualAverageMassDensityV1.Assembly
open Family8FrozenCoarseB2FrostmanActualDatumV1
open Family8ParentAggregatedShadingActiveCoarseXUpperV3.StickyScaleCover
open Family8CanonicalBufferedTauActiveFrozenOuterThirdFactorV2.Witness
open Family8CanonicalBufferedTauActiveKatzTaoEveryScaleV3.Witness
open Family8EighthNormalizedSelectedFrostmanThirdFactorV3
open Family8ThreeScaleFrostmanFactorAlgebraV2

noncomputable section

/-!
# Canonical frozen outer third factor from every-scale Katz--Tao control

The native Katz--Tao premise of the same-assembly endpoint is produced from
the coherent cover's actual every-scale certificate.  No certificate for a
synthetic tau-active datum is requested.
-/

namespace Witness

variable {delta : NNReal} {iota : Type}
  [Fintype iota] [DecidableEq iota]
  {depth N : Nat} {stoppingEpsilon : Real}
  {stoppingEta : Nat -> Real}

theorem exists_canonicalBufferedTauActive_frozenOuter_le_thirdFactor_of_everyScale
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible)
    (Cmulti : CoherentStickyMultiscaleCover D.family)
    (Sseq : FiniteScaleSequence delta depth)
    (W : IdentifiedFrostmanDividingWitness D.family Cmulti N
      stoppingEpsilon stoppingEta Sseq)
    (hstopping : 0 <= stoppingEpsilon)
    (hstoppingHalf : stoppingEpsilon <= 1 / 2)
    (hbufferedSixteenth :
      canonicalBufferedRadius W <= (1 / 16 : NNReal))
    {beta epsilon etaF : Real} {delta0 : NNReal}
    (hF : FrostmanAtParameters beta epsilon etaF delta0)
    (hbetaTwo : beta <= 2)
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
    {conflictThreshold : Nat}
    (hconflict : forall k,
      (normalizedConflictIndices
        (frozenCoarseActualDatum Pcoarse Y A) k).card <= conflictThreshold)
    {CKT : ENNReal}
    (hKTEvery : Cmulti.base.IsKatzTaoAtEveryScale CKT)
    (hdelta0 : canonicalBufferedRadius W / 8 <= delta0)
    {sourceFloor baseFloor : ENNReal}
    (hsource0 :
      (sourceActiveFineShading
        Pcoarse.asConvexFactorization Y).shadingMass ≠ 0)
    (hsourceLower : sourceFloor <=
      (sourceActiveFineShading
        Pcoarse.asConvexFactorization Y).shadingMass)
    (hdensityScalar :
      ((((canonicalBufferedRadius W / 8 : NNReal) : ENNReal) ^ etaF *
            ((conflictThreshold + 1 : Nat) : ENNReal)) * 128) *
          (((A.loss : ENNReal) *
              ((Pcoarse.branchingLoss * Pcoarse.branching : Nat) : ENNReal)) *
            (8 * (1024 * CKT))) <= sourceFloor)
    (hbaseLower : baseFloor <=
      (activeCoarseCardScaleMass
        (canonicalBufferedTauActiveCover D hD Cmulti Sseq W
          hstopping hstoppingHalf) : ENNReal))
    (hbaseScalar :
      ((conflictThreshold + 1 : Nat) : ENNReal) *
          ((128 * CKT) * volume (unitBallBody : Set Space)) <=
        (((canonicalBufferedRadius W / 8 : NNReal) : ENNReal) ^ (-etaF)) *
          (baseFloor / 128)) :
    exists selected : Finset
        (Fin (activeFineRestrictedScaleCover
          (canonicalBufferedTauActiveCover D hD Cmulti Sseq W
            hstopping hstoppingHalf)).coarseCard),
      selected.Nonempty /\
      A.frozenCoarse.averageMultiplicity <=
        eighthSelectedThirdFactorLoss (canonicalBufferedRadius W)
            ((conflictThreshold + 1 : Nat) : ENNReal) epsilon beta *
          sectionEightScaleCountFrostmanFactor
            (canonicalBufferedRadius W) 1
            (activeFineRestrictedScaleCover
              (canonicalBufferedTauActiveCover D hD Cmulti Sseq W
                hstopping hstoppingHalf)).coarseCard beta := by
  have hKT :=
    canonicalBufferedTauActiveCover_isKatzTaoAtScale_of_everyScale
      D hD Cmulti Sseq W hstopping hstoppingHalf hKTEvery
  exact exists_canonicalBufferedTauActive_frozenOuter_le_thirdFactor
    D hD Cmulti Sseq W hstopping hstoppingHalf hbufferedSixteenth
      hF hbetaTwo Pcoarse Y A hconflict hKT hdelta0 hsource0 hsourceLower
      hdensityScalar hbaseLower hbaseScalar

#print axioms
  exists_canonicalBufferedTauActive_frozenOuter_le_thirdFactor_of_everyScale

end Witness
end
end Family8CanonicalBufferedTauActiveFrozenOuterThirdFactorV3
