import Family8Grounding.Family8CanonicalBufferedTauActiveFrozenOuterFrostmanEndpointV4
import Family8Grounding.Family8EighthNormalizedSelectedFrostmanThirdFactorV3
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8CanonicalBufferedTauActiveFrozenOuterThirdFactorV2

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
open Family8CanonicalBufferedTauActiveFrozenOuterFrostmanEndpointV4.Witness
open Family8EighthNormalizedSelectedFrostmanThirdFactorV3
open Family8ThreeScaleFrostmanFactorAlgebraV2

noncomputable section

/-!
# Canonical frozen outer estimate in the official third-factor normalization

The canonical B2/Frostman endpoint returns a selected actual-volume RHS at
radius `b / 8`.  This module immediately converts that literal conclusion to
the Section 8 scale-count factor from the canonical buffered radius `b` to
one, with every fixed, epsilon, and conflict loss displayed explicitly.

V1 was a namespace/notation draft and is intentionally not imported.
-/

namespace Witness

variable {delta : NNReal} {iota : Type}
  [Fintype iota] [DecidableEq iota]
  {depth N : Nat} {stoppingEpsilon : Real}
  {stoppingEta : Nat -> Real}

/-- The actual same-assembly frozen outer estimate supplies the third factor
required by the arbitrary-middle three-scale composition. -/
theorem exists_canonicalBufferedTauActive_frozenOuter_le_thirdFactor
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
    (hKT :
      (canonicalBufferedTauActiveCover D hD Cmulti Sseq W
        hstopping hstoppingHalf).IsKatzTaoAtScale CKT)
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
  obtain ⟨selected, hselected, haverage⟩ :=
    exists_canonicalBufferedTauActive_normalizedFrozenOuter_of_sourceMass
      D hD Cmulti Sseq W hstopping hstoppingHalf hbufferedSixteenth
        hF Pcoarse Y A hconflict hKT hdelta0 hsource0 hsourceLower
        hdensityScalar hbaseLower hbaseScalar
  have hrhoPos : 0 < canonicalBufferedRadius W :=
    canonicalBufferedRadius_pos W hD.delta_pos hstopping
  have hsixteenHalf : (1 / 16 : NNReal) <= (2 : NNReal)⁻¹ := by
    change (1 : Real) / 16 <= (2 : Real)⁻¹
    norm_num
  have hrhoHalf : canonicalBufferedRadius W <= (2 : NNReal)⁻¹ :=
    hbufferedSixteenth.trans hsixteenHalf
  have htransport :=
    loss_mul_selectedRHS_le_eighthLoss_mul_thirdFactor
      (Family8FiniteRandomRigidMotionB2NormalizedDatumV1.eighthNormalizedDatum
        (frozenCoarseActualDatum Pcoarse Y A)) selected
      (loss := ((conflictThreshold + 1 : Nat) : ENNReal))
      (epsilon := epsilon) (gamma := beta)
      hrhoPos hrhoHalf hbetaTwo
  refine ⟨selected, hselected, haverage.trans ?_⟩
  simpa only [Fintype.card_fin] using htransport

#print axioms
  exists_canonicalBufferedTauActive_frozenOuter_le_thirdFactor

end Witness
end
end Family8CanonicalBufferedTauActiveFrozenOuterThirdFactorV2
