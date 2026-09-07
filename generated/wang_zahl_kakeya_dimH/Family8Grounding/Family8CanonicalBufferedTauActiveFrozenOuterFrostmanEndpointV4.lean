import Family8Grounding.Family8CanonicalBufferedTauActiveRestrictedCoarseB2SupportV3
import Family8Grounding.Family8StickyActiveFrozenCoarseSourceMassFrostmanScaleSupportV1
import Family8Grounding.Family8StickyActiveCoarseKatzTaoCardScaleMassSupportV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8CanonicalBufferedTauActiveFrozenOuterFrostmanEndpointV4

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
open Family8CanonicalBufferedTauActiveRestrictedCoarseB2SupportV3.Witness
open Family8StickyActiveFrozenCoarseSourceMassFrostmanScaleSupportV1
open Family8StickyActiveCoarseKatzTaoCardScaleMassSupportV1.StickyScaleCover
open Family8StickyParentHullVolumeBoundV1

noncomputable section

/-!
# Canonical buffered tau-active frozen outer Frostman endpoint

This specializes the same-data scale-support endpoint to the canonical
buffered tau-active cover.  Radius-two support is inherited from the original
admissible datum.  The card--scale upper bound is proved from the native
Katz--Tao certificate on the very same tau-active cover and radius-four
support, so no admissibility assertion for the intermediate datum occurs.
-/

namespace Witness

variable {delta : NNReal} {iota : Type}
  [Fintype iota] [DecidableEq iota]
  {depth N : Nat} {stoppingEpsilon : Real}
  {stoppingEta : Nat -> Real}

theorem exists_canonicalBufferedTauActive_normalizedFrozenOuter_of_sourceMass
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
        ((conflictThreshold + 1 : Nat) : ENNReal) *
          frostmanMultiplicityRHS (canonicalBufferedRadius W / 8)
            (restrictActualTubeDatum
              (Family8FiniteRandomRigidMotionB2NormalizedDatumV1.eighthNormalizedDatum
                (frozenCoarseActualDatum Pcoarse Y A))
              selected).actualFamilyVolume epsilon beta := by
  let U := canonicalBufferedTauActiveCover
    D hD Cmulti Sseq W hstopping hstoppingHalf
  let G := canonicalBufferedGlobalCover
    W hD.delta_pos hstopping hstoppingHalf
  have hrhoPos : 0 < canonicalBufferedRadius W :=
    canonicalBufferedRadius_pos W hD.delta_pos hstopping
  have hsixteenHalf : (1 / 16 : NNReal) <= (2 : NNReal)⁻¹ := by
    change (1 : Real) / 16 <= (2 : Real)⁻¹
    norm_num
  have hrhoHalf : canonicalBufferedRadius W <= (2 : NNReal)⁻¹ :=
    hbufferedSixteenth.trans hsixteenHalf
  have hfamily : U.activeCoarseFamily = G.activeCoarseFamily :=
    canonicalBufferedTauActiveCover_activeCoarseFamily_eq_global
      D hD Cmulti Sseq W hstopping hstoppingHalf
  have hcontained : forall k,
      (U.activeCoarseFamily k : Set Space) <=
        (closedBallFourBody : Set Space) := by
    intro k
    rw [hfamily]
    exact activeCoarseFamily_body_subset_closedBall_four
      D hD G (hrhoHalf.trans (by norm_num)) k
  have hXUpper : (activeCoarseCardScaleMass U : ENNReal) <= 1024 * CKT :=
    activeCoarseCardScaleMass_le_1024_mul_of_isKatzTaoAtScale_of_contained
      U hrhoHalf hKT hcontained
  exact exists_normalized_activeFrozenCoarse_of_sourceMass_scaleSupport
    hF U Pcoarse Y A hrhoPos hrhoHalf
      (canonicalBufferedTauActiveRestrictedCoarse_carrier_subset_closedBall_two
        D hD Cmulti Sseq W hstopping hstoppingHalf hbufferedSixteenth)
      hconflict hKT hdelta0 hsource0 hsourceLower hXUpper hdensityScalar
      hbaseLower hbaseScalar

#print axioms
  exists_canonicalBufferedTauActive_normalizedFrozenOuter_of_sourceMass

end Witness
end
end Family8CanonicalBufferedTauActiveFrozenOuterFrostmanEndpointV4
