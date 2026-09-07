import Family8Grounding.Family8CanonicalBufferedGlobalFirstFactorPowerInputsV1
import Family8Grounding.Family8StickyActiveFrozenCoarseSourceMassFrostmanScaleSupportV1
import Family8Grounding.Family8StickyActiveRestrictedCoarseB2SupportV1
import Family8Grounding.Family8StickyActiveCoarseKatzTaoCardScaleMassUpperV4
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 8000000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8CanonicalBufferedGlobalFrozenOuterFrostmanEndpointV2

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8KatzTaoFrostmanPropertiesV1
open Family8GeneralizedKatzTaoMultiplicityV1
open Family8FiniteRandomRigidMotionB2FreshGreedyV1
open Family8FrozenCoarseB2FrostmanActualDatumV1
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainCoherentIntervalProducerV1
open FamilyStickyScaleChainIdentifiedFrostmanDividingWitnessV4
open Family8IdentifiedDividingWitnessCanonicalBufferedCoverV5.Witness
open Family8StickyScaleCoverActiveFineRestrictionV2.ScaleCover
open Family8FrozenComparableActualAverageMassDensityV1.Assembly
open Family8StickyActiveFrozenCoarseSourceMassFrostmanScaleSupportV1
open Family8StickyActiveRestrictedCoarseB2SupportV1
open Family8StickyActiveCoarseKatzTaoCardScaleMassUpperV4.StickyScaleCover
open Family8ParentAggregatedShadingActiveCoarseXUpperV3.StickyScaleCover

noncomputable section

/-!
# Frozen outer Frostman endpoint on the canonical global cover, V2

The canonical first-factor endpoint already constructs a bounded frozen
assembly on the active-fine restriction of the global delta-to-buffered
cover.  The general scale-support Frostman theorem applies to that very same
partition and assembly.  Consequently the third factor can be attached
without passing through the source-to-tau parent shading and without paying
its natural fibre cap.  V1 omitted two namespace opens and is not imported.
-/

namespace Witness

variable {delta : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {depth N : Nat} {stoppingEpsilon : Real}
  {stoppingEta : Nat -> Real}

theorem exists_canonicalBufferedGlobal_normalizedFrozenOuter_of_sourceMass
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
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
        (canonicalBufferedGlobalCover W hD.delta_pos
          hstopping hstoppingHalf))
      (activeFineRestrictedScaleCover
        (canonicalBufferedGlobalCover W hD.delta_pos
          hstopping hstoppingHalf)).coarse)
    (Y : Shading
      (activeFineRestrictedFamily
        (canonicalBufferedGlobalCover W hD.delta_pos
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
        (canonicalBufferedGlobalCover W hD.delta_pos
          hstopping hstoppingHalf) : ENNReal))
    (hbaseScalar :
      ((conflictThreshold + 1 : Nat) : ENNReal) *
          ((128 * CKT) * volume (unitBallBody : Set Space)) <=
        (((canonicalBufferedRadius W / 8 : NNReal) : ENNReal) ^ (-etaF)) *
          (baseFloor / 128)) :
    exists selected : Finset
        (Fin (activeFineRestrictedScaleCover
          (canonicalBufferedGlobalCover W hD.delta_pos
            hstopping hstoppingHalf)).coarseCard),
      selected.Nonempty /\
      A.frozenCoarse.averageMultiplicity <=
        ((conflictThreshold + 1 : Nat) : ENNReal) *
          frostmanMultiplicityRHS (canonicalBufferedRadius W / 8)
            (restrictActualTubeDatum
              (Family8FiniteRandomRigidMotionB2NormalizedDatumV1.eighthNormalizedDatum
                (frozenCoarseActualDatum Pcoarse Y A))
              selected).actualFamilyVolume epsilon beta := by
  let G := canonicalBufferedGlobalCover W hD.delta_pos
    hstopping hstoppingHalf
  have hrhoPos : 0 < canonicalBufferedRadius W :=
    canonicalBufferedRadius_pos W hD.delta_pos hstopping
  have hsixteenthHalf : (1 / 16 : NNReal) <= (2 : NNReal)⁻¹ := by
    change (1 : Real) / 16 <= (2 : Real)⁻¹
    norm_num
  have hrhoHalf : canonicalBufferedRadius W <= (2 : NNReal)⁻¹ :=
    hbufferedSixteenth.trans hsixteenthHalf
  have hscale : delta <= canonicalBufferedRadius W :=
    (Sseq.delta_le_tau W.m).trans
      (tau_le_canonicalBufferedRadius W hD.delta_pos hstopping)
  have hrhoOne : canonicalBufferedRadius W <= 1 :=
    canonicalBufferedRadius_le_one W hD.delta_pos hstopping hstoppingHalf
  have hKT : G.IsKatzTaoAtScale CKT :=
    hKTEvery (canonicalBufferedRadius W) hscale hrhoOne
  have hXUpper : (activeCoarseCardScaleMass G : ENNReal) <= 1024 * CKT :=
    activeCoarseCardScaleMass_le_1024_mul_of_isKatzTaoAtScale
      D hD G hrhoHalf hKT
  exact exists_normalized_activeFrozenCoarse_of_sourceMass_scaleSupport
    hF G Pcoarse Y A hrhoPos hrhoHalf
      (activeFineRestrictedScaleCover_coarse_carrier_subset_closedBall_two
        D hD G hbufferedSixteenth)
      hconflict hKT hdelta0 hsource0 hsourceLower hXUpper hdensityScalar
      hbaseLower hbaseScalar

#print axioms
  exists_canonicalBufferedGlobal_normalizedFrozenOuter_of_sourceMass

end Witness
end
end Family8CanonicalBufferedGlobalFrozenOuterFrostmanEndpointV2
