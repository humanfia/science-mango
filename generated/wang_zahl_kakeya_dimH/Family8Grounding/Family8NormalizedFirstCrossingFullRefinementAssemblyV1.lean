import Family8Grounding.Family8NormalizedLongIntervalWitnessV1
import Family8Grounding.Family8NormalizedCrossingSourceTauActualAverageV2
import Family8Grounding.Family8IdentifiedDividingWitnessSourceTauFrozenProductV3
import Mathlib.Tactic

/-!
# The selected normalized first crossing on the full refinement

The finite stopping selector used by the paper returns a first strict
crossing together with every earlier barrier.  Earlier adapters constructed
the literal source-to-`tau` shading and frozen comparable assembly, but did
not package the selector output as data consumed by those adapters.

This file closes that seam.  The crossing witness stores the literal coherent
interval cover, its strict upper crossing, and all earlier lower barriers.
For the full refinement, a Frostman source supplies the required nonzero
active mass automatically, so the selected crossing produces the actual
same-data frozen assembly without a positivity callback.
-/

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8NormalizedFirstCrossingFullRefinementAssemblyV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8AllFrostmanStickyUnionProducerV1
open Family8ComparableMultiplicityBucketsV1
open Family8FrozenComparableActualAverageMassDensityV1
open Family8FrozenComparableActualAverageMassDensityV1.Assembly
open Family8FullRefinementActualDatumV1
open Family8IdentifiedDividingWitnessSourceTauFrozenProductV3.Witness
open Family8KatzTaoFrostmanPropertiesV1
open Family8NormalizedCFDividingWitnessBridgeV2.StickyScaleCover
open Family8NormalizedCFDividingWitnessFiniteSelectionV4.CoherentStickyMultiscaleCover
open Family8NormalizedCrossingFrozenComparableAdapterV3
open Family8StickyScaleCoverFrozenComparableAdapterV2
open Family8NormalizedCrossingSourceTauActualAverageV2
open Family8NormalizedCrossingSourceTauShadingV2
open Family8NormalizedLongIntervalWitnessV1
open Family8NormalizedLongIntervalWitnessV1.CoherentStickyMultiscaleCover
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainCoherentIntervalProducerV1
open FamilyStickyHierarchyEndpointPrefixShadingTransportV1.StickyScaleCover

noncomputable section

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false

variable {delta : NNReal} {iota : Type}
  [Fintype iota] [DecidableEq iota]
  {depth : Nat}

/-- The literal first normalized crossing, including the barriers at every
strictly earlier stopping stage. -/
structure FirstActualNormalizedCrossingWitness
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible)
    (C : CoherentStickyMultiscaleCover D.family)
    (S : FiniteScaleSequence delta depth)
    (epsilon : Real) (hepsilon : 0 <= epsilon)
    (eta : Nat -> Real) (N : Nat) where
  stage : Nat
  stage_le : stage <= N
  m : Fin depth
  rho : NNReal
  notLarge : ¬ S.IsLarge epsilon m
  buffered : S.IsBuffered epsilon m rho
  strict_crossing :
    parentNormalizedFiberCFMax
        (bufferedIntervalCover D hD C S epsilon hepsilon m rho buffered) <
      (((rho / S.tau m : NNReal) : ENNReal) ^ eta stage)
  earlier_barrier : forall earlier : Nat, earlier < stage ->
    forall m' : Fin depth, ¬ S.IsLarge epsilon m' ->
      forall rho' : NNReal, (hbuffered : S.IsBuffered epsilon m' rho') ->
        (((rho' / S.tau m' : NNReal) : ENNReal) ^ eta earlier) <=
          parentNormalizedFiberCFMax
            (bufferedIntervalCover D hD C S epsilon hepsilon
              m' rho' hbuffered)

namespace FirstActualNormalizedCrossingWitness

variable {D : ActualTubeDatum delta iota} {hD : D.IsAdmissible}
  {C : CoherentStickyMultiscaleCover D.family}
  {S : FiniteScaleSequence delta depth}
  {epsilon : Real} {hepsilon : 0 <= epsilon}
  {eta : Nat -> Real} {N : Nat}

/-- Package the raw existential emitted by the finite selector without
weakening either its first strict crossing or its earlier barriers. -/
theorem nonempty_of_selector_output
    (hfirst :
      exists stage : Nat, stage <= N /\
        (exists m : Fin depth, exists rho : NNReal,
          exists _hnotLarge : ¬ S.IsLarge epsilon m,
          exists hbuffered : S.IsBuffered epsilon m rho,
            parentNormalizedFiberCFMax
                (C.intervalScaleCover (S.tau m) rho
                  (S.delta_le_tau m)
                  (actualDatum_tau_le_of_isBuffered
                    D hD S hepsilon m rho hbuffered)
                  (buffered_le_one S hepsilon m rho hbuffered)) <
              (((rho / S.tau m : NNReal) : ENNReal) ^ eta stage)) /\
        forall earlier : Nat, earlier < stage ->
          forall m : Fin depth, ¬ S.IsLarge epsilon m ->
            forall rho : NNReal,
              (hbuffered : S.IsBuffered epsilon m rho) ->
                (((rho / S.tau m : NNReal) : ENNReal) ^ eta earlier) <=
                  parentNormalizedFiberCFMax
                    (C.intervalScaleCover (S.tau m) rho
                      (S.delta_le_tau m)
                      (actualDatum_tau_le_of_isBuffered
                        D hD S hepsilon m rho hbuffered)
                      (buffered_le_one S hepsilon m rho hbuffered))) :
    Nonempty
      (FirstActualNormalizedCrossingWitness
        D hD C S epsilon hepsilon eta N) := by
  rcases hfirst with
    ⟨stage, hstage, ⟨m, rho, hnotLarge, hbuffered, hstrict⟩,
      hearlier⟩
  refine ⟨{
    stage := stage
    stage_le := hstage
    m := m
    rho := rho
    notLarge := hnotLarge
    buffered := hbuffered
    strict_crossing := ?_
    earlier_barrier := ?_ }⟩
  · exact hstrict
  · intro earlier hearlierStage m' hnotLarge' rho' hbuffered'
    exact hearlier earlier hearlierStage m' hnotLarge' rho' hbuffered'

end FirstActualNormalizedCrossingWitness

/-- The paper-normalized long-interval trichotomy with the recursive branch
now represented by a stable witness rather than a nested existential. -/
theorem allLarge_or_normalizedLongIntervalWitness_or_firstCrossingWitness
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible)
    (C : CoherentStickyMultiscaleCover D.family)
    (S : FiniteScaleSequence delta depth)
    (epsilon : Real) (hepsilon : 0 <= epsilon)
    (eta : Nat -> Real) (N : Nat) (hN : 1 <= N)
    (hsource : forall m : Fin depth,
      parentNormalizedFiberCFMax
          (C.base.cover (S.tau m) (S.delta_le_tau m)
            ((S.tau_le_theta m).trans (S.theta_le_one m))) <=
        (((S.tau m / delta : NNReal) : ENNReal) ^ eta (N - 1)))
    (hadjacent : forall m : Fin depth,
      parentNormalizedFiberCFMax
          (C.intervalScaleCover (S.tau m) (S.theta m)
            (S.delta_le_tau m) (S.tau_le_theta m)
            (S.theta_le_one m)) <=
        (((S.theta m / S.tau m : NNReal) : ENNReal) ^ eta (N - 1))) :
    ((S.AllStepsLarge epsilon ∨
        Nonempty
          (NormalizedLongIntervalWitness D.family C N epsilon eta S)) ∨
      Nonempty
        (FirstActualNormalizedCrossingWitness
          D hD C S epsilon hepsilon eta N)) := by
  rcases
      allLarge_or_normalizedLongIntervalWitness_or_firstActualNormalizedCrossing
        D hD C S epsilon hepsilon eta N hN hsource hadjacent with
    hterminal | hfirst
  · exact Or.inl hterminal
  · exact Or.inr
      (FirstActualNormalizedCrossingWitness.nonempty_of_selector_output
        hfirst)

namespace FirstActualNormalizedCrossingWitness

variable {etaF : Real}

/-- On the full refinement, Frostman mass makes the selected first crossing
feed the callback-free source-to-`tau` frozen assembly.  The same witness
still carries the strict crossing and all earlier barriers. -/
theorem exists_frozenComparableAssembly_of_fullRefinement_frostman
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible)
    (C : CoherentStickyMultiscaleCover (fullRefinementDatum D).family)
    (S : FiniteScaleSequence delta depth)
    (epsilon : Real) (hepsilon : 0 <= epsilon)
    (eta : Nat -> Real) (N : Nat)
    (W : FirstActualNormalizedCrossingWitness
      (fullRefinementDatum D) (fullRefinementDatum_isAdmissible hD)
        C S epsilon hepsilon eta N)
    (hF : FrostmanHypotheses D etaF)
    (r : Real) (hr : 0 < r) :
    let Y := sourceTauFullShading (fullRefinementDatum D) C S W.m
    let U := bufferedIntervalCover
      (fullRefinementDatum D) (fullRefinementDatum_isAdmissible hD)
        C S epsilon hepsilon W.m W.rho W.buffered
    let hsourceTau :
        (IndexedShadingRefinement.restrictTo
          (fullRefinementDatum D).shading
          (sourceTauCover (fullRefinementDatum D) C S W.m).activeFine).shading.shadingMass ≠
            0 := by
      have hfloor : (delta : ENNReal) ^ (2 * etaF) <=
          D.shading.shadingMass :=
        delta_rpow_two_eta_le_shadingMass_of_frostman D hD hF
      have hpositive : 0 < (delta : ENNReal) ^ (2 * etaF) :=
        ENNReal.rpow_pos (ENNReal.coe_pos.mpr hD.delta_pos) ENNReal.coe_ne_top
      exact fullRefinement_sourceTau_activeMass_ne_zero D C S W.m
        (ne_of_gt (hpositive.trans_le hfloor))
    let hsource :
        (IndexedShadingRefinement.restrictTo Y U.activeFine).shading.shadingMass ≠
          0 :=
      sourceTauFullShading_restrictedMass_ne_zero
        (fullRefinementDatum D) (fullRefinementDatum_isAdmissible hD)
          C S epsilon hepsilon W.m W.rho W.buffered hsourceTau
    exists A : Family8FrozenNeighborhoodAssemblyV1.Assembly
        (sourceMassCoarseTubePartition U
          (actualDatum_tau_le_of_isBuffered
            (fullRefinementDatum D) (fullRefinementDatum_isAdmissible hD)
              S hepsilon W.m W.rho W.buffered) Y hsource).asConvexFactorization
          Y r,
      A.loss = frozenComparableLoss
          (bufferedLowerIndex (fullRefinementDatum D) C S W.m)
          (Fin U.coarseCard) /\
      (parentAggregatedShading
          (sourceTauCover (fullRefinementDatum D) C S W.m)
          (fullRefinementDatum D).shading).averageMultiplicity <=
        (frozenComparableLoss
          (bufferedLowerIndex (fullRefinementDatum D) C S W.m)
          (Fin U.coarseCard) : ENNReal) *
          (actualRefinementShading A).averageMultiplicity /\
      exists k : Fin U.coarseCard, k ∈ U.activeCoarse /\
        0 < volume (finalFiberShading A k).shadedUnion /\
        (actualRefinementShading A).averageMultiplicity <=
          4 * (A.frozenCoarse.averageMultiplicity *
            (finalFiberShading A k).averageMultiplicity) := by
  dsimp only
  have hfloor : (delta : ENNReal) ^ (2 * etaF) <=
      D.shading.shadingMass :=
    delta_rpow_two_eta_le_shadingMass_of_frostman D hD hF
  have hpositive : 0 < (delta : ENNReal) ^ (2 * etaF) :=
    ENNReal.rpow_pos (ENNReal.coe_pos.mpr hD.delta_pos) ENNReal.coe_ne_top
  have hsourceTau :=
    fullRefinement_sourceTau_activeMass_ne_zero D C S W.m
      (ne_of_gt (hpositive.trans_le hfloor))
  exact exists_frozenComparableAssembly_with_sourceTau_actualAverage
    (fullRefinementDatum D) (fullRefinementDatum_isAdmissible hD)
      C S epsilon hepsilon W.m W.rho W.buffered r hr hsourceTau

#print axioms FirstActualNormalizedCrossingWitness.nonempty_of_selector_output
#print axioms allLarge_or_normalizedLongIntervalWitness_or_firstCrossingWitness
#print axioms
  FirstActualNormalizedCrossingWitness.exists_frozenComparableAssembly_of_fullRefinement_frostman

end FirstActualNormalizedCrossingWitness

end

end Family8NormalizedFirstCrossingFullRefinementAssemblyV1
