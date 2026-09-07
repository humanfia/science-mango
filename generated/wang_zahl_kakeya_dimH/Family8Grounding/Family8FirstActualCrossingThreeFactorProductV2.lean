import Family8Grounding.Family8FirstActualCrossingNormalizedFrostmanV2
import Family8Grounding.Family8IdentifiedDividingWitnessFirstOuterParentTransportV1

/-!
# Literal three-factor product at the first actual crossing

For the fixed first-crossing witness, Frostman source mass constructs the
same-data frozen comparable assembly.  Source Katz--Tao transports the
original average multiplicity to the source-to-tau parent average.  The two
retention inequalities of that assembly then expose the literal first cap,
frozen coarse average, and surviving final-fibre average in one product.

V1 used Boolean inequality notation in two dependent let-bindings and
omitted the namespace of the Katz--Tao cap; it is not imported.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2600000
set_option linter.unusedSectionVars false

open Set MeasureTheory
open scoped ENNReal NNReal

namespace Family8FirstActualCrossingThreeFactorProductV2

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8AllFrostmanStickyUnionProducerV1
open Family8FrozenComparableActualAverageMassDensityV1
open Family8FrozenComparableActualAverageMassDensityV1.Assembly
open Family8FullRefinementActualDatumV1
open Family8IdentifiedDividingWitnessFirstOuterParentTransportV1.Witness
open Family8KatzTaoFrostmanPropertiesV1
open Family8NormalizedCFDividingWitnessFiniteSelectionV4.CoherentStickyMultiscaleCover
open Family8NormalizedCrossingFrozenComparableAdapterV3
open Family8NormalizedCrossingSourceTauShadingV2
open Family8NormalizedFirstCrossingFullRefinementAssemblyV1
open Family8StickyScaleCoverFrozenComparableAdapterV2
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainCoherentIntervalProducerV1
open FamilyStickyHierarchyEndpointPrefixShadingTransportV1.StickyScaleCover

noncomputable section

variable {delta : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {depth : Nat} {etaF etaKT : Real}

namespace FirstActualNormalizedCrossingWitness

/-- The original datum average is bounded by the actual three factors on the
frozen assembly selected by this very first-crossing witness. -/
theorem exists_fullRefinement_threeFactorProduct
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (C : CoherentStickyMultiscaleCover (fullRefinementDatum D).family)
    (S : FiniteScaleSequence delta depth)
    (epsilon : Real) (hepsilon : 0 <= epsilon)
    (eta : Nat -> Real) (N : Nat)
    (W : FirstActualNormalizedCrossingWitness
      (fullRefinementDatum D) (fullRefinementDatum_isAdmissible hD)
        C S epsilon hepsilon eta N)
    (hF : FrostmanHypotheses D etaF)
    (hKT : KatzTaoHypotheses D etaKT) :
    let E := fullRefinementDatum D
    let Y := sourceTauFullShading E C S W.m
    let U := bufferedIntervalCover
      E (fullRefinementDatum_isAdmissible hD)
        C S epsilon hepsilon W.m W.rho W.buffered
    let hsourceTau :
        (IndexedShadingRefinement.restrictTo E.shading
          (sourceTauCover E C S W.m).activeFine).shading.shadingMass ≠ 0 := by
      have hfloor : (delta : ENNReal) ^ (2 * etaF) <=
          D.shading.shadingMass :=
        delta_rpow_two_eta_le_shadingMass_of_frostman D hD hF
      have hpositive : 0 < (delta : ENNReal) ^ (2 * etaF) :=
        ENNReal.rpow_pos (ENNReal.coe_pos.mpr hD.delta_pos)
          ENNReal.coe_ne_top
      exact
        Family8IdentifiedDividingWitnessSourceTauFrozenProductV3.Witness.fullRefinement_sourceTau_activeMass_ne_zero
          D C S W.m (ne_of_gt (hpositive.trans_le hfloor))
    let hsource :
        (IndexedShadingRefinement.restrictTo Y
          U.activeFine).shading.shadingMass ≠ 0 :=
      sourceTauFullShading_restrictedMass_ne_zero
        E (fullRefinementDatum_isAdmissible hD)
          C S epsilon hepsilon W.m W.rho W.buffered hsourceTau
    exists A : Family8FrozenNeighborhoodAssemblyV1.Assembly
        (sourceMassCoarseTubePartition U
          (actualDatum_tau_le_of_isBuffered
            E (fullRefinementDatum_isAdmissible hD)
              S hepsilon W.m W.rho W.buffered) Y hsource).asConvexFactorization
          Y 1,
      A.loss = frozenComparableLoss
          (bufferedLowerIndex E C S W.m) (Fin U.coarseCard) /\
      exists k : Fin U.coarseCard, k ∈ U.activeCoarse /\
        0 < volume (finalFiberShading A k).shadedUnion /\
        D.shading.averageMultiplicity <=
          (Family8PaperConflictOwnerActiveOwnerKatzTaoDoubledFiberCapV3.katzTaoDoubledFiberNatCap
              delta (S.tau W.m) ((delta : ENNReal) ^ (-etaKT)) : ENNReal) *
            ((4 *
                (frozenComparableLoss
                  (bufferedLowerIndex E C S W.m)
                  (Fin U.coarseCard) : ENNReal)) *
              (A.frozenCoarse.averageMultiplicity *
                (finalFiberShading A k).averageMultiplicity)) := by
  dsimp only
  obtain ⟨A, hloss, hretained, k, hk, hfiber, hproduct⟩ :=
    W.exists_frozenComparableAssembly_of_fullRefinement_frostman
      D hD C S epsilon hepsilon eta N hF 1 (by norm_num)
  refine ⟨A, hloss, k, hk, hfiber, ?_⟩
  have hfirst :=
    fullRefinement_averageMultiplicity_le_hypothesisCap_mul_sourceTauParent
      D hD C S W.m hKT
  have hsecond :=
    Family8IdentifiedDividingWitnessSourceTauFrozenProductV3.sourceAverage_le_fourLoss_mul_outerFiber
      hretained hproduct
  exact hfirst.trans (mul_le_mul' le_rfl hsecond)

#print axioms exists_fullRefinement_threeFactorProduct

end FirstActualNormalizedCrossingWitness

end
end Family8FirstActualCrossingThreeFactorProductV2
