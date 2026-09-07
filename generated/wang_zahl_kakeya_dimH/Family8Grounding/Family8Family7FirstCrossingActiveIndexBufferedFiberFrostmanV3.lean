import Family8Grounding.Family8Family7FirstCrossingBufferedFiberFrostmanV4
import Family8Grounding.Family8StickyActiveRestrictedCoarseKatzTaoV1
import Family8Grounding.Family8StickyActiveIndexFrozenComparableAssemblyV5
import Family8Grounding.Family8StickyScaleCoverActiveFineRestrictedFiberFrostmanV2
import Family8Grounding.Family8StickyScaleCoverFrostmanInheritanceV1
import Family8Grounding.Family8StickySourceMassFactorizationRoundTripV1

/-!
# FirstCrossing fibre Frostman certificates on the active index, V3

V2 is frozen after direct validation exposed two omitted namespace owners.
This clean successor opens the exact `toConvexFactorization` and selected
buffered-fibre namespaces; the witness and transport proof are unchanged.
-/

set_option autoImplicit false
set_option warningAsError true

open Set MeasureTheory
open scoped ENNReal NNReal

namespace Family8Family7FirstCrossingActiveIndexBufferedFiberFrostmanV3

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8Family7FirstCrossingBufferedFiberFrostmanV4
open Family8Family7FirstCrossingBufferedFiberFrostmanV4.FirstActualNormalizedCrossingWitness
open Family8FirstActualCrossingNormalizedFrostmanV2
open Family8FirstActualCrossingNormalizedFrostmanV2.FirstActualNormalizedCrossingWitness
open Family8KatzTaoFrostmanPropertiesV1
open Family8NormalizedCFDividingWitnessFiniteSelectionV4.CoherentStickyMultiscaleCover
open Family8NormalizedCrossingFrozenComparableAdapterV3
open Family8NormalizedFirstCrossingFullRefinementAssemblyV1
open Family8StickyActiveRestrictedCoarseKatzTaoV1
open Family8StickyActiveIndexFrozenComparableAssemblyV5
open Family8StickyScaleCoverActiveFineRestrictionV2.ScaleCover
open Family8StickyScaleCoverActiveFineRestrictedFiberFrostmanV2
open Family8StickyScaleCoverActiveFineRestrictedFiberFrostmanV2.StickyScaleCover
open Family8StickyScaleCoverActiveFineRestrictedParentTransportV2.StickyScaleCover
open Family8StickyScaleCoverFrostmanInheritanceV1.StickyScaleCover
open Family8StickyScaleCoverFrozenComparableAdapterV2
open Family8StickySourceMassFactorizationRoundTripV1
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainCoherentIntervalProducerV1

noncomputable section

variable {delta : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {depth : Nat}

namespace FirstActualNormalizedCrossingWitness

/-- Every fibre of the exact active-index source-mass factorization has the
same first-crossing Frostman constant in its literal reindexed parent body. -/
theorem activeIndex_sourceMassFactorization_fibers_isFrostmanOn
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (C : CoherentStickyMultiscaleCover D.family)
    (S : FiniteScaleSequence delta depth)
    (epsilon : Real) (hepsilon : 0 ≤ epsilon)
    (eta : Nat → Real) (N : Nat)
    (W : FirstActualNormalizedCrossingWitness
      D hD C S epsilon hepsilon eta N)
    (Y : Shading (bufferedLowerFamily D C S W.m).bodyFamily)
    (hsource :
      (IndexedShadingRefinement.restrictTo Y
        (bufferedIntervalCover
          D hD C S epsilon hepsilon W.m W.rho W.buffered).activeFine).shading.shadingMass ≠ 0) :
    let U := bufferedIntervalCover
      D hD C S epsilon hepsilon W.m W.rho W.buffered
    let T := activeFineRestrictedScaleCover U
    let hscale : S.tau W.m ≤ W.rho :=
      actualDatum_tau_le_of_isBuffered
        D hD S hepsilon W.m W.rho W.buffered
    let YR := activeFineRestrictedShading U Y
    let hsourceR := activeFineRestrictedSourceMass_ne_zero U Y hsource
    let P := (sourceMassCoarseTubePartition
      T hscale YR hsourceR).asConvexFactorization
    ∀ q ∈ P.index.coarse,
      IsFrostmanOn
        ((((W.rho / S.tau W.m : NNReal) : ENNReal) ^ eta W.stage))
        (activeFineRestrictedFamily U).bodyFamily
        (P.index.fiber q) (T.coarse.tubes q).body := by
  dsimp only
  let U := bufferedIntervalCover
    D hD C S epsilon hepsilon W.m W.rho W.buffered
  let T := activeFineRestrictedScaleCover U
  let hscale : S.tau W.m ≤ W.rho :=
    actualDatum_tau_le_of_isBuffered
      D hD S hepsilon W.m W.rho W.buffered
  let YR := activeFineRestrictedShading U Y
  let hsourceR := activeFineRestrictedSourceMass_ne_zero U Y hsource
  let P := (sourceMassCoarseTubePartition
    T hscale YR hsourceR).asConvexFactorization
  intro q _hq
  have hround : P = toConvexFactorization T := by
    exact sourceMass_asConvexFactorization_eq_toConvexFactorization
      T hscale YR hsourceR
  let p : {p // p ∈ U.activeCoarse} :=
    restrictedCoarseEquivActive U q
  have hOriginal := selectedBufferedIntervalCover_fiber_isFrostmanOn
    D hD C S epsilon hepsilon eta N W p.1 p.2
  have hparentBody :
      (T.coarse.tubes q).body = (U.coarse.tubes p.1).body := by
    rfl
  have hOriginalT : IsFrostmanOn
      ((((W.rho / S.tau W.m : NNReal) : ENNReal) ^ eta W.stage))
      (bufferedLowerFamily D C S W.m).bodyFamily
      (U.fiber p.1) (T.coarse.tubes q).body := by
    rw [hparentBody]
    exact hOriginal
  have hRestricted := activeFineRestricted_fiber_isFrostmanOn
    U q (T.coarse.tubes q).body hOriginalT
  change IsFrostmanOn
    ((((W.rho / S.tau W.m : NNReal) : ENNReal) ^ eta W.stage))
    (activeFineRestrictedFamily U).bodyFamily
    (P.index.fiber q) (T.coarse.tubes q).body
  rw [hround]
  simpa only [toConvexFactorization_fiber] using hRestricted

#print axioms activeIndex_sourceMassFactorization_fibers_isFrostmanOn

end FirstActualNormalizedCrossingWitness

end
end Family8Family7FirstCrossingActiveIndexBufferedFiberFrostmanV3
