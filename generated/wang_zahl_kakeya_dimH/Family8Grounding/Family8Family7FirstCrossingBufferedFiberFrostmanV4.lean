import Family8Grounding.Family8FirstActualCrossingNormalizedFrostmanV2
import Family8Grounding.Family8NormalizedLongIntervalFrostmanInheritanceV1
import Family8Grounding.Family8StickyScaleCoverFrozenComparableAdapterV2
import Family8Grounding.Family8StickySourceMassFactorizationRoundTripV1

/-!
# Literal fibre Frostman certificates at the first normalized crossing, V4

V3 is frozen after its second theorem unfolded the local factorization before
two rewrites.  This ADD-only successor folds the hypotheses and goal back to
the named local `P`; the cover, fibre, parent, and certificate are unchanged.
-/

set_option autoImplicit false
set_option warningAsError true

open Set MeasureTheory
open scoped ENNReal NNReal

namespace Family8Family7FirstCrossingBufferedFiberFrostmanV4

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8FirstActualCrossingNormalizedFrostmanV2
open Family8FirstActualCrossingNormalizedFrostmanV2.FirstActualNormalizedCrossingWitness
open Family8KatzTaoFrostmanPropertiesV1
open Family8NormalizedCFDividingWitnessFiniteSelectionV4.CoherentStickyMultiscaleCover
open Family8NormalizedCrossingFrozenComparableAdapterV3
open Family8NormalizedFirstCrossingFullRefinementAssemblyV1
open Family8NormalizedLongIntervalFrostmanInheritanceV1
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

/-- Every active fibre of the literal selected buffered cover has the exact
at-scale Frostman constant stored by the first-crossing witness. -/
theorem selectedBufferedIntervalCover_fiber_isFrostmanOn
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (C : CoherentStickyMultiscaleCover D.family)
    (S : FiniteScaleSequence delta depth)
    (epsilon : Real) (hepsilon : 0 ≤ epsilon)
    (eta : Nat → Real) (N : Nat)
    (W : FirstActualNormalizedCrossingWitness
      D hD C S epsilon hepsilon eta N)
    (k : Fin (bufferedIntervalCover
      D hD C S epsilon hepsilon W.m W.rho W.buffered).coarseCard)
    (hk : k ∈ (bufferedIntervalCover
      D hD C S epsilon hepsilon W.m W.rho W.buffered).activeCoarse) :
    IsFrostmanOn
      ((((W.rho / S.tau W.m : NNReal) : ENNReal) ^ eta W.stage))
      (bufferedLowerFamily D C S W.m).bodyFamily
      ((bufferedIntervalCover
        D hD C S epsilon hepsilon W.m W.rho W.buffered).fiber k)
      ((bufferedIntervalCover
        D hD C S epsilon hepsilon W.m W.rho W.buffered).coarse.tubes k).body := by
  let U := bufferedIntervalCover
    D hD C S epsilon hepsilon W.m W.rho W.buffered
  have hAt := selectedBufferedIntervalCover_isFrostmanAtScale
    D hD C S epsilon hepsilon eta N W
  have hIn : IsFrostmanIn
      ((((W.rho / S.tau W.m : NNReal) : ENNReal) ^ eta W.stage))
      (U.fiberFamily k) (U.coarse.tubes k).body := by
    apply isFrostmanIn_iff_concentration_le.mpr
    exact ⟨U.fiber_carrier_subset_parent k, hAt k hk⟩
  exact
    (isFrostmanOn_iff_isFrostmanIn_activeSubtypeFamily
      (bufferedLowerFamily D C S W.m).bodyFamily
      (U.fiber k) (U.coarse.tubes k).body).mpr hIn

/-- The same fibre certificate, rewritten onto the exact source-mass
factorization used by the frozen assembly. -/
theorem selectedBufferedIntervalCover_sourceMassFactorization_fibers_isFrostmanOn
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
    let hscale : S.tau W.m ≤ W.rho :=
      actualDatum_tau_le_of_isBuffered
        D hD S hepsilon W.m W.rho W.buffered
    let P := (sourceMassCoarseTubePartition U hscale Y hsource).asConvexFactorization
    ∀ k ∈ P.index.coarse,
      IsFrostmanOn
        ((((W.rho / S.tau W.m : NNReal) : ENNReal) ^ eta W.stage))
        (bufferedLowerFamily D C S W.m).bodyFamily
        (P.index.fiber k) (U.coarse.tubes k).body := by
  dsimp only
  let U := bufferedIntervalCover
    D hD C S epsilon hepsilon W.m W.rho W.buffered
  let hscale : S.tau W.m ≤ W.rho :=
    actualDatum_tau_le_of_isBuffered
      D hD S hepsilon W.m W.rho W.buffered
  let P := (sourceMassCoarseTubePartition U hscale Y hsource).asConvexFactorization
  intro k hk
  change k ∈ P.index.coarse at hk
  have hround : P = toConvexFactorization U := by
    exact sourceMass_asConvexFactorization_eq_toConvexFactorization
      U hscale Y hsource
  have hkU : k ∈ U.activeCoarse := by
    rw [hround] at hk
    simpa only [toConvexFactorization_coarse] using hk
  have hF := selectedBufferedIntervalCover_fiber_isFrostmanOn
    D hD C S epsilon hepsilon eta N W k hkU
  change IsFrostmanOn
    ((((W.rho / S.tau W.m : NNReal) : ENNReal) ^ eta W.stage))
    (bufferedLowerFamily D C S W.m).bodyFamily
    (P.index.fiber k) (U.coarse.tubes k).body
  rw [hround]
  simpa only [toConvexFactorization_fiber] using hF

#print axioms selectedBufferedIntervalCover_fiber_isFrostmanOn
#print axioms
  selectedBufferedIntervalCover_sourceMassFactorization_fibers_isFrostmanOn

end FirstActualNormalizedCrossingWitness

end
end Family8Family7FirstCrossingBufferedFiberFrostmanV4
