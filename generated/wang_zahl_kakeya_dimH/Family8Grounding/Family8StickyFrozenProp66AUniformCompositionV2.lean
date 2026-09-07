import Family8Grounding.Family8FrozenProp66AActualAverageCompositionV2
import Family8Grounding.Family8StickyUniformCountLossV2
import Family8Grounding.Family8StickyScaleCoverFrozenComparableAdapterV2
import Mathlib.Tactic

/-!
# Literal Sticky uniformity feeds the frozen Proposition 6.6(A) endpoint

The surviving fibre is chosen from the actual frozen assembly. Its literal
Sticky fibre cardinality is then used as the inner tube count, while the
literal number of active parents is used as the outer plank count. Therefore
`IsCUniform S C` supplies the count comparison automatically and the final
loss is exactly `C^(1 - beta/2)`.

V1 is a failed namespace/unfolding draft and is not imported.
-/

open Set MeasureTheory
open scoped ENNReal NNReal

namespace Family8StickyFrozenProp66AUniformCompositionV2

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Family8KatzTaoFrostmanPropertiesV1
open FamilyStickyAtEveryScaleCoreV1
open Family8Def212ConvexWolffAtEveryScaleV2.ScaleCover
open Family8StickyScaleCoverFrozenComparableAdapterV2
open Family8FrozenComparableActualAverageMassDensityV1
open Family8Prop66AFrostmanAspectGainAlgebraV1
open Family8Prop66AOuterInnerProductAlgebraV1
open Family8StickyUniformCountLossV2

noncomputable section

set_option autoImplicit false
set_option warningAsError true

variable {delta rho : NNReal} {iota : Type}
  [Fintype iota] [DecidableEq iota]

/-- On one literal Sticky cover, actual fibre uniformity discharges the
cardinality premise of the frozen Proposition 6.6(A) composition. -/
theorem exists_survivingFiber_actualRefinement_le_of_stickyUniform
    (D : ActualTubeDatum delta iota)
    (S : StickyScaleCover D.family rho) (hscale : delta ≤ rho)
    (r : Real)
    (hsource :
      (IndexedShadingRefinement.restrictTo D.shading
        S.activeFine).shading.shadingMass ≠ 0)
    (A : Family8FrozenNeighborhoodAssemblyV1.Assembly
      (sourceMassCoarseTubePartition S hscale D.shading hsource).asConvexFactorization
        D.shading r)
    {C : ENNReal} (huniform : IsCUniform S C)
    {a b : NNReal} {CF : ENNReal} {epsilon beta : Real}
    (hD : D.IsAdmissible) (ha : 0 < a) (hb : 0 < b)
    (hbeta : 0 ≤ beta) (hbetaOne : beta ≤ 1)
    (houter : A.frozenCoarse.averageMultiplicity ≤
      proposition66AOuterFactor delta a b S.activeCoarse.card CF epsilon beta)
    (hinner : ∀ k, k ∈ S.activeCoarse →
      (Assembly.finalFiberShading A k).averageMultiplicity ≤
        proposition66AInnerFactor delta a b (S.fiber k).card epsilon beta) :
    ∃ k ∈ S.activeCoarse,
      0 < volume (Assembly.finalFiberShading A k).shadedUnion ∧
      (Assembly.actualRefinementShading A).averageMultiplicity ≤
        4 * (C ^ (1 - beta / 2) *
          ((proposition66AFrostmanAspectGain a b CF beta *
              (2 : ENNReal) ^ (1 - beta / 2)) *
            frostmanMultiplicityRHS delta D.actualFamilyVolume epsilon beta)) := by
  have hsourceP :
      (IndexedShadingRefinement.restrictTo D.shading
        (sourceMassCoarseTubePartition S hscale D.shading hsource).index.fine).shading.shadingMass
          ≠ 0 := by
    change
      (IndexedShadingRefinement.restrictTo D.shading
        (sourceMassCoarseTubePartition S hscale D.shading hsource).fineIndices).shading.shadingMass
          ≠ 0
    simpa only [sourceMassCoarseTubePartition_fineIndices] using hsource
  obtain ⟨k, hk, hfiber, _hrefinement, houterVolume⟩ :=
    Assembly.exists_positive_finalFiber A hsourceP
  have hkS : k ∈ S.activeCoarse := by
    change k ∈
      (sourceMassCoarseTubePartition S hscale D.shading hsource).coarseIndices at hk
    simpa only [sourceMassCoarseTubePartition_coarseIndices] using hk
  have hcount :
      (((S.activeCoarse.card * (S.fiber k).card : Nat) : ENNReal)) ≤
        C * (Fintype.card iota : ENNReal) :=
    activeCoarse_card_mul_fiber_card_le_uniformity_mul_total_card
      S huniform k hkS
  refine ⟨k, hkS, hfiber, ?_⟩
  exact
    Family8FrozenProp66AActualAverageCompositionV2.Assembly.actualRefinement_averageMultiplicity_le_uniformCountLoss_mul_actualFrostmanRHS
      A k hk (ne_of_gt hfiber) (ne_of_gt houterVolume)
        hD ha hb hbeta hbetaOne hcount houter (hinner k hkS)

#print axioms
  exists_survivingFiber_actualRefinement_le_of_stickyUniform

end
end Family8StickyFrozenProp66AUniformCompositionV2
