import Family8Grounding.Family8CanonicalGraphFrozenRawEq66IdentityBridgeV1
import Mathlib.Tactic

/-!
# Same-graph lower bound from the retained Family7 density

The canonical graph certificate stores a density lower bound on the literal
selected graph subtype.  This file converts that retained density to the
average multiplicity of the exact graph stored in the same identity record.

No displayed-coefficient comparison is assumed here.  The resulting source
density quotient is the largest automatic lower bound currently carried by
the graph certificate, so it exposes the precise scalar still needed from
the first-hit/selection layer without reselecting a graph or an assembly.
-/

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8CanonicalGraphFrozenDisplayedGraphLowerProducerV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.HeavyParentSelection
open Submission.Kakeya.Uniformity
open Family8CanonicalGraphFrozenRawEq66IdentityBridgeV1
open Family8Family7FirstCrossingFamilyGraphBucketV12
open Family8Family7FirstCrossingFullCoefficientGraphCertificateV4
open Family8Family7WeightedVerticalGraphCBucketV1
open Family8FrozenComparableActualAverageMassDensityV1.Assembly
open FamilyStickyAtEveryScaleCoreV1

noncomputable section

universe u

/-! ## Generic support-to-average conversion -/

/-- Reindexing a shading to a finite set containing its literal support can
only increase its density up to the original shading's average
multiplicity.  The proof uses the actual selected family volume; no
positivity or cancellation hypothesis is needed. -/
theorem selectedCoarseShading_density_le_averageMultiplicity_of_supported
    {iota : Type u} [Fintype iota] [DecidableEq iota]
    {F : ConvexFamily iota}
    (Z : Shading F) (s : Finset iota)
    (hsupport : forall i, i ∉ s -> Z.carrier i = (∅ : Set Space)) :
    (selectedCoarseShading Z s).shadingDensity <=
      Z.averageMultiplicity := by
  have hmass : (selectedCoarseShading Z s).shadingMass = Z.shadingMass := by
    rw [selectedCoarseShading_mass]
    unfold Shading.shadingMass
    apply Finset.sum_subset (Finset.subset_univ s)
    intro i _hi his
    rw [hsupport i his, measure_empty]
  have hunion : Z.shadedUnion <=
      familyUnion (selectedCoarseFamily F s) := by
    intro x hx
    obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hx
    have hi : i ∈ s := by
      by_contra his
      rw [hsupport i his] at hxi
      exact hxi
    exact Set.mem_iUnion.mpr ⟨⟨i, hi⟩, Z.carrier_subset i hxi⟩
  unfold Shading.shadingDensity Shading.averageMultiplicity
  rw [hmass]
  exact ENNReal.div_le_div_left
    ((measure_mono hunion).trans
      (volume_familyUnion_le (selectedCoarseFamily F s))) _

/-! ## The literal GraphFrozen lower bound -/

variable {tau rho : NNReal} {fineIndex : Type}
  [Fintype fineIndex] [DecidableEq fineIndex]
  {F : UniformTubeFamily tau fineIndex}
  {T : StickyScaleCover F rho}
  {P : ConvexFactorization F.bodyFamily T.coarse.bodyFamily}
  {Y : Shading F.bodyFamily} {fibreCF : ENNReal}

/-- The density quotient retained by the same-assembly Family7 graph
certificate is bounded by the average multiplicity of that exact graph.
This is the strongest automatic source-side lower bound on
`R.graphAverage` available from the current record. -/
theorem sourceDensityQuotient_le_graphAverage
    (R : SameAssemblyFullCoefficientGraphIdentity F T P Y fibreCF) :
    ((sourceActiveFineShading P Y).shadingDensity /
        ((R.A.loss : ENNReal) *
          (P.index.coarse.card : ENNReal))) /
        R.graphLoss <= R.graphAverage := by
  let graph := verticalSourceGraphCBucketFiber ((tau : Real) / 2)
    (firstCrossingFamilyVerticalSource R.axis F P R.k) R.label
  let Z := firstCrossingFamilyGraphBucketShading
    R.axis R.label F P R.A R.k
  let Q := Classical.choice R.graphCertificate
  have hcertificate :
      ((sourceActiveFineShading P Y).shadingDensity /
          ((R.A.loss : ENNReal) *
            (P.index.coarse.card : ENNReal))) /
          R.graphLoss <=
        (selectedCoarseShading Z graph).shadingDensity := by
    simpa only [SameAssemblyFullCoefficientGraphIdentity.graphLoss,
      graph, Z] using Q.graph_density
  have hsupported : forall i, i ∉ graph ->
      Z.carrier i = (∅ : Set Space) := by
    intro i hi
    dsimp only [Z]
    rw [firstCrossingFamilyGraphBucketShading,
      IndexedShadingRefinement.restrictTo_carrier, if_neg hi]
  have hselected : (selectedCoarseShading Z graph).shadingDensity <=
      Z.averageMultiplicity :=
    selectedCoarseShading_density_le_averageMultiplicity_of_supported
      Z graph hsupported
  exact hcertificate.trans (by
    simpa only [SameAssemblyFullCoefficientGraphIdentity.graphAverage,
      Z] using hselected)

#print axioms
  selectedCoarseShading_density_le_averageMultiplicity_of_supported
#print axioms sourceDensityQuotient_le_graphAverage

end
end Family8CanonicalGraphFrozenDisplayedGraphLowerProducerV1
