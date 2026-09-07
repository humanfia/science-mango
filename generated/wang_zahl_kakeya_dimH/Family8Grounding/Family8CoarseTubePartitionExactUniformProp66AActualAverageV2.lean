import Family8Grounding.Family8JointTubeFactoringExactUniformProp66AProductV4
import Family8Grounding.Family8Prop66AActualAverageCompositionV2

/-!
# Actual-average Proposition 6.6(A) on an exact-uniform tube partition, V2

Both analytic multiplicity bounds refer to the same `CoarseTubePartition`
and `ExactAssembly`. Branching loss one supplies the exact outer-count times
inner-count identity, so no abstract count equality is requested.

V1 is a failed namespace draft and is not imported.
-/

open Set MeasureTheory
open scoped ENNReal NNReal

namespace Family8CoarseTubePartitionExactUniformProp66AActualAverageV2

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FactoringMultiplicityAssembly
open Submission.Kakeya.Uniformity
open Family8ExactAssemblyActualAverageBridgeV1
open Family8ExactAssemblyActualAverageBridgeV1.ExactAssembly
open Family8Prop66AFrostmanAspectGainAlgebraV1
open Family8Prop66AOuterInnerProductAlgebraV1
open Family8JointTubeFactoringExactUniformProp66AProductV4

noncomputable section

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false

variable {delta rho : NNReal} {iota kappa : Type*}
  [Fintype iota] [Fintype kappa]
  [DecidableEq iota] [DecidableEq kappa]
  {fine : UniformTubeFamily delta iota}
  {coarse : UniformTubeFamily rho kappa}
  {Y : Shading fine.bodyFamily} {loss : Nat}

/-- The actual outer and inner average-multiplicity estimates on one literal
exact-uniform tube partition compose with no separate count callback. -/
theorem refinement_averageMultiplicity_le_exactUniform_proposition66AFrostmanFactor
    (P : CoarseTubePartition fine coarse)
    (A : FactoringMultiplicityAssembly.ExactAssembly
      P.asConvexFactorization Y loss)
    (hloss : P.branchingLoss = 1)
    (hsource :
      (IndexedShadingRefinement.restrictTo Y
        P.asConvexFactorization.index.fine).shading.shadingMass ≠ 0)
    {a b : NNReal} {CF : ENNReal} {epsilon beta : Real}
    (hdelta : 0 < delta) (ha : 0 < a) (hb : 0 < b)
    (hbeta : 0 ≤ beta) (hbetaOne : beta ≤ 1)
    (houter :
      (P.asConvexFactorization.inducedShading
        A.refinement.shading).averageMultiplicity ≤
          proposition66AOuterFactor delta a b P.coarseIndices.card
            CF epsilon beta)
    (hinner : ∀ k, k ∈ P.asConvexFactorization.index.coarse →
      (sourceFineLevelShading A k).averageMultiplicity ≤
        proposition66AInnerFactor delta a b P.branching epsilon beta) :
    A.refinement.shading.averageMultiplicity ≤
      proposition66AFrostmanFactor delta a b P.fineIndices.card
        CF epsilon beta := by
  exact
    Family8Prop66AActualAverageCompositionV2.ExactAssembly.refinement_averageMultiplicity_le_proposition66AFrostmanFactor
      A hsource hdelta ha hb hbeta hbetaOne
      (fineIndices_card_eq_coarseIndices_card_mul_branching_of_branchingLoss_eq_one
        P hloss)
      houter hinner

#print axioms
  refinement_averageMultiplicity_le_exactUniform_proposition66AFrostmanFactor

end
end Family8CoarseTubePartitionExactUniformProp66AActualAverageV2
