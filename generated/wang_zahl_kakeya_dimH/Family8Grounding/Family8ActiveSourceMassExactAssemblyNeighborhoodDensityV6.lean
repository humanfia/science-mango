import Family8Grounding.Family8FrozenComparableActualAverageMassDensityV1
import Family8Grounding.Family8StickyActiveIndexFrozenComparableAssemblyV5
import Family8Grounding.Family8TubeFiberRelativeSquareCoveringGrowthV3
import Family8Grounding.Family8TubeRelativeSquareInducedDensityNormalizationV3
import Submission.Kakeya.ConvexFactoring.InducedShadingDensityAlgebra

/-!
# Relative-square neighborhood density for an exact assembly, V6

V1--V3 and malformed V5 are frozen drafts.  V4 is the SAFE fixed-radius
core; this successor keeps
the exact `768 * branchingLoss^2` calculation at the universe used by the
Family7 actual data.  The proof-dependent active source-mass wrapper is
deliberately separated from this generic theorem.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000
set_option linter.unusedSectionVars false

open Set MeasureTheory
open scoped ENNReal NNReal

namespace Family8ActiveSourceMassExactAssemblyNeighborhoodDensityV6

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.InducedShadingDensityAlgebra
open Submission.Kakeya.Uniformity
open Family8FrozenNeighborhoodAssemblyV1
open Family8TubeFiberRelativeSquareCoveringGrowthV3
open Family8TubeRelativeSquareInducedDensityNormalizationV3

noncomputable section

variable {delta rho : NNReal} {iota kappa : Type}
  [Fintype iota] [Fintype kappa]
  [DecidableEq iota] [DecidableEq kappa]
  {fine : UniformTubeFamily delta iota}
  {coarse : UniformTubeFamily rho kappa}

/-- Full fine/coarse index sets, assembly retention, and literal tube-fibre
growth imply the exact recomputed-neighborhood density lower bound. -/
theorem assembly_sourceDensity_sq_div_loss_mul_768_branchingLoss_sq_le
    (P : CoarseTubePartition fine coarse)
    (Y : Shading fine.bodyFamily)
    {r : Real}
    (A : Family8FrozenNeighborhoodAssemblyV1.Assembly
      P.asConvexFactorization Y r)
    (hfine : P.fineIndices = Finset.univ)
    (hcoarse : P.coarseIndices = Finset.univ)
    (hdelta : 0 < delta) (hrho : 0 < rho)
    (hrhoHalf : rho <= (2 : NNReal)⁻¹) :
    Y.shadingDensity ^ 2 /
        ((A.loss : ENNReal) *
          (768 * (P.branchingLoss : ENNReal) ^ 2)) <=
      (P.asConvexFactorization.neighborhoodInducedShading
        A.refinement.shading (rho : Real)).shadingDensity := by
  have hretained : WithinFactor A.loss
      Y.shadingMass A.refinement.shading.shadingMass := by
    have h := A.retained
    change WithinFactor A.loss
      (IndexedShadingRefinement.restrictTo Y
        P.fineIndices).shading.shadingMass
      A.refinement.shading.shadingMass at h
    simpa only [hfine,
      Family8StickyActiveIndexFrozenComparableAssemblyV5.restrictTo_univ_shadingMass]
      using h
  have hgrowthRaw :=
    hasFiberCoveringGrowth_of_partition_branching
      P A.refinement.shading hdelta hrho
  have hgrowth :
      Submission.Kakeya.ConvexFactoring.InducedShadingDensityAlgebra.HasFiberCoveringGrowth
        P.asConvexFactorization A.refinement.shading (rho : Real)
        ((rho : ENNReal) ^ 2)
        ((((P.branchingLoss * P.branching : Nat) : ENNReal) * 48) *
          (delta : ENNReal) ^ 2) := by
    simpa only [tubeFiberRelativeSquareGrowth] using hgrowthRaw
  exact sourceDensity_sq_div_loss_mul_768_branchingLoss_sq_le
    P Y A.refinement A.loss hfine hcoarse hretained hgrowth
      hdelta hrho hrhoHalf

#print axioms
  assembly_sourceDensity_sq_div_loss_mul_768_branchingLoss_sq_le

end
end Family8ActiveSourceMassExactAssemblyNeighborhoodDensityV6
