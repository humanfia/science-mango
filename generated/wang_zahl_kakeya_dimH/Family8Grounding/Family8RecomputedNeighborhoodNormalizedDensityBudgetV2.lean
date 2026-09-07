import Family8Grounding.Family8ActiveSourceMassExactAssemblyNeighborhoodDensityV6
import Family8Grounding.Family8EighthNormalizationSelectionDensityBudgetAlgebraV1
import Family8Grounding.Family8FrozenCoarseB2DensityTransportScaleOnlyV1
import Family8Grounding.Family8RecomputedNeighborhoodActualTubeDatumV2

/-!
# Normalized density budget for the recomputed neighborhood, V2

V1 is a frozen namespace-owner draft.  This successor directly opens the
owner of Shading.  The exact-assembly relative-square lower bound is
transported to the literal recomputed datum and through eighth normalization.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

open scoped ENNReal NNReal

namespace Family8RecomputedNeighborhoodNormalizedDensityBudgetV2

open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8ActiveSourceMassExactAssemblyNeighborhoodDensityV6
open Family8EighthNormalizationSelectionDensityBudgetAlgebraV1
open Family8FiniteRandomRigidMotionB2NormalizedDatumV1
open Family8FrozenCoarseB2DensityTransportScaleOnlyV1
open Family8RecomputedNeighborhoodActualTubeDatumV2

noncomputable section

variable {delta rho : NNReal} {iota kappa : Type}
  [Fintype iota] [Fintype kappa] [Nonempty kappa]
  [DecidableEq iota] [DecidableEq kappa]
  {fine : UniformTubeFamily delta iota}
  {coarse : UniformTubeFamily rho kappa}

/-- A scalar lower bound on the exact source-density square produces the
density premise of the fresh normalized Frostman selector on the same
recomputed neighborhood datum. -/
theorem eighthNormalized_recomputedNeighborhood_densityBudget
    (P : CoarseTubePartition fine coarse)
    (Y : Shading fine.bodyFamily) {r : Real}
    (A : Family8FrozenNeighborhoodAssemblyV1.Assembly
      P.asConvexFactorization Y r)
    (hfine : P.fineIndices = Finset.univ)
    (hcoarse : P.coarseIndices = Finset.univ)
    (hdelta : 0 < delta) (hrho : 0 < rho)
    (hrhoHalf : rho ≤ (2 : NNReal)⁻¹)
    {eta : Real} {selectionLoss : ENNReal}
    (hloss0 : selectionLoss ≠ 0)
    (hlossTop : selectionLoss ≠ ∞)
    (hscalar :
      ((rho / 8 : NNReal) : ENNReal) ^ eta *
          (128 * selectionLoss) ≤
        Y.shadingDensity ^ 2 /
          ((A.loss : ENNReal) *
            (768 * (P.branchingLoss : ENNReal) ^ 2))) :
    ((rho / 8 : NNReal) : ENNReal) ^ eta ≤
      (eighthNormalizedDatum
        (recomputedNeighborhoodActualTubeDatum
          P A.refinement.shading)).shading.shadingDensity /
        selectionLoss := by
  let D := recomputedNeighborhoodActualTubeDatum
    P A.refinement.shading
  let lower :=
    Y.shadingDensity ^ 2 /
      ((A.loss : ENNReal) *
        (768 * (P.branchingLoss : ENNReal) ^ 2))
  have hlowerNeighborhood : lower ≤
      (P.asConvexFactorization.neighborhoodInducedShading
        A.refinement.shading (rho : Real)).shadingDensity := by
    simpa only [lower] using
      (assembly_sourceDensity_sq_div_loss_mul_768_branchingLoss_sq_le
        P Y A hfine hcoarse hdelta hrho hrhoHalf)
  have hlowerDatum : lower ≤ D.shading.shadingDensity := by
    exact recomputedNeighborhoodActualTubeDatum_density_lower
      P A.refinement.shading hlowerNeighborhood
  have hnormalized :
      D.shading.shadingDensity / 128 ≤
        (eighthNormalizedDatum D).shading.shadingDensity :=
    source_shadingDensity_div_128_le_eighthNormalized_of_scale
      D hrho hrhoHalf
  exact target_le_normalized_div_loss_of_mul_128_loss_le_lower
    (((rho / 8 : NNReal) : ENNReal) ^ eta)
    D.shading.shadingDensity
    (eighthNormalizedDatum D).shading.shadingDensity
    lower selectionLoss hloss0 hlossTop hlowerDatum hnormalized
    (by simpa only [lower] using hscalar)

#print axioms eighthNormalized_recomputedNeighborhood_densityBudget

end
end Family8RecomputedNeighborhoodNormalizedDensityBudgetV2
