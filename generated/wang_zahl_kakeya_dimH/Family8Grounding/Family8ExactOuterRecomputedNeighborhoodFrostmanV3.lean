import Family8Grounding.Family8ExactOuterTubeInducedAverageBridgeV6
import Family8Grounding.Family8FiniteRandomRigidMotionB2FreshGreedyV1
import Family8Grounding.Family8FiniteRandomRigidMotionB2FrostmanScaleSupportV2
import Family8Grounding.Family8RecomputedNeighborhoodActualTubeDatumV2

/-!
# Exact outer Frostman bound at an arbitrary assembly radius, V3

V1 is frozen and V2 is the radius-matched form.  This clean successor uses
the generalized factor-432 bridge, so the assembly's auxiliary real radius
is arbitrary while the recomputed neighborhood remains at the literal
coarse tube radius `rho`.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

open Set MeasureTheory
open scoped ENNReal NNReal

namespace Family8ExactOuterRecomputedNeighborhoodFrostmanV3

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8ExactOuterTubeInducedAverageBridgeV6
open Family8FiniteRandomRigidMotionB2FreshGreedyV1
open Family8FiniteRandomRigidMotionB2FrostmanScaleSupportV2
open Family8FiniteRandomRigidMotionB2NormalizedDatumV1
open Family8FrozenNeighborhoodAssemblyV1
open Family8GeneralizedKatzTaoMultiplicityV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8RecomputedNeighborhoodActualTubeDatumV2

noncomputable section

variable {delta rho : NNReal} {iota kappa : Type}
  [Fintype iota] [Fintype kappa] [Nonempty kappa]
  [DecidableEq iota] [DecidableEq kappa]
  {fine : UniformTubeFamily delta iota}
  {coarse : UniformTubeFamily rho kappa}

/-- A Frostman selection on the literal recomputed neighborhood controls
the exact frozen outer average independently of the assembly radius. -/
theorem exists_selected_frozenCoarse_average_le_432_mul_normalizedFrostmanRHS
    {beta epsilon eta : Real} {delta0 : NNReal}
    (hF : FrostmanAtParameters beta epsilon eta delta0)
    (P : CoarseTubePartition fine coarse)
    (Y : Shading fine.bodyFamily) {r : Real}
    (A : Family8FrozenNeighborhoodAssemblyV1.Assembly
      P.asConvexFactorization Y r)
    (hrhoPos : 0 < rho)
    (hrhoHalf : rho <= (2 : NNReal)⁻¹)
    (hmass : A.refinement.shading.shadingMass ≠ 0)
    (hfrozen : A.frozenCoarse =
      P.asConvexFactorization.inducedShading A.refinement.shading)
    (hB2 : ∀ k : kappa,
      (coarse.tubes k).carrier ⊆ Metric.closedBall (0 : Space) 2)
    {conflictThreshold : Nat}
    (hconflict : ∀ k : kappa,
      (normalizedConflictIndices
        (recomputedNeighborhoodActualTubeDatum P A.refinement.shading)
        k).card <= conflictThreshold)
    {C : ENNReal}
    (hKT : IsKatzTao C coarse.bodyFamily)
    (hdelta0 : rho / 8 <= delta0)
    (hdensityBudget :
      ((rho / 8 : NNReal) : ENNReal) ^ eta <=
        (eighthNormalizedDatum
          (recomputedNeighborhoodActualTubeDatum
            P A.refinement.shading)).shading.shadingDensity /
          (conflictThreshold + 1 : Nat))
    (hbaseBudget :
      (conflictThreshold + 1 : Nat) *
          ((128 * C) * volume (unitBallBody : Set Space)) <=
        ((rho / 8 : NNReal) : ENNReal) ^ (-eta) *
          ((Fintype.card kappa : ENNReal) *
            (((rho / 8 : NNReal) : ENNReal) ^ 2 / 2))) :
    ∃ selected : Finset kappa,
      selected.Nonempty ∧
      A.frozenCoarse.averageMultiplicity <=
        432 *
          ((conflictThreshold + 1 : Nat) *
            frostmanMultiplicityRHS (rho / 8)
              (restrictActualTubeDatum
                (eighthNormalizedDatum
                  (recomputedNeighborhoodActualTubeDatum
                    P A.refinement.shading))
                selected).actualFamilyVolume epsilon beta) := by
  obtain ⟨selected, hselected, hneighborhood⟩ :=
    exists_normalized_source_averageMultiplicity_le_frostmanRHS_of_scale_support
      hF (recomputedNeighborhoodActualTubeDatum P A.refinement.shading)
      hrhoPos hrhoHalf
      (recomputedNeighborhoodActualTubeDatum_B2
        P A.refinement.shading hB2)
      hconflict
      (recomputedNeighborhoodActualTubeDatum_isKatzTao
        P A.refinement.shading hKT)
      hdelta0 hdensityBudget hbaseBudget
  refine ⟨selected, hselected, ?_⟩
  have houter :=
    frozenCoarse_averageMultiplicity_le_432_mul_neighborhood
      P Y A hrhoPos hmass hfrozen
  calc
    A.frozenCoarse.averageMultiplicity <=
        432 *
          (P.asConvexFactorization.neighborhoodInducedShading
            A.refinement.shading (rho : Real)).averageMultiplicity :=
      houter
    _ <= 432 *
        ((conflictThreshold + 1 : Nat) *
          frostmanMultiplicityRHS (rho / 8)
            (restrictActualTubeDatum
              (eighthNormalizedDatum
                (recomputedNeighborhoodActualTubeDatum
                  P A.refinement.shading))
              selected).actualFamilyVolume epsilon beta) := by
      exact mul_le_mul' le_rfl hneighborhood

#print axioms
  exists_selected_frozenCoarse_average_le_432_mul_normalizedFrostmanRHS

end
end Family8ExactOuterRecomputedNeighborhoodFrostmanV3
