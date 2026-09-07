import Family8Grounding.Family8CoreNativeFrozenThirdBundleV1
import Family8Grounding.Family8EighthNormalizedSelectedFrostmanThirdFactorV3
import Family8Grounding.Family8ExactOuterRecomputedNeighborhoodFrostmanV3
import Family8Grounding.Family8FiniteRandomRigidMotionB2FreshGreedyV1
import Family8Grounding.Family8ThreeScaleFrostmanFactorAlgebraV2
import Mathlib.Tactic

/-!
# Core-native third bundle from the exact recomputed neighborhood, V2

V1 is a frozen symbol-visibility draft.  This clean successor keeps the
same selected subtype and imports the authoritative Section-8 factor owner
directly.  Its total loss remains exactly
`432 * (conflictThreshold + 1)`.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

open Set MeasureTheory
open scoped ENNReal NNReal

namespace Family8ExactOuterRecomputedNeighborhoodCoreNativeThirdBundleV2

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8CoreNativeFrozenThirdBundleV1
open Family8EighthNormalizedSelectedFrostmanThirdFactorV3
open Family8ExactOuterRecomputedNeighborhoodFrostmanV3
open Family8FiniteRandomRigidMotionB2FreshGreedyV1
open Family8FiniteRandomRigidMotionB2NormalizedDatumV1
open Family8FrozenNeighborhoodAssemblyV1
open Family8GeneralizedKatzTaoMultiplicityV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8RecomputedNeighborhoodActualTubeDatumV2
open Family8ThreeScaleFrostmanFactorAlgebraV2

noncomputable section

variable {delta rho : NNReal} {iota kappa : Type}
  [Fintype iota] [Fintype kappa] [Nonempty kappa]
  [DecidableEq iota] [DecidableEq kappa]
  {fine : UniformTubeFamily delta iota}
  {coarse : UniformTubeFamily rho kappa}

/-- The selected subtype produced by the recomputed-neighborhood Frostman
composite is the selected field of a literal Core-native third bundle. -/
theorem nonempty_exactOuter_recomputedNeighborhood_coreNativeThirdBundle
    {beta epsilon eta : Real} {delta0 : NNReal}
    (hF : FrostmanAtParameters beta epsilon eta delta0)
    (hbetaTwo : beta <= 2)
    (P : CoarseTubePartition fine coarse)
    (Y : Shading fine.bodyFamily)
    (A : Family8FrozenNeighborhoodAssemblyV1.Assembly
      P.asConvexFactorization Y 1)
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
    Nonempty
      (CoreNativeFrozenThirdBundle P.asConvexFactorization Y A rho
        (eighthSelectedThirdFactorLoss rho
          ((432 : ENNReal) *
            ((conflictThreshold + 1 : Nat) : ENNReal)) epsilon beta)
        beta) := by
  obtain ⟨selected, hselected, haverage⟩ :=
    exists_selected_frozenCoarse_average_le_432_mul_normalizedFrostmanRHS
      hF P Y A hrhoPos hrhoHalf hmass hfrozen hB2 hconflict hKT
      hdelta0 hdensityBudget hbaseBudget
  have htransport :=
    loss_mul_selectedRHS_le_eighthLoss_mul_thirdFactor
      (eighthNormalizedDatum
        (recomputedNeighborhoodActualTubeDatum P A.refinement.shading))
      selected
      (loss := (432 : ENNReal) *
        ((conflictThreshold + 1 : Nat) : ENNReal))
      (epsilon := epsilon) (gamma := beta)
      hrhoPos hrhoHalf hbetaTwo
  refine Nonempty.intro
    { selected := selected
      selected_nonempty := hselected
      bound := ?_ }
  calc
    A.frozenCoarse.averageMultiplicity <=
        432 *
          ((conflictThreshold + 1 : Nat) *
            frostmanMultiplicityRHS (rho / 8)
              (restrictActualTubeDatum
                (eighthNormalizedDatum
                  (recomputedNeighborhoodActualTubeDatum
                    P A.refinement.shading))
                selected).actualFamilyVolume epsilon beta) :=
      haverage
    _ = ((432 : ENNReal) *
          ((conflictThreshold + 1 : Nat) : ENNReal)) *
        frostmanMultiplicityRHS (rho / 8)
          (restrictActualTubeDatum
            (eighthNormalizedDatum
              (recomputedNeighborhoodActualTubeDatum
                P A.refinement.shading))
            selected).actualFamilyVolume epsilon beta := by
      ac_rfl
    _ <= eighthSelectedThirdFactorLoss rho
          ((432 : ENNReal) *
            ((conflictThreshold + 1 : Nat) : ENNReal)) epsilon beta *
        sectionEightScaleCountFrostmanFactor
          rho 1 (Fintype.card kappa) beta :=
      htransport

#print axioms
  nonempty_exactOuter_recomputedNeighborhood_coreNativeThirdBundle

end
end Family8ExactOuterRecomputedNeighborhoodCoreNativeThirdBundleV2
