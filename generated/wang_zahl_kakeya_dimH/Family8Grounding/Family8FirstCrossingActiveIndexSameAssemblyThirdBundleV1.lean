import Family8Grounding.Family8CoreNativeFrozenThirdBundleV1
import Family8Grounding.Family8FiniteRandomRigidMotionB2FreshGreedyV1
import Family8Grounding.Family8ParentAggregatedShadingActiveCoarseXUpperV3
import Family8Grounding.Family8EighthNormalizedSelectedFrostmanThirdFactorV3
import Family8Grounding.Family8StickyActiveFrozenCoarseSourceMassFrostmanEndpointV2
import Mathlib.Tactic

/-!
# Same-assembly active-index third bundle for FirstCrossing

This structural connector is independent of the particular FirstCrossing
graph selection.  It applies the native active frozen-coarse selector to the
very same source-mass assembly, then converts its eighth-normalized Frostman
RHS into the official `rho -> 1` Section-8 third factor.  Only the genuine
density/base scalar budgets remain as hypotheses.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8FirstCrossingActiveIndexSameAssemblyThirdBundleV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8CoreNativeFrozenThirdBundleV1
open Family8EighthNormalizedSelectedFrostmanThirdFactorV3
open Family8FiniteRandomRigidMotionB2NormalizedDatumV1
open Family8FiniteRandomRigidMotionB2FreshGreedyV1
open Family8FrozenCoarseB2FrostmanActualDatumV1
open Family8FrozenComparableActualAverageMassDensityV1.Assembly
open Family8GeneralizedKatzTaoMultiplicityV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8ParentAggregatedShadingActiveCoarseXUpperV3.StickyScaleCover
open Family8StickyActiveFrozenCoarseSourceMassFrostmanEndpointV2
open Family8StickyScaleCoverActiveFineRestrictionV2.ScaleCover
open FamilyStickyAtEveryScaleCoreV1

noncomputable section

variable {delta rho : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]

/-- The same active-index assembly carries a Core-native third bundle with
the explicit eighth-normalization loss. -/
theorem nonempty_activeIndex_sameAssembly_coreNativeThirdBundle
    {beta epsilon eta : Real} {delta0 : NNReal}
    (hF : FrostmanAtParameters beta epsilon eta delta0)
    (hbetaTwo : beta ≤ 2)
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (S : StickyScaleCover D.family rho)
    (hrho : rho ≤ (1 / 16 : NNReal))
    (P : CoarseTubePartition
      (activeFineRestrictedFamily S)
      (activeFineRestrictedScaleCover S).coarse)
    (Y : Shading (activeFineRestrictedFamily S).bodyFamily)
    (A : Family8FrozenNeighborhoodAssemblyV1.Assembly
      P.asConvexFactorization Y 1)
    {conflictThreshold : Nat}
    (hconflict : ∀ k,
      (normalizedConflictIndices (frozenCoarseActualDatum P Y A) k).card ≤
        conflictThreshold)
    {C : ENNReal} (hKT : S.IsKatzTaoAtScale C)
    (hdelta0 : rho / 8 ≤ delta0)
    {sourceFloor baseFloor : ENNReal}
    (hsource0 :
      (sourceActiveFineShading P.asConvexFactorization Y).shadingMass ≠ 0)
    (hsourceLower : sourceFloor ≤
      (sourceActiveFineShading P.asConvexFactorization Y).shadingMass)
    (hdensityScalar :
      ((((rho / 8 : NNReal) : ENNReal) ^ eta *
            ((conflictThreshold + 1 : Nat) : ENNReal)) * 128) *
          (((A.loss : ENNReal) *
              ((P.branchingLoss * P.branching : Nat) : ENNReal)) *
            (8 * (1024 * C))) ≤ sourceFloor)
    (hbaseLower :
      baseFloor ≤ (activeCoarseCardScaleMass S : ENNReal))
    (hbaseScalar :
      ((conflictThreshold + 1 : Nat) : ENNReal) *
          ((128 * C) * volume (unitBallBody : Set Space)) ≤
        ((rho / 8 : NNReal) : ENNReal) ^ (-eta) *
          (baseFloor / 128)) :
    Nonempty (CoreNativeFrozenThirdBundle P.asConvexFactorization Y A rho
      (eighthSelectedThirdFactorLoss rho
        ((conflictThreshold + 1 : Nat) : ENNReal) epsilon beta)
      beta) := by
  have hrhoPos : 0 < rho := hD.delta_pos.trans_le P.scale_le
  have hsixteenHalf : (1 / 16 : NNReal) ≤ (2 : NNReal)⁻¹ := by
    change (1 : Real) / 16 ≤ (2 : Real)⁻¹
    norm_num
  have hrhoHalf : rho ≤ (2 : NNReal)⁻¹ := hrho.trans hsixteenHalf
  obtain ⟨selected, hselected, haverage⟩ :=
    exists_normalized_activeFrozenCoarse_of_sourceMass_cardScaleMass
      hF D hD S hrho P Y A hconflict hKT hdelta0
        hsource0 hsourceLower hdensityScalar hbaseLower hbaseScalar
  have htransport :=
    loss_mul_selectedRHS_le_eighthLoss_mul_thirdFactor
      (eighthNormalizedDatum (frozenCoarseActualDatum P Y A)) selected
      (loss := ((conflictThreshold + 1 : Nat) : ENNReal))
      (epsilon := epsilon) (gamma := beta) hrhoPos hrhoHalf hbetaTwo
  refine Nonempty.intro
    { selected := selected
      selected_nonempty := hselected
      bound := ?_ }
  exact haverage.trans (by
    simpa only [Fintype.card_fin] using htransport)

#print axioms nonempty_activeIndex_sameAssembly_coreNativeThirdBundle

end
end Family8FirstCrossingActiveIndexSameAssemblyThirdBundleV1
