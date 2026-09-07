import Family8Grounding.Family8StickyActiveFrozenCoarseB2KatzTaoFrostmanV1
import Family8Grounding.Family8FrozenCoarseSameDataDensityBudgetV2
import Family8Grounding.Family8FrozenCoarseB2CardScaleBaseBudgetV6
import Family8Grounding.Family8StickyActiveCoarseKatzTaoCardScaleMassUpperV4
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8StickyActiveFrozenCoarseSourceMassFrostmanEndpointV2

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8KatzTaoFrostmanPropertiesV1
open Family8GeneralizedKatzTaoMultiplicityV1
open Family8FiniteRandomRigidMotionB2FreshGreedyV1
open FamilyStickyAtEveryScaleCoreV1
open Family8StickyScaleCoverActiveFineRestrictionV2.ScaleCover
open Family8FrozenComparableActualAverageMassDensityV1.Assembly
open Family8FrozenCoarseB2FrostmanActualDatumV1
open Family8ParentAggregatedShadingActiveCoarseXUpperV3.StickyScaleCover
open Family8FrozenCoarseSameDataDensityBudgetV2
open Family8FrozenCoarseB2CardScaleBaseBudgetV6
open Family8StickyActiveCoarseKatzTaoCardScaleMassUpperV4.StickyScaleCover
open Family8StickyActiveFrozenCoarseB2KatzTaoFrostmanV1

noncomputable section

/-!
# Literal frozen-outer Frostman endpoint from source mass and card-scale mass

This is the first same-object composition of the native sticky Katz--Tao
certificate, the actual frozen assembly, and the B2 Frostman selector.  The
density budget is derived from source mass on the same `P/A`; the base budget
is derived from the exact active-parent card-scale mass.  The Katz--Tao
certificate itself automatically supplies the upper envelope `X <= 1024 C`.
-/

variable {delta rho : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]

theorem exists_normalized_activeFrozenCoarse_of_sourceMass_cardScaleMass
    {beta epsilon eta : Real} {delta0 : NNReal}
    (hF : FrostmanAtParameters beta epsilon eta delta0)
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (S : StickyScaleCover D.family rho)
    (hrho : rho <= (1 / 16 : NNReal))
    (P : CoarseTubePartition
      (activeFineRestrictedFamily S)
      (activeFineRestrictedScaleCover S).coarse)
    (Y : Shading (activeFineRestrictedFamily S).bodyFamily) {r : Real}
    (A : Family8FrozenNeighborhoodAssemblyV1.Assembly
      P.asConvexFactorization Y r)
    {conflictThreshold : Nat}
    (hconflict : forall k,
      (normalizedConflictIndices (frozenCoarseActualDatum P Y A) k).card <=
        conflictThreshold)
    {C : ENNReal} (hKT : S.IsKatzTaoAtScale C)
    (hdelta0 : rho / 8 <= delta0)
    {sourceFloor baseFloor : ENNReal}
    (hsource0 :
      (sourceActiveFineShading P.asConvexFactorization Y).shadingMass ≠ 0)
    (hsourceLower : sourceFloor <=
      (sourceActiveFineShading P.asConvexFactorization Y).shadingMass)
    (hdensityScalar :
      ((((rho / 8 : NNReal) : ENNReal) ^ eta *
            ((conflictThreshold + 1 : Nat) : ENNReal)) * 128) *
          (((A.loss : ENNReal) *
              ((P.branchingLoss * P.branching : Nat) : ENNReal)) *
            (8 * (1024 * C))) <= sourceFloor)
    (hbaseLower :
      baseFloor <= (activeCoarseCardScaleMass S : ENNReal))
    (hbaseScalar :
      ((conflictThreshold + 1 : Nat) : ENNReal) *
          ((128 * C) * volume (unitBallBody : Set Space)) <=
        ((rho / 8 : NNReal) : ENNReal) ^ (-eta) *
          (baseFloor / 128)) :
    exists selected :
        Finset (Fin (activeFineRestrictedScaleCover S).coarseCard),
      selected.Nonempty /\
      A.frozenCoarse.averageMultiplicity <=
        ((conflictThreshold + 1 : Nat) : ENNReal) *
          frostmanMultiplicityRHS (rho / 8)
            (restrictActualTubeDatum
              (Family8FiniteRandomRigidMotionB2NormalizedDatumV1.eighthNormalizedDatum
                (frozenCoarseActualDatum P Y A))
              selected).actualFamilyVolume epsilon beta := by
  have hsixteenHalf : (1 / 16 : NNReal) <= (2 : NNReal)⁻¹ := by
    change (1 : Real) / 16 <= (2 : Real)⁻¹
    norm_num
  have hrhoHalf : rho <= (2 : NNReal)⁻¹ := hrho.trans hsixteenHalf
  have hrhoPos : 0 < rho := hD.delta_pos.trans_le P.scale_le
  have hXUpper :
      (activeCoarseCardScaleMass S : ENNReal) <= 1024 * C :=
    activeCoarseCardScaleMass_le_1024_mul_of_isKatzTaoAtScale
      D hD S hrhoHalf hKT
  have hdensityBudget :
      ((rho / 8 : NNReal) : ENNReal) ^ eta <=
        (Family8FiniteRandomRigidMotionB2NormalizedDatumV1.eighthNormalizedDatum
          (frozenCoarseActualDatum P Y A)).shading.shadingDensity /
            ((conflictThreshold + 1 : Nat) : ENNReal) :=
    activeFrozenCoarse_normalizedDensityBudget_of_sourceMass
      S P Y A hrhoPos hrhoHalf (by omega) hsource0 hsourceLower hXUpper
        hdensityScalar
  have hbaseBudget :
      ((conflictThreshold + 1 : Nat) : ENNReal) *
          ((128 * C) * volume (unitBallBody : Set Space)) <=
        ((rho / 8 : NNReal) : ENNReal) ^ (-eta) *
          ((Fintype.card
              (Fin (activeFineRestrictedScaleCover S).coarseCard) : ENNReal) *
            ((((rho / 8 : NNReal) : ENNReal) ^ 2) / 2)) :=
    activeFrozenCoarse_baseBudget_of_cardScaleMassLower
      S hbaseLower hbaseScalar
  exact exists_normalized_activeFrozenCoarse_of_isKatzTaoAtScale
    hF D hD S hrho P Y A hconflict hKT hdelta0 hdensityBudget hbaseBudget

#print axioms
  exists_normalized_activeFrozenCoarse_of_sourceMass_cardScaleMass

end
end Family8StickyActiveFrozenCoarseSourceMassFrostmanEndpointV2
