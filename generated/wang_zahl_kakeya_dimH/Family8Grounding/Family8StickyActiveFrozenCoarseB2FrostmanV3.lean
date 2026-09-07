import Family8Grounding.Family8FrozenCoarseB2FrostmanActualDatumV1
import Family8Grounding.Family8StickyActiveRestrictedCoarseB2SupportV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000
set_option linter.style.haveILetI false

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8StickyActiveFrozenCoarseB2FrostmanV3

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8KatzTaoFrostmanPropertiesV1
open Family8GeneralizedKatzTaoMultiplicityV1
open FamilyStickyAtEveryScaleCoreV1
open Family8StickyScaleCoverActiveFineRestrictionV2.ScaleCover
open Family8FiniteRandomRigidMotionB2NormalizedDatumV1
open Family8FiniteRandomRigidMotionB2FreshGreedyV1
open Family8FrozenCoarseB2FrostmanActualDatumV1
open Family8StickyActiveRestrictedCoarseB2SupportV1

noncomputable section

/-!
# Automatic B2 discharge for the actual sticky frozen coarse datum

For the active-index reindexed sticky cover, admissibility of the original
fine datum and the paper scale restriction `rho <= 1/16` already put every
actual coarse parent in the ball of radius two.  A genuine coarse partition
also supplies both `delta <= rho` and a coarse index, so positivity of `rho`
and nonemptiness of the actual reindexed parent type are automatic as well.

The endpoints below retain only the analytic Katz--Tao, density, base, and
conflict budgets. Their source average is literally the frozen coarse average
of the same assembly.
-/

variable {delta rho : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]

theorem exists_normalized_activeFrozenCoarse_averageMultiplicity_le_frostmanRHS
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
    {C : ENNReal}
    (hKT : IsKatzTao C
      (activeFineRestrictedScaleCover S).coarse.bodyFamily)
    (hdelta0 : rho / 8 <= delta0)
    (hdensityBudget :
      ((rho / 8 : NNReal) : ENNReal) ^ eta <=
        (eighthNormalizedDatum
          (frozenCoarseActualDatum P Y A)).shading.shadingDensity /
            (conflictThreshold + 1 : Nat))
    (hbaseBudget :
      (conflictThreshold + 1 : Nat) *
          ((128 * C) * volume (unitBallBody : Set Space)) <=
        ((rho / 8 : NNReal) : ENNReal) ^ (-eta) *
          ((Fintype.card
              (Fin (activeFineRestrictedScaleCover S).coarseCard) : ENNReal) *
            (((rho / 8 : NNReal) : ENNReal) ^ 2 / 2))) :
    exists selected :
        Finset (Fin (activeFineRestrictedScaleCover S).coarseCard),
      selected.Nonempty /\
      A.frozenCoarse.averageMultiplicity <=
        (conflictThreshold + 1 : Nat) *
          frostmanMultiplicityRHS (rho / 8)
            (restrictActualTubeDatum
              (eighthNormalizedDatum (frozenCoarseActualDatum P Y A))
              selected).actualFamilyVolume epsilon beta := by
  classical
  haveI : Nonempty
      (Fin (activeFineRestrictedScaleCover S).coarseCard) := by
    obtain ⟨q, _hq⟩ := P.coarse_nonempty
    exact ⟨q⟩
  have hrhoPos : 0 < rho := hD.delta_pos.trans_le P.scale_le
  have hsixteenHalf : (1 / 16 : NNReal) <= (2 : NNReal)⁻¹ := by
    change (1 : Real) / 16 <= (2 : Real)⁻¹
    norm_num
  have hrhoHalf : rho <= (2 : NNReal)⁻¹ := hrho.trans hsixteenHalf
  exact
    exists_normalized_frozenCoarse_averageMultiplicity_le_frostmanRHS
      hF P Y A hrhoPos hrhoHalf
        (activeFineRestrictedScaleCover_coarse_carrier_subset_closedBall_two
          D hD S hrho)
        hconflict hKT hdelta0 hdensityBudget hbaseBudget

theorem exists_automatic_normalized_activeFrozenCoarse_averageMultiplicity_le_frostmanRHS
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
    {C : ENNReal}
    (hKT : IsKatzTao C
      (activeFineRestrictedScaleCover S).coarse.bodyFamily)
    (hdelta0 : rho / 8 <= delta0)
    (hdensityBudget :
      ((rho / 8 : NNReal) : ENNReal) ^ eta <=
        (eighthNormalizedDatum
          (frozenCoarseActualDatum P Y A)).shading.shadingDensity /
            (Fintype.card
              (Fin (activeFineRestrictedScaleCover S).coarseCard) + 1 : Nat))
    (hbaseBudget :
      (Fintype.card
          (Fin (activeFineRestrictedScaleCover S).coarseCard) + 1 : Nat) *
          ((128 * C) * volume (unitBallBody : Set Space)) <=
        ((rho / 8 : NNReal) : ENNReal) ^ (-eta) *
          ((Fintype.card
              (Fin (activeFineRestrictedScaleCover S).coarseCard) : ENNReal) *
            (((rho / 8 : NNReal) : ENNReal) ^ 2 / 2))) :
    exists selected :
        Finset (Fin (activeFineRestrictedScaleCover S).coarseCard),
      selected.Nonempty /\
      A.frozenCoarse.averageMultiplicity <=
        (Fintype.card
          (Fin (activeFineRestrictedScaleCover S).coarseCard) + 1 : Nat) *
          frostmanMultiplicityRHS (rho / 8)
            (restrictActualTubeDatum
              (eighthNormalizedDatum (frozenCoarseActualDatum P Y A))
              selected).actualFamilyVolume epsilon beta := by
  classical
  haveI : Nonempty
      (Fin (activeFineRestrictedScaleCover S).coarseCard) := by
    obtain ⟨q, _hq⟩ := P.coarse_nonempty
    exact ⟨q⟩
  have hrhoPos : 0 < rho := hD.delta_pos.trans_le P.scale_le
  have hsixteenHalf : (1 / 16 : NNReal) <= (2 : NNReal)⁻¹ := by
    change (1 : Real) / 16 <= (2 : Real)⁻¹
    norm_num
  have hrhoHalf : rho <= (2 : NNReal)⁻¹ := hrho.trans hsixteenHalf
  exact
    exists_automatic_normalized_frozenCoarse_averageMultiplicity_le_frostmanRHS
      hF P Y A hrhoPos hrhoHalf
        (activeFineRestrictedScaleCover_coarse_carrier_subset_closedBall_two
          D hD S hrho)
        hKT hdelta0 hdensityBudget hbaseBudget

#print axioms
  exists_normalized_activeFrozenCoarse_averageMultiplicity_le_frostmanRHS
#print axioms
  exists_automatic_normalized_activeFrozenCoarse_averageMultiplicity_le_frostmanRHS

end
end Family8StickyActiveFrozenCoarseB2FrostmanV3
