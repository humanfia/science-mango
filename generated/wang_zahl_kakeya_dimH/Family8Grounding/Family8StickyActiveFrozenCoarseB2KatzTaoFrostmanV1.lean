import Family8Grounding.Family8StickyActiveFrozenCoarseB2FrostmanV3
import Family8Grounding.Family8StickyActiveRestrictedCoarseKatzTaoV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8StickyActiveFrozenCoarseB2KatzTaoFrostmanV1

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
open Family8StickyActiveFrozenCoarseB2FrostmanV3
open Family8StickyActiveRestrictedCoarseKatzTaoV1

noncomputable section

/-!
# Frozen coarse B2 Frostman selection from native sticky Katz--Tao data

This connector combines the automatic radius-two support with the exact
active-parent reindex transport.  Consequently the Katz--Tao premise is now
the native `StickyScaleCover.IsKatzTaoAtScale` certificate on the same actual
cover, rather than a separately restated property of its Fin reindexing.
-/

variable {delta rho : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]

theorem exists_normalized_activeFrozenCoarse_of_isKatzTaoAtScale
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
  exact
    exists_normalized_activeFrozenCoarse_averageMultiplicity_le_frostmanRHS
      hF D hD S hrho P Y A hconflict
        (activeFineRestrictedScaleCover_coarse_isKatzTao S hKT)
        hdelta0 hdensityBudget hbaseBudget

#print axioms exists_normalized_activeFrozenCoarse_of_isKatzTaoAtScale

end
end Family8StickyActiveFrozenCoarseB2KatzTaoFrostmanV1
