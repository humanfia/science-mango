import Family8Grounding.Family8CoreNativeFrozenThirdBundleBetaGammaNoLossV3
import Family8Grounding.Family8FirstCrossingActiveIndexSameAssemblyThirdBundleV1
import Family8Grounding.Family8KatzTaoFrostmanPropertiesV1
import Family8Grounding.Family8ParentAggregatedShadingActiveCoarseXUpperV3

/-!
# Active-index fourth-card refold and beta-to-gamma third factor

The canonical LongCore power theorem is stated with
`activeCoarseCardScaleMass` on the active-fine-restricted cover.  The native
third bundle spells the same quantity as `rho^2 * Fintype.card`.  This module
records their literal equality and applies the existing lossless beta-to-
gamma conversion without changing the assembly, selection, count, or loss.
-/

set_option autoImplicit false
set_option warningAsError true

open scoped BigOperators ENNReal NNReal

namespace Family8FirstCrossingActiveIndexThirdBetaGammaRefoldV4

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8CoreNativeFrozenThirdBundleBetaGammaNoLossV3
open Family8CoreNativeFrozenThirdBundleV1
open Family8FrozenComparableActualAverageMassDensityV1.Assembly
open Family8FrozenNeighborhoodAssemblyV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8ParentAggregatedShadingActiveCoarseXUpperV3.StickyScaleCover
open Family8StickyScaleCoverActiveFineRestrictionV2.ScaleCover
open FamilyStickyAtEveryScaleCoreV1

noncomputable section

variable {delta rho : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]

/-- Refold the normalized active-parent card-scale mass into the exact
fourth-card expression expected by the native beta-to-gamma bridge. -/
theorem activeFineRestricted_fourth_cardScale_of_cardScaleMass
    {fine : UniformTubeFamily delta index}
    (S : StickyScaleCover fine rho)
    (hcardScale :
      ((rho : ENNReal) ^ (4 : Nat)) *
        (activeCoarseCardScaleMass
          (activeFineRestrictedScaleCover S) : ENNReal) ≤ 1) :
    ((rho : ENNReal) ^ (4 : Nat)) *
        (((rho : ENNReal) ^ (2 : Nat)) *
          (Fintype.card
            (Fin (activeFineRestrictedScaleCover S).coarseCard) : ENNReal)) ≤
      1 := by
  let U := activeFineRestrictedScaleCover S
  have hcard : U.activeCoarse.card =
      Fintype.card (Fin U.coarseCard) := by
    rw [activeFineRestrictedScaleCover_activeCoarse, Finset.card_univ]
  have hraw : ((rho : ENNReal) ^ (4 : Nat)) *
      ((U.activeCoarse.card : ENNReal) *
        (rho : ENNReal) ^ (2 : Nat)) ≤ 1 := by
    change ((rho : ENNReal) ^ (4 : Nat)) *
      ((U.activeCoarse.card : ENNReal) *
        (rho : ENNReal) ^ (2 : Nat)) ≤ 1 at hcardScale
    exact hcardScale
  rw [← hcard]
  calc
    ((rho : ENNReal) ^ (4 : Nat)) *
        (((rho : ENNReal) ^ (2 : Nat)) *
          (U.activeCoarse.card : ENNReal)) =
      ((rho : ENNReal) ^ (4 : Nat)) *
        ((U.activeCoarse.card : ENNReal) *
          (rho : ENNReal) ^ (2 : Nat)) := by
      ac_rfl
    _ ≤ 1 := hraw

/-- Apply the lossless beta-to-gamma conversion directly from the canonical
active-coarse card-scale statement. -/
def CoreNativeFrozenThirdBundle.toGammaOfActiveFineCardScale
    (D : ActualTubeDatum delta index)
    (S : StickyScaleCover D.family rho)
    (P : CoarseTubePartition
      (activeFineRestrictedFamily S)
      (activeFineRestrictedScaleCover S).coarse)
    (Y : Shading (activeFineRestrictedFamily S).bodyFamily)
    (A : Family8FrozenNeighborhoodAssemblyV1.Assembly
      P.asConvexFactorization Y 1)
    {loss : ENNReal} {beta gamma : Real}
    (X : CoreNativeFrozenThirdBundle
      P.asConvexFactorization Y A rho loss beta)
    (hrho : 0 < rho) (hbetaGamma : beta ≤ gamma)
    (hcardScale :
      ((rho : ENNReal) ^ (4 : Nat)) *
        (activeCoarseCardScaleMass
          (activeFineRestrictedScaleCover S) : ENNReal) ≤ 1) :
    CoreNativeFrozenThirdBundle
      P.asConvexFactorization Y A rho loss gamma :=
  Family8CoreNativeFrozenThirdBundleBetaGammaNoLossV3.CoreNativeFrozenThirdBundle.toGammaOfFourthCardScale
    X hrho hbetaGamma
      (activeFineRestricted_fourth_cardScale_of_cardScaleMass S hcardScale)

#print axioms activeFineRestricted_fourth_cardScale_of_cardScaleMass
#print axioms CoreNativeFrozenThirdBundle.toGammaOfActiveFineCardScale

end
end Family8FirstCrossingActiveIndexThirdBetaGammaRefoldV4
