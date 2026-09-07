import Family8Grounding.Family8StickyBoundedFiberPartitionCoreV1
import Family8Grounding.Family8KatzTaoDoubledFiberActiveIndexCapV3
import Family8Grounding.Family8StickyScaleCoverActiveFineRestrictionV2
import Family8Grounding.Family8GreedyOccurrenceCanonicalFrostmanBridgeV2
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8StickyKatzTaoBoundedFiberPartitionV4

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.HeavyParentSelection
open Submission.Kakeya.Uniformity
open Family8KatzTaoFrostmanPropertiesV1
open Family8Def212ConvexWolffAtEveryScaleV2.ScaleCover
open Family8PaperConflictOwnerActiveOwnerKatzTaoDoubledFiberCapV3
open Family8GreedyOccurrenceCanonicalFrostmanBridgeV2
open FamilyStickyAtEveryScaleCoreV1
open Family8StickyScaleCoverActiveFineRestrictionV2.ScaleCover

noncomputable section

variable {delta rho : NNReal} {iota : Type}
  [Fintype iota] [DecidableEq iota]
  {fine : UniformTubeFamily delta iota}

/-- Restricting a native source Katz--Tao family to the literal active-fine
subtype introduces no concentration loss. -/
theorem activeFineRestrictedFamily_isKatzTao
    (S : StickyScaleCover fine rho) {A : ENNReal}
    (hKT : IsKatzTao A fine.bodyFamily) :
    IsKatzTao A (activeFineRestrictedFamily S).bodyFamily := by
  change IsKatzTao A (selectedCoarseFamily fine.bodyFamily S.activeFine)
  exact isKatzTao_selectedCoarseFamily_of_isKatzTaoOn
    (hKT.on S.activeFine)

/-- The exact Katz--Tao doubled-fibre incidence cap bounds every literal
fibre of the fully active reindexed cover. -/
theorem activeFineRestrictedScaleCover_fiber_card_le_katzTaoCap
    (S : StickyScaleCover fine rho)
    (hdeltaPos : 0 < delta)
    (hdeltaHalf : delta <= (2 : NNReal)⁻¹)
    (hrhoOne : rho <= 1)
    {A : ENNReal} (hAfinite : A ≠ ∞)
    (hKT : IsKatzTao A fine.bodyFamily) :
    forall k : Fin (activeFineRestrictedScaleCover S).coarseCard,
      k ∈ (activeFineRestrictedScaleCover S).activeCoarse ->
      ((activeFineRestrictedScaleCover S).fiber k).card <=
        katzTaoDoubledFiberNatCap delta rho A := by
  intro k _hk
  let U := activeFineRestrictedScaleCover S
  have hKTActive : IsKatzTao A (activeFineRestrictedFamily S).bodyFamily :=
    activeFineRestrictedFamily_isKatzTao S hKT
  calc
    (U.fiber k).card <= (doubledFiber U k).card :=
      Finset.card_le_card (fiber_subset_doubledFiber U k)
    _ <= katzTaoDoubledFiberNatCap delta rho A :=
      doubledFiber_card_le_katzTaoDoubledFiberNatCap U
        hdeltaPos hdeltaHalf hrhoOne hAfinite hKTActive k

#print axioms activeFineRestrictedFamily_isKatzTao
#print axioms
  activeFineRestrictedScaleCover_fiber_card_le_katzTaoCap

end
end Family8StickyKatzTaoBoundedFiberPartitionV4
