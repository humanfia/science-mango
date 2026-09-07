import Family8Grounding.Family8PaperConflictOwnerActiveOwnerKatzTaoDoubledFiberCapV3
import FamilyStickyGrounding.FamilyStickyHierarchyEndpointPrefixShadingTransportV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

open scoped ENNReal NNReal

namespace Family8KatzTaoDoubledFiberActiveIndexCapV3

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8KatzTaoFrostmanPropertiesV1
open Family8Def212ConvexWolffAtEveryScaleV2
open Family8Def212ConvexWolffAtEveryScaleV2.ScaleCover
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyHierarchyEndpointPrefixShadingTransportV1.StickyScaleCover
open Family8PaperConflictOwnerActiveOwnerKatzTaoDoubledFiberCapV3

noncomputable section

/-!
# Exact Katz--Tao cap for the active-subtype parent fibres

The geometric theorem bounds `doubledFiber S k`, while parent shading mass
is regrouped by the fibres of `activeIndexFactorization S`.  Subtype
projection injects every latter fibre into the former.  This file supplies
that missing literal bridge and specializes it to the exact Katz--Tao Nat
cap.
-/

namespace StickyScaleCover

variable {delta rho : NNReal} {iota : Type}
  [Fintype iota] [DecidableEq iota]
  {fine : UniformTubeFamily delta iota}

/-- Projecting one active-subtype factorization fibre to the source index
lands in the corresponding doubled geometric fibre. -/
theorem activeIndexFiber_val_image_subset_doubledFiber
    (S : StickyScaleCover fine rho)
    (k : {k // k ∈ S.activeCoarse}) :
    ((activeIndexFactorization S).fiber k).image Subtype.val ⊆
      doubledFiber S k.1 := by
  intro i hi
  obtain ⟨ii, hii, rfl⟩ := Finset.mem_image.mp hi
  have hifactor :=
    (IndexFactorization.mem_fiber (activeIndexFactorization S) ii k).mp hii
  have hparent : S.parent ii.1 = k.1 :=
    congrArg Subtype.val hifactor.2
  apply fiber_subset_doubledFiber S k.1
  exact (S.mem_fiber ii.1 k.1).mpr ⟨ii.2, hparent⟩

/-- Hence the active-subtype parent fibre has no larger cardinality than
the doubled geometric fibre. -/
theorem activeIndexFiber_card_le_doubledFiber_card
    (S : StickyScaleCover fine rho)
    (k : {k // k ∈ S.activeCoarse}) :
    ((activeIndexFactorization S).fiber k).card <=
      (doubledFiber S k.1).card := by
  rw [← Finset.card_image_of_injective _ Subtype.val_injective]
  exact Finset.card_le_card
    (activeIndexFiber_val_image_subset_doubledFiber S k)

/-- Any doubled-fibre cap therefore supplies the exact `hMcard` interface
used by the parent-mass/X-lower connector. -/
theorem activeIndexFiber_card_le_of_doubledFiberCap
    (S : StickyScaleCover fine rho) (M : Nat)
    (hcap : forall k : Fin S.coarseCard, k ∈ S.activeCoarse ->
      (doubledFiber S k).card <= M) :
    forall k : {k // k ∈ S.activeCoarse},
      ((activeIndexFactorization S).fiber k).card <= M := by
  intro k
  exact (activeIndexFiber_card_le_doubledFiber_card S k).trans
    (hcap k.1 k.2)

/-- Canonical exact choice
`M = katzTaoDoubledFiberNatCap delta rho A`.  This discharges `hMcard`
directly from the real source Katz--Tao hypothesis. -/
theorem activeIndexFiber_card_le_katzTaoDoubledFiberNatCap
    (S : StickyScaleCover fine rho)
    (hdeltaPos : 0 < delta)
    (hdeltaHalf : delta <= (2 : NNReal)⁻¹)
    (hrhoOne : rho <= 1)
    {A : ENNReal} (hAfinite : A ≠ ∞)
    (hKT : IsKatzTao A fine.bodyFamily) :
    forall k : {k // k ∈ S.activeCoarse},
      ((activeIndexFactorization S).fiber k).card <=
        katzTaoDoubledFiberNatCap delta rho A := by
  apply activeIndexFiber_card_le_of_doubledFiberCap S
  intro k _hk
  exact doubledFiber_card_le_katzTaoDoubledFiberNatCap
    S hdeltaPos hdeltaHalf hrhoOne hAfinite hKT k

#print axioms activeIndexFiber_val_image_subset_doubledFiber
#print axioms activeIndexFiber_card_le_doubledFiber_card
#print axioms activeIndexFiber_card_le_of_doubledFiberCap
#print axioms activeIndexFiber_card_le_katzTaoDoubledFiberNatCap

end StickyScaleCover
end
end Family8KatzTaoDoubledFiberActiveIndexCapV3
