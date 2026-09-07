import Family8Grounding.Family8EndpointLongCoreIdentityIntervalCountsV3
import Family8Grounding.Family8SelectedFineFiberCardCapTransportV2
import Mathlib.Tactic

/-!
# Selected-fine endpoint count comparison

The first endpoint count is one.  A finite selection inside a selected-fine
fibre inherits the honest old-fibre cap `M`, while the identity interval's
third count is the source index cardinality.  Their literal product therefore
has count loss `M`.
-/

set_option autoImplicit false
set_option warningAsError true

open scoped ENNReal NNReal

namespace Family8SelectedFineEndpointCountComparisonV1

open Submission.Kakeya.Uniformity
open Family8SelectedFineFiberCardCapTransportV2
open Family8StickySelectedFineSubtypeScaleCoverV1
open FamilyStickyAtEveryScaleCoreV1

noncomputable section

variable {delta rho : NNReal} {index sourceIndex : Type}
  [Fintype index] [DecidableEq index]
  [Fintype sourceIndex]
  {fine : UniformTubeFamily delta index}

/-- Literal `hCount` with `firstCount = 1`, selected-fibre middle count,
identity-interval third count, and honest count loss `M`. -/
theorem selectedFine_endpoint_countComparison
    (S : StickyScaleCover fine rho)
    (selectedFine : Finset index)
    (hselectedFine : selectedFine ⊆ S.activeFine)
    (q : Fin (selectedFineParentValues S selectedFine).card)
    (picked : Finset {i // i ∈
      (selectedFineScaleCover S selectedFine hselectedFine).fiber q})
    (M : Nat)
    (hM : forall k, k ∈ S.activeCoarse -> (S.fiber k).card <= M)
    (hcoarseCard : S.coarseCard = Fintype.card sourceIndex) :
    (((1 * (picked.card * Fintype.card (Fin S.coarseCard)) : Nat) : ENNReal)) <=
      (M : ENNReal) * (Fintype.card sourceIndex : ENNReal) := by
  have hpicked : picked.card <= M :=
    selectedFineScaleCover_selected_card_le_parent_cap
      S selectedFine hselectedFine q picked M hM
  have hnat :
      1 * (picked.card * Fintype.card (Fin S.coarseCard)) <=
        M * Fintype.card sourceIndex := by
    simpa only [one_mul, Fintype.card_fin, hcoarseCard] using
      Nat.mul_le_mul_right (Fintype.card sourceIndex) hpicked
  exact_mod_cast hnat

#print axioms selectedFine_endpoint_countComparison

end
end Family8SelectedFineEndpointCountComparisonV1
