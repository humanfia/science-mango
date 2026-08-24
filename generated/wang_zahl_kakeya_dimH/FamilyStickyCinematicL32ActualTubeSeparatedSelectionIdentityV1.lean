import FamilyStickyCinematicL32ActualTubeCoefficientSelectionV1

set_option autoImplicit false

namespace FamilyStickyCinematicL32ActualTubeSeparatedSelectionIdentityV1

open Submission.Kakeya.ConvexGeometry
open FamilyStickyCinematicL32ActualTubeCoefficientDistancesV1
open FamilyStickyCinematicL32ActualTubeCoefficientSelectionV1

noncomputable section

/-! # A separated family is fixed by the maximal coefficient selection -/

/-- Applying the canonical maximal selection to a family which is already
pairwise separated retains every tube. -/
theorem selectedTubes_eq_self_of_pairwise_separated
    {radius : NNReal} (family : Finset (Tube radius)) (delta : Real)
    (hpair : ∀ T, T ∈ family → ∀ U, U ∈ family → T ≠ U →
      delta ≤ projectedTubePairCoefficientDistance T U) :
    selectedTubes family delta = family := by
  classical
  apply Finset.Subset.antisymm (selectedTubes_subset family delta)
  intro T hT
  let member : TubeMember family := ⟨T, hT⟩
  let C := coefficientSelection family delta
  let center : C.Cell := C.code member
  have hcenterFamily : center.1.1 ∈ family := center.1.2
  have hvalue : T = center.1.1 := by
    rcases C.eq_or_not_separated_code member with heq | hnot
    · exact congrArg Subtype.val heq
    · by_contra hne
      exact hnot (hpair T hT center.1.1 hcenterFamily hne)
  rw [selectedTubes, Finset.mem_image]
  exact ⟨center.1, center.2, hvalue.symm⟩

#print axioms selectedTubes_eq_self_of_pairwise_separated

end

end FamilyStickyCinematicL32ActualTubeSeparatedSelectionIdentityV1
