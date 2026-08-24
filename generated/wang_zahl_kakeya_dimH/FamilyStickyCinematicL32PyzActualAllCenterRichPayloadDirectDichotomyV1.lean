import FamilyStickyCinematicL32PyzE2DyadicDegreeWindowV1

set_option autoImplicit false

namespace FamilyStickyCinematicL32PyzActualAllCenterRichPayloadDirectDichotomyV1

open FamilyStickyCinematicL32PyzE2DyadicDegreeWindowV1

/-!
# High/low split on an already selected rich payload

No final-label range is needed at this logical stage: the selector has
already produced one whole payload for every positive centre.  The split is
therefore directly on the final-label accessor of that same payload, so all
geometry and retention fields remain available in both branches.
-/

theorem actualAllCenter_richPayload_high_or_all_low
    {Center : Type*}
    (centers : Finset Center) (positiveMassCell : Center → Prop)
    (Payload : Center → Type*)
    (finalLabel : ∀ center, Payload center → Int)
    (logCount : Nat)
    (hpayload : ∀ center, center ∈ centers → positiveMassCell center →
      Nonempty (Payload center)) :
    (∃ center ∈ centers, positiveMassCell center ∧
      ∃ payload : Payload center,
        24 * logCount ≤ pyzE2DegreeLower (finalLabel center payload)) ∨
    (∀ center, center ∈ centers → positiveMassCell center →
      ∃ payload : Payload center,
        pyzE2DegreeLower (finalLabel center payload) < 24 * logCount) := by
  classical
  by_cases hhigh : ∃ center ∈ centers, positiveMassCell center ∧
      ∃ payload : Payload center,
        24 * logCount ≤ pyzE2DegreeLower (finalLabel center payload)
  · exact Or.inl hhigh
  · refine Or.inr ?_
    intro center hcenter hpositive
    obtain ⟨payload⟩ := hpayload center hcenter hpositive
    refine ⟨payload, Nat.lt_of_not_ge ?_⟩
    intro hdegree
    exact hhigh ⟨center, hcenter, hpositive, payload, hdegree⟩

#print axioms actualAllCenter_richPayload_high_or_all_low

end FamilyStickyCinematicL32PyzActualAllCenterRichPayloadDirectDichotomyV1
