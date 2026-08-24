import FamilyStickyCinematicL32FiniteIncidenceTangencyAfterNormCoverV1

set_option autoImplicit false

open Set

namespace FamilyStickyCinematicL32FiniteLocalizedTangencyCarrierSubsetV1

open FamilyStickyCinematicL32FiniteMeasurableIncidencePatternV1
open FamilyStickyCinematicL32FiniteIncidenceTangencyAfterNormCoverV1

noncomputable section

/-!
# Localized tangency carriers retain their source incidence

The first conjunct in the literal post-norm-cover `Y₁` acceptance predicate
is membership in the original active incidence family.  This module exposes
the corresponding carrier containment without any geometric callback.
-/

theorem finiteIncidenceLocalizedTangencyCarrier_subset_incidence
    {X index alpha : Type*} [MeasurableSpace X]
    (ambient : Finset index) (incidence : index → X → Prop)
    (familyOfActive : Finset index → Finset alpha)
    (normDistance : alpha → alpha → Real)
    (globalScale : Real) (globalCenter : alpha)
    (tangencyDistance : Finset index → alpha → alpha → Real)
    (elementOfIndex : index → alpha)
    (delta ceiling exponent threshold : Real) (i : index) :
    finiteIncidenceLocalizedTangencyCarrier ambient incidence familyOfActive
        normDistance globalScale globalCenter tangencyDistance elementOfIndex
        delta ceiling exponent threshold i ⊆
      {x | incidence i x} := by
  intro x hx
  have hiActive : i ∈ finiteIncidenceActiveAtPoint ambient incidence x :=
    hx.1
  exact (mem_finiteIncidenceActiveAtPoint ambient incidence x i).mp
    hiActive |>.2

#print axioms finiteIncidenceLocalizedTangencyCarrier_subset_incidence

end
end FamilyStickyCinematicL32FiniteLocalizedTangencyCarrierSubsetV1
