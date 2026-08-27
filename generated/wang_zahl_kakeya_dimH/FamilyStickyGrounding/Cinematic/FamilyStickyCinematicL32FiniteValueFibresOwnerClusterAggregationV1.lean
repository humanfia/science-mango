import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32FiniteValueFibresV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true

open scoped BigOperators ENNReal

namespace FamilyStickyCinematicL32FiniteValueFibresOwnerClusterAggregationV1

noncomputable section

universe u v

/-!
# Package-free aggregation of finite-fibre owner-cluster bounds

These lemmas isolate the exact algebra needed after running the two-stage
selector independently on every occupied value fibre.  They make no
reference to fixed-C provenance, sampling packages, rectangles, or the
origin of the owner-cluster cap.
-/

/-- A lossless finite partition and one uniform packing bound aggregate to
the sum of the per-fibre owner-cluster masses. -/
theorem card_le_packing_mul_sum_clusterMass_of_fibres
    {item : Type u} {value : Type v}
    (items : Finset item) (values : Finset value)
    (fiber : value -> Finset item) (packingBound : ENNReal)
    (clusterMass : value -> ENNReal)
    (hpartition : items.card =
      ∑ c ∈ values, (fiber c).card)
    (hfiber : forall c, c ∈ values ->
      ((fiber c).card : ENNReal) <= packingBound * clusterMass c) :
    (items.card : ENNReal) <=
      packingBound * ∑ c ∈ values, clusterMass c := by
  have hpartitionENN : (items.card : ENNReal) =
      ∑ c ∈ values, ((fiber c).card : ENNReal) := by
    exact_mod_cast hpartition
  calc
    (items.card : ENNReal) =
        ∑ c ∈ values, ((fiber c).card : ENNReal) := hpartitionENN
    _ <= ∑ c ∈ values, packingBound * clusterMass c := by
      exact Finset.sum_le_sum fun c hc => hfiber c hc
    _ = packingBound * ∑ c ∈ values, clusterMass c := by
      rw [Finset.mul_sum]

/-- If every fibre's total selected owner-cluster mass is capped by its
selected cardinality times one common cap, the raw cardinality is bounded by
the total selected cardinality with the same cap. -/
theorem card_le_packing_mul_sum_selectedCard_mul_cap_of_fibres
    {item : Type u} {value : Type v}
    (items : Finset item) (values : Finset value)
    (fiber : value -> Finset item) (packingBound cap : ENNReal)
    (selectedCard : value -> Nat) (clusterMass : value -> ENNReal)
    (hpartition : items.card =
      ∑ c ∈ values, (fiber c).card)
    (hfiber : forall c, c ∈ values ->
      ((fiber c).card : ENNReal) <= packingBound * clusterMass c)
    (hcap : forall c, c ∈ values ->
      clusterMass c <= (selectedCard c : ENNReal) * cap) :
    (items.card : ENNReal) <=
      packingBound *
        (∑ c ∈ values, (selectedCard c : ENNReal)) * cap := by
  calc
    (items.card : ENNReal) <=
        packingBound * ∑ c ∈ values, clusterMass c :=
      card_le_packing_mul_sum_clusterMass_of_fibres items values fiber
        packingBound clusterMass hpartition hfiber
    _ <= packingBound *
        ∑ c ∈ values, ((selectedCard c : ENNReal) * cap) := by
      gcongr with c hc
      exact hcap c hc
    _ = packingBound *
        (∑ c ∈ values, (selectedCard c : ENNReal)) * cap := by
      rw [← Finset.sum_mul]
      ac_rfl

/-- If every selected fibre has the same endpoint bound `lensBound`, the
only remaining aggregation loss is the honest number of occupied values. -/
theorem card_le_packing_mul_valueCard_mul_lensBound_mul_cap_of_fibres
    {item : Type u} {value : Type v}
    (items : Finset item) (values : Finset value)
    (fiber : value -> Finset item)
    (packingBound lensBound cap : ENNReal)
    (selectedCard : value -> Nat) (clusterMass : value -> ENNReal)
    (hpartition : items.card =
      ∑ c ∈ values, (fiber c).card)
    (hfiber : forall c, c ∈ values ->
      ((fiber c).card : ENNReal) <= packingBound * clusterMass c)
    (hcap : forall c, c ∈ values ->
      clusterMass c <= (selectedCard c : ENNReal) * cap)
    (hselected : forall c, c ∈ values ->
      (selectedCard c : ENNReal) <= lensBound) :
    (items.card : ENNReal) <=
      packingBound * (values.card : ENNReal) * lensBound * cap := by
  have hselectedSum :
      (∑ c ∈ values, (selectedCard c : ENNReal)) <=
        (values.card : ENNReal) * lensBound := by
    calc
      (∑ c ∈ values, (selectedCard c : ENNReal)) <=
          ∑ _c ∈ values, lensBound := by
        exact Finset.sum_le_sum fun c hc => hselected c hc
      _ = (values.card : ENNReal) * lensBound := by
        simp [nsmul_eq_mul]
  calc
    (items.card : ENNReal) <=
        packingBound *
          (∑ c ∈ values, (selectedCard c : ENNReal)) * cap :=
      card_le_packing_mul_sum_selectedCard_mul_cap_of_fibres items values
        fiber packingBound cap selectedCard clusterMass hpartition hfiber hcap
    _ <= packingBound * ((values.card : ENNReal) * lensBound) * cap := by
      gcongr
    _ = packingBound * (values.card : ENNReal) * lensBound * cap := by
      ac_rfl

#print axioms card_le_packing_mul_sum_clusterMass_of_fibres
#print axioms card_le_packing_mul_sum_selectedCard_mul_cap_of_fibres
#print axioms card_le_packing_mul_valueCard_mul_lensBound_mul_cap_of_fibres

end

end FamilyStickyCinematicL32FiniteValueFibresOwnerClusterAggregationV1
