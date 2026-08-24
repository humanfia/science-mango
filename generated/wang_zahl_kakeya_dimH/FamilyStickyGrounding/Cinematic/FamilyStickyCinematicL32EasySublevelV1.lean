import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32SublevelShapeV1

set_option autoImplicit false

open Set

namespace FamilyStickyCinematicL32EasySublevelV1

open FamilyStickyCinematicL32SublevelIntervalV1
open FamilyStickyCinematicL32SublevelShapeV1

/-!
# The derivative-separated sublevel regime

Provenance: the easier cases in Pramanik--Yang--Zahl,
arXiv:2207.02259v3, Lemma 3.8(2b).  When `|h'|` is uniformly separated
from zero, the sublevel set has one monotone branch and each sublevel interval
has length at most `2 * delta / m`.

The derivative sign, monotonicity, order-connectedness, and length bound are
all produced below; none is accepted as a callback.
-/

/-- Uniform nonvanishing of a continuous first derivative makes the full
sublevel set order-connected. -/
theorem sublevelOn_ordConnected_of_abs_deriv_lower
    (h h1 : Real -> Real) (delta : Real) {A B m : Real}
    (hAB : A <= B) (hm : 0 < m)
    (hderiv : forall z, z ∈ Icc A B -> HasDerivAt h (h1 z) z)
    (h1Continuous : ContinuousOn h1 (Icc A B))
    (hfirstLower : forall z, z ∈ Icc A B -> m <= |h1 z|) :
    (SublevelOn h delta (Icc A B)).OrdConnected := by
  rcases continuous_fixed_sign_of_abs_lower_on_Icc
      h1 hAB hm h1Continuous hfirstLower with hpositive | hnegative
  · apply sublevelOn_ordConnected_of_monotoneOn
      h delta ordConnected_Icc
    apply monotoneOn_of_hasDerivWithinAt_nonneg
      (convex_Icc A B) (HasDerivAt.continuousOn hderiv)
    · intro z hz
      exact (hderiv z (interior_subset hz)).hasDerivWithinAt
    · intro z hz
      exact (le_of_lt hm).trans (hpositive z (interior_subset hz))
  · apply sublevelOn_ordConnected_of_antitoneOn
      h delta ordConnected_Icc
    apply antitoneOn_of_hasDerivWithinAt_nonpos
      (convex_Icc A B) (HasDerivAt.continuousOn hderiv)
    · intro z hz
      exact (hderiv z (interior_subset hz)).hasDerivWithinAt
    · intro z hz
      exact (hnegative z (interior_subset hz)).trans (neg_nonpos.2 (le_of_lt hm))

/-- Any interval contained in the easy-regime sublevel set has the explicit
length bound `2 * delta / m`. -/
theorem easy_sublevel_interval_length_le
    (h h1 : Real -> Real) {A B x y delta m : Real}
    (hxy : x <= y) (hxDomain : x ∈ Icc A B) (hyDomain : y ∈ Icc A B)
    (hm : 0 < m)
    (hderiv : forall z, z ∈ Icc A B -> HasDerivAt h (h1 z) z)
    (h1Continuous : ContinuousOn h1 (Icc A B))
    (hfirstLower : forall z, z ∈ Icc A B -> m <= |h1 z|)
    (hcomponentSublevel : forall z, z ∈ Icc x y -> |h z| <= delta) :
    y - x <= 2 * delta / m := by
  have hcomponentSubset : Icc x y ⊆ Icc A B :=
    Icc_subset_Icc hxDomain.1 hyDomain.2
  exact sublevel_interval_length_le_of_abs_deriv_lower
    h h1 hxy hm
    (hcomponentSublevel x (left_mem_Icc.2 hxy))
    (hcomponentSublevel y (right_mem_Icc.2 hxy))
    (fun z hz => hderiv z (hcomponentSubset hz))
    (h1Continuous.mono hcomponentSubset)
    (fun z hz => hfirstLower z (hcomponentSubset hz))

#print axioms sublevelOn_ordConnected_of_abs_deriv_lower
#print axioms easy_sublevel_interval_length_le

end FamilyStickyCinematicL32EasySublevelV1
