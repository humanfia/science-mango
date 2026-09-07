import Family8Grounding.Family8SelfImprovementIterationV1
import Family8Grounding.Family8FrostmanExponentTransportV1

namespace Family8SelfImprovementLimitClosureV1

open Family8KatzTaoFrostmanPropertiesV1
open Family8SelfImprovementIterationV1
open Family8FrostmanExponentTransportV1

noncomputable section

set_option autoImplicit false
set_option warningAsError true

/-!
# Closing a monotone open self-improvement at the limiting exponent

For a nondecreasing improvement function `nu`, positivity only at exponents
strictly larger than `beta` does not imply `0 < nu beta`.  That endpoint
condition is unnecessary when the property has a right-limit closure.

Fix any `target > beta`.  If `target < 1`, positivity of `nu target` and
monotonicity give the uniform lower bound

`nu target ≤ nu gamma` for `target < gamma ≤ 1`.

The existing finite uniform-step engine therefore proves `P target`.  If
`1 ≤ target`, exponent transport from the base case `P 1` proves the same
claim directly.  Thus `P gamma` holds for every `gamma > beta`, and an
explicit right-limit closure yields `P beta`.

No value or positivity assumption at `nu beta` is used.
-/

/-- Monotone open-interval improvement proves the property at every strict
super-target of `beta`. -/
theorem property_at_every_strict_super_target_of_monotone_improvement
    (P : Real → Prop) (nu : Real → Real) {beta : Real}
    (hbase : P 1)
    (htransport : ∀ ⦃lower upper : Real⦄,
      lower ≤ upper → P lower → P upper)
    (himprove : ∀ gamma : Real, beta < gamma → gamma ≤ 1 →
      P gamma → P (gamma - nu gamma))
    (hpositive : ∀ gamma : Real, beta < gamma → gamma ≤ 1 →
      0 < nu gamma)
    (hmonotone : Monotone nu) :
    ∀ target : Real, beta < target → P target := by
  intro target hbetaTarget
  by_cases htarget : target < 1
  · apply property_at_target_of_uniform_improvement
      P nu htarget (hpositive target hbetaTarget htarget.le)
      hbase htransport
    · intro gamma htargetGamma hgammaOne hP
      exact himprove gamma (hbetaTarget.trans htargetGamma) hgammaOne hP
    · intro gamma htargetGamma _hgammaOne
      exact hmonotone htargetGamma.le
  · exact htransport (le_of_not_gt htarget) hbase

/-- Abstract limit-closure theorem requiring positivity only on
`(beta, 1]`, never at `beta`. -/
theorem property_at_target_of_monotone_improvement_limit
    (P : Real → Prop) (nu : Real → Real) {beta : Real}
    (hbase : P 1)
    (htransport : ∀ ⦃lower upper : Real⦄,
      lower ≤ upper → P lower → P upper)
    (himprove : ∀ gamma : Real, beta < gamma → gamma ≤ 1 →
      P gamma → P (gamma - nu gamma))
    (hpositive : ∀ gamma : Real, beta < gamma → gamma ≤ 1 →
      0 < nu gamma)
    (hmonotone : Monotone nu)
    (hclosure : (∀ gamma : Real, beta < gamma → P gamma) → P beta) :
    P beta := by
  apply hclosure
  exact property_at_every_strict_super_target_of_monotone_improvement
    P nu hbase htransport himprove hpositive hmonotone

/-- Frostman-property specialization.  Its endpoint closure is the proved
epsilon-limit theorem `frostmanProperty_of_forall_gt`; no direct use of
`nu beta` remains. -/
theorem frostmanProperty_at_target_of_monotone_improvement_limit
    (nu : Real → Real) {beta : Real}
    (hbase : FrostmanProperty 1)
    (htransport : ∀ ⦃lower upper : Real⦄,
      lower ≤ upper → FrostmanProperty lower → FrostmanProperty upper)
    (himprove : ∀ gamma : Real, beta < gamma → gamma ≤ 1 →
      FrostmanProperty gamma →
        FrostmanProperty (gamma - nu gamma))
    (hpositive : ∀ gamma : Real, beta < gamma → gamma ≤ 1 →
      0 < nu gamma)
    (hmonotone : Monotone nu) :
    FrostmanProperty beta := by
  exact property_at_target_of_monotone_improvement_limit
    FrostmanProperty nu hbase htransport himprove hpositive hmonotone
      frostmanProperty_of_forall_gt

#print axioms
  property_at_every_strict_super_target_of_monotone_improvement
#print axioms property_at_target_of_monotone_improvement_limit
#print axioms frostmanProperty_at_target_of_monotone_improvement_limit

end

end Family8SelfImprovementLimitClosureV1
