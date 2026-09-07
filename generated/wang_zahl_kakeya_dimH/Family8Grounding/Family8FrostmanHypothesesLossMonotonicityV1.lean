import Family8Grounding.Family8KatzTaoFrostmanPropertiesV1
import Mathlib.Tactic

open scoped ENNReal NNReal

namespace Family8FrostmanHypothesesLossMonotonicityV1

open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Family8KatzTaoFrostmanPropertiesV1

noncomputable section

set_option autoImplicit false
set_option warningAsError true

/-!
# Frostman loss-exponent monotonicity

The generalized Katz--Tao property module already proves the analogous
bridge for `KatzTaoHypotheses`.  This file supplies the missing Frostman
counterpart needed when the final one-step proof takes a minimum of several
positive loss exponents.

On an admissible scale `delta <= 1/2`, decreasing the hypothesis exponent
makes both premises stronger: the required shading-density floor increases,
while the allowed Frostman constant decreases.  Hence hypotheses at
`etaSmall` imply hypotheses at `etaLarge` whenever
`etaSmall <= etaLarge`.
-/

/-- Frostman hypotheses with a smaller loss exponent imply those with a
larger loss exponent on every admissible datum. -/
theorem frostmanHypotheses_of_eta_le
    {delta : NNReal} {index : Type}
    [Fintype index] [DecidableEq index]
    {etaSmall etaLarge : Real}
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (heta : etaSmall <= etaLarge)
    (hsmall : FrostmanHypotheses D etaSmall) :
    FrostmanHypotheses D etaLarge := by
  have hdeltaOne : (delta : ENNReal) <= 1 := by
    exact_mod_cast hD.delta_le_half.trans (by norm_num)
  constructor
  · exact
      (ENNReal.rpow_le_rpow_of_exponent_ge hdeltaOne heta).trans hsmall.1
  · exact hsmall.2.mono
      (ENNReal.rpow_le_rpow_of_exponent_ge hdeltaOne (by linarith))

/-- A fixed-parameter Frostman theorem accepting a larger loss exponent can
be applied to data satisfying any smaller loss exponent. -/
theorem frostmanAtParameters_of_eta_le
    {beta epsilon etaSmall etaLarge : Real} {delta0 : NNReal}
    (h : FrostmanAtParameters beta epsilon etaLarge delta0)
    (heta : etaSmall <= etaLarge) :
    FrostmanAtParameters beta epsilon etaSmall delta0 := by
  intro delta index _ _ D hD hdelta hsmall
  exact h delta index D hD hdelta
    (frostmanHypotheses_of_eta_le D hD heta hsmall)

#print axioms frostmanHypotheses_of_eta_le
#print axioms frostmanAtParameters_of_eta_le

end

end Family8FrostmanHypothesesLossMonotonicityV1
