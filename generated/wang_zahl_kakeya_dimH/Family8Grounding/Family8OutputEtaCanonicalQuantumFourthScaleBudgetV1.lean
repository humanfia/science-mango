import Family8Grounding.Family8CanonicalGlobalOuterParameterAllocationV1
import Family8Grounding.Family8SectionEightOutputEtaV1
import Mathlib.Tactic

/-!
# Output-eta budget for lossless fourth-scale absorption

The output exponent is at most the zero-stage ladder exponent, hence at most
`epsilon / 5`; the canonical quantum is at most `epsilon / 100`.  These fit
with ample room inside the four absolute buffered-scale powers.
-/

set_option autoImplicit false
set_option warningAsError true

namespace Family8OutputEtaCanonicalQuantumFourthScaleBudgetV1

open Family8CanonicalGlobalOuterParameterAllocationV1
open Family8ParameterLadderV1
open Family8Section8FixedPositiveSelfImprovementBudgetV3
open Family8SectionEightOutputEtaV1

noncomputable section

/-- The canonical small output exponent and one finite-constant quantum fit
inside the exact `4 * epsilon * (1-epsilon)` absolute-scale gain. -/
theorem outputEta_add_canonicalQuantum_le_four_epsilon_one_sub
    {epsilon0 beta gamma sourceEta : Real}
    (P : ParameterLadder epsilon0 beta gamma)
    (hepsilonHalf : P.epsilon <= 1 / 2) :
    sectionEightOutputEta P sourceEta +
        canonicalGlobalOuterQuantum P (sectionEightOutputEta P sourceEta) <=
      4 * (P.epsilon * (1 - P.epsilon)) := by
  have houtputFixed : sectionEightOutputEta P sourceEta <=
      sectionEightFixedNu P :=
    sectionEightOutputEta_le_fixedNu P sourceEta
  have hfixed : sectionEightFixedNu P <= P.epsilon / 5 := by
    exact P.eta_le_epsilon_div_five 0
  have hquantum :
      canonicalGlobalOuterQuantum P (sectionEightOutputEta P sourceEta) <=
        P.epsilon / 100 :=
    canonicalGlobalOuterQuantum_le_epsilon_div P
  nlinarith [P.epsilon_pos]

#print axioms outputEta_add_canonicalQuantum_le_four_epsilon_one_sub

end
end Family8OutputEtaCanonicalQuantumFourthScaleBudgetV1
