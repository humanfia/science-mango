import Family8Grounding.Family8FrostmanHypothesesLossMonotonicityV1
import Family8Grounding.Family8Section8FixedPositiveSelfImprovementBudgetV3

/-!
# Canonical output hypothesis exponent for Section 8

The datum-level endpoint asks for a positive output exponent no larger than
the fixed Section 8 decrement, while the geometric producers consume the
source Frostman exponent.  Their canonical common choice is the minimum of
the source exponent and the fixed decrement.  Loss monotonicity then sends
the stronger output hypotheses back to the original source exponent.
-/

set_option autoImplicit false
set_option warningAsError true

open scoped ENNReal NNReal

namespace Family8SectionEightOutputEtaV1

open Submission.Kakeya.ConvexGeometry
open Family8FrostmanHypothesesLossMonotonicityV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8ParameterLadderV1
open Family8Section8FixedPositiveSelfImprovementBudgetV3

noncomputable section

def sectionEightOutputEta
    {epsilon0 beta gamma : Real}
    (P : ParameterLadder epsilon0 beta gamma)
    (sourceEta : Real) : Real :=
  min sourceEta (sectionEightFixedNu P)

theorem sectionEightOutputEta_pos
    {epsilon0 beta gamma sourceEta : Real}
    (P : ParameterLadder epsilon0 beta gamma)
    (hSourceEta : 0 < sourceEta) :
    0 < sectionEightOutputEta P sourceEta := by
  rw [sectionEightOutputEta, lt_min_iff]
  exact ⟨hSourceEta, sectionEightFixedNu_pos P⟩

theorem sectionEightOutputEta_le_source
    {epsilon0 beta gamma : Real}
    (P : ParameterLadder epsilon0 beta gamma)
    (sourceEta : Real) :
    sectionEightOutputEta P sourceEta <= sourceEta := by
  exact min_le_left _ _

theorem sectionEightOutputEta_le_fixedNu
    {epsilon0 beta gamma : Real}
    (P : ParameterLadder epsilon0 beta gamma)
    (sourceEta : Real) :
    sectionEightOutputEta P sourceEta <= sectionEightFixedNu P := by
  exact min_le_right _ _

theorem sourceFrostmanHypotheses_of_sectionEightOutputEta
    {delta : NNReal} {index : Type}
    [Fintype index] [DecidableEq index]
    {epsilon0 beta gamma sourceEta : Real}
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (P : ParameterLadder epsilon0 beta gamma)
    (hOutput : FrostmanHypotheses D
      (sectionEightOutputEta P sourceEta)) :
    FrostmanHypotheses D sourceEta := by
  exact frostmanHypotheses_of_eta_le D hD
    (sectionEightOutputEta_le_source P sourceEta) hOutput

#print axioms sectionEightOutputEta_pos
#print axioms sectionEightOutputEta_le_source
#print axioms sectionEightOutputEta_le_fixedNu
#print axioms sourceFrostmanHypotheses_of_sectionEightOutputEta

end
end Family8SectionEightOutputEtaV1
