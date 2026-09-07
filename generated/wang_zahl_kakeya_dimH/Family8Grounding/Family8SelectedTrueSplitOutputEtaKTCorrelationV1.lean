import Family8Grounding.Family8ParameterSelectedTrueSplitEtaStrongFrostmanLongCoreOnlyMainLemmaV3

/-!
# Selected true-split output exponent: `etaKT` correlation

This file contains only the numerical interface needed to correlate the
selected source exponent with an `etaKT` budget.  In particular, it does not
alter the legacy parameter-selection modules or state a Family 8 endpoint.
-/

set_option autoImplicit false
set_option warningAsError true

namespace Family8SelectedTrueSplitOutputEtaKTCorrelationV1

open Family8ParameterLadderV1
open Family8ParameterSelectedTrueSplitEtaStrongFrostmanLongCoreOnlyMainLemmaV3

noncomputable section

/-- If `thirdEta` is capped by half of `etaKT`, the sixteen source copies fit
inside the `etaKT` budget.  No positivity assumption on `thirdEta` is needed:
the two sign cases use, respectively, `P.epsilon_pos` and
`P.epsilon < 1`. -/
theorem sixteen_mul_selectedTrueSplitOutputEta_le_etaKT
    {epsilon0 beta gamma thirdEta etaKT : Real}
    (P : ParameterLadder epsilon0 beta gamma)
    (hEpsilonOne : P.epsilon < 1)
    (hEtaKT : 0 < etaKT)
    (hThirdEtaCap : thirdEta <= etaKT / 2) :
    16 * selectedTrueSplitOutputEta P thirdEta <= etaKT := by
  unfold selectedTrueSplitOutputEta
  by_cases hThirdEta : 0 <= thirdEta
  · have hFactorLe : 1 - P.epsilon <= 1 := by
      linarith [P.epsilon_pos]
    have hMulLe : (1 - P.epsilon) * thirdEta <= thirdEta := by
      simpa using mul_le_mul_of_nonneg_right hFactorLe hThirdEta
    nlinarith
  · have hThirdEtaNonpos : thirdEta <= 0 := le_of_not_ge hThirdEta
    have hFactorNonneg : 0 <= 1 - P.epsilon := by
      linarith
    have hMulNonpos : (1 - P.epsilon) * thirdEta <= 0 :=
      mul_nonpos_of_nonneg_of_nonpos hFactorNonneg hThirdEtaNonpos
    nlinarith

/-- The top-level third exponent simultaneously respects the raw producer,
the parameter ladder, and one half of the `etaKT` budget. -/
def selectedTrueSplitTopThirdEta
    {epsilon0 beta gamma : Real}
    (P : ParameterLadder epsilon0 beta gamma)
    (etaThirdRaw etaKT : Real) : Real :=
  min etaThirdRaw (min (P.eta 0) (etaKT / 2))

theorem selectedTrueSplitTopThirdEta_pos
    {epsilon0 beta gamma etaThirdRaw etaKT : Real}
    (P : ParameterLadder epsilon0 beta gamma)
    (hEtaThirdRaw : 0 < etaThirdRaw)
    (hEtaKT : 0 < etaKT) :
    0 < selectedTrueSplitTopThirdEta P etaThirdRaw etaKT := by
  unfold selectedTrueSplitTopThirdEta
  exact lt_min hEtaThirdRaw (lt_min (P.eta_pos 0) (by linarith))

theorem selectedTrueSplitTopThirdEta_le_raw
    {epsilon0 beta gamma etaThirdRaw etaKT : Real}
    (P : ParameterLadder epsilon0 beta gamma) :
    selectedTrueSplitTopThirdEta P etaThirdRaw etaKT <= etaThirdRaw := by
  unfold selectedTrueSplitTopThirdEta
  exact min_le_left _ _

theorem selectedTrueSplitTopThirdEta_le_eta_zero
    {epsilon0 beta gamma etaThirdRaw etaKT : Real}
    (P : ParameterLadder epsilon0 beta gamma) :
    selectedTrueSplitTopThirdEta P etaThirdRaw etaKT <= P.eta 0 := by
  unfold selectedTrueSplitTopThirdEta
  exact (min_le_right _ _).trans (min_le_left _ _)

/-- All facts consumed by the top-level caller, bundled without exposing an
extra half-budget lemma. -/
theorem selectedTrueSplitTopThirdEta_correlation_bundle
    {epsilon0 beta gamma etaThirdRaw etaKT : Real}
    (P : ParameterLadder epsilon0 beta gamma)
    (hEtaThirdRaw : 0 < etaThirdRaw)
    (hEtaKT : 0 < etaKT) :
    0 < selectedTrueSplitTopThirdEta P etaThirdRaw etaKT /\
      selectedTrueSplitTopThirdEta P etaThirdRaw etaKT <= etaThirdRaw /\
      selectedTrueSplitTopThirdEta P etaThirdRaw etaKT <= P.eta 0 /\
      16 * selectedTrueSplitOutputEta P
          (selectedTrueSplitTopThirdEta P etaThirdRaw etaKT) <= etaKT := by
  have hPositive := selectedTrueSplitTopThirdEta_pos
    P hEtaThirdRaw hEtaKT
  have hRaw := selectedTrueSplitTopThirdEta_le_raw
    (P := P) (etaThirdRaw := etaThirdRaw) (etaKT := etaKT)
  have hEtaZero := selectedTrueSplitTopThirdEta_le_eta_zero
    (P := P) (etaThirdRaw := etaThirdRaw) (etaKT := etaKT)
  have hHalf :
      selectedTrueSplitTopThirdEta P etaThirdRaw etaKT <= etaKT / 2 := by
    unfold selectedTrueSplitTopThirdEta
    exact (min_le_right _ _).trans (min_le_right _ _)
  have hFactorLe : 1 - P.epsilon <= 1 := by
    linarith [P.epsilon_pos]
  have hMulLe :
      (1 - P.epsilon) *
          selectedTrueSplitTopThirdEta P etaThirdRaw etaKT <=
        selectedTrueSplitTopThirdEta P etaThirdRaw etaKT := by
    simpa using mul_le_mul_of_nonneg_right hFactorLe hPositive.le
  have hCorrelation :
      16 * selectedTrueSplitOutputEta P
          (selectedTrueSplitTopThirdEta P etaThirdRaw etaKT) <= etaKT := by
    unfold selectedTrueSplitOutputEta
    nlinarith
  exact ⟨hPositive, hRaw, hEtaZero, hCorrelation⟩

#print axioms sixteen_mul_selectedTrueSplitOutputEta_le_etaKT
#print axioms selectedTrueSplitTopThirdEta_pos
#print axioms selectedTrueSplitTopThirdEta_le_raw
#print axioms selectedTrueSplitTopThirdEta_le_eta_zero
#print axioms selectedTrueSplitTopThirdEta_correlation_bundle

end
end Family8SelectedTrueSplitOutputEtaKTCorrelationV1
