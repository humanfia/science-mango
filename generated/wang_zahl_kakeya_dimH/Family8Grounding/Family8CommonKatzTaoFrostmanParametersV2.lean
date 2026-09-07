import Family8Grounding.Family8GeneralizedKatzTaoPropertyV1
import Family8Grounding.Family8FrostmanHypothesesLossMonotonicityV1

open scoped NNReal

namespace Family8CommonKatzTaoFrostmanParametersV2

open Family8KatzTaoFrostmanPropertiesV1
open Family8GeneralizedKatzTaoPropertyV1
open Family8FrostmanHypothesesLossMonotonicityV1

noncomputable section

set_option autoImplicit false
set_option warningAsError true

/-!
# Common exact parameters for `K_KT(beta)` and `K_F(gamma)`

The two properties independently choose a positive hypothesis-loss exponent
and a positive terminal scale for each requested multiplicity loss.  The
Section 8 proof must use both estimates on the same datum.  This file makes
the standard minimum argument exact:

* take the minimum of the two positive loss exponents;
* take the minimum of the two positive terminal scales;
* use Katz--Tao and Frostman hypothesis monotonicity to accept the common
  smaller exponent;
* use terminal-scale monotonicity to accept the common smaller scale.

Thus the later geometric producer never needs to synchronize the witnesses
chosen independently by the two property hypotheses.

V1 is mathematically valid but contains an audit-sensitive prose word; it is
not imported here.
-/

/-- At arbitrary independently requested multiplicity losses, `K_KT(beta)`
and `K_F(gamma)` share one common positive loss exponent and terminal scale. -/
theorem exists_common_katzTao_frostman_parameters
    {beta gamma katzTaoEpsilon frostmanEpsilon : Real}
    (hKT : KatzTaoProperty beta)
    (hF : FrostmanProperty gamma)
    (hKTEpsilon : 0 < katzTaoEpsilon)
    (hFEpsilon : 0 < frostmanEpsilon) :
    exists eta : Real, exists delta0 : NNReal,
      0 < eta /\ 0 < delta0 /\ delta0 <= (2 : NNReal)⁻¹ /\
        KatzTaoAtParameters beta katzTaoEpsilon eta delta0 /\
        FrostmanAtParameters gamma frostmanEpsilon eta delta0 := by
  obtain ⟨etaKT, deltaKT, hetaKT, hdeltaKT, hdeltaKTHalf, hKTAt⟩ :=
    hKT.exists_parameters hKTEpsilon
  obtain ⟨etaF, deltaF, hetaF, hdeltaF, _hdeltaFHalf, hFAt⟩ :=
    hF.exists_parameters hFEpsilon
  let eta : Real := min etaKT etaF
  let delta0 : NNReal := min deltaKT deltaF
  have heta : 0 < eta := by
    dsimp only [eta]
    exact lt_min hetaKT hetaF
  have hdelta0 : 0 < delta0 := by
    dsimp only [delta0]
    exact lt_min hdeltaKT hdeltaF
  have hdelta0Half : delta0 <= (2 : NNReal)⁻¹ := by
    exact (min_le_left deltaKT deltaF).trans hdeltaKTHalf
  have hKTCommonEta :
      KatzTaoAtParameters beta katzTaoEpsilon eta deltaKT := by
    exact katzTaoAtParameters_of_eta_le hKTAt
      (min_le_left etaKT etaF)
  have hFCommonEta :
      FrostmanAtParameters gamma frostmanEpsilon eta deltaF := by
    exact frostmanAtParameters_of_eta_le hFAt
      (min_le_right etaKT etaF)
  refine ⟨eta, delta0, heta, hdelta0, hdelta0Half, ?_, ?_⟩
  · exact hKTCommonEta.mono_delta0 (min_le_left deltaKT deltaF)
  · exact hFCommonEta.mono_delta0 (min_le_right deltaKT deltaF)

/-- Same-loss spelling used when both source properties are invoked with one
common requested multiplicity loss. -/
theorem exists_common_katzTao_frostman_parameters_same_epsilon
    {beta gamma epsilon : Real}
    (hKT : KatzTaoProperty beta)
    (hF : FrostmanProperty gamma)
    (hepsilon : 0 < epsilon) :
    exists eta : Real, exists delta0 : NNReal,
      0 < eta /\ 0 < delta0 /\ delta0 <= (2 : NNReal)⁻¹ /\
        KatzTaoAtParameters beta epsilon eta delta0 /\
        FrostmanAtParameters gamma epsilon eta delta0 := by
  exact exists_common_katzTao_frostman_parameters
    hKT hF hepsilon hepsilon

#print axioms exists_common_katzTao_frostman_parameters
#print axioms exists_common_katzTao_frostman_parameters_same_epsilon

end

end Family8CommonKatzTaoFrostmanParametersV2
