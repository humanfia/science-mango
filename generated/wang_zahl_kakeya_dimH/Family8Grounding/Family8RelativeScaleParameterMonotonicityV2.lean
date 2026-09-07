import Family8Grounding.Family8GeneralizedScaleTrivialBranchV1
import Mathlib.Tactic

open scoped ENNReal NNReal

namespace Family8RelativeScaleParameterMonotonicityV2

open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Family8KatzTaoFrostmanPropertiesV1
open Family8GeneralizedScalePropertiesV1
open Family8GeneralizedScaleTrivialBranchV1

noncomputable section

set_option autoImplicit false
set_option warningAsError true

/-!
# Relative-scale loss and terminal-scale monotonicity

The full generalized `K_KT` and `K_F` adapters choose their witnesses
independently.  To take common minima later, the relative-scale predicates
need the same monotonicity API already available at the original scale.

For every invocation, `tau <= delta <= 1/2`.  Thus hypotheses at a smaller
loss exponent imply hypotheses at a larger exponent, both for Katz--Tao and
Frostman nonconcentration.  Fixed-parameter theorems therefore accept any
smaller common loss exponent.  Shrinking the terminal scale is immediate.

V1 is a failed parser-precedence draft and is not imported.
-/

theorem katzTaoHypothesesAtRelativeScale_of_eta_le
    {delta tau : NNReal} {index : Type}
    [Fintype index] [DecidableEq index]
    {etaSmall etaLarge : Real}
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (htauDelta : tau <= delta) (heta : etaSmall <= etaLarge)
    (hsmall : KatzTaoHypothesesAtRelativeScale D tau etaSmall) :
    KatzTaoHypothesesAtRelativeScale D tau etaLarge := by
  have htauOneNN : tau <= (1 : NNReal) :=
    htauDelta.trans (hD.delta_le_half.trans (by norm_num))
  have htauOne : (tau : ENNReal) <= 1 := by
    exact_mod_cast htauOneNN
  constructor
  · exact
      (ENNReal.rpow_le_rpow_of_exponent_ge htauOne heta).trans hsmall.1
  · exact hsmall.2.trans
      (ENNReal.rpow_le_rpow_of_exponent_ge htauOne (by linarith))

theorem frostmanHypothesesAtRelativeScale_of_eta_le
    {delta tau : NNReal} {index : Type}
    [Fintype index] [DecidableEq index]
    {etaSmall etaLarge : Real}
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (htauDelta : tau <= delta) (heta : etaSmall <= etaLarge)
    (hsmall : FrostmanHypothesesAtRelativeScale D tau etaSmall) :
    FrostmanHypothesesAtRelativeScale D tau etaLarge := by
  have htauOneNN : tau <= (1 : NNReal) :=
    htauDelta.trans (hD.delta_le_half.trans (by norm_num))
  have htauOne : (tau : ENNReal) <= 1 := by
    exact_mod_cast htauOneNN
  constructor
  · exact
      (ENNReal.rpow_le_rpow_of_exponent_ge htauOne heta).trans hsmall.1
  · exact hsmall.2.mono
      (ENNReal.rpow_le_rpow_of_exponent_ge htauOne (by linarith))

theorem katzTaoAtNontrivialRelativeScaleParameters_of_eta_le
    {beta epsilon etaSmall etaLarge : Real} {delta0 : NNReal}
    (h : KatzTaoAtNontrivialRelativeScaleParameters
      beta epsilon etaLarge delta0)
    (heta : etaSmall <= etaLarge) :
    KatzTaoAtNontrivialRelativeScaleParameters
      beta epsilon etaSmall delta0 := by
  intro delta tau index _ _ D hD hdelta htau htauDelta hthreshold hsmall
  exact h delta tau index D hD hdelta htau htauDelta hthreshold
    (katzTaoHypothesesAtRelativeScale_of_eta_le
      D hD htauDelta heta hsmall)

theorem frostmanAtNontrivialRelativeScaleParameters_of_eta_le
    {beta epsilon etaSmall etaLarge : Real} {delta0 : NNReal}
    (h : FrostmanAtNontrivialRelativeScaleParameters
      beta epsilon etaLarge delta0)
    (heta : etaSmall <= etaLarge) :
    FrostmanAtNontrivialRelativeScaleParameters
      beta epsilon etaSmall delta0 := by
  intro delta tau index _ _ D hD hdelta htau htauDelta hthreshold hsmall
  exact h delta tau index D hD hdelta htau htauDelta hthreshold
    (frostmanHypothesesAtRelativeScale_of_eta_le
      D hD htauDelta heta hsmall)

theorem katzTaoAtRelativeScaleParameters_of_eta_le
    {beta epsilon etaSmall etaLarge : Real} {delta0 : NNReal}
    (h : KatzTaoAtRelativeScaleParameters beta epsilon etaLarge delta0)
    (heta : etaSmall <= etaLarge) :
    KatzTaoAtRelativeScaleParameters beta epsilon etaSmall delta0 := by
  intro delta tau index _ _ D hD hdelta htau htauDelta hsmall
  exact h delta tau index D hD hdelta htau htauDelta
    (katzTaoHypothesesAtRelativeScale_of_eta_le
      D hD htauDelta heta hsmall)

theorem frostmanAtRelativeScaleParameters_of_eta_le
    {beta epsilon etaSmall etaLarge : Real} {delta0 : NNReal}
    (h : FrostmanAtRelativeScaleParameters beta epsilon etaLarge delta0)
    (heta : etaSmall <= etaLarge) :
    FrostmanAtRelativeScaleParameters beta epsilon etaSmall delta0 := by
  intro delta tau index _ _ D hD hdelta htau htauDelta hsmall
  exact h delta tau index D hD hdelta htau htauDelta
    (frostmanHypothesesAtRelativeScale_of_eta_le
      D hD htauDelta heta hsmall)

theorem katzTaoAtRelativeScaleParameters_mono_delta0
    {beta epsilon eta : Real} {delta0 delta0' : NNReal}
    (h : KatzTaoAtRelativeScaleParameters beta epsilon eta delta0)
    (hsmall : delta0' <= delta0) :
    KatzTaoAtRelativeScaleParameters beta epsilon eta delta0' := by
  intro delta tau index _ _ D hD hdelta htau htauDelta hrelative
  exact h delta tau index D hD (hdelta.trans hsmall)
    htau htauDelta hrelative

theorem frostmanAtRelativeScaleParameters_mono_delta0
    {beta epsilon eta : Real} {delta0 delta0' : NNReal}
    (h : FrostmanAtRelativeScaleParameters beta epsilon eta delta0)
    (hsmall : delta0' <= delta0) :
    FrostmanAtRelativeScaleParameters beta epsilon eta delta0' := by
  intro delta tau index _ _ D hD hdelta htau htauDelta hrelative
  exact h delta tau index D hD (hdelta.trans hsmall)
    htau htauDelta hrelative

#print axioms katzTaoHypothesesAtRelativeScale_of_eta_le
#print axioms frostmanHypothesesAtRelativeScale_of_eta_le
#print axioms katzTaoAtNontrivialRelativeScaleParameters_of_eta_le
#print axioms frostmanAtNontrivialRelativeScaleParameters_of_eta_le
#print axioms katzTaoAtRelativeScaleParameters_of_eta_le
#print axioms frostmanAtRelativeScaleParameters_of_eta_le
#print axioms katzTaoAtRelativeScaleParameters_mono_delta0
#print axioms frostmanAtRelativeScaleParameters_mono_delta0

end

end Family8RelativeScaleParameterMonotonicityV2
