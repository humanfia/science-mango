import FamilyStickyGrounding.FamilyStickyScaleChainParentFiberMassProducerV1

set_option autoImplicit false

open scoped ENNReal NNReal

namespace FamilyStickyScaleChainCoherentParentFiberMassProducerV1

open Submission.Kakeya.Uniformity
open FamilyStickyScaleChainCoherentIntervalProducerV1
open FamilyStickyScaleChainNestedMassLocalizationV1.StickyScaleCover
open FamilyStickyScaleChainCoherentTreeLocalizationV1
open FamilyStickyScaleChainParentFiberMassProducerV1.StickyScaleCover

noncomputable section

/-!
# Sticky Kakeya: coherent parent-fiber mass producer

This module totalizes the actual finite fiber/parent measure ratio on every
legal coherent interval, and uses it to construct the parent-fiber field of
`CoherentIntervalLocalizationGeometry`.  Only captured-thickening volume
control remains to be supplied.
-/

namespace CoherentIntervalLocalizationGeometry

variable {delta : NNReal} {iota : Type*}
  [Fintype iota] [DecidableEq iota]
  {fine : UniformTubeFamily delta iota}
  {depth : Nat}
  (C : CoherentStickyMultiscaleCover fine)
  (S : FamilyStickyDividingScalesFiniteStoppingV1.FiniteScaleSequence
    delta depth)

/-- Totalized actual parent-fiber loss for a coherent subinterval.  On legal
scales it is the literal supremum of finite fiber/parent mass ratios. -/
def coherentActualParentFiberMassLoss
    (m : Fin depth) (sigma rho : NNReal) : ENNReal :=
  if hTauSigma : S.tau m <= sigma then
    if hSigmaRho : sigma <= rho then
      if hRhoOne : rho <= 1 then
        actualParentFiberMassLoss
          (C.intervalScaleCover sigma rho
            ((S.delta_le_tau m).trans hTauSigma) hSigmaRho hRhoOne)
      else 0
    else 0
  else 0

@[simp] theorem coherentActualParentFiberMassLoss_eq
    (m : Fin depth) (sigma rho : NNReal)
    (hTauSigma : S.tau m <= sigma) (hSigmaRho : sigma <= rho)
    (hRhoOne : rho <= 1) :
    coherentActualParentFiberMassLoss C S m sigma rho =
      actualParentFiberMassLoss
        (C.intervalScaleCover sigma rho
          ((S.delta_le_tau m).trans hTauSigma) hSigmaRho hRhoOne) := by
  simp [coherentActualParentFiberMassLoss, hTauSigma, hSigmaRho, hRhoOne]

/-- Construct the coherent localization geometry after supplying only the
still-unproved captured-thickening volume control.  Parent-fiber mass is
generated automatically from the literal interval-cover measures. -/
def ofActualParentFiberMass
    (tau_pos : forall m, 0 < S.tau m)
    (bodyLoss : Fin depth -> NNReal -> NNReal -> ENNReal)
    (capturingThickening : forall m sigma rho
      (hTauSigma : S.tau m <= sigma) (hSigmaRho : sigma <= rho)
      (hRhoOne : rho <= 1),
      CapturingThickeningVolumeControl
        (C.intervalScaleCover sigma rho
          ((S.delta_le_tau m).trans hTauSigma) hSigmaRho hRhoOne)
        (bodyLoss m sigma rho)) :
    CoherentIntervalLocalizationGeometry C S where
  massLoss := coherentActualParentFiberMassLoss C S
  bodyLoss := bodyLoss
  parentFiberMass := by
    intro m sigma rho hTauSigma hSigmaRho hRhoOne
    rw [coherentActualParentFiberMassLoss_eq C S m sigma rho
      hTauSigma hSigmaRho hRhoOne]
    exact actualParentFiberMassMonotonicity
      (C.intervalScaleCover sigma rho
        ((S.delta_le_tau m).trans hTauSigma) hSigmaRho hRhoOne)
      ((tau_pos m).trans_le (hTauSigma.trans hSigmaRho))
  capturingThickening := capturingThickening

end CoherentIntervalLocalizationGeometry

#print axioms CoherentIntervalLocalizationGeometry.coherentActualParentFiberMassLoss_eq
#print axioms CoherentIntervalLocalizationGeometry.ofActualParentFiberMass

end
end FamilyStickyScaleChainCoherentParentFiberMassProducerV1
