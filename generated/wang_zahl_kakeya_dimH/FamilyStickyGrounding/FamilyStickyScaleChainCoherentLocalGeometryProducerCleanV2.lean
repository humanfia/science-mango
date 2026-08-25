import FamilyStickyGrounding.FamilyStickyScaleChainCapturingThickeningProducerCleanV2
import FamilyStickyGrounding.FamilyStickyScaleChainCoherentParentFiberMassProducerV1

set_option autoImplicit false

open scoped ENNReal NNReal

namespace FamilyStickyScaleChainCoherentLocalGeometryProducerV1

open Submission.Kakeya.Uniformity
open FamilyStickyScaleChainCoherentIntervalProducerV1
open FamilyStickyScaleChainCoherentTreeLocalizationV1
open FamilyStickyScaleChainCoherentParentFiberMassProducerV1
open FamilyStickyScaleChainCapturingThickeningProducerV1.StickyScaleCover
open FamilyStickyCapturedTubeBoxWidthV1

noncomputable section

/-!
# Fully actual coherent local geometry

For the interval `[sigma,rho]`, the actual fine family consists of the
chosen radius-`sigma` tubes.  Positivity of `tau_m` therefore makes the
captured-tube John-box producer applicable.  Together with the already
automatic parent-fiber ratio, this removes both local numerical inequalities
from the constructor input.
-/

namespace CoherentIntervalLocalizationGeometry

variable {delta : NNReal} {iota : Type*}
  [Fintype iota] [DecidableEq iota]
  {fine : UniformTubeFamily delta iota}
  {depth : Nat}
  (C : CoherentStickyMultiscaleCover fine)
  (S : FamilyStickyDividingScalesFiniteStoppingV1.FiniteScaleSequence
    delta depth)

/-- The explicit interval body loss: one longitudinal constant factor and
two transverse `rho/sigma` factors. -/
def coherentCapturedTubeBoxLoss
    (_m : Fin depth) (sigma rho : NNReal) : ENNReal :=
  capturedTubeBoxLoss sigma rho

/-- Construct all coherent localization geometry from the actual interval
covers.  The sole input is scale positivity; neither parent-fiber mass nor
captured-thickening volume comparison is supplied by the caller. -/
def ofActualLocalGeometry
    (tau_pos : ∀ m, 0 < S.tau m) :
    CoherentIntervalLocalizationGeometry C S :=
  CoherentIntervalLocalizationGeometry.ofActualParentFiberMass C S tau_pos
    coherentCapturedTubeBoxLoss (by
      intro m sigma rho hTauSigma hSigmaRho hRhoOne
      exact actualCapturingThickeningVolumeControl
        (C.intervalScaleCover sigma rho
          ((S.delta_le_tau m).trans hTauSigma) hSigmaRho hRhoOne)
        ((tau_pos m).trans_le hTauSigma))

@[simp] theorem ofActualLocalGeometry_bodyLoss
    (tau_pos : ∀ m, 0 < S.tau m)
    (m : Fin depth) (sigma rho : NNReal) :
    (ofActualLocalGeometry C S tau_pos).bodyLoss m sigma rho =
      capturedTubeBoxLoss sigma rho := by
  rfl

#print axioms ofActualLocalGeometry
#print axioms ofActualLocalGeometry_bodyLoss

end CoherentIntervalLocalizationGeometry

end
end FamilyStickyScaleChainCoherentLocalGeometryProducerV1
