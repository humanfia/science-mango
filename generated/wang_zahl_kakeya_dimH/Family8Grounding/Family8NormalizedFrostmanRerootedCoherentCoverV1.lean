import Family8Grounding.Family8NormalizedCFDividingWitnessBridgeV2
import FamilyStickyGrounding.FamilyStickyScaleChainCoherentIntervalProducerV1

open scoped ENNReal NNReal

namespace Family8NormalizedFrostmanRerootedCoherentCoverV1

open Submission.Kakeya.Uniformity
open Family8NormalizedCFDividingWitnessBridgeV2.StickyScaleCover
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyScaleChainCoherentIntervalProducerV1

noncomputable section

set_option autoImplicit false
set_option warningAsError true

variable {delta : NNReal} {iota : Type*}
  [Fintype iota] [DecidableEq iota]
  {fine : UniformTubeFamily delta iota}

namespace CoherentStickyMultiscaleCover

/-- Re-root one coherent multiscale cover at an actual selected scale.

The new fine family is the literal coarse family selected by the original
cover at `tau`.  Its cover at every later radius and every cross-parent map
are inherited from the original coherent object; no fresh cover or
compatibility callback is introduced. -/
def reroot
    (C : CoherentStickyMultiscaleCover fine)
    (tau : NNReal) (hdeltaTau : delta <= tau) (hTauOne : tau <= 1) :
    CoherentStickyMultiscaleCover
      (C.base.cover tau hdeltaTau hTauOne).coarse where
  base := C.intervalMultiscaleCover tau hdeltaTau hTauOne
  parent := fun rho sigma hTauRho hRhoSigma hSigmaOne =>
    C.parent rho sigma (hdeltaTau.trans hTauRho) hRhoSigma hSigmaOne
  parent_mem := by
    intro rho sigma hTauRho hRhoSigma hSigmaOne k hk
    exact C.parent_mem rho sigma
      (hdeltaTau.trans hTauRho) hRhoSigma hSigmaOne k hk
  parent_surjective := by
    intro rho sigma hTauRho hRhoSigma hSigmaOne k hk
    exact C.parent_surjective rho sigma
      (hdeltaTau.trans hTauRho) hRhoSigma hSigmaOne k hk
  carrier_subset := by
    intro rho sigma hTauRho hRhoSigma hSigmaOne k hk
    exact C.carrier_subset rho sigma
      (hdeltaTau.trans hTauRho) hRhoSigma hSigmaOne k hk

@[simp] theorem reroot_base
    (C : CoherentStickyMultiscaleCover fine)
    (tau : NNReal) (hdeltaTau : delta <= tau) (hTauOne : tau <= 1) :
    (reroot C tau hdeltaTau hTauOne).base =
      C.intervalMultiscaleCover tau hdeltaTau hTauOne :=
  rfl

/-- A cover selected after re-rooting is definitionally the original literal
`tau -> rho` interval cover. -/
@[simp] theorem reroot_base_cover
    (C : CoherentStickyMultiscaleCover fine)
    (tau rho : NNReal) (hdeltaTau : delta <= tau)
    (hTauOne : tau <= 1) (hTauRho : tau <= rho)
    (hRhoOne : rho <= 1) :
    (reroot C tau hdeltaTau hTauOne).base.cover
        rho hTauRho hRhoOne =
      C.intervalScaleCover tau rho hdeltaTau hTauRho hRhoOne :=
  rfl

/-- Re-rooting is associative on literal interval covers: the child
`rho -> sigma` obtained inside the `tau`-rooted object is exactly the
original coherent `rho -> sigma` cover. -/
@[simp] theorem reroot_intervalScaleCover
    (C : CoherentStickyMultiscaleCover fine)
    (tau rho sigma : NNReal) (hdeltaTau : delta <= tau)
    (hTauOne : tau <= 1) (hTauRho : tau <= rho)
    (hRhoSigma : rho <= sigma) (hSigmaOne : sigma <= 1) :
    (reroot C tau hdeltaTau hTauOne).intervalScaleCover
        rho sigma hTauRho hRhoSigma hSigmaOne =
      C.intervalScaleCover rho sigma
        (hdeltaTau.trans hTauRho) hRhoSigma hSigmaOne :=
  rfl

/-- Consequently the upper child's normalized Frostman constant is computed
on the same actual cover before and after re-rooting. -/
@[simp] theorem reroot_interval_parentNormalizedFiberCFMax
    (C : CoherentStickyMultiscaleCover fine)
    (tau rho sigma : NNReal) (hdeltaTau : delta <= tau)
    (hTauOne : tau <= 1) (hTauRho : tau <= rho)
    (hRhoSigma : rho <= sigma) (hSigmaOne : sigma <= 1) :
    parentNormalizedFiberCFMax
        ((reroot C tau hdeltaTau hTauOne).intervalScaleCover
          rho sigma hTauRho hRhoSigma hSigmaOne) =
      parentNormalizedFiberCFMax
        (C.intervalScaleCover rho sigma
          (hdeltaTau.trans hTauRho) hRhoSigma hSigmaOne) :=
  rfl

#print axioms reroot
#print axioms reroot_intervalScaleCover
#print axioms reroot_interval_parentNormalizedFiberCFMax

end CoherentStickyMultiscaleCover

end
end Family8NormalizedFrostmanRerootedCoherentCoverV1
