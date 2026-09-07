import FamilyStickyGrounding.FamilyStickyHierarchyTerminalIdentityMultiscaleFrostmanBridgeV1
import Family8Grounding.Family8KatzTaoFrostmanPropertiesV1

set_option autoImplicit false
set_option warningAsError true

open scoped ENNReal NNReal

namespace Family8FrostmanAtEveryScaleInterfaceObstructionV1

open Submission.Kakeya.Uniformity
open Family8KatzTaoFrostmanPropertiesV1
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyScaleChainCoherentIntervalProducerV1
open FamilyStickyScaleChainSelectedCanonicalCoverCoordinatesProducerV1
open FamilyStickyCapturedTubeBoxWidthV1
open FamilyStickyHierarchyTerminalIdentityMultiscaleFrostmanBridgeV1

noncomputable section

/-!
# Why the current at-every-scale interface is not yet Theorem 7.3(A)

The paper fixes the genuine essentially-distinct thickening of one uniform
family at every scale.  The present `StickyMultiscaleCover` interface instead
allows an arbitrary supplied cover at each scale.  In particular, the
already-proved radius-changed identity cover has singleton parent fibres and
is Frostman at every scale for *every* formal `UniformTubeFamily`.

The two wrappers below record this fact at the exact Family 8 datum boundary.
Consequently a literal shaded-union lower bound cannot honestly be derived
from the bare existential availability of an
`IsFrostmanAtEveryScale` cover.  A completed §7.3(A) producer must additionally
bind the cover to the paper's coarse thickening, full activity, coarse
essential distinctness, branching uniformity, and the global cinematic
high/low mass charging.
-/

/-- Every formal uniform tube family admits the singleton-fibre identity
cover satisfying the current at-every-scale Frostman predicate. -/
theorem exists_identity_frostmanAtEveryScale
    {delta : NNReal} {iota : Type} [Fintype iota] [DecidableEq iota]
    (fine : UniformTubeFamily delta iota) (hdelta : 0 < delta) :
    exists C : CoherentStickyMultiscaleCover fine,
      C.base.IsFrostmanAtEveryScale (capturedTubeBoxLoss delta 1) := by
  exact ⟨identityRadiusCoherentCover fine,
    identityRadiusCoherentCover_isFrostmanAtEveryScale fine hdelta⟩

/-- The same obstruction at the actual Family 8 datum interface; the shading
plays no role in constructing the singleton-fibre cover. -/
theorem ActualTubeDatum.exists_identity_frostmanAtEveryScale
    {delta : NNReal} {iota : Type} [Fintype iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible) :
    exists C : CoherentStickyMultiscaleCover D.family,
      C.base.IsFrostmanAtEveryScale (capturedTubeBoxLoss delta 1) := by
  exact Family8FrostmanAtEveryScaleInterfaceObstructionV1.exists_identity_frostmanAtEveryScale D.family hD.delta_pos

#print axioms exists_identity_frostmanAtEveryScale
#print axioms ActualTubeDatum.exists_identity_frostmanAtEveryScale

end

end Family8FrostmanAtEveryScaleInterfaceObstructionV1
