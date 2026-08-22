import FamilyStickyGrounding.FamilyStickyDeltaMaxFiniteChainV2

open scoped ENNReal NNReal

namespace FamilyStickyAdjacentScaleStepV2

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDeltaMaxFiniteChainV2.StickyScaleCover

noncomputable section

/-!
# Sticky Kakeya: the honest adjacent-scale interface

This module packages only the part of the adjacent-scale estimate that the
current finite-family API can prove without new geometry.  Both sides are
literal maximal concentrations of the supplied cover: the fine active
family, the worst actual parent fiber, and the actual active coarse family.

The remaining field is pointwise in the test convex body.  It is the missing
geometric cross-scale comparison (the source proof constructs a thickened
test body at the parent scale).  Taking its `iSup` is proved below.  Thus the
one-step `Delta_max` inequality is not accepted as a final sticky callback.
-/

namespace StickyScaleCover

variable {delta rho : NNReal} {iota : Type*}
  [Fintype iota] [DecidableEq iota]
  {fine : UniformTubeFamily delta iota}

/-- The genuine active fine family at the lower endpoint of this cover. -/
def activeFineFamily (S : StickyScaleCover fine rho) :
    ConvexFamily {i // i ∈ S.activeFine} :=
  fun i => fine.bodyFamily i.1

/-- The lower-end `Delta_max`, with no abstract scalar substituted for it. -/
def fineDeltaMax (S : StickyScaleCover fine rho) : ENNReal :=
  maximalConcentration (activeFineFamily S)

/-- Exact residual left by the current geometry API.

For each test body, the source proof must relate its contained fine mass to a
parent-scale thickening, then separate the coarse-family concentration from
the worst rescaled fiber concentration.  The repository currently exposes
neither that thickened test-body construction nor its volume comparison. -/
def HasAdjacentTestBodyCrossBound
    (S : StickyScaleCover fine rho) (dimensionalLoss : ENNReal) : Prop :=
  ∀ K : ConvexBody Space,
    concentration (activeFineFamily S) K ≤
      (dimensionalLoss * fiberDeltaMax S) * coarseDeltaMax S

/-- The available producer: the pointwise geometric comparison yields the
actual adjacent-scale maximal-concentration inequality by taking `iSup`. -/
theorem fineDeltaMax_le_of_hasAdjacentTestBodyCrossBound
    (S : StickyScaleCover fine rho) (dimensionalLoss : ENNReal)
    (hcross : HasAdjacentTestBodyCrossBound S dimensionalLoss) :
    fineDeltaMax S ≤
      (dimensionalLoss * fiberDeltaMax S) * coarseDeltaMax S := by
  apply iSup_le
  exact hcross

/-- Adapter to the scalar shape consumed by `FiniteDeltaMaxChain.step_le`.
The fine and coarse values remain the actual values of the same cover. -/
theorem adjacent_step_le
    (S : StickyScaleCover fine rho) (dimensionalLoss : ENNReal)
    (hcross : HasAdjacentTestBodyCrossBound S dimensionalLoss) :
    fineDeltaMax S ≤
      (dimensionalLoss * fiberDeltaMax S) * coarseDeltaMax S :=
  fineDeltaMax_le_of_hasAdjacentTestBodyCrossBound S dimensionalLoss hcross

end StickyScaleCover

#print axioms StickyScaleCover.fineDeltaMax_le_of_hasAdjacentTestBodyCrossBound
#print axioms StickyScaleCover.adjacent_step_le

end

end FamilyStickyAdjacentScaleStepV2
