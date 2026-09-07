import Family8Grounding.Family8StickyScaleCoverActiveFineRestrictionV2
import Family8Grounding.Family8StickySelectedParentGreedyBlockFrostmanV3
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

open Set MeasureTheory
open scoped ENNReal NNReal

namespace Family8StickyActiveRestrictedCoarseKatzTaoV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open FamilyStickyAtEveryScaleCoreV1
open Family8StickyScaleCoverActiveFineRestrictionV2.ScaleCover
open Family8StickySelectedParentGreedyBlockFrostmanV3

noncomputable section

/-!
# Katz--Tao transport through the active-coarse Fin reindexing

The fully active restricted scale cover changes only the finite index type of
the actual active parents.  Its coarse tube bodies are pointwise identical
under `Finset.equivFin`, hence Katz--Tao concentration transports with no
loss.  This closes the type seam between `StickyScaleCover.IsKatzTaoAtScale`
and the literal coarse family consumed by the frozen B2 connector.
-/

variable {delta rho : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {fine : UniformTubeFamily delta index}

/-- The actual reindexed parent type is equivalent to the active-parent
subtype of the original cover. -/
noncomputable def restrictedCoarseEquivActive
    (S : StickyScaleCover fine rho) :
    Fin (activeFineRestrictedScaleCover S).coarseCard ≃
      {k // k ∈ S.activeCoarse} :=
  S.activeCoarse.equivFin.symm

/-- The equivalence preserves the actual coarse tube body pointwise. -/
@[simp] theorem restrictedCoarse_body_eq_activeCoarseBody
    (S : StickyScaleCover fine rho)
    (q : Fin (activeFineRestrictedScaleCover S).coarseCard) :
    (activeFineRestrictedScaleCover S).coarse.bodyFamily q =
      S.activeCoarseFamily (restrictedCoarseEquivActive S q) := by
  rfl

/-- Katz--Tao at the original active-parent scale transports exactly to the
fully active Fin-indexed coarse family used by a frozen assembly. -/
theorem activeFineRestrictedScaleCover_coarse_isKatzTao
    (S : StickyScaleCover fine rho) {C : ENNReal}
    (hKT : S.IsKatzTaoAtScale C) :
    IsKatzTao C (activeFineRestrictedScaleCover S).coarse.bodyFamily := by
  apply isKatzTao_iff_concentration_le.mpr
  intro K
  rw [concentration_eq_of_bodyPreservingEquiv
    (restrictedCoarseEquivActive S)
    (activeFineRestrictedScaleCover S).coarse.bodyFamily
    S.activeCoarseFamily
    (restrictedCoarse_body_eq_activeCoarseBody S) K]
  exact hKT K

#print axioms restrictedCoarseEquivActive
#print axioms restrictedCoarse_body_eq_activeCoarseBody
#print axioms activeFineRestrictedScaleCover_coarse_isKatzTao

end
end Family8StickyActiveRestrictedCoarseKatzTaoV1
