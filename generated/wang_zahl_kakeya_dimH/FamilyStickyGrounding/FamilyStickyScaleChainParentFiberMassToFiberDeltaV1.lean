import FamilyStickyGrounding.FamilyStickyScaleChainParentFiberMassProducerV1

set_option autoImplicit false

open Set
open scoped ENNReal NNReal

namespace FamilyStickyScaleChainParentFiberMassToFiberDeltaV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDeltaMaxFiniteChainV2.StickyScaleCover
open FamilyStickyScaleChainParentFiberMassProducerV1.StickyScaleCover

noncomputable section

/-!
# Parent-fiber mass is an actual fiber concentration

Every member of one literal parent fiber lies in that parent tube.  Hence
the fiber/parent mass ratio is the concentration of that fiber evaluated at
the parent body, and is bounded by the genuine `fiberDeltaMax`.
-/

namespace StickyScaleCover

variable {delta rho : NNReal} {iota : Type*}
  [Fintype iota] [DecidableEq iota]
  {fine : UniformTubeFamily delta iota}
  (S : StickyScaleCover fine rho)

/-- All indices in a literal fiber are contained in its actual parent body. -/
theorem containedIndices_fiberFamily_parent_eq_univ
    (k : {k // k ∈ S.activeCoarse}) :
    containedIndices (S.fiberFamily k.1) (S.activeCoarseFamily k) =
      Finset.univ := by
  classical
  apply Finset.eq_univ_iff_forall.mpr
  intro i
  rw [mem_containedIndices]
  simpa [StickyScaleCover.fiberFamily, StickyScaleCover.activeCoarseFamily,
    UniformTubeFamily.bodyFamily, Tube.coe_body] using
    S.fiber_carrier_subset_parent k.1 i

/-- The literal mass ratio is exactly a genuine fiber concentration. -/
theorem parentFiberMassRatio_eq_concentration_parent
    (k : {k // k ∈ S.activeCoarse}) :
    parentFiberMassRatio S k =
      concentration (S.fiberFamily k.1) (S.activeCoarseFamily k) := by
  unfold parentFiberMassRatio concentration familyVolume
  rw [containedIndices_fiberFamily_parent_eq_univ S k]

/-- Every parent-fiber mass ratio is bounded by the actual adjacent fiber
maximal concentration. -/
theorem parentFiberMassRatio_le_fiberDeltaMax
    (k : {k // k ∈ S.activeCoarse}) :
    parentFiberMassRatio S k ≤ fiberDeltaMax S := by
  rw [parentFiberMassRatio_eq_concentration_parent S k]
  exact (concentration_le_maximalConcentration
      (S.fiberFamily k.1) (S.activeCoarseFamily k)).trans
    (maximalConcentration_fiber_le_fiberDeltaMax S k)

/-- The computed supremum used by local geometry is bounded by the genuine
fiber value; no additional mass-loss exponent is needed. -/
theorem actualParentFiberMassLoss_le_fiberDeltaMax :
    actualParentFiberMassLoss S ≤ fiberDeltaMax S := by
  apply iSup_le
  exact parentFiberMassRatio_le_fiberDeltaMax S

#print axioms containedIndices_fiberFamily_parent_eq_univ
#print axioms parentFiberMassRatio_eq_concentration_parent
#print axioms parentFiberMassRatio_le_fiberDeltaMax
#print axioms actualParentFiberMassLoss_le_fiberDeltaMax

end StickyScaleCover

end
end FamilyStickyScaleChainParentFiberMassToFiberDeltaV1
