import Family8Grounding.Family8DoubledParentConflictWeightedCWAInheritanceV2
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8DoubledParentConflictWeightedDef212WitnessV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.Uniformity
open Family8Def212ConvexWolffAtEveryScaleV2
open Family8Def212ConvexWolffAtEveryScaleV2.ScaleCover
open Family8DoubledParentConflictClusteringV2.ScaleCover
open Family8DoubledParentConflictWeightedRetentionV3.ScaleCover
open Family8DoubledParentConflictWeightedRestrictedCoverEndpointV2.ScaleCover
open Family8DoubledParentConflictWeightedCWAInheritanceV2.ScaleCover
open FamilyStickyAtEveryScaleCoreV1

noncomputable section

/-!
# A quantitative doubled-parent selection as an actual Def. 2.12 witness

The selected-parent endpoint already carries one conflict-free restricted
cover, its unchanged uniformity constant, and paper essential distinctness.
The CWA inheritance theorem supplies the last fibrewise field after the John
normalizations are restricted by parent reindexing.  This module packages all
of those facts into one literal `Def212ScaleWitness`, while retaining the same
weighted selection and hence its cardinality and mass inequalities.
-/

namespace ScaleCover

variable {delta rho rho0 Cnn : NNReal}
variable {index : Type} [Fintype index] [DecidableEq index]
variable {fine : UniformTubeFamily delta index}
variable {S : StickyScaleCover fine rho}
variable {weight : Fin S.coarseCard → ENNReal} {B : ENNReal}

/-- The quantitative endpoint and the paper scale witness are kept on the
same selected family, so the selection's cardinality and arbitrary-mass
retention evidence remains directly available. -/
structure WeightedDef212ScaleEndpoint
    (S : StickyScaleCover fine rho)
    (weight : Fin S.coarseCard → ENNReal) (B : ENNReal)
    (rho0 Cnn : NNReal) where
  restricted :
    WeightedRestrictedCoverEndpoint S weight B (Cnn : ENNReal)
  witness :
    Def212ScaleWitness
      (weightedSelectedAssignedFineFamily restricted.selection) rho0 Cnn

namespace WeightedDef212ScaleEndpoint

/-- The original occupied-parent cardinality is retained with the exact
closed-conflict-neighbourhood loss stored by the common selection. -/
theorem activeCoarse_card_le
    (E : WeightedDef212ScaleEndpoint S weight B rho0 Cnn) :
    (S.activeCoarse.card : ENNReal) ≤
      B * (E.restricted.selection.selected.card : ENNReal) :=
  E.restricted.selection.card_le

/-- The same selection retains the requested arbitrary parent weight with
the identical loss. -/
theorem activeCoarse_weight_le
    (E : WeightedDef212ScaleEndpoint S weight B rho0 Cnn) :
    (∑ k ∈ S.activeCoarse, weight k) ≤
      B * ∑ k ∈ E.restricted.selection.selected, weight k :=
  E.restricted.selection.mass_le

end WeightedDef212ScaleEndpoint

/-- A bounded literal doubled-parent conflict neighbourhood produces an
actual paper scale witness on the retained fine family.  No new CWA callback
is assumed: the source fibrewise CWA is transported through the exact fibre
equivalence of the restricted cover. -/
theorem exists_weightedDef212ScaleEndpoint
    (S : StickyScaleCover fine rho)
    (weight : Fin S.coarseCard → ENNReal) (B : ENNReal)
    (hrho0 : rho0 ≤ rho) (hrhoOne : rho ≤ 1)
    (hrhoWindow : rho < Cnn * rho0)
    (R : UnitRescalingGeometry S)
    (hCWA : R.FibresSatisfyCWA (Cnn : ENNReal))
    (hneighbour : ClosedDoubledParentConflictDegreeBound S B)
    (huniform : IsCUniform S (Cnn : ENNReal))
    (hpaper : Set.Pairwise (Set.univ : Set index) fun i j ↦
      PaperEssentiallyDistinct (fine.tubes i) (fine.tubes j)) :
    Nonempty (WeightedDef212ScaleEndpoint S weight B rho0 Cnn) := by
  obtain ⟨E⟩ := exists_weightedRestrictedCoverEndpoint
    S weight B (Cnn : ENNReal) hneighbour huniform hpaper
  let Rselected :=
    Family8DoubledParentConflictWeightedRestrictedCoverEndpointV2.ScaleCover.UnitRescalingGeometry.restrictToWeightedSelection
      R E.selection
  have hselectedCWA : Rselected.FibresSatisfyCWA (Cnn : ENNReal) :=
    UnitRescalingGeometry.fibresSatisfyCWA_restrictToWeightedSelection
      R E.selection hCWA
  exact ⟨
    { restricted := E
      witness :=
        { rho := rho
          rho0_le_rho := hrho0
          rho_le_one := hrhoOne
          rho_lt_C_mul_rho0 := hrhoWindow
          cover := weightedSelectedParentScaleCover E.selection
          c_uniform := E.c_uniform
          doubled_parent_partitioning := E.doubled_parent_partitioning
          unitRescalingGeometry := Rselected
          rescaled_fibres_cwa := hselectedCWA } }⟩

#print axioms WeightedDef212ScaleEndpoint.activeCoarse_card_le
#print axioms WeightedDef212ScaleEndpoint.activeCoarse_weight_le
#print axioms exists_weightedDef212ScaleEndpoint

end ScaleCover
end
end Family8DoubledParentConflictWeightedDef212WitnessV1
