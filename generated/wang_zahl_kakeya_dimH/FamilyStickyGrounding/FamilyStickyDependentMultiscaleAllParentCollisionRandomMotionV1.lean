import FamilyStickyGrounding.FamilyStickyAllParentLayerCollisionRandomMotionV1
import FamilyStickyGrounding.FamilyStickyDependentMultiscaleAllParentRandomMotionV1

open scoped BigOperators ENNReal NNReal

namespace FamilyStickyDependentMultiscaleAllParentCollisionRandomMotionV1

open LeanEval.Analysis.WangZahlKakeya
open FamilyStickyAllParentLayerDataV1
open FamilyStickyAllParentLayerCollisionRandomMotionV1
open FamilyStickyDependentMultiscaleAllParentRandomMotionV1
open FamilyStickyDependentMultiscaleAllParentRandomMotionV1.DependentMultiscaleAllParentSourceData

noncomputable section
set_option linter.unusedSectionVars false

/-!
# Dependent multiscale output retaining per-parent collision control

Each scale invokes the proved two-family layer producer.  The projection
`toAnalyticOutput` forgets only the extra collision fields and is literally an
ordinary `DependentMultiscaleAllParentSourceData.Output`; consequently all
existing common-prefix composition and hierarchy containment theorems remain
available without a second random choice.
-/

variable {depth : Nat} {Parent Child : Fin depth -> Type*}
  [forall k, Fintype (Parent k)]
  [forall k, DecidableEq (Parent k)]
  [forall k, DecidableEq (Child k)]

structure Output
    (D : DependentMultiscaleAllParentSourceData depth Parent Child) where
  layerOutput : forall k,
    AllParentLayerCollisionOutput (D.layer k) (D.motionRadius k)

namespace Output

variable {D : DependentMultiscaleAllParentSourceData depth Parent Child}
  (O : Output D)

/-- The same vectors, viewed through the pre-existing analytic hierarchy
certificate interface. -/
def toAnalyticOutput : D.Output where
  omega := fun k j => (((O.layerOutput k).omega j).1 : Space)
  repetitions_one_le := fun k => (O.layerOutput k).repetitions_one_le
  allParentLoad := fun k q hq => (O.layerOutput k).allParentLoad q hq
  vector_norm_le := fun k j => (O.layerOutput k).vector_norm_le j

/-- Per-parent collision cap for the very same vector family at scale `k`. -/
theorem allParentCollisionLoad
    (k : Fin depth) (p : Parent k)
    (hp : p ∈ (D.layer k).activeParents)
    (a : FamilyStickyRandomModelTubeCollisionGridV1.ModelCandidate
      (parentPackingGrid (D.layer k) (O.layerOutput k).certificate p)) :
    (∑ j,
      FamilyStickyRandomModelTubeCollisionGridV1.candidateCollisionLoad
        (parentPackingGrid (D.layer k) (O.layerOutput k).certificate p)
        a ((O.layerOutput k).omega j)) <=
      Nat.ceil
        (FamilyStickyRandomTwoFamilyTailV1.completionTail
            (activeCollisionTests (D.layer k)
              (O.layerOutput k).certificate).card
            (FamilyStickyAllParentLayerNumericsV1.AllParentLayerData.sourceTailParameter
              (D.layer k)) *
          FamilyStickyRandomWZCommonNeighbourPackingV1.commonHundredNeighbourPackingConstant) :=
  (O.layerOutput k).allParentCollisionLoad p hp a

theorem repetitions_one_le (Q : Output D) (k : Fin depth) :
    1 <= D.repetitions k :=
  (toAnalyticOutput Q).repetitions_one_le k

#print axioms toAnalyticOutput
#print axioms allParentCollisionLoad

end Output

/-- Per-scale faithful producer.  It differs from the analytic multiscale
theorem only by the actual WZ separation, `100δ` smallness, and the transparent
`J m <= C_WZ` source inequality at each parent fibre. -/
theorem exists_output
    (D : DependentMultiscaleAllParentSourceData depth Parent Child)
    (hsmall : forall k,
      FamilyStickyRandomModelTubeCollisionGridV1.hundredRadius (D.delta k) <=
        (2 : NNReal)⁻¹)
    (hpair : forall k,
      ParentFibreWZSeparated (D.layer k))
    (hcollisionScale : forall k,
      ParentCollisionScale (D.layer k) (D.motionRadius k)) :
    Nonempty (Output D) := by
  have hk : forall k,
      Nonempty (AllParentLayerCollisionOutput (D.layer k)
        (D.motionRadius k)) := by
    intro k
    exact exists_allParentLayerCollisionOutput
      (D.layer k) (D.motionRadius k)
      (D.delta_le_half k) (D.delta_pos k)
      (D.delta_le_motionRadius k) (hsmall k)
      (D.delta_le_side_zero k) (D.delta_le_side_one k)
      (D.sourceMeanScale k) (hpair k) (hcollisionScale k)
  exact ⟨{
    layerOutput := fun k => Classical.choice (hk k) }⟩

#print axioms exists_output

end

end FamilyStickyDependentMultiscaleAllParentCollisionRandomMotionV1
