import FamilyStickyGrounding.FamilyStickyAllParentLayerRandomMotionV1
import FamilyStickyGrounding.FamilyStickyMultiscaleSharedMotionCompositionV1
import FamilyStickyGrounding.FamilyStickyCommonPrefixLoadInvarianceV1

open scoped BigOperators ENNReal NNReal

namespace FamilyStickyDependentMultiscaleAllParentRandomMotionV1

open LeanEval.Analysis.WangZahlKakeya
open FamilyStickyAllParentLayerDataV1
open FamilyStickyPaperRandomMotionNondegeneracyV1.ActualTubeTestData
open FamilyStickyMultiscaleSharedMotionCompositionV1

noncomputable section

/-!
# Dependent-index multiscale shared random motion

Actual hierarchy levels have different child and parent index types.  This is
the dependent-index version of the already audited multiscale endpoint.  At
each scale it invokes the proved all-parent theorem directly; the output
vectors alone are then composed in the common ambient `Space`.
-/

structure DependentMultiscaleAllParentSourceData
    (depth : Nat) (Parent Child : Fin depth -> Type*)
    [forall k, Fintype (Parent k)]
    [forall k, DecidableEq (Parent k)]
    [forall k, DecidableEq (Child k)] where
  delta : Fin depth -> NNReal
  motionRadius : Fin depth -> NNReal
  layer : forall k, AllParentLayerData (delta k) (Parent k) (Child k)
  delta_le_half : forall k, delta k <= (2 : NNReal)⁻¹
  delta_pos : forall k, 0 < delta k
  delta_le_motionRadius : forall k, delta k <= motionRadius k
  delta_le_side_zero : forall k q, q ∈ (layer k).activeTests ->
    delta k <= ((layer k).parentData q.1).side q.2 0
  delta_le_side_one : forall k q, q ∈ (layer k).activeTests ->
    delta k <= ((layer k).parentData q.1).side q.2 1
  sourceMeanScale : forall k q, q ∈ (layer k).activeTests ->
    SourceMeanScale ((layer k).parentData q.1).data
      ((layer k).parentData q.1).Cbox
      ((layer k).parentData q.1).side (motionRadius k) q.2

namespace DependentMultiscaleAllParentSourceData

variable {depth : Nat} {Parent Child : Fin depth -> Type*}
  [forall k, Fintype (Parent k)]
  [forall k, DecidableEq (Parent k)]
  [forall k, DecidableEq (Child k)]

def repetitions
    (D : DependentMultiscaleAllParentSourceData depth Parent Child)
    (k : Fin depth) : Nat :=
  FamilyStickyAllParentLayerNumericsV1.AllParentLayerData.paperRepetitions
    (D.layer k) ((D.layer k).paperMean (D.motionRadius k))

def tailParameter
    (D : DependentMultiscaleAllParentSourceData depth Parent Child)
    (k : Fin depth) : Real :=
  FamilyStickyAllParentLayerNumericsV1.AllParentLayerData.sourceTailParameter
    (D.layer k)

structure Output
    (D : DependentMultiscaleAllParentSourceData depth Parent Child) where
  omega : forall k, Fin (D.repetitions k) -> Space
  repetitions_one_le : forall k, 1 <= D.repetitions k
  allParentLoad : forall k q, q ∈ (D.layer k).activeTests ->
    (∑ j, ((D.layer k).singleLoadAt q (omega k j) : Real)) <=
      D.tailParameter k * (D.layer k).paperCap q
  vector_norm_le : forall k j,
    ‖omega k j‖ <= (D.motionRadius k : Real)

namespace Output

variable (D : DependentMultiscaleAllParentSourceData depth Parent Child)
  (O : D.Output)

def toComposition : MultiscaleSharedMotionComposition depth where
  repetitions := D.repetitions
  scaleVector := O.omega
  scaleRadius := D.motionRadius
  scaleVector_norm_le := O.vector_norm_le

theorem path_nonempty : Nonempty (toComposition D O).Path :=
  (toComposition D O).path_nonempty O.repetitions_one_le

theorem norm_composedVector_le_budget
    (path : (toComposition D O).Path) {budget : NNReal}
    (hbudget : (∑ k, D.motionRadius k) <= budget) :
    ‖(toComposition D O).composedVector path‖ <= (budget : Real) := by
  apply (toComposition D O).norm_composedVector_le_budget path
  simpa [toComposition,
    FamilyStickyMultiscaleSharedMotionCompositionV1.MultiscaleSharedMotionComposition.totalRadius]
    using hbudget

def prefixVector (path : (toComposition D O).Path)
    (k : Fin depth) : Space :=
  ∑ i ∈ Finset.univ.filter (fun i => i < k), O.omega i (path i)

def prefixRadius (k : Fin depth) : NNReal :=
  ∑ i ∈ Finset.univ.filter (fun i => i < k), D.motionRadius i

theorem norm_prefixVector_le_prefixRadius
    (path : (toComposition D O).Path) (k : Fin depth) :
    ‖prefixVector D O path k‖ <= (prefixRadius D k : Real) := by
  calc
    ‖prefixVector D O path k‖ <=
        ∑ i ∈ Finset.univ.filter (fun i => i < k),
          ‖O.omega i (path i)‖ := norm_sum_le _ _
    _ <= ∑ i ∈ Finset.univ.filter (fun i => i < k),
        (D.motionRadius i : Real) := by
      exact Finset.sum_le_sum fun i _ => O.vector_norm_le i (path i)
    _ = (prefixRadius D k : Real) := by simp [prefixRadius]

theorem allParentCommonPrefixLoad
    (path : (toComposition D O).Path) (k : Fin depth)
    (q : (D.layer k).Test) (hq : q ∈ (D.layer k).activeTests) :
    (∑ j,
      (FamilyStickyCommonPrefixLoadInvarianceV1.AllParentLayerData.commonPrefixSingleLoadAt
        (D.layer k) q (prefixVector D O path k) (O.omega k j) : Real)) <=
      D.tailParameter k * (D.layer k).paperCap q := by
  simpa only [
    FamilyStickyCommonPrefixLoadInvarianceV1.AllParentLayerData.commonPrefixSingleLoadAt_eq_singleLoadAt]
    using O.allParentLoad k q hq

end Output

theorem exists_output
    (D : DependentMultiscaleAllParentSourceData depth Parent Child) :
    Nonempty D.Output := by
  have hk : forall k,
      (1 <= D.repetitions k) ∧
        exists omega : Fin (D.repetitions k) -> Space,
          (forall q, q ∈ (D.layer k).activeTests ->
            (∑ j, ((D.layer k).singleLoadAt q (omega j) : Real)) <=
              D.tailParameter k * (D.layer k).paperCap q) ∧
          (forall j, ‖omega j‖ <= (D.motionRadius k : Real)) := by
    intro k
    exact
      FamilyStickyAllParentLayerRandomMotionV1.AllParentLayerData.exists_shared_vectors_good_for_all_parents
        (D.layer k) (D.motionRadius k) (D.delta_le_half k) (D.delta_pos k)
        (D.delta_le_motionRadius k) (D.delta_le_side_zero k)
        (D.delta_le_side_one k) (D.sourceMeanScale k)
  let omega : forall k, Fin (D.repetitions k) -> Space :=
    fun k => Classical.choose (hk k).2
  exact ⟨{
    omega := omega
    repetitions_one_le := fun k => (hk k).1
    allParentLoad := fun k q hq => (Classical.choose_spec (hk k).2).1 q hq
    vector_norm_le := fun k j => (Classical.choose_spec (hk k).2).2 j }⟩

#print axioms Output.path_nonempty
#print axioms Output.norm_composedVector_le_budget
#print axioms Output.norm_prefixVector_le_prefixRadius
#print axioms Output.allParentCommonPrefixLoad
#print axioms exists_output

end DependentMultiscaleAllParentSourceData

end
end FamilyStickyDependentMultiscaleAllParentRandomMotionV1
