import FamilyStickyGrounding.FamilyStickyAllParentLayerJointCollisionRandomMotionV1
import FamilyStickyGrounding.FamilyStickyDependentMultiscaleAllParentRandomMotionV1
import FamilyStickyGrounding.FamilyStickyMultiscaleSharedMotionCompositionV1
import FamilyStickyGrounding.FamilyStickyCommonPrefixLoadInvarianceV1

open scoped BigOperators NNReal

namespace FamilyStickyDependentMultiscaleAllParentJointRandomMotionV1

open LeanEval.Analysis.WangZahlKakeya
open FamilyStickyAllParentLayerDataV1
open FamilyStickyAllParentLayerCollisionRandomMotionV1
open FamilyStickyAllParentLayerJointRepetitionsV1
open FamilyStickyAllParentLayerJointCollisionRandomMotionV1
open FamilyStickyDependentMultiscaleAllParentRandomMotionV1
open FamilyStickyDependentMultiscaleAllParentRandomMotionV1.DependentMultiscaleAllParentSourceData
open FamilyStickyMultiscaleSharedMotionCompositionV1

noncomputable section
set_option linter.unusedSectionVars false

/-!
# Multiscale composition using the faithful joint repetition count

Unlike the older analytic-only output, the path coordinate at scale `k` has
length `jointRepetitions`.  All prefix loads, collision loads, and radius
bounds therefore refer to the same actual occurrence family.
-/

variable {depth : Nat} {Parent Child : Fin depth -> Type*}
  [forall k, Fintype (Parent k)]
  [forall k, DecidableEq (Parent k)]
  [forall k, DecidableEq (Child k)]

def repetitions
    (D : DependentMultiscaleAllParentSourceData depth Parent Child)
    (k : Fin depth) : Nat :=
  jointRepetitions (D.layer k) (D.motionRadius k)

structure Output
    (D : DependentMultiscaleAllParentSourceData depth Parent Child) where
  layerOutput : forall k,
    AllParentLayerJointCollisionOutput (D.layer k) (D.motionRadius k)

namespace Output

variable {D : DependentMultiscaleAllParentSourceData depth Parent Child}
  (O : Output D)

def omega (k : Fin depth) : Fin (repetitions D k) -> Space :=
  fun j => (((O.layerOutput k).omega j).1 : Space)

def toComposition : MultiscaleSharedMotionComposition depth where
  repetitions := repetitions D
  scaleVector := O.omega
  scaleRadius := D.motionRadius
  scaleVector_norm_le := fun k j => (O.layerOutput k).vector_norm_le j

abbrev Path := O.toComposition.Path

theorem path_nonempty : Nonempty O.Path :=
  O.toComposition.path_nonempty fun k =>
    (O.layerOutput k).repetitions_one_le

def prefixVector (path : O.Path) (k : Fin depth) : Space :=
  ∑ i ∈ Finset.univ.filter (fun i => i < k), O.omega i (path i)

def prefixRadius (k : Fin depth) : NNReal :=
  ∑ i ∈ Finset.univ.filter (fun i => i < k), D.motionRadius i

theorem norm_prefixVector_le_prefixRadius
    (path : O.Path) (k : Fin depth) :
    ‖O.prefixVector path k‖ <= (prefixRadius (D := D) k : Real) := by
  calc
    ‖O.prefixVector path k‖ <=
        ∑ i ∈ Finset.univ.filter (fun i => i < k),
          ‖O.omega i (path i)‖ := norm_sum_le _ _
    _ <= ∑ i ∈ Finset.univ.filter (fun i => i < k),
        (D.motionRadius i : Real) := by
      exact Finset.sum_le_sum fun i _ =>
        (O.layerOutput i).vector_norm_le (path i)
    _ = (prefixRadius (D := D) k : Real) := by simp [prefixRadius]

theorem allParentCommonPrefixLoad
    (path : O.Path) (k : Fin depth)
    (q : (D.layer k).Test) (hq : q ∈ (D.layer k).activeTests) :
    (∑ j,
      (FamilyStickyCommonPrefixLoadInvarianceV1.AllParentLayerData.commonPrefixSingleLoadAt
        (D.layer k) q (O.prefixVector path k) (O.omega k j) : Real)) <=
      FamilyStickyAllParentLayerNumericsV1.AllParentLayerData.sourceTailParameter
          (D.layer k) *
        (D.layer k).paperCap q := by
  simp_rw [
    FamilyStickyCommonPrefixLoadInvarianceV1.AllParentLayerData.commonPrefixSingleLoadAt_eq_singleLoadAt]
  unfold omega
  exact (O.layerOutput k).allParentLoad q hq

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

theorem norm_composedVector_le_totalRadius (path : O.Path) :
    ‖O.toComposition.composedVector path‖ <=
      ((∑ k, D.motionRadius k : NNReal) : Real) := by
  simpa [toComposition,
    MultiscaleSharedMotionComposition.totalRadius] using
    O.toComposition.norm_composedVector_le_totalRadius path

#print axioms path_nonempty
#print axioms allParentCommonPrefixLoad
#print axioms allParentCollisionLoad
#print axioms norm_composedVector_le_totalRadius

end Output

theorem exists_output
    (D : DependentMultiscaleAllParentSourceData depth Parent Child)
    (hsmall : forall k,
      FamilyStickyRandomModelTubeCollisionGridV1.hundredRadius (D.delta k) <=
        (2 : NNReal)⁻¹)
    (hpair : forall k,
      ParentFibreWZSeparated (D.layer k))
    (hcollisionUnit : forall k p, p ∈ (D.layer k).activeParents ->
      parentCollisionMean (D.layer k) (D.motionRadius k) p <=
        (FamilyStickyRandomWZCommonNeighbourPackingV1.commonHundredNeighbourPackingConstant : Real)) :
    Nonempty (Output D) := by
  have hk : forall k,
      Nonempty (AllParentLayerJointCollisionOutput
        (D.layer k) (D.motionRadius k)) := by
    intro k
    exact exists_allParentLayerJointCollisionOutput
      (D.layer k) (D.motionRadius k)
      (D.delta_le_half k) (D.delta_pos k)
      (D.delta_le_motionRadius k) (hsmall k)
      (D.delta_le_side_zero k) (D.delta_le_side_one k)
      (D.sourceMeanScale k) (hpair k) (hcollisionUnit k)
  exact ⟨{
    layerOutput := fun k => Classical.choice (hk k) }⟩

/-- Joint multiscale output using unconditional collision outer boxes. -/
theorem exists_output_without_hundred_small
    (D : DependentMultiscaleAllParentSourceData depth Parent Child)
    (hpair : forall k,
      ParentFibreWZSeparated (D.layer k))
    (hcollisionUnit : forall k p, p ∈ (D.layer k).activeParents ->
      parentCollisionMean (D.layer k) (D.motionRadius k) p <=
        (FamilyStickyRandomWZCommonNeighbourPackingV1.commonHundredNeighbourPackingConstant : Real)) :
    Nonempty (Output D) := by
  have hk : forall k,
      Nonempty (AllParentLayerJointCollisionOutput
        (D.layer k) (D.motionRadius k)) := by
    intro k
    exact exists_allParentLayerJointCollisionOutput_without_hundred_small
      (D.layer k) (D.motionRadius k)
      (D.delta_le_half k) (D.delta_pos k)
      (D.delta_le_motionRadius k)
      (D.delta_le_side_zero k) (D.delta_le_side_one k)
      (D.sourceMeanScale k) (hpair k) (hcollisionUnit k)
  exact ⟨{
    layerOutput := fun k => Classical.choice (hk k) }⟩

#print axioms exists_output_without_hundred_small
#print axioms exists_output

end

end FamilyStickyDependentMultiscaleAllParentJointRandomMotionV1
