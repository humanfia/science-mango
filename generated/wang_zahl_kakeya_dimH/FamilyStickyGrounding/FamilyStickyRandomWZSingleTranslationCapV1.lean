import FamilyStickyGrounding.FamilyStickyRandomWZCommonNeighbourPackingV1

open Set
open scoped NNReal

namespace FamilyStickyRandomWZSingleTranslationCapV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open FamilyStickyActualTubeTranslationV1
open FamilyStickyActualTubeTranslationGridV1
open FamilyStickyRandomModelTubeCollisionGridV1
open FamilyStickyRandomHundredContainerSelectionV1
open FamilyStickyRandomHundredContainerSelectionV1.MaximalSelection
open FamilyStickyRandomWZLineParameterGeometryV1
open FamilyStickyRandomWZCommonNeighbourPackingV1
open FamilyStickyRandomProductCoordinatePackingV1

noncomputable section
set_option linter.unusedSectionVars false

/-!
# Direct WZ constant cap for one shared translation

This is the fibre-preserving replacement for a global source selection.
If all translated tubes counted by one `100T_0` test share that container,
then after translating back they all lie in the common-container
neighbourhood of any one member.  WZ endpoint-parameter separation and the
already proved line-space packing theorem bound this entire neighbourhood by
the fixed dimension-only constant `C_WZ`.

No source tube is discarded, so any later restriction to a hierarchy parent
fibre retains its parent/path label.
-/

theorem productCoordinatePackingConstant_pos :
    0 < productCoordinatePackingConstant := by
  have hzero : (0 : LineParameter) ∈
      Metric.closedBall (0 : LineParameter)
        (normalizedParameterRadius : Real) := by simp
  obtain ⟨c, hc, _⟩ :=
    canonicalPackingNet.cover hzero
  unfold productCoordinatePackingConstant
  exact Finset.card_pos.mpr ⟨c, hc⟩

theorem commonHundredNeighbourPackingConstant_pos :
    0 < commonHundredNeighbourPackingConstant := by
  unfold commonHundredNeighbourPackingConstant
  exact Nat.mul_pos (by norm_num) productCoordinatePackingConstant_pos

variable {delta : NNReal} {translation tubeIndex : Type*}
  [Fintype translation] [DecidableEq translation]
  [DecidableEq tubeIndex]

/-- Every original source collision cell has the fixed WZ cap, with no
maximal source refinement. -/
theorem candidateCollisionLoad_le_WZConstant
    (G : ActualTubeTranslationGrid delta translation tubeIndex)
    (hdelta : 0 < delta)
    (hpair : Set.Pairwise (G.tubes : Set tubeIndex) fun i j =>
      WZEndpointParameterSeparated (G.tube i) (G.tube j))
    (a : ModelCandidate G) (g : translation) :
    candidateCollisionLoad G a g <=
      commonHundredNeighbourPackingConstant := by
  classical
  let F := candidateCollisionFinset G a g
  by_cases hF : F.Nonempty
  · obtain ⟨b, hb⟩ := hF
    have hbData := (mem_candidateCollisionFinset G a g b).mp hb
    let bActive : ActiveSource G := ⟨b, hbData.1⟩
    let target := ↥(commonHundredNeighbourFinset G bActive)
    let f : ↥F → target := fun i => ⟨
      ⟨i.1, ((mem_candidateCollisionFinset G a g i.1).mp i.2).1⟩, by
        have hiData :=
          (mem_candidateCollisionFinset G a g i.1).mp i.2
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _, ?_⟩
        by_cases hib : i.1 = b
        · left
          apply Subtype.ext
          exact hib
        · right
          apply commonHundredContainer_of_translate
          exact ⟨modelCandidateTube G a, hiData.2, hbData.2⟩⟩
    have hinjective : Function.Injective f := by
      intro i j hij
      apply Subtype.ext
      exact congrArg (fun z : target => z.1.1) hij
    calc
      candidateCollisionLoad G a g = F.card := rfl
      _ = Fintype.card ↥F := (Fintype.card_coe F).symm
      _ <= Fintype.card target :=
        Fintype.card_le_of_injective f hinjective
      _ = (commonHundredNeighbourFinset G bActive).card :=
        Fintype.card_coe _
      _ <= commonHundredNeighbourPackingConstant :=
        commonHundredNeighbourFinset_card_le_constant G hdelta hpair bActive
  · have hEmpty : F = ∅ := Finset.not_nonempty_iff_eq_empty.mp hF
    simp [candidateCollisionLoad, F, hEmpty]

/-- Actual collision-grid single-load form of the same direct cap. -/
theorem collisionGrid_singleLoad_le_WZConstant
    (G : ActualTubeTranslationGrid delta translation tubeIndex)
    (hdelta : 0 < delta)
    (hpair : Set.Pairwise (G.tubes : Set tubeIndex) fun i j =>
      WZEndpointParameterSeparated (G.tube i) (G.tube j))
    (a : ModelCandidate G) (g : translation) :
    (collisionGrid G).singleLoad (modelCandidateIndex G a) g <=
      commonHundredNeighbourPackingConstant := by
  rw [collisionGrid_singleLoad_candidate]
  exact candidateCollisionLoad_le_WZConstant G hdelta hpair a g

#print axioms productCoordinatePackingConstant_pos
#print axioms commonHundredNeighbourPackingConstant_pos
#print axioms candidateCollisionLoad_le_WZConstant
#print axioms collisionGrid_singleLoad_le_WZConstant

end
end FamilyStickyRandomWZSingleTranslationCapV1
