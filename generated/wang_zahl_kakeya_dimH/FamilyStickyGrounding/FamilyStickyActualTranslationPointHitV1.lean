import FamilyStickyGrounding.FamilyStickyActualTubeTranslationGridV1

open Set
open scoped BigOperators ENNReal NNReal

namespace FamilyStickyActualTranslationPointHitV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open FamilyStickyActualTubeTranslationV1
open FamilyStickyActualTubeTranslationGridV1

noncomputable section

/-!
# Actual per-tube grid hits reduce to point hits

This is the deterministic geometric step in the appendix estimate
`P[R(T) ⊆ K] ≲ |K|/|T_rho|`: choose the base point of the tube axis.
If the whole translated tube lies in `K`, then that translated base point
lies in `K`.  Thus a point-counting estimate for the finite grid implies the
required per-tube incidence estimate, without assuming any probability tail.
-/

namespace ActualTubeTranslationGrid

variable {delta : NNReal} {translation tubeIndex : Type*}
  [Fintype translation] [DecidableEq translation]
  [DecidableEq tubeIndex]

/-- Number of grid vectors that move one ambient point into one test body. -/
def pointHitCount
    (G : ActualTubeTranslationGrid delta translation tubeIndex)
    (K : Fin G.testCard) (x : Space) : Nat := by
  classical
  exact (Finset.univ.filter fun g =>
    G.gridVector g + x ∈ (G.testBody K : Set Space)).card

/-- Literal grid property needed for the appendix incidence estimate.  It is
local in one point and one test body, not a many-translation conclusion. -/
def HasPointHitCap
    (G : ActualTubeTranslationGrid delta translation tubeIndex)
    (translationBudget : Fin G.testCard -> Nat) : Prop :=
  forall K, K ∈ G.activeTests -> forall x : Space,
    pointHitCount G K x <= translationBudget K

/-- Containment of a whole translated tube forces containment of the
translated base point chosen on its axis. -/
theorem translated_axisBase_mem_testBody_of_carrier_subset
    (G : ActualTubeTranslationGrid delta translation tubeIndex)
    (K : Fin G.testCard) (i : tubeIndex) (g : translation)
    (hsubset :
      (translateTube (G.tube i) (G.gridVector g)).carrier ⊆
        (G.testBody K : Set Space)) :
    G.gridVector g + (G.tube i).axis.base ∈
      (G.testBody K : Set Space) := by
  apply hsubset
  rw [translateTube_carrier]
  exact ⟨(G.tube i).axis.base,
    (G.tube i).axis_subset_carrier (G.tube i).axis.base_mem_carrier,
    rfl⟩

/-- The actual per-tube translation hit count is bounded by the point hit
count at the tube's axis base. -/
theorem tubeHitCount_le_pointHitCount_axisBase
    (G : ActualTubeTranslationGrid delta translation tubeIndex)
    (K : Fin G.testCard) (i : tubeIndex) :
    G.tubeHitCount K i <=
      pointHitCount G K (G.tube i).axis.base := by
  classical
  unfold FamilyStickyActualTubeTranslationGridV1.ActualTubeTranslationGrid.tubeHitCount
    pointHitCount
  apply Finset.card_le_card
  intro g hg
  rw [Finset.mem_filter] at hg ⊢
  exact ⟨Finset.mem_univ g,
    translated_axisBase_mem_testBody_of_carrier_subset G K i g hg.2⟩

/-- A uniform finite-grid point cap automatically supplies every per-tube
incidence cap consumed by the Chernoff adapter. -/
theorem tubeHitCount_le_of_hasPointHitCap
    (G : ActualTubeTranslationGrid delta translation tubeIndex)
    (translationBudget : Fin G.testCard -> Nat)
    (hpoint : HasPointHitCap G translationBudget) :
    forall K, K ∈ G.activeTests -> forall i, i ∈ G.tubes ->
      G.tubeHitCount K i <= translationBudget K := by
  intro K hK i _hi
  exact (tubeHitCount_le_pointHitCount_axisBase G K i).trans
    (hpoint K hK (G.tube i).axis.base)

#print axioms translated_axisBase_mem_testBody_of_carrier_subset
#print axioms tubeHitCount_le_pointHitCount_axisBase
#print axioms tubeHitCount_le_of_hasPointHitCap

end ActualTubeTranslationGrid

end

end FamilyStickyActualTranslationPointHitV1
