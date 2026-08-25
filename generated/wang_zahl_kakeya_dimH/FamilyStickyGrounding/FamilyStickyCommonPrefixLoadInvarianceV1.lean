import FamilyStickyGrounding.FamilyStickyAllParentLayerDataV1
import FamilyStickyGrounding.FamilyStickyMultiscaleSharedMotionCompositionV1

open Set
open scoped BigOperators NNReal

namespace FamilyStickyCommonPrefixLoadInvarianceV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open FamilyStickyActualTubeTranslationV1
open FamilyStickyActualTubeTestDataV1
open FamilyStickyActualTubeTestDataV1.ActualTubeTestData
open FamilyStickyAllParentLayerDataV1
open FamilyStickyAllParentLayerDataV1.AllParentLayerData

noncomputable section

/-!
# Common-prefix invariance for a scale-local load

GWZ `lemmasubsticky`, pinned source lines 1514--1518, compares a child tube
and its coarse parent after the same already-chosen prefix translation.  The
prefix cancels: containment of the newly translated child in the newly
translated test body is exactly the original scale-local containment.

This is an actual carrier/counting statement, not an abstract invariance
callback.  It is the bridge from the per-layer all-parent union bound to the
iterated translations used in the final multiscale family.
-/

/-- Translating both sides of a containment by the same vector is an
equivalence. -/
theorem add_image_subset_add_image_iff
    (pfx : Space) (A B : Set Space) :
    (fun x => pfx + x) '' A ⊆ (fun x => pfx + x) '' B ↔ A ⊆ B := by
  constructor
  · intro h x hx
    have hpx : pfx + x ∈ (fun y => pfx + y) '' A := ⟨x, hx, rfl⟩
    rcases h hpx with ⟨y, hy, hxy⟩
    have : x = y := add_left_cancel hxy.symm
    simpa [this] using hy
  · intro h _ hz
    rcases hz with ⟨x, hx, rfl⟩
    exact ⟨x, h hx, rfl⟩

/-- Literal tube-carrier version of common-prefix cancellation. -/
theorem commonPrefix_carrier_subset_iff
    {delta : NNReal} (T : Tube delta) (v pfx : Space)
    (B : Set Space) :
    (translateTube (translateTube T v) pfx).carrier ⊆
        (fun x => pfx + x) '' B ↔
      (translateTube T v).carrier ⊆ B := by
  rw [translateTube_carrier]
  exact add_image_subset_add_image_iff pfx
    (translateTube T v).carrier B

namespace ActualTubeTestData

variable {delta : NNReal} {tubeIndex : Type*} [DecidableEq tubeIndex]

/-- Load after applying a common old prefix to both the locally translated
tubes and the test body. -/
def commonPrefixSingleLoad (D : ActualTubeTestData delta tubeIndex)
    (K : Fin D.testCard) (pfx v : Space) : Nat := by
  classical
  exact (D.tubes.filter fun i =>
    (translateTube (translateTube (D.tube i) v) pfx).carrier ⊆
      (fun x => pfx + x) '' (D.testBody K : Set Space)).card

/-- Common-prefix translation does not change the literal finite load. -/
theorem commonPrefixSingleLoad_eq_singleLoadAt
    (D : ActualTubeTestData delta tubeIndex)
    (K : Fin D.testCard) (pfx v : Space) :
    commonPrefixSingleLoad D K pfx v = D.singleLoadAt K v := by
  classical
  unfold commonPrefixSingleLoad FamilyStickyActualTubeTestDataV1.ActualTubeTestData.singleLoadAt
  apply congrArg Finset.card
  ext i
  simp only [Finset.mem_filter]
  rw [commonPrefix_carrier_subset_iff]

end ActualTubeTestData

namespace AllParentLayerData

variable {delta : NNReal} {parent tubeIndex : Type*}
  [Fintype parent] [DecidableEq parent] [DecidableEq tubeIndex]

/-- Parent-local version, retaining the dependent `(parent,test)` index. -/
def commonPrefixSingleLoadAt
    (L : AllParentLayerData delta parent tubeIndex)
    (q : L.Test) (pfx v : Space) : Nat :=
  FamilyStickyCommonPrefixLoadInvarianceV1.ActualTubeTestData.commonPrefixSingleLoad
    (L.parentData q.1).data q.2 pfx v

theorem commonPrefixSingleLoadAt_eq_singleLoadAt
    (L : AllParentLayerData delta parent tubeIndex)
    (q : L.Test) (pfx v : Space) :
    commonPrefixSingleLoadAt L q pfx v = L.singleLoadAt q v :=
  ActualTubeTestData.commonPrefixSingleLoad_eq_singleLoadAt
    (L.parentData q.1).data q.2 pfx v

end AllParentLayerData

#print axioms add_image_subset_add_image_iff
#print axioms commonPrefix_carrier_subset_iff
#print axioms ActualTubeTestData.commonPrefixSingleLoad_eq_singleLoadAt
#print axioms AllParentLayerData.commonPrefixSingleLoadAt_eq_singleLoadAt

end
end FamilyStickyCommonPrefixLoadInvarianceV1
