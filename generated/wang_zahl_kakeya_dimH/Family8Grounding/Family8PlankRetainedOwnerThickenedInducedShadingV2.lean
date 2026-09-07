import Family8Grounding.Family8PlankThickControlRetainedOwnerFamilyV3
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8PlankRetainedOwnerThickenedInducedShadingV2

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Family6AffinePlankAnalyticHypothesesStableV1
open Family8PlankThickControlActualClusterV1
open Family8PlankThickControlMutualContainmentClusteringV2
open Family8PlankThickControlOwnerFiberLogBucketV2
open Family8PlankThickControlRetainedOwnerFamilyV3

noncomputable section

universe u

variable {iota : Type u} [Fintype iota] [DecidableEq iota]
variable {a b : NNReal}

/-!
# The actual thickened-owner family and its induced shading

For every retained selected owner, package the literal closed
`theta * b`-neighborhood of its source plank as a convex body.  Its shading
is the finite union of the original shaded carriers in that exact owner
fibre.  The resulting coarse shaded union is definitionally reconstructed
from the retained source family: no union or density conclusion is an input.

This is the same-object construction on which the later dense-ball
refinement must prove a quantitative density lower bound.
-/

/-- The literal closed thickening of one source owner, packaged as a genuine
compact nonempty convex body. -/
def ownerThickenedBody
    (D : ShadedConvexPlankFamily iota a b) (theta : NNReal) (s : iota) :
    ConvexBody Space where
  carrier := Metric.cthickening ((theta * b : NNReal) : Real)
    (D.family s : Set Space)
  convex' := (D.family s).convex.cthickening _
  isCompact' := (D.family s).isCompact.cthickening
  nonempty' := (D.family s).nonempty.mono
    (Metric.self_subset_cthickening _)

@[simp] theorem coe_ownerThickenedBody
    (D : ShadedConvexPlankFamily iota a b) (theta : NNReal) (s : iota) :
    (ownerThickenedBody D theta s : Set Space) =
      Metric.cthickening ((theta * b : NNReal) : Real)
        (D.family s : Set Space) := rfl

/-- The exact union of original shaded pieces assigned to one owner. -/
def ownerFiberInducedCarrier
    {D : ShadedConvexPlankFamily iota a b} {theta : NNReal}
    (C : MutualThickeningClustering D theta) (s : iota) : Set Space :=
  ⋃ i : {i // i ∈ ownerFiber C s}, D.shading.carrier i.1

theorem measurableSet_ownerFiberInducedCarrier
    {D : ShadedConvexPlankFamily iota a b} {theta : NNReal}
    (C : MutualThickeningClustering D theta) (s : iota) :
    MeasurableSet (ownerFiberInducedCarrier C s) :=
  MeasurableSet.iUnion fun i => D.shading.measurable_carrier i.1

/-- Every member of an owner fibre contributes its unchanged shaded carrier
to the induced coarse carrier. -/
theorem sourceCarrier_subset_ownerFiberInducedCarrier
    {D : ShadedConvexPlankFamily iota a b} {theta : NNReal}
    (C : MutualThickeningClustering D theta) (s i : iota)
    (hi : i ∈ ownerFiber C s) :
    D.shading.carrier i ⊆ ownerFiberInducedCarrier C s := by
  intro x hx
  exact Set.mem_iUnion.mpr ⟨⟨i, hi⟩, hx⟩

/-- The induced owner-fibre carrier lies in the literal thickened owner body,
using the constructed owner containment rather than an assumed coarse
shading. -/
theorem ownerFiberInducedCarrier_subset_ownerThickenedBody
    (D : ShadedConvexPlankFamily iota a b) (theta : NNReal)
    (C : MutualThickeningClustering D theta) (s : iota) :
    ownerFiberInducedCarrier C s ⊆ (ownerThickenedBody D theta s : Set Space) := by
  intro x hx
  obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hx
  have hiThick : i.1 ∈ thickenedPlankIndices D theta s :=
    ownerFiber_subset_thickenedPlankIndices C s i.2
  have hiBody := (mem_thickenedPlankIndices_iff D theta s i.1).1 hiThick
  exact hiBody (D.shading.carrier_subset i.1 hxi)

/-- The selected thickened owners form an actual indexed convex family. -/
def retainedOwnerThickenedFamily
    (D : ShadedConvexPlankFamily iota a b) {theta : NNReal}
    (C : MutualThickeningClustering D theta)
    (q : Fin (Nat.log 2 (Fintype.card iota) + 1)) :
    ConvexFamily {s // s ∈ selectedOwnerLogBucket C q} :=
  fun s => ownerThickenedBody D theta s.1

/-- The actual induced shading on retained thickened owners. -/
def retainedOwnerThickenedShading
    (D : ShadedConvexPlankFamily iota a b) {theta : NNReal}
    (C : MutualThickeningClustering D theta)
    (q : Fin (Nat.log 2 (Fintype.card iota) + 1)) :
    Shading (retainedOwnerThickenedFamily D C q) where
  carrier := fun s => ownerFiberInducedCarrier C s.1
  measurable_carrier := fun s =>
    measurableSet_ownerFiberInducedCarrier C s.1
  carrier_subset := fun s =>
    ownerFiberInducedCarrier_subset_ownerThickenedBody D theta C s.1

@[simp] theorem retainedOwnerThickenedShading_carrier
    (D : ShadedConvexPlankFamily iota a b) {theta : NNReal}
    (C : MutualThickeningClustering D theta)
    (q : Fin (Nat.log 2 (Fintype.card iota) + 1))
    (s : {s // s ∈ selectedOwnerLogBucket C q}) :
    (retainedOwnerThickenedShading D C q).carrier s =
      ownerFiberInducedCarrier C s.1 := rfl

/-- Exact geometric reconstruction: grouping the retained source shading by
its constructed owner changes neither the point set nor the objects used to
witness membership. -/
theorem retainedOwnerThickenedShading_shadedUnion_eq
    (D : ShadedConvexPlankFamily iota a b) {theta : NNReal}
    (C : MutualThickeningClustering D theta)
    (q : Fin (Nat.log 2 (Fintype.card iota) + 1)) :
    (retainedOwnerThickenedShading D C q).shadedUnion =
      (retainedOwnerPlankFamily D C q).shading.shadedUnion := by
  ext x
  constructor
  · intro hx
    obtain ⟨s, hsx⟩ := Set.mem_iUnion.mp hx
    obtain ⟨i, hix⟩ := Set.mem_iUnion.mp hsx
    have howner : C.owner i.1 = s.1 := (mem_ownerFiber C s.1 i.1).1 i.2
    have hownerMem : C.owner i.1 ∈ selectedOwnerLogBucket C q := by
      rw [howner]
      exact s.2
    have hiRetained : i.1 ∈ retainedOwnerSourceIndices C q :=
      (mem_retainedOwnerSourceIndices C q i.1).2 hownerMem
    exact Set.mem_iUnion.mpr ⟨⟨i.1, hiRetained⟩, hix⟩
  · intro hx
    obtain ⟨i, hix⟩ := Set.mem_iUnion.mp hx
    have howner : C.owner i.1 ∈ selectedOwnerLogBucket C q :=
      (mem_retainedOwnerSourceIndices C q i.1).1 i.2
    let s : {s // s ∈ selectedOwnerLogBucket C q} :=
      ⟨C.owner i.1, howner⟩
    have hiFiber : i.1 ∈ ownerFiber C s.1 :=
      (mem_ownerFiber C s.1 i.1).2 rfl
    exact Set.mem_iUnion.mpr
      ⟨s, Set.mem_iUnion.mpr ⟨⟨i.1, hiFiber⟩, hix⟩⟩

#print axioms coe_ownerThickenedBody
#print axioms measurableSet_ownerFiberInducedCarrier
#print axioms sourceCarrier_subset_ownerFiberInducedCarrier
#print axioms ownerFiberInducedCarrier_subset_ownerThickenedBody
#print axioms retainedOwnerThickenedShading_carrier
#print axioms retainedOwnerThickenedShading_shadedUnion_eq

end
end Family8PlankRetainedOwnerThickenedInducedShadingV2
