import Family8Grounding.Family8PlankRetainedOwnerThickenedInducedShadingV2
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8PlankRetainedOwnerThickenedMassTransportV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Family6AffinePlankAnalyticHypothesesStableV1
open Family8PlankThickControlMutualContainmentClusteringV2
open Family8PlankThickControlOwnerFiberLogBucketV2
open Family8PlankThickControlRetainedOwnerFamilyV3
open Family8PlankRetainedOwnerThickenedInducedShadingV2

noncomputable section

universe u

variable {iota : Type u} [Fintype iota] [DecidableEq iota]
variable {a b : NNReal}

/-!
# Mass transport for the retained thickened-owner shading

The owner-fibre induced carrier is a finite union of unchanged source shaded
pieces.  Subadditivity therefore bounds its mass by the literal owner-fibre
mass.  Summing over the selected owners and using their exact disjoint fibre
partition transports this to the retained source datum.  Together with the
exact shaded-union reconstruction, this also gives an average-multiplicity
comparison without any density or multiplicity hypothesis.
-/

/-- Finite-union subadditivity for one actual owner fibre. -/
theorem ownerFiberInducedCarrier_volume_le_ownerFiberMass
    {D : ShadedConvexPlankFamily iota a b} {theta : NNReal}
    (C : MutualThickeningClustering D theta) (s : iota) :
    volume (ownerFiberInducedCarrier C s) ≤ ownerFiberMass C s := by
  calc
    volume (ownerFiberInducedCarrier C s) ≤
        ∑ i : {i // i ∈ ownerFiber C s},
          volume (D.shading.carrier i.1) :=
      measure_iUnion_fintype_le volume
        (fun i : {i // i ∈ ownerFiber C s} ↦ D.shading.carrier i.1)
    _ = ∑ i ∈ ownerFiber C s, volume (D.shading.carrier i) := by
      symm
      exact Finset.sum_subtype _ (fun _i ↦ Iff.rfl) _
    _ = ownerFiberMass C s := rfl

/-- Grouping the retained source pieces by owner can only decrease the
multiplicity-counted mass. -/
theorem retainedOwnerThickenedShading_shadingMass_le
    (D : ShadedConvexPlankFamily iota a b) {theta : NNReal}
    (C : MutualThickeningClustering D theta)
    (q : Fin (Nat.log 2 (Fintype.card iota) + 1)) :
    (retainedOwnerThickenedShading D C q).shadingMass ≤
      (retainedOwnerPlankFamily D C q).shading.shadingMass := by
  rw [retainedOwnerPlankFamily_shadingMass]
  unfold Shading.shadingMass
  calc
    ∑ s : {s // s ∈ selectedOwnerLogBucket C q},
        volume (ownerFiberInducedCarrier C s.1) ≤
        ∑ s : {s // s ∈ selectedOwnerLogBucket C q},
          ownerFiberMass C s.1 := by
      exact Finset.sum_le_sum fun s _hs ↦
        ownerFiberInducedCarrier_volume_le_ownerFiberMass C s.1
    _ = ∑ s ∈ selectedOwnerLogBucket C q, ownerFiberMass C s := by
      symm
      exact Finset.sum_subtype _ (fun _s ↦ Iff.rfl) _

/-- The induced thickened-owner datum has no larger average multiplicity
than the actual retained source datum, because their shaded unions agree
exactly. -/
theorem retainedOwnerThickenedShading_averageMultiplicity_le
    (D : ShadedConvexPlankFamily iota a b) {theta : NNReal}
    (C : MutualThickeningClustering D theta)
    (q : Fin (Nat.log 2 (Fintype.card iota) + 1)) :
    (retainedOwnerThickenedShading D C q).averageMultiplicity ≤
      (retainedOwnerPlankFamily D C q).shading.averageMultiplicity := by
  unfold Shading.averageMultiplicity
  rw [retainedOwnerThickenedShading_shadedUnion_eq]
  exact ENNReal.div_le_div_right
    (retainedOwnerThickenedShading_shadingMass_le D C q) _

#print axioms ownerFiberInducedCarrier_volume_le_ownerFiberMass
#print axioms retainedOwnerThickenedShading_shadingMass_le
#print axioms retainedOwnerThickenedShading_averageMultiplicity_le

end
end Family8PlankRetainedOwnerThickenedMassTransportV1
