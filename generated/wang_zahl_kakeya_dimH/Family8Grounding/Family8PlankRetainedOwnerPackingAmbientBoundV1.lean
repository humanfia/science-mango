import Family8Grounding.Family8PlankRetainedOwnerCubeWeightDenseBallV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8PlankRetainedOwnerPackingAmbientBoundV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexGeometry.FrameBoxInducedCoveringGrowth
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
# Ambient bound for the actual retained-owner packing count

Both the retained source planks and the induced thickened-owner bodies lie in
the closed `theta*b` thickening of the original unit-scale ambient body.
Consequently the genuine separated packing used by the dense-ball connector
has its cardinality times the small-ball volume bounded by one explicit
ambient thickening volume.  This is the geometric cross-multiplied estimate
needed to turn CubeWeight's `mass / (K * packingCard)` cutoff into a local
ball-density lower bound; no cardinality estimate is assumed.
-/

/-- The retained source family remains in the original ambient body. -/
theorem retainedOwnerPlankFamily_familyUnion_subset_ambient
    (D : ShadedConvexPlankFamily iota a b) {theta : NNReal}
    (C : MutualThickeningClustering D theta)
    (q : Fin (Nat.log 2 (Fintype.card iota) + 1)) :
    familyUnion (retainedOwnerPlankFamily D C q).family ⊆
      (D.ambient : Set Space) := by
  intro x hx
  obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hx
  exact D.contained_in_ambient i.1 (by
    simpa only [retainedOwnerPlankFamily_family_apply] using hxi)

/-- Every retained thickened owner lies in the same-radius thickening of the
source ambient body. -/
theorem retainedOwnerThickenedFamily_familyUnion_subset_ambientThickening
    (D : ShadedConvexPlankFamily iota a b) {theta : NNReal}
    (C : MutualThickeningClustering D theta)
    (q : Fin (Nat.log 2 (Fintype.card iota) + 1)) :
    familyUnion (retainedOwnerThickenedFamily D C q) ⊆
      Metric.cthickening ((theta * b : NNReal) : Real)
        (D.ambient : Set Space) := by
  intro x hx
  obtain ⟨s, hxs⟩ := Set.mem_iUnion.mp hx
  exact Metric.cthickening_subset_of_subset
    (((theta * b : NNReal) : Real)) (D.contained_in_ambient s.1) (by
      simpa only [retainedOwnerThickenedFamily, coe_ownerThickenedBody]
        using hxs)

/-- The union used as the CubeWeight packing ambient is contained in one
literal thickening of the original ambient body. -/
theorem retainedOwnerPackingAmbient_subset_ambientThickening
    (D : ShadedConvexPlankFamily iota a b) {theta : NNReal}
    (C : MutualThickeningClustering D theta)
    (q : Fin (Nat.log 2 (Fintype.card iota) + 1)) :
    familyUnion (retainedOwnerPlankFamily D C q).family ∪
        familyUnion (retainedOwnerThickenedFamily D C q) ⊆
      Metric.cthickening ((theta * b : NNReal) : Real)
        (D.ambient : Set Space) := by
  apply Set.union_subset
  · exact (retainedOwnerPlankFamily_familyUnion_subset_ambient D C q).trans
      (Metric.self_subset_cthickening _)
  · exact
      retainedOwnerThickenedFamily_familyUnion_subset_ambientThickening D C q

/-- Thickening the actual packing ambient by the packing radius stays inside
the sum-radius thickening of the original unit-scale ambient body. -/
theorem retainedOwnerPackingAmbient_thickening_subset
    (D : ShadedConvexPlankFamily iota a b) {theta : NNReal}
    (C : MutualThickeningClustering D theta)
    (q : Fin (Nat.log 2 (Fintype.card iota) + 1)) (r : NNReal) :
    Metric.thickening (r : Real)
        (familyUnion (retainedOwnerPlankFamily D C q).family ∪
          familyUnion (retainedOwnerThickenedFamily D C q)) ⊆
      Metric.thickening
        ((r : Real) + ((theta * b : NNReal) : Real))
        (D.ambient : Set Space) := by
  exact (Metric.thickening_subset_of_subset (r : Real)
    (retainedOwnerPackingAmbient_subset_ambientThickening D C q)).trans
      (Metric.thickening_cthickening_subset (r : Real)
        (by positivity : 0 ≤ ((theta * b : NNReal) : Real))
        (D.ambient : Set Space))

/-- Genuine packing separation bounds the literal center count, in the
division-free form used by the later cutoff comparison. -/
theorem retainedOwnerPacking_card_smul_ballVolume_le_ambientThickening
    (D : ShadedConvexPlankFamily iota a b) {theta : NNReal}
    (C : MutualThickeningClustering D theta)
    (q : Fin (Nat.log 2 (Fintype.card iota) + 1)) (r : NNReal)
    (P : PackingCertificate
      (familyUnion (retainedOwnerPlankFamily D C q).family ∪
        familyUnion (retainedOwnerThickenedFamily D C q)) r) :
    P.centers.card • volume (Metric.ball (0 : Space) (r : Real)) ≤
      volume (Metric.thickening
        ((r : Real) + ((theta * b : NNReal) : Real))
        (D.ambient : Set Space)) := by
  exact P.card_smul_ballVolume_le_thickening.trans
    (measure_mono (retainedOwnerPackingAmbient_thickening_subset D C q r))

/-- The ambient volume in the packing-card bound is finite. -/
theorem retainedOwnerPacking_ambientThickening_volume_lt_top
    (D : ShadedConvexPlankFamily iota a b) {theta : NNReal}
    (r : NNReal) :
    volume (Metric.thickening
      ((r : Real) + ((theta * b : NNReal) : Real))
      (D.ambient : Set Space)) < ∞ := by
  exact (measure_mono (Metric.thickening_subset_cthickening _ _)).trans_lt
    D.ambient.isCompact.cthickening.measure_lt_top

#print axioms retainedOwnerPlankFamily_familyUnion_subset_ambient
#print axioms retainedOwnerThickenedFamily_familyUnion_subset_ambientThickening
#print axioms retainedOwnerPackingAmbient_subset_ambientThickening
#print axioms retainedOwnerPackingAmbient_thickening_subset
#print axioms retainedOwnerPacking_card_smul_ballVolume_le_ambientThickening
#print axioms retainedOwnerPacking_ambientThickening_volume_lt_top

end
end Family8PlankRetainedOwnerPackingAmbientBoundV1
