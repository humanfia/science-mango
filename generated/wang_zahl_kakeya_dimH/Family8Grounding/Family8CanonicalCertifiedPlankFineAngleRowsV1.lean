import Family8Grounding.Family8PlankRetainedOwnerCellRestrictedCanonicalSlabV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal InnerProductSpace

namespace Family8CanonicalCertifiedPlankFineAngleRowsV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Family6AffinePlankAnalyticHypothesesStableV1
open Family6FaithfulPlankSlabIncidenceCoreV9
open Family6CanonicalCertifiedPlankSlabIncidenceCoreV3
open Family8PlankThickControlMutualContainmentClusteringV2
open Family8PlankThickControlOwnerFiberLogBucketV2
open Family8PlankThickControlRetainedOwnerFamilyV3
open Family8PlankRetainedOwnerCellRestrictedCanonicalSlabV1

noncomputable section

universe u v w

/-!
# Canonical certified slab members lie in literal fine-angle rows

The canonical certified incidence fixes one slab certificate for each query.
Consequently two actual members share that certificate and their framed short
normals have projective sine at most twice the tangent scale.  This file
constructs the resulting finite rows and their exact occupancy; no
scale-dependent count estimate is assumed.
-/

def canonicalCertifiedPairSine
    {sourceIndex : Type v} [Fintype sourceIndex] [DecidableEq sourceIndex]
    {index : Type u} [Fintype index] [DecidableEq index]
    {a b : NNReal} {D : ShadedConvexPlankFamily index a b}
    {slabComparisonConstant tangentComparisonConstant : NNReal}
    (R : CanonicalCertifiedPlankSlabIncidence sourceIndex index D
      slabComparisonConstant tangentComparisonConstant)
    (i j : index) : NNReal :=
  Real.toNNReal <| Real.sin <|
    InnerProductGeometry.angle
      ((R.plank i).box.frame 0) ((R.plank j).box.frame 0)

def canonicalCertifiedFineAngleRow
    {sourceIndex : Type v} [Fintype sourceIndex] [DecidableEq sourceIndex]
    {index : Type u} [Fintype index] [DecidableEq index]
    {a b : NNReal} {D : ShadedConvexPlankFamily index a b}
    {slabComparisonConstant tangentComparisonConstant : NNReal}
    (R : CanonicalCertifiedPlankSlabIncidence sourceIndex index D
      slabComparisonConstant tangentComparisonConstant)
    (angleComparisonConstant theta : NNReal) (i : index) : Finset index := by
  classical
  exact Finset.univ.filter fun j =>
    canonicalCertifiedPairSine R i j ≤ angleComparisonConstant * theta

@[simp] theorem mem_canonicalCertifiedFineAngleRow
    {sourceIndex : Type v} [Fintype sourceIndex] [DecidableEq sourceIndex]
    {index : Type u} [Fintype index] [DecidableEq index]
    {a b : NNReal} {D : ShadedConvexPlankFamily index a b}
    {slabComparisonConstant tangentComparisonConstant : NNReal}
    (R : CanonicalCertifiedPlankSlabIncidence sourceIndex index D
      slabComparisonConstant tangentComparisonConstant)
    (angleComparisonConstant theta : NNReal) (i j : index) :
    j ∈ canonicalCertifiedFineAngleRow R angleComparisonConstant theta i ↔
      canonicalCertifiedPairSine R i j ≤ angleComparisonConstant * theta := by
  classical
  simp [canonicalCertifiedFineAngleRow]

theorem canonicalCertifiedPairSine_le_two_mul
    {sourceIndex : Type v} [Fintype sourceIndex] [DecidableEq sourceIndex]
    {index : Type u} [Fintype index] [DecidableEq index]
    {a b : NNReal} {D : ShadedConvexPlankFamily index a b}
    {slabComparisonConstant tangentComparisonConstant : NNReal}
    (R : CanonicalCertifiedPlankSlabIncidence sourceIndex index D
      slabComparisonConstant tangentComparisonConstant)
    {theta : NNReal} {S : ConvexBody Space}
    (hS : IsSlab slabComparisonConstant theta S)
    {i j : index} (hi : i ∈ R.members theta S)
    (hj : j ∈ R.members theta S) :
    canonicalCertifiedPairSine R i j ≤
      (2 * tangentComparisonConstant) * theta := by
  have hpair := R.pair_sine_le_two_mul hS hi hj
  have hsineNonneg := InnerProductGeometry.sin_angle_nonneg
    ((R.plank i).box.frame 0) ((R.plank j).box.frame 0)
  apply NNReal.coe_le_coe.mp
  simp only [canonicalCertifiedPairSine, Real.coe_toNNReal _ hsineNonneg,
    NNReal.coe_mul, NNReal.coe_ofNat]
  simpa [mul_assoc] using hpair

theorem canonicalCertified_members_subset_angleRow
    {sourceIndex : Type v} [Fintype sourceIndex] [DecidableEq sourceIndex]
    {index : Type u} [Fintype index] [DecidableEq index]
    {a b : NNReal} {D : ShadedConvexPlankFamily index a b}
    {slabComparisonConstant tangentComparisonConstant : NNReal}
    (R : CanonicalCertifiedPlankSlabIncidence sourceIndex index D
      slabComparisonConstant tangentComparisonConstant)
    {theta : NNReal} {S : ConvexBody Space}
    (hS : IsSlab slabComparisonConstant theta S)
    {i : index} (hi : i ∈ R.members theta S) :
    R.members theta S ⊆
      canonicalCertifiedFineAngleRow R
        (2 * tangentComparisonConstant) theta i := by
  intro j hj
  exact (mem_canonicalCertifiedFineAngleRow
    R (2 * tangentComparisonConstant) theta i j).2
      (canonicalCertifiedPairSine_le_two_mul R hS hi hj)

def canonicalCertifiedFineAngleOccupancy
    {sourceIndex : Type v} [Fintype sourceIndex] [DecidableEq sourceIndex]
    {index : Type u} [Fintype index] [DecidableEq index]
    {a b : NNReal} {D : ShadedConvexPlankFamily index a b}
    {slabComparisonConstant tangentComparisonConstant : NNReal}
    (R : CanonicalCertifiedPlankSlabIncidence sourceIndex index D
      slabComparisonConstant tangentComparisonConstant)
    (angleComparisonConstant theta : NNReal) : Nat :=
  Finset.univ.sup fun i =>
    (canonicalCertifiedFineAngleRow R angleComparisonConstant theta i).card

theorem canonicalCertified_members_card_le_angleOccupancy
    {sourceIndex : Type v} [Fintype sourceIndex] [DecidableEq sourceIndex]
    {index : Type u} [Fintype index] [DecidableEq index]
    {a b : NNReal} {D : ShadedConvexPlankFamily index a b}
    {slabComparisonConstant tangentComparisonConstant : NNReal}
    (R : CanonicalCertifiedPlankSlabIncidence sourceIndex index D
      slabComparisonConstant tangentComparisonConstant)
    {theta : NNReal} {S : ConvexBody Space}
    (hS : IsSlab slabComparisonConstant theta S) :
    (R.members theta S).card ≤
      canonicalCertifiedFineAngleOccupancy R
        (2 * tangentComparisonConstant) theta := by
  classical
  by_cases hne : (R.members theta S).Nonempty
  · obtain ⟨i, hi⟩ := hne
    exact (Finset.card_le_card
      (canonicalCertified_members_subset_angleRow R hS hi)).trans
        (Finset.le_sup
          (f := fun j =>
            (canonicalCertifiedFineAngleRow R
              (2 * tangentComparisonConstant) theta j).card)
          (Finset.mem_univ i))
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne]
    simp

/-- Specialization to the literal cell-restricted retained fine datum.  The
angle constant is exactly `2` because its canonical incidence has tangent
comparison constant `1`. -/
theorem retainedOwnerCellRestricted_members_card_le_angleOccupancy
    {iota : Type u} [Fintype iota] [DecidableEq iota]
    {a b theta : NNReal} (D : ShadedConvexPlankFamily iota a b)
    (C : MutualThickeningClustering D theta)
    (q : Fin (Nat.log 2 (Fintype.card iota) + 1))
    {cellIndex : Type w} (cell : cellIndex → Set Space)
    (hcell : ∀ p, MeasurableSet (cell p)) (selected : Finset cellIndex)
    (hmass : (retainedOwnerPlankFamily D C q).shading.shadingMass ≠ 0)
    {tau : NNReal} {S : ConvexBody Space} (hS : IsSlab 1 tau S) :
    let R := retainedOwnerCellRestrictedCanonicalUnitSlabIncidence
      D C q cell hcell selected hmass
    (R.members tau S).card ≤
      canonicalCertifiedFineAngleOccupancy R 2 tau := by
  dsimp only
  simpa using canonicalCertified_members_card_le_angleOccupancy
    (retainedOwnerCellRestrictedCanonicalUnitSlabIncidence
      D C q cell hcell selected hmass) hS

#print axioms canonicalCertifiedPairSine_le_two_mul
#print axioms canonicalCertified_members_subset_angleRow
#print axioms canonicalCertified_members_card_le_angleOccupancy
#print axioms retainedOwnerCellRestricted_members_card_le_angleOccupancy

end
end Family8CanonicalCertifiedPlankFineAngleRowsV1
