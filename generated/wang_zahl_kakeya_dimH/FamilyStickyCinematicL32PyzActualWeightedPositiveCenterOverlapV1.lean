import FamilyStickyCinematicL32PyzActualProjectedNormThreeBallIndexedOverlapV1

set_option autoImplicit false

open Set MeasureTheory
open scoped BigOperators ENNReal

namespace FamilyStickyCinematicL32PyzActualWeightedPositiveCenterOverlapV1

open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open Family4GlobalExtremalUpstream
open FamilyStickyCinematicL32FiniteMetricMaximalCoverV1
open FamilyStickyCinematicL32ActualTubeCoefficientDistancesV1
open FamilyStickyCinematicL32Lemma57EssentiallyDistinctTubeImageV1
open FamilyStickyCinematicL32PyzActualCenteredHalfLocalizedSupportActualCleanV1
open FamilyStickyCinematicL32PyzActualProjectedNormThreeBallIndexedOverlapV1

noncomputable section

local instance tubeDecidableEq {radius : NNReal} :
    DecidableEq (Tube radius) := Classical.decEq _

/-!
# Weighted aggregation from positive centre cells only

The localized argument only needs to construct data for cover-centre cells of
positive measure.  A zero-measure cell contributes zero to the weighted sum,
so no dummy payload or retained-mass functions are needed there.  The indexed
`19 ^ 3` overlap theorem then removes the number of cover centres.
-/

universe u v

/-- Aggregate direct local estimates supplied only for positive-measure
cover-centre cells.  Zero-measure cells are discharged automatically, and the
conclusion contains no factor involving the number of centres. -/
theorem actual_weighted_positiveCenter_overlap
    {X : Type v} [MeasurableSpace X]
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    (mu : Measure X) (E : Set X)
    (fine : UniformTubeFamily radius iota) (ambient : Finset iota)
    (hradius : 0 < radius)
    (hpair : Set.Pairwise (ambient : Set iota) fun i j ↦
      EssentiallyDistinct (fine.tubes i) (fine.tubes j))
    {globalScale : Real} (hglobalScale : 0 < globalScale)
    (cell : Tube radius → Set X)
    (weight commonCost : ENNReal)
    (hpartition :
      mu E = ∑ center ∈ finiteMetricCoverCenters
          (activeTubeImage fine ambient)
          projectedTubePairCoefficientDistance globalScale
          (fun U V ↦ projectedTubePairCoefficientDistance_comm U V),
        mu (cell center))
    (hpositiveCell : ∀ center, center ∈ finiteMetricCoverCenters
        (activeTubeImage fine ambient)
        projectedTubePairCoefficientDistance globalScale
        (fun U V ↦ projectedTubePairCoefficientDistance_comm U V) →
      0 < mu (cell center) →
      weight * mu (cell center) ≤
        commonCost *
          ((actualProjectedNormThreeBallIndices fine ambient globalScale
            center).card : ENNReal)) :
    weight * mu E ≤
      commonCost * ((19 ^ 3 * ambient.card : Nat) : ENNReal) := by
  let centers := finiteMetricCoverCenters
    (activeTubeImage fine ambient)
    projectedTubePairCoefficientDistance globalScale
    (fun U V ↦ projectedTubePairCoefficientDistance_comm U V)
  have hcell : ∀ center, center ∈ centers →
      weight * mu (cell center) ≤
        commonCost *
          ((actualProjectedNormThreeBallIndices fine ambient globalScale
            center).card : ENNReal) := by
    intro center hcenter
    by_cases hpositive : 0 < mu (cell center)
    · exact hpositiveCell center (by simpa only [centers] using hcenter) hpositive
    · have hzero : mu (cell center) = 0 :=
        nonpos_iff_eq_zero.mp (not_lt.mp hpositive)
      simp only [hzero, mul_zero, zero_le]
  have hsumCard :
      ∑ center ∈ centers,
          (actualProjectedNormThreeBallIndices fine ambient globalScale
            center).card ≤
        19 ^ 3 * ambient.card := by
    simpa only [centers] using
      sum_actualProjectedNormThreeBallIndices_card_le fine ambient hradius
        hpair hglobalScale
  have hsumCardCast :
      ((∑ center ∈ centers,
          (actualProjectedNormThreeBallIndices fine ambient globalScale
            center).card : Nat) : ENNReal) ≤
        ((19 ^ 3 * ambient.card : Nat) : ENNReal) := by
    exact_mod_cast hsumCard
  calc
    weight * mu E =
        ∑ center ∈ centers, weight * mu (cell center) := by
      rw [hpartition]
      simp only [centers, Finset.mul_sum]
    _ ≤ ∑ center ∈ centers,
        commonCost *
          ((actualProjectedNormThreeBallIndices fine ambient globalScale
            center).card : ENNReal) := by
      exact Finset.sum_le_sum fun center hcenter ↦ hcell center hcenter
    _ = commonCost *
        ((∑ center ∈ centers,
          (actualProjectedNormThreeBallIndices fine ambient globalScale
            center).card : Nat) : ENNReal) := by
      simp only [Nat.cast_sum, Finset.mul_sum]
    _ ≤ commonCost * ((19 ^ 3 * ambient.card : Nat) : ENNReal) := by
      exact mul_le_mul_right hsumCardCast commonCost

#print axioms actual_weighted_positiveCenter_overlap

end

end FamilyStickyCinematicL32PyzActualWeightedPositiveCenterOverlapV1
