import FamilyStickyCinematicL32PyzActualCenteredHalfLocalizedSupportActualCleanV1
import FamilyStickyCinematicL32ProjectedCoverCenterFloorGridOverlapV1
import FamilyStickyCinematicL32Lemma57EssentiallyDistinctTubeImageV1

set_option autoImplicit false

open Set
open scoped BigOperators

namespace FamilyStickyCinematicL32PyzActualProjectedNormThreeBallIndexedOverlapV1

open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open Family4GlobalExtremalUpstream
open FamilyStickyCinematicL32Lemma57EssentiallyDistinctTubeImageV1
open FamilyStickyCinematicL32ActualTubeCoefficientDistancesV1
open FamilyStickyCinematicL32FiniteMetricMaximalCoverV1
open FamilyStickyCinematicL32FiniteNormGlobalCoverLocalizationV1
open FamilyStickyCinematicL32ProjectedCoverCenterFloorGridOverlapV1
open FamilyStickyCinematicL32PyzActualCenteredHalfLocalizedSupportActualCleanV1

noncomputable section

local instance tubeDecidableEq {radius : NNReal} :
    DecidableEq (Tube radius) := Classical.decEq _

/-!
# Bounded overlap for the indexed actual projected `3B` families

The coefficient-cover overlap theorem is stated for a concrete finite family
of tubes, whereas the low-multiplicity moment is indexed by the ambient tube
indices.  Positive-radius essential distinctness makes the actual tube map
injective on those indices.  Thus every closed projected `3B` has exactly the
same cardinality in the two representations, and the dimension-only
`19 ^ 3` overlap bound transfers without a centre-count loss.
-/

/-- The concrete localized tube family is the image of the corresponding
indexed actual projected `3B`. -/
theorem finiteGlobalNormLocalizedFamily_eq_threeBallIndices_image
    {radius : NNReal} {iota : Type*} [DecidableEq iota]
    (fine : UniformTubeFamily radius iota) (ambient : Finset iota)
    (globalScale : Real) (globalCenter : Tube radius) :
    finiteGlobalNormLocalizedFamily (activeTubeImage fine ambient)
        projectedTubePairCoefficientDistance globalScale globalCenter =
      (actualProjectedNormThreeBallIndices fine ambient globalScale
        globalCenter).image fine.tubes := by
  classical
  ext T
  change
    (T ∈ (ambient.image fine.tubes).filter fun U =>
      projectedTubePairCoefficientDistance U globalCenter ≤
        3 * globalScale) ↔
    T ∈ (ambient.filter fun i =>
      projectedTubePairCoefficientDistance (fine.tubes i) globalCenter ≤
        3 * globalScale).image fine.tubes
  simp only [Finset.mem_filter, Finset.mem_image]
  constructor
  · rintro ⟨⟨i, hi, rfl⟩, hdistance⟩
    exact ⟨i, ⟨hi, hdistance⟩, rfl⟩
  · rintro ⟨i, ⟨hi, hdistance⟩, rfl⟩
    exact ⟨⟨i, hi, rfl⟩, hdistance⟩

/-- Under positive-radius essential distinctness, a concrete localized tube
family and its indexed actual projected `3B` have equal cardinality. -/
theorem finiteGlobalNormLocalizedFamily_card_eq_threeBallIndices_card
    {radius : NNReal} {iota : Type*} [DecidableEq iota]
    (fine : UniformTubeFamily radius iota) (ambient : Finset iota)
    (hradius : 0 < radius)
    (hpair : Set.Pairwise (ambient : Set iota) fun i j =>
      EssentiallyDistinct (fine.tubes i) (fine.tubes j))
    (globalScale : Real) (globalCenter : Tube radius) :
    (finiteGlobalNormLocalizedFamily (activeTubeImage fine ambient)
      projectedTubePairCoefficientDistance globalScale globalCenter).card =
      (actualProjectedNormThreeBallIndices fine ambient globalScale
        globalCenter).card := by
  classical
  rw [finiteGlobalNormLocalizedFamily_eq_threeBallIndices_image]
  apply Finset.card_image_iff.mpr
  intro i hi j hj htube
  have hiAmbient : i ∈ ambient := (Finset.mem_filter.mp hi).1
  have hjAmbient : j ∈ ambient := (Finset.mem_filter.mp hj).1
  exact tubes_injectiveOn_active_of_essentiallyDistinct fine ambient
    hradius hpair hiAmbient hjAmbient htube

/-- Summing the indexed actual projected `3B` cardinalities over every
maximal-cover centre costs only the bounded-overlap constant `19 ^ 3`, not
the number of centres. -/
theorem sum_actualProjectedNormThreeBallIndices_card_le
    {radius : NNReal} {iota : Type*} [DecidableEq iota]
    (fine : UniformTubeFamily radius iota) (ambient : Finset iota)
    (hradius : 0 < radius)
    (hpair : Set.Pairwise (ambient : Set iota) fun i j =>
      EssentiallyDistinct (fine.tubes i) (fine.tubes j))
    {globalScale : Real} (hglobalScale : 0 < globalScale) :
    ∑ globalCenter ∈ finiteMetricCoverCenters
        (activeTubeImage fine ambient)
        projectedTubePairCoefficientDistance globalScale
        (fun U V => projectedTubePairCoefficientDistance_comm U V),
      (actualProjectedNormThreeBallIndices fine ambient globalScale
        globalCenter).card ≤
      19 ^ 3 * ambient.card := by
  classical
  calc
    (∑ globalCenter ∈ finiteMetricCoverCenters
        (activeTubeImage fine ambient)
        projectedTubePairCoefficientDistance globalScale
        (fun U V => projectedTubePairCoefficientDistance_comm U V),
      (actualProjectedNormThreeBallIndices fine ambient globalScale
        globalCenter).card) =
        ∑ globalCenter ∈ finiteMetricCoverCenters
          (activeTubeImage fine ambient)
          projectedTubePairCoefficientDistance globalScale
          (fun U V => projectedTubePairCoefficientDistance_comm U V),
        (finiteGlobalNormLocalizedFamily (activeTubeImage fine ambient)
          projectedTubePairCoefficientDistance globalScale
          globalCenter).card := by
      apply Finset.sum_congr rfl
      intro globalCenter _hglobalCenter
      exact (finiteGlobalNormLocalizedFamily_card_eq_threeBallIndices_card
        fine ambient hradius hpair globalScale globalCenter).symm
    _ ≤ 19 ^ 3 * (activeTubeImage fine ambient).card :=
      sum_projected_globalNormLocalizedFamily_card_le
        (activeTubeImage fine ambient) hglobalScale
    _ = 19 ^ 3 * ambient.card := by
      rw [activeTubeImage_card fine ambient hradius hpair]

#print axioms finiteGlobalNormLocalizedFamily_eq_threeBallIndices_image
#print axioms finiteGlobalNormLocalizedFamily_card_eq_threeBallIndices_card
#print axioms sum_actualProjectedNormThreeBallIndices_card_le

end

end FamilyStickyCinematicL32PyzActualProjectedNormThreeBallIndexedOverlapV1
