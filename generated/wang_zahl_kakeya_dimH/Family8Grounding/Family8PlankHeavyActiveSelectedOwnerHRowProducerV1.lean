import Family8Grounding.Family8PlankHeavyActiveSelectedOwnerRowMassEndpointV2
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal InnerProductSpace

namespace Family8PlankHeavyActiveSelectedOwnerHRowProducerV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Family6AffinePlankAnalyticHypothesesStableV1
open Family6CanonicalCertifiedPlankSlabIncidenceCoreV3
open Family8PlankThickControlMutualContainmentClusteringV2
open Family8PlankThickControlOwnerFiberLogBucketV2
open Family8PlankThickControlRetainedOwnerFamilyV3
open Family8PlankRetainedOwnerHeavyMassSelectionV3
open Family8CanonicalCertifiedPlankFineAngleRowsV1
open Family8PlankHeavyRetainedOwnerCellRestrictedCanonicalSlabV1
open Family8PlankHeavyRetainedOwnerActiveCellCommonBallContainerV1
open Family8PlankHeavyRetainedOwnerActiveCertifiedOwnerIncidenceV1
open Family8PlankHeavyActiveSelectedOwnerRepresentativeDatumV2
open Family8PlankHeavyActiveSelectedOwnerFlatPrismCountV1
open Family8PlankHeavyActiveSelectedOwnerRowMassEndpointV2

noncomputable section

universe u v

variable {iota : Type u} [Fintype iota] [DecidableEq iota]
variable {a b : NNReal}

/-!
# Producing one genuine nonempty active selected-owner row

The active certified incidence already records selected tangent coverage for
every active fine index.  Choosing one index from the proved nonempty active
support therefore produces a concrete scale and certified slab.  Its selected
coarse owner lies in the image row by construction, so the row is nonempty.
-/

/-- A nonempty active fine support produces one actual certified query whose
deduplicated selected-owner row is nonempty. -/
theorem exists_activeSelectedOwnersInCertifiedSlab_nonempty
    (D : ShadedConvexPlankFamily iota a b) {theta : NNReal}
    (C : MutualThickeningClustering D theta)
    (q : Fin (Nat.log 2 (Fintype.card iota) + 1))
    {cellIndex : Type v} (cell : cellIndex → Set Space)
    (hcell : ∀ p, MeasurableSet (cell p)) (selected : Finset cellIndex)
    (hmass :
      (retainedOwnerPlankFamily D C q).shading.shadingMass ≠ 0)
    (hactive : (activeRetainedOwnerCellIndices
      D C q cell hcell selected).Nonempty) :
    ∃ (thetaScale : NNReal) (S : ConvexBody Space)
        (_hS : IsSlab 1 thetaScale S),
      a / b ≤ thetaScale ∧ thetaScale ≤ 1 ∧
        (activeSelectedOwnersInCertifiedSlab
          D C q cell hcell selected hmass hactive thetaScale S).Nonempty := by
  let R := activeRetainedOwnerCellCertifiedIncidence
    D C q cell hcell selected hmass hactive
  let i : {i // i ∈ activeRetainedOwnerCellIndices
      D C q cell hcell selected} :=
    ⟨hactive.choose, hactive.choose_spec⟩
  obtain ⟨thetaScale, S, hS, hthetaLower, hthetaUpper, hi⟩ :=
    R.member_coverage i
  refine ⟨thetaScale, S, hS, hthetaLower, hthetaUpper, ?_⟩
  refine ⟨selectedOwnerOfRetained C q i.1, ?_⟩
  exact Finset.mem_image.mpr ⟨i, hi, rfl⟩

/-- The produced row simultaneously carries the existing geometric count
bound and the complete-owner-fibre mass floor on every row member. -/
theorem exists_activeSelectedOwnersInCertifiedSlab_propertyRow
    (D : ShadedConvexPlankFamily iota a b) {theta : NNReal}
    (C : MutualThickeningClustering D theta)
    (q : Fin (Nat.log 2 (Fintype.card iota) + 1))
    {cellIndex : Type v} (cell : cellIndex → Set Space)
    (hcell : ∀ p, MeasurableSet (cell p)) (selected : Finset cellIndex)
    (hmass :
      (retainedOwnerPlankFamily D C q).shading.shadingMass ≠ 0)
    (hactive : (activeRetainedOwnerCellIndices
      D C q cell hcell selected).Nonempty) :
    ∃ (thetaScale : NNReal) (S : ConvexBody Space)
        (_hS : IsSlab 1 thetaScale S),
      a / b ≤ thetaScale ∧ thetaScale ≤ 1 ∧
      (activeSelectedOwnersInCertifiedSlab
        D C q cell hcell selected hmass hactive thetaScale S).Nonempty ∧
      (activeSelectedOwnersInCertifiedSlab
        D C q cell hcell selected hmass hactive thetaScale S).card ≤
          canonicalCertifiedFineAngleOccupancy
            (heavyRetainedOwnerCellRestrictedCanonicalUnitSlabIncidence
              D C q cell hcell selected hmass) 2 thetaScale ∧
      ((activeSelectedOwnersInCertifiedSlab
          D C q cell hcell selected hmass hactive thetaScale S).card : ENNReal) *
          (((D.comparisonConstant⁻¹ : NNReal) : ENNReal) ^ 3 *
            ((a : ENNReal) * (b : ENNReal))) ≤
        maximalConcentration D.family *
          (((thetaScale : ENNReal) +
              4 * ((theta : ENNReal) * (b : ENNReal))) *
            (((1 : ENNReal) +
              4 * ((theta : ENNReal) * (b : ENNReal))) ^ 2)) ∧
      ∀ s : {s // s ∈ activeSelectedOwnersInCertifiedSlab
          D C q cell hcell selected hmass hactive thetaScale S},
        retainedOwnerHalfAverageFloor C q ≤ ownerFiberMass C s.1.1 := by
  obtain ⟨thetaScale, S, hS, hthetaLower, hthetaUpper, hrow⟩ :=
    exists_activeSelectedOwnersInCertifiedSlab_nonempty
      D C q cell hcell selected hmass hactive
  have hangle :=
    activeSelectedOwnersInCertifiedSlab_card_le_angleOccupancy
      D C q cell hcell selected hmass hactive hS
  have hflat :=
    activeSelectedOwners_card_mul_plankVolumeLower_le_flatPrismReserve
      D C q cell hcell selected hmass hactive hS
  have hfloor :
      ∀ s : {s // s ∈ activeSelectedOwnersInCertifiedSlab
          D C q cell hcell selected hmass hactive thetaScale S},
        retainedOwnerHalfAverageFloor C q ≤ ownerFiberMass C s.1.1 := by
    intro s
    exact activeSelectedOwner_halfAverageFloor_le_ownerFiberMass
      D C q cell hcell selected hmass hactive thetaScale S s
  exact ⟨thetaScale, S, hS, hthetaLower, hthetaUpper,
    hrow, hangle, hflat, hfloor⟩

#print axioms exists_activeSelectedOwnersInCertifiedSlab_nonempty
#print axioms exists_activeSelectedOwnersInCertifiedSlab_propertyRow

end
end Family8PlankHeavyActiveSelectedOwnerHRowProducerV1
