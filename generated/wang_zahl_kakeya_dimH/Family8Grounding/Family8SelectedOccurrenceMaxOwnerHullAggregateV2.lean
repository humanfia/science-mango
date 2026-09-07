import Family8Grounding.Family8SelectedOccurrenceMaxOwnerHullQualityV3
import Mathlib.Tactic

/-!
# Aggregate mass and average loss for quality-owner occurrence hulls

The per-block finite-argmax estimate is summed over any selected occurrence
set.  Under a literal fibre-card upper bound `M`, both selected shaded mass
and average multiplicity lose at most `M`.  The average statement uses the
proved inclusion of the refined shaded union in the original selected union.
-/

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8SelectedOccurrenceMaxOwnerHullAggregateV2

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
open Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
open Submission.Kakeya.Uniformity
open Family8SelectedOccurrenceActiveParentOwnerV7
open Family8SelectedOccurrenceDensityFrostmanV1
open Family8SelectedOccurrenceMaxOwnerHullQualityV3
open FamilyStickyAtEveryScaleCoreV1

noncomputable section

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5000000

local instance (p : Prop) : Decidable p := Classical.propDecidable p

variable {delta rho : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {fine : UniformTubeFamily delta index}
  (C : StickyScaleCover fine rho)
  (P : GreedyDensityPartition fine.bodyFamily
    (hullCandidates C.activeFine) (hullContainer fine.bodyFamily)
    C.activeFine)
  (Y : Shading fine.bodyFamily)

/-- The selected family of genuine quality-owner hulls. -/
abbrev selectedOccurrenceMaxOwnerHullFamily
    (R : Finset (Fin (blocks fine.bodyFamily P).length)) :
    ConvexFamily {q // q ∈ selectedOccurrenceIndices P R} :=
  fun q => occurrenceMaxOwnerHull C P Y
    (selectedOccurrencePosition C R q)

/-- The corresponding literal union shading of the chosen actual-parent
subfibre in each occurrence. -/
def selectedOccurrenceMaxOwnerHullShading
    (R : Finset (Fin (blocks fine.bodyFamily P).length)) :
    Shading (selectedOccurrenceMaxOwnerHullFamily C P Y R) where
  carrier q := occurrenceMaxOwnerCarrier C P Y
    (selectedOccurrencePosition C R q)
  measurable_carrier q := measurableSet_occurrenceMaxOwnerCarrier C P Y
    (selectedOccurrencePosition C R q)
  carrier_subset q := occurrenceMaxOwnerCarrier_subset_hull C P Y
    (selectedOccurrencePosition C R q)

/-- Selected occurrence labels are equivalent to the literal selected block
positions. -/
def selectedOccurrencePositionEquiv
    (R : Finset (Fin (blocks fine.bodyFamily P).length)) :
    {k // k ∈ R} ≃ {q // q ∈ selectedOccurrenceIndices P R} where
  toFun k := selectedOccurrenceIndexOf P R k.1 k.2
  invFun q := ⟨selectedOccurrencePosition C R q,
    selectedOccurrencePosition_mem C R q⟩
  left_inv k := by
    apply Subtype.ext
    exact Option.some.inj
      (some_selectedOccurrencePosition_eq C R
        (selectedOccurrenceIndexOf P R k.1 k.2))
  right_inv q := (selectedOccurrence_eq_indexOf C R q).symm

/-- Exact sum formula for the refined selected shaded mass. -/
theorem selectedOccurrenceMaxOwnerHullShading_mass_eq_sum
    (R : Finset (Fin (blocks fine.bodyFamily P).length)) :
    (selectedOccurrenceMaxOwnerHullShading C P Y R).shadingMass =
      ∑ k ∈ R, volume (occurrenceMaxOwnerCarrier C P Y k) := by
  classical
  unfold Shading.shadingMass
  calc
    (∑ q, volume
        ((selectedOccurrenceMaxOwnerHullShading C P Y R).carrier q)) =
        ∑ k : {k // k ∈ R},
          volume (occurrenceMaxOwnerCarrier C P Y k.1) := by
      symm
      apply Fintype.sum_equiv (selectedOccurrencePositionEquiv C P R)
        (fun k : {k // k ∈ R} =>
          volume (occurrenceMaxOwnerCarrier C P Y k.1))
        (fun q => volume
          ((selectedOccurrenceMaxOwnerHullShading C P Y R).carrier q))
      intro k
      have hpos : selectedOccurrencePosition C R
          (selectedOccurrenceIndexOf P R k.1 k.2) = k.1 :=
        Option.some.inj
          (some_selectedOccurrencePosition_eq C R
            (selectedOccurrenceIndexOf P R k.1 k.2))
      change volume (occurrenceMaxOwnerCarrier C P Y k.1) =
        volume (occurrenceMaxOwnerCarrier C P Y
          (selectedOccurrencePosition C R
            (selectedOccurrenceIndexOf P R k.1 k.2)))
      exact (congrArg
        (fun t => volume (occurrenceMaxOwnerCarrier C P Y t)) hpos).symm
    _ = ∑ k ∈ R, volume (occurrenceMaxOwnerCarrier C P Y k) := by
      symm
      exact Finset.sum_subtype _ (fun _k => Iff.rfl) _

/-- The refined carrier of one block is contained in its original induced
outer carrier. -/
theorem occurrenceMaxOwnerCarrier_subset_outerCarrier
    (k : Fin (blocks fine.bodyFamily P).length) :
    occurrenceMaxOwnerCarrier C P Y k ⊆
      ((convexFactorization fine.bodyFamily P).inducedShading Y).carrier
        (some k) := by
  intro x hx
  obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hx
  apply (ConvexFactorization.mem_inducedShading_carrier_iff
    (convexFactorization fine.bodyFamily P) Y (some k) x).2
  constructor
  · change some k ∈ occurrenceIndices fine.bodyFamily P
    simp [occurrenceIndices]
  · refine ⟨i.1, ?_, hxi⟩
    change i.1 ∈ (indexFactorization fine.bodyFamily P).fiber (some k)
    rw [indexFactorization_fiber_eq_blockAt]
    exact (mem_occurrenceMaxOwnerSubfiber C P Y k i.1).mp i.2 |>.1

/-- Memberwise refined selected carriers sit inside the old selected outer
shading on the same occurrence. -/
theorem selectedOccurrenceMaxOwnerHullShading_carrier_subset_outer
    (R : Finset (Fin (blocks fine.bodyFamily P).length))
    (q : {q // q ∈ selectedOccurrenceIndices P R}) :
    (selectedOccurrenceMaxOwnerHullShading C P Y R).carrier q ⊆
      (selectedOccurrenceOuterShading P Y R).carrier q := by
  let k := selectedOccurrencePosition C R q
  have hk := selectedOccurrencePosition_mem C R q
  have hq : q = selectedOccurrenceIndexOf P R k hk := by
    simpa only [k] using selectedOccurrence_eq_indexOf C R q
  have hpos : selectedOccurrencePosition C R
      (selectedOccurrenceIndexOf P R k hk) = k :=
    Option.some.inj
      (some_selectedOccurrencePosition_eq C R
        (selectedOccurrenceIndexOf P R k hk))
  rw [hq, selectedOccurrenceOuterShading_carrier_indexOf]
  change occurrenceMaxOwnerCarrier C P Y
      (selectedOccurrencePosition C R
        (selectedOccurrenceIndexOf P R k hk)) ⊆
    ((convexFactorization fine.bodyFamily P).inducedShading Y).carrier (some k)
  rw [hpos]
  exact occurrenceMaxOwnerCarrier_subset_outerCarrier C P Y k

/-- Hence the full refined selected shaded union is a literal subset of the
old selected shaded union. -/
theorem selectedOccurrenceMaxOwnerHullShading_shadedUnion_subset_outer
    (R : Finset (Fin (blocks fine.bodyFamily P).length)) :
    (selectedOccurrenceMaxOwnerHullShading C P Y R).shadedUnion ⊆
      (selectedOccurrenceOuterShading P Y R).shadedUnion := by
  intro x hx
  obtain ⟨q, hxq⟩ := Set.mem_iUnion.mp hx
  exact Set.mem_iUnion.mpr
    ⟨q, selectedOccurrenceMaxOwnerHullShading_carrier_subset_outer
      C P Y R q hxq⟩

/-- A uniform literal fibre-card cap gives the same explicit aggregate mass
loss for the quality-owner refinement. -/
theorem selectedOccurrenceOuterShading_mass_le_maxOwnerHull
    (R : Finset (Fin (blocks fine.bodyFamily P).length))
    (M : Nat)
    (hcard : ∀ k ∈ R, (blockAt fine.bodyFamily P k).fiber.card ≤ M) :
    (selectedOccurrenceOuterShading P Y R).shadingMass ≤
      (M : ENNReal) *
        (selectedOccurrenceMaxOwnerHullShading C P Y R).shadingMass := by
  rw [selectedOccurrenceOuterShading_mass,
    selectedOccurrenceMaxOwnerHullShading_mass_eq_sum]
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro k hk
  calc
    volume (((convexFactorization fine.bodyFamily P).inducedShading Y).carrier
        (some k)) ≤
      (((blockAt fine.bodyFamily P k).fiber.card : Nat) : ENNReal) *
        volume (occurrenceMaxOwnerCarrier C P Y k) :=
      occurrenceOuterCarrier_volume_le_card_mul_maxOwnerCarrier C P Y k
    _ ≤ (M : ENNReal) * volume (occurrenceMaxOwnerCarrier C P Y k) := by
      gcongr
      exact_mod_cast hcard k hk

/-- The identical `M` loss transports to selected average multiplicity. -/
theorem selectedOccurrenceOuterShading_average_le_maxOwnerHull
    (R : Finset (Fin (blocks fine.bodyFamily P).length))
    (M : Nat)
    (hcard : ∀ k ∈ R, (blockAt fine.bodyFamily P k).fiber.card ≤ M) :
    (selectedOccurrenceOuterShading P Y R).averageMultiplicity ≤
      (M : ENNReal) *
        (selectedOccurrenceMaxOwnerHullShading C P Y R).averageMultiplicity := by
  have hmass := selectedOccurrenceOuterShading_mass_le_maxOwnerHull
    C P Y R M hcard
  have hunion :=
    selectedOccurrenceMaxOwnerHullShading_shadedUnion_subset_outer C P Y R
  unfold Shading.averageMultiplicity
  calc
    (selectedOccurrenceOuterShading P Y R).shadingMass /
          volume (selectedOccurrenceOuterShading P Y R).shadedUnion ≤
        ((M : ENNReal) *
          (selectedOccurrenceMaxOwnerHullShading C P Y R).shadingMass) /
          volume (selectedOccurrenceOuterShading P Y R).shadedUnion :=
      ENNReal.div_le_div_right hmass _
    _ ≤ ((M : ENNReal) *
          (selectedOccurrenceMaxOwnerHullShading C P Y R).shadingMass) /
          volume
            (selectedOccurrenceMaxOwnerHullShading C P Y R).shadedUnion := by
      exact ENNReal.div_le_div_left (measure_mono hunion) _
    _ = (M : ENNReal) *
          ((selectedOccurrenceMaxOwnerHullShading C P Y R).shadingMass /
            volume
              (selectedOccurrenceMaxOwnerHullShading C P Y R).shadedUnion) := by
      simp only [div_eq_mul_inv]
      ac_rfl

#print axioms selectedOccurrencePositionEquiv
#print axioms selectedOccurrenceMaxOwnerHullShading_mass_eq_sum
#print axioms occurrenceMaxOwnerCarrier_subset_outerCarrier
#print axioms selectedOccurrenceMaxOwnerHullShading_shadedUnion_subset_outer
#print axioms selectedOccurrenceOuterShading_mass_le_maxOwnerHull
#print axioms selectedOccurrenceOuterShading_average_le_maxOwnerHull

end

end Family8SelectedOccurrenceMaxOwnerHullAggregateV2
