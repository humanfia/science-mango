import Family8Grounding.Family8PlankActiveSelectedOwnerFlatPrismCountV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal InnerProductSpace

namespace Family8PlankActiveSelectedOwnerSameScaleLinearCountV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Family6AffinePlankAnalyticHypothesesStableV1
open Family8CanonicalCertifiedPlankFineAngleRowsV1
open Family8PlankThickControlMutualContainmentClusteringV2
open Family8PlankThickControlOwnerFiberLogBucketV2
open Family8PlankThickControlRetainedOwnerFamilyV3
open Family8PlankRetainedOwnerCellRestrictedCanonicalSlabV1
open Family8PlankRetainedOwnerActiveCellCommonBallContainerV1
open Family8PlankRetainedOwnerActiveCertifiedOwnerIncidenceV1
open Family8PlankActiveSelectedOwnerRepresentativeDatumV1
open Family8PlankActiveSelectedOwnerFlatPrismCountV1

noncomputable section

universe u v

variable {iota : Type u} [Fintype iota] [DecidableEq iota]
variable {a b : NNReal}

/-!
# Same-scale linear count for the active selected-owner row

At the same slab and clustering scale, `b ≤ 1` makes the double owner
thickening of a `theta × 1 × 1` slab have volume at most `125 * theta`.
Combining this certified geometric fact with the previous contained-mass
reserve gives a scale-linear Family6-style owner count.  The final theorem
records the minimum of this analytic count and the independent V279 angle
occupancy count.
-/

/-- The controlled flat-prism container has scale-linear volume when the
slab query and owner clustering use the same scale. -/
theorem IsSlab.volume_doubleThetaMulB_closedThickening_le_125_mul
    {C theta b : NNReal} {S : ConvexBody Space}
    (hS : IsSlab C theta S) (hb : b ≤ 1) :
    volume (Metric.cthickening
      (2 * ((theta * b : NNReal) : Real)) (S : Set Space)) ≤
        125 * (theta : ENNReal) := by
  have hraw := IsSlab.volume_doubleThetaMulB_closedThickening_le
    hS (theta := theta) (b := b)
  have htb : theta * b ≤ theta := by
    nlinarith
  have hshort : theta + 4 * (theta * b) ≤ 5 * theta := by
    nlinarith
  have hlong : 1 + 4 * (theta * b) ≤ 5 := by
    have htheta : theta ≤ 1 := hS.2.1
    nlinarith
  calc
    volume (Metric.cthickening
        (2 * ((theta * b : NNReal) : Real)) (S : Set Space)) ≤
      ((theta : ENNReal) +
          4 * ((theta : ENNReal) * (b : ENNReal))) *
        (((1 : ENNReal) +
          4 * ((theta : ENNReal) * (b : ENNReal))) ^ 2) := hraw
    _ ≤ (5 * (theta : ENNReal)) * ((5 : ENNReal) ^ 2) := by
      gcongr
      · exact_mod_cast hshort
      · exact_mod_cast hlong
    _ = 125 * (theta : ENNReal) := by ring

/-- Same-scale Family6-style cross-multiplied count reserve. -/
theorem activeSelectedOwners_card_mul_plankVolumeLower_le_125_linearReserve
    (D : ShadedConvexPlankFamily iota a b) {theta : NNReal}
    (C : MutualThickeningClustering D theta)
    (q : Fin (Nat.log 2 (Fintype.card iota) + 1))
    {cellIndex : Type v} (cell : cellIndex → Set Space)
    (hcell : ∀ p, MeasurableSet (cell p)) (selected : Finset cellIndex)
    (hmass : (retainedOwnerPlankFamily D C q).shading.shadingMass ≠ 0)
    (hactive : (activeRetainedOwnerCellIndices D C q cell hcell selected).Nonempty)
    {S : ConvexBody Space} (hS : IsSlab 1 theta S) :
    ((activeSelectedOwnersInCertifiedSlab
        D C q cell hcell selected hmass hactive theta S).card : ENNReal) *
        (((D.comparisonConstant⁻¹ : NNReal) : ENNReal) ^ 3 *
          ((a : ENNReal) * (b : ENNReal))) ≤
      maximalConcentration D.family * (125 * (theta : ENNReal)) := by
  have hcross :=
    activeSelectedOwners_card_mul_plankVolumeLower_le_flatPrismReserve
      D C q cell hcell selected hmass hactive hS
  have hretained :=
    retainedOwnerSourceIndices_nonempty_of_mass_ne_zero D C q hmass
  let i0 : iota := hretained.choose
  have hb : b ≤ 1 := (D.all_isPlank i0).2.2.1
  have htb : theta * b ≤ theta := by
    nlinarith
  have hshort : theta + 4 * (theta * b) ≤ 5 * theta := by
    nlinarith
  have hlong : 1 + 4 * (theta * b) ≤ 5 := by
    have htheta : theta ≤ 1 := hS.2.1
    nlinarith
  calc
    ((activeSelectedOwnersInCertifiedSlab
        D C q cell hcell selected hmass hactive theta S).card : ENNReal) *
        (((D.comparisonConstant⁻¹ : NNReal) : ENNReal) ^ 3 *
          ((a : ENNReal) * (b : ENNReal))) ≤
      maximalConcentration D.family *
        (((theta : ENNReal) +
            4 * ((theta : ENNReal) * (b : ENNReal))) *
          (((1 : ENNReal) +
            4 * ((theta : ENNReal) * (b : ENNReal))) ^ 2)) := hcross
    _ ≤ maximalConcentration D.family * (125 * (theta : ENNReal)) := by
      apply mul_le_mul' le_rfl
      calc
        ((theta : ENNReal) + 4 * ((theta : ENNReal) * (b : ENNReal))) *
          (((1 : ENNReal) + 4 * ((theta : ENNReal) * (b : ENNReal))) ^ 2) ≤
              (5 * (theta : ENNReal)) * ((5 : ENNReal) ^ 2) := by
          gcongr
          · exact_mod_cast hshort
          · exact_mod_cast hlong
        _ = 125 * (theta : ENNReal) := by ring

/-- The certified plank-volume factor is positive and finite, so the linear
reserve can be stated as an explicit cardinal upper bound. -/
theorem activeSelectedOwners_card_le_125_linearReserve_div_plankVolume
    (D : ShadedConvexPlankFamily iota a b) {theta : NNReal}
    (C : MutualThickeningClustering D theta)
    (q : Fin (Nat.log 2 (Fintype.card iota) + 1))
    {cellIndex : Type v} (cell : cellIndex → Set Space)
    (hcell : ∀ p, MeasurableSet (cell p)) (selected : Finset cellIndex)
    (hmass : (retainedOwnerPlankFamily D C q).shading.shadingMass ≠ 0)
    (hactive : (activeRetainedOwnerCellIndices D C q cell hcell selected).Nonempty)
    {S : ConvexBody Space} (hS : IsSlab 1 theta S) :
    ((activeSelectedOwnersInCertifiedSlab
      D C q cell hcell selected hmass hactive theta S).card : ENNReal) ≤
      (maximalConcentration D.family * (125 * (theta : ENNReal))) /
        (((D.comparisonConstant⁻¹ : NNReal) : ENNReal) ^ 3 *
          ((a : ENNReal) * (b : ENNReal))) := by
  have hretained :=
    retainedOwnerSourceIndices_nonempty_of_mass_ne_zero D C q hmass
  let i0 : iota := hretained.choose
  have ha : 0 < a := (D.all_isPlank i0).1
  have hab : a ≤ b := (D.all_isPlank i0).2.1
  have hb : 0 < b := ha.trans_le hab
  have hC : 0 < D.comparisonConstant :=
    zero_lt_one.trans_le (D.all_isPlank i0).2.2.2.1
  have hv0 :
      (((D.comparisonConstant⁻¹ : NNReal) : ENNReal) ^ 3 *
        ((a : ENNReal) * (b : ENNReal))) ≠ 0 := by
    simp [hC.ne', ha.ne', hb.ne']
  have hvTop :
      (((D.comparisonConstant⁻¹ : NNReal) : ENNReal) ^ 3 *
        ((a : ENNReal) * (b : ENNReal))) ≠ ∞ := by
    exact ENNReal.mul_ne_top
      (ENNReal.pow_ne_top ENNReal.coe_ne_top)
      (ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.coe_ne_top)
  apply (ENNReal.le_div_iff_mul_le (Or.inl hv0) (Or.inl hvTop)).2
  exact activeSelectedOwners_card_mul_plankVolumeLower_le_125_linearReserve
    D C q cell hcell selected hmass hactive hS

/-- The honest owner count is simultaneously controlled by the geometric
linear reserve and by the V279 fine-angle occupancy. -/
theorem activeSelectedOwners_card_le_min_angleOccupancy_linearReserve
    (D : ShadedConvexPlankFamily iota a b) {theta : NNReal}
    (C : MutualThickeningClustering D theta)
    (q : Fin (Nat.log 2 (Fintype.card iota) + 1))
    {cellIndex : Type v} (cell : cellIndex → Set Space)
    (hcell : ∀ p, MeasurableSet (cell p)) (selected : Finset cellIndex)
    (hmass : (retainedOwnerPlankFamily D C q).shading.shadingMass ≠ 0)
    (hactive : (activeRetainedOwnerCellIndices D C q cell hcell selected).Nonempty)
    {S : ConvexBody Space} (hS : IsSlab 1 theta S) :
    ((activeSelectedOwnersInCertifiedSlab
      D C q cell hcell selected hmass hactive theta S).card : ENNReal) ≤
      min
        (canonicalCertifiedFineAngleOccupancy
          (retainedOwnerCellRestrictedCanonicalUnitSlabIncidence
            D C q cell hcell selected hmass) 2 theta : ENNReal)
        ((maximalConcentration D.family * (125 * (theta : ENNReal))) /
          (((D.comparisonConstant⁻¹ : NNReal) : ENNReal) ^ 3 *
            ((a : ENNReal) * (b : ENNReal)))) := by
  apply le_min
  · exact_mod_cast
      activeSelectedOwnersInCertifiedSlab_card_le_angleOccupancy
        D C q cell hcell selected hmass hactive hS
  · exact activeSelectedOwners_card_le_125_linearReserve_div_plankVolume
      D C q cell hcell selected hmass hactive hS

#print axioms IsSlab.volume_doubleThetaMulB_closedThickening_le_125_mul
#print axioms activeSelectedOwners_card_mul_plankVolumeLower_le_125_linearReserve
#print axioms activeSelectedOwners_card_le_125_linearReserve_div_plankVolume
#print axioms activeSelectedOwners_card_le_min_angleOccupancy_linearReserve

end
end Family8PlankActiveSelectedOwnerSameScaleLinearCountV1
