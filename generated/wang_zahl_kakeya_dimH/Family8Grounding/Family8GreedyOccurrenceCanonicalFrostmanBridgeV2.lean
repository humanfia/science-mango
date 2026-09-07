import Submission.Kakeya.ConvexFactoring.GreedyAllOccurrenceFrostman
import Submission.Kakeya.ConvexFactoring.HeavyParentSelection
import Family6Grounding.Family6CanonicalFrostmanConstantCoreV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2400000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8GreedyOccurrenceCanonicalFrostmanBridgeV2

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
open Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
open Submission.Kakeya.ConvexFactoring.GreedyDensityBucketing
open Submission.Kakeya.ConvexFactoring.GreedyAllOccurrenceFrostman
open Submission.Kakeya.ConvexFactoring.HeavyParentSelection
open Family6CanonicalFrostmanConstantCoreV1

noncomputable section

universe u

/-!
# Actual greedy occurrence blocks and the canonical Frostman constant

The constant-one Frostman theorem produced by full-convex greedy selection is
an active-family theorem on one actual fine fibre.  This module first changes
that finite active set to its literal subtype family.  It then proves that the
Family 6 canonical constant is bounded by any genuine `IsFrostmanIn`
certificate, and specializes this to every actual occurrence block.

A second theorem records the closest available coarse-family statement:
density-comparable selected occurrence bodies have an explicit canonical
constant bound.  Neither statement identifies those hull occurrences with a
separately supplied `StickyScaleCover.activeCoarseFamily`.
-/

/-- Restricting a family to a finite subtype turns active contained mass into
ordinary contained mass, without changing the sum. -/
theorem containedMass_selectedCoarseFamily_eq_containedMassOn
    {index : Type u} [Fintype index] [DecidableEq index]
    (F : ConvexFamily index) (s : Finset index) (K : ConvexBody Space) :
    containedMass (selectedCoarseFamily F s) K =
      containedMassOn F s K := by
  classical
  unfold containedMass containedMassOn containedIndices
  simp only [selectedCoarseFamily_apply]
  calc
    (∑ i ∈ s.attach with (F i.1 : Set Space) ⊆ (K : Set Space),
        volume (F i.1 : Set Space)) =
        ∑ i ∈ s.attach,
          if (F i.1 : Set Space) ⊆ (K : Set Space) then
            volume (F i.1 : Set Space) else 0 := by
      rw [Finset.sum_filter]
    _ = ∑ i ∈ s,
          if (F i : Set Space) ⊆ (K : Set Space) then
            volume (F i : Set Space) else 0 := by
      simpa using (Finset.sum_attach s (fun i =>
        if (F i : Set Space) ⊆ (K : Set Space) then
          volume (F i : Set Space) else (0 : ENNReal)))
    _ = ∑ i ∈ s ∩ Finset.univ.filter
          (fun i => (F i : Set Space) ⊆ (K : Set Space)),
          volume (F i : Set Space) := by
      rw [show s ∩ Finset.univ.filter
        (fun i => (F i : Set Space) ⊆ (K : Set Space)) =
          s.filter (fun i => (F i : Set Space) ⊆ (K : Set Space)) by
        ext i
        simp]
      rw [Finset.sum_filter]
  · apply Finset.sum_congr
    · ext i
      simp
    · intro i hi
      rfl

/-- An active Frostman certificate is exactly a full Frostman certificate on
the attached selected-family subtype. -/
theorem isFrostmanIn_selectedCoarseFamily_of_isFrostmanOn
    {index : Type u} [Fintype index] [DecidableEq index]
    {C : ENNReal} {F : ConvexFamily index} {s : Finset index}
    {K : ConvexBody Space} (hF : IsFrostmanOn C F s K) :
    IsFrostmanIn C (selectedCoarseFamily F s) K := by
  refine ⟨?_, ?_⟩
  · intro i
    exact hF.1 i.1 i.2
  · intro Kprime hKprime
    rw [containedMass_selectedCoarseFamily_eq_containedMassOn,
      containedMass_selectedCoarseFamily_eq_containedMassOn]
    exact hF.2 Kprime hKprime

/-- Density on the full active index set is the ordinary family
concentration. -/
theorem densityInside_univ_eq_concentration
    {index : Type u} [Fintype index]
    (F : ConvexFamily index) (K : ConvexBody Space) :
    densityInside F Finset.univ K = concentration F K := by
  classical
  simp [densityInside, massInside, concentration, indicesInside,
    containedIndices]

/-- A Frostman certificate in `K` controls the global maximal concentration,
not only test bodies already contained in `K`.  For an arbitrary test body,
take the closed convex hull of exactly the indexed members contained in it;
that hull is also contained in `K`. -/
theorem maximalConcentration_le_mul_concentration_of_isFrostmanIn
    {index : Type u} [Fintype index]
    {C : ENNReal} {F : ConvexFamily index} {K : ConvexBody Space}
    (hF : IsFrostmanIn C F K) :
    maximalConcentration F <= C * concentration F K := by
  classical
  apply iSup_le
  intro L
  by_cases hempty : indicesInside F Finset.univ L = ∅
  · rw [← densityInside_univ_eq_concentration F L]
    simp [densityInside, massInside, hempty]
  · have hs : (indicesInside F Finset.univ L).Nonempty :=
      Finset.nonempty_iff_ne_empty.mpr hempty
    let H : ConvexBody Space :=
      hullContainer F (indicesInside F Finset.univ L)
    have hHL : (H : Set Space) ⊆ (L : Set Space) := by
      exact hullContainer_indicesInside_subset F Finset.univ L hs
    have hHK : (H : Set Space) ⊆ (K : Set Space) := by
      apply hullContainer_subset F hs
      intro i hi
      exact hF.1 i
    calc
      concentration F L = densityInside F Finset.univ L :=
        (densityInside_univ_eq_concentration F L).symm
      _ <= densityInside F Finset.univ H := by
        exact densityInside_le_hullContainer_indicesInside
          F Finset.univ L hs
      _ = concentration F H :=
        densityInside_univ_eq_concentration F H
      _ <= C * concentration F K := hF.concentration_le hHK

/-- The Family 6 canonical scalar is no larger than any genuine Frostman
constant for the same family and ambient body.  The only cancellation premise
is that the actually contained family mass is nonzero. -/
theorem canonicalFrostmanConstant_le_of_isFrostmanIn
    {index : Type u} [Fintype index]
    {C : ENNReal} {F : ConvexFamily index} {K : ConvexBody Space}
    (hF : IsFrostmanIn C F K) (hmass0 : containedMass F K ≠ 0) :
    canonicalFrostmanConstant F K <= C := by
  have hvol0 : volume (K : Set Space) ≠ 0 := by
    intro hzero
    exact hmass0 (containedMass_eq_zero_of_volume_eq_zero F K hzero)
  have hvolTop : volume (K : Set Space) ≠ ∞ :=
    K.isCompact.measure_lt_top.ne
  have hmassTop : containedMass F K ≠ ∞ :=
    (containedMass_lt_top F K).ne
  have hmax :=
    maximalConcentration_le_mul_concentration_of_isFrostmanIn hF
  unfold canonicalFrostmanConstant
  rw [concentration_eq_containedMass_div] at hmax
  calc
    maximalConcentration F * volume (K : Set Space) / containedMass F K <=
        (C * (containedMass F K / volume (K : Set Space))) *
          volume (K : Set Space) / containedMass F K := by
      gcongr
    _ = C := by
      calc
        (C * (containedMass F K / volume (K : Set Space))) *
              volume (K : Set Space) / containedMass F K =
            C * ((containedMass F K / volume (K : Set Space)) *
              volume (K : Set Space)) / containedMass F K := by
                ac_rfl
        _ = C * containedMass F K / containedMass F K := by
          rw [ENNReal.div_mul_cancel hvol0 hvolTop]
        _ = C := ENNReal.mul_div_cancel_right hmass0 hmassTop

/-- The ordinary mass of an attached selected family in a body containing all
its members is its literal selected subsum. -/
theorem containedMass_selectedCoarseFamily_eq_sum_of_contained
    {index : Type u} [Fintype index] [DecidableEq index]
    (F : ConvexFamily index) (s : Finset index) (K : ConvexBody Space)
    (hcontained : ∀ i ∈ s, (F i : Set Space) ⊆ (K : Set Space)) :
    containedMass (selectedCoarseFamily F s) K =
      ∑ i ∈ s, volume (F i : Set Space) := by
  rw [containedMass_eq_familyVolume_of_contained]
  · exact selectedCoarseFamily_volume F s
  · intro i
    exact hcontained i.1 i.2

/-- One nonempty selected set of positive-volume members has nonzero
contained mass in any body containing it. -/
theorem containedMass_selectedCoarseFamily_ne_zero_of_positive
    {index : Type u} [Fintype index] [DecidableEq index]
    (F : ConvexFamily index) (s : Finset index) (K : ConvexBody Space)
    (hs : s.Nonempty)
    (hcontained : ∀ i ∈ s, (F i : Set Space) ⊆ (K : Set Space))
    (hpositive : ∀ i ∈ s, 0 < volume (F i : Set Space)) :
    containedMass (selectedCoarseFamily F s) K ≠ 0 := by
  rw [containedMass_selectedCoarseFamily_eq_sum_of_contained
    F s K hcontained]
  obtain ⟨i, hi⟩ := hs
  have hle : volume (F i : Set Space) <=
      ∑ j ∈ s, volume (F j : Set Space) := by
    exact Finset.single_le_sum
      (fun j _ => show (0 : ENNReal) <= volume (F j : Set Space) from bot_le)
      hi
  exact (hpositive i hi).trans_le hle |>.ne'

/-- Every actual full-convex greedy occurrence block yields a literal
constant-one Family 6 canonical Frostman bound on its selected fine subtype.
The positivity premise is member geometry, not a desired scalar bound. -/
theorem occurrenceBlock_canonicalFrostmanConstant_le_one
    {index : Type u} [Fintype index] [DecidableEq index]
    (F : ConvexFamily index) (base : Finset index)
    {active : Finset index}
    (P : GreedyDensityPartition F (hullCandidates base)
      (hullContainer F) active)
    (hactive : active ⊆ base) (k : Fin (blocks F P).length)
    (hpositive : ∀ i ∈ active, 0 < volume (F i : Set Space)) :
    canonicalFrostmanConstant
        (selectedCoarseFamily F (blockAt F P k).fiber)
        (blockAt F P k).body <= 1 := by
  have hblock : IsFrostmanOn 1 F (blockAt F P k).fiber
      (blockAt F P k).body :=
    every_block_isFrostmanOn_one F base P hactive k
  have hselected : IsFrostmanIn 1
      (selectedCoarseFamily F (blockAt F P k).fiber)
      (blockAt F P k).body :=
    isFrostmanIn_selectedCoarseFamily_of_isFrostmanOn hblock
  apply canonicalFrostmanConstant_le_of_isFrostmanIn hselected
  apply containedMass_selectedCoarseFamily_ne_zero_of_positive
  · exact (blockAt F P k).fiber_nonempty
  · exact (blockAt F P k).contained
  · intro i hi
    exact hpositive i (blockAt_fiber_subset_active F P k hi)

/-- Katz--Tao on a finite active set becomes ordinary Katz--Tao on the
attached selected-family subtype. -/
theorem isKatzTao_selectedCoarseFamily_of_isKatzTaoOn
    {index : Type u} [Fintype index] [DecidableEq index]
    {A : ENNReal} {F : ConvexFamily index} {s : Finset index}
    (hKT : IsKatzTaoOn A F s) :
    IsKatzTao A (selectedCoarseFamily F s) := by
  intro K
  change containedMass (selectedCoarseFamily F s) K <=
    A * volume (K : Set Space)
  rw [containedMass_selectedCoarseFamily_eq_containedMassOn]
  exact hKT K

theorem maximalConcentration_selectedCoarseFamily_le_of_isKatzTaoOn
    {index : Type u} [Fintype index] [DecidableEq index]
    {A : ENNReal} {F : ConvexFamily index} {s : Finset index}
    (hKT : IsKatzTaoOn A F s) :
    maximalConcentration (selectedCoarseFamily F s) <= A := by
  apply iSup_le
  intro K
  exact (isKatzTao_iff_concentration_le.mp
    (isKatzTao_selectedCoarseFamily_of_isKatzTaoOn hKT)) K

/-- Strongest automatic canonical scalar bound for a selected family with a
known active Katz--Tao constant.  The ambient is the actual full selected
hull, so no containment callback occurs. -/
theorem selectedCoarseFamily_canonicalFrostmanConstant_fullHull_le
    {index : Type u} [Fintype index] [DecidableEq index]
    {A : ENNReal} {F : ConvexFamily index} {s : Finset index}
    (hKT : IsKatzTaoOn A F s) :
    canonicalFrostmanConstant (selectedCoarseFamily F s)
        (hullContainer (selectedCoarseFamily F s) Finset.univ) <=
      A * volume
          (hullContainer (selectedCoarseFamily F s) Finset.univ : Set Space) /
        familyVolume (selectedCoarseFamily F s) := by
  unfold canonicalFrostmanConstant
  rw [containedMass_eq_familyVolume_of_contained]
  · gcongr
    exact maximalConcentration_selectedCoarseFamily_le_of_isKatzTaoOn hKT
  · intro i
    exact body_subset_hullContainer (selectedCoarseFamily F s)
      (Finset.mem_univ i) ⟨i, Finset.mem_univ i⟩

/-- Actual density-comparable greedy occurrences therefore have an explicit
canonical Frostman upper bound on their selected occurrence-body family. -/
theorem occurrenceSelected_canonicalFrostmanConstant_fullHull_le_of_comparable
    {index : Type u} [Fintype index] [DecidableEq index]
    (F : ConvexFamily index) (base : Finset index)
    {active : Finset index}
    (P : GreedyDensityPartition F (hullCandidates base)
      (hullContainer F) active)
    (hactive : active ⊆ base)
    (S : Finset (Fin (blocks F P).length)) (delta A : ENNReal)
    (hdelta0 : delta ≠ 0) (hdeltaTop : delta ≠ ∞)
    (hlower : ∀ k ∈ S, delta <= blockDensity F (blockAt F P k))
    (hupper : initialDensity F base P <= A * delta) :
    canonicalFrostmanConstant
        (selectedCoarseFamily (occurrenceFamily F P) S)
        (hullContainer
          (selectedCoarseFamily (occurrenceFamily F P) S) Finset.univ) <=
      A * volume
          (hullContainer
            (selectedCoarseFamily (occurrenceFamily F P) S) Finset.univ :
              Set Space) /
        familyVolume (selectedCoarseFamily (occurrenceFamily F P) S) := by
  apply selectedCoarseFamily_canonicalFrostmanConstant_fullHull_le
  exact occurrenceFamily_isKatzTaoOn_of_comparable F base P hactive S
    delta A hdelta0 hdeltaTop hlower hupper

#print axioms containedMass_selectedCoarseFamily_eq_containedMassOn
#print axioms isFrostmanIn_selectedCoarseFamily_of_isFrostmanOn
#print axioms densityInside_univ_eq_concentration
#print axioms maximalConcentration_le_mul_concentration_of_isFrostmanIn
#print axioms canonicalFrostmanConstant_le_of_isFrostmanIn
#print axioms containedMass_selectedCoarseFamily_ne_zero_of_positive
#print axioms occurrenceBlock_canonicalFrostmanConstant_le_one
#print axioms isKatzTao_selectedCoarseFamily_of_isKatzTaoOn
#print axioms maximalConcentration_selectedCoarseFamily_le_of_isKatzTaoOn
#print axioms selectedCoarseFamily_canonicalFrostmanConstant_fullHull_le
#print axioms
  occurrenceSelected_canonicalFrostmanConstant_fullHull_le_of_comparable

end

end Family8GreedyOccurrenceCanonicalFrostmanBridgeV2
