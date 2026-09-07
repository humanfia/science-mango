import Family8Grounding.Family8SelectedOccurrenceMaxOwnerHullUniqueOwnerV2
import Family8Grounding.Family8GreedyOccurrenceCanonicalFrostmanBridgeV2
import Mathlib.Tactic

/-!
# Owner-fibre Katz--Tao from actual ambient Frostman data

For each arbitrary test body, the hull of the family members it contains lies
in both that test body and the ambient Frostman body.  This upgrades ambient
Frostman plus actual ambient density to global Katz--Tao, and then restricts
to every literal owner fibre without a callback.
-/

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8OwnerFiberKatzTaoFromAmbientFrostmanV2

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
open Family6AffinePlankAnalyticHypothesesStableV1
open Family8GreedyOccurrenceCanonicalFrostmanBridgeV2
open Family8UniqueOwnerLocalDeltaMaxThickControlV1

noncomputable section

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5000000

local instance (p : Prop) : Decidable p := Classical.propDecidable p

universe u v

/-- Ambient Frostman control and ambient mass density imply a global
Katz--Tao estimate on the same actual family. -/
theorem isKatzTao_of_isFrostmanIn_of_ambientMass
    {iota : Type u} [Fintype iota]
    {F : ConvexFamily iota} {ambient : ConvexBody Space}
    {CF A : ENNReal}
    (hF : IsFrostmanIn CF F ambient)
    (hbase : containedMass F ambient ≤ A * volume (ambient : Set Space)) :
    IsKatzTao (CF * A) F := by
  classical
  intro K
  let s := containedIndices F K
  by_cases hs : s.Nonempty
  · let H := hullContainer F s
    have hHK : (H : Set Space) ⊆ (K : Set Space) := by
      apply hullContainer_subset F hs
      intro i hi
      exact (mem_containedIndices F K i).mp hi
    have hHAmbient : (H : Set Space) ⊆ (ambient : Set Space) := by
      apply hullContainer_subset F hs
      intro i _hi
      exact hF.family_subset i
    have hmass : containedMass F K ≤ containedMass F H := by
      unfold containedMass
      apply Finset.sum_le_sum_of_subset
      intro i hi
      rw [mem_containedIndices]
      exact body_subset_hullContainer F hi hs
    calc
      containedMass F K ≤ containedMass F H := hmass
      _ ≤ (CF * A) * volume (H : Set Space) :=
        hF.local_katzTao hbase H hHAmbient
      _ ≤ (CF * A) * volume (K : Set Space) := by
        gcongr
  · have hsEmpty : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
    change (∑ i ∈ s, volume (F i : Set Space)) ≤
      (CF * A) * volume (K : Set Space)
    rw [hsEmpty]
    simp

/-- A global Katz--Tao estimate restricts to every literal owner fibre. -/
theorem isKatzTao_ownerFiberFamily_of_global
    {iota : Type u} [Fintype iota] [DecidableEq iota]
    {ownerIndex : Type v} [DecidableEq ownerIndex]
    {a b : NNReal} (D : ShadedConvexPlankFamily iota a b)
    (owner : iota → ownerIndex) {Delta : ENNReal}
    (hKT : IsKatzTao Delta D.family) (p : ownerIndex) :
    IsKatzTao Delta (ownerFiberFamily D owner p) := by
  apply isKatzTao_selectedCoarseFamily_of_isKatzTaoOn
  intro K
  calc
    containedMassOn D.family (ownerFiberIndices owner p) K ≤
        containedMassOn D.family Finset.univ K :=
      containedMassOn_mono (Finset.subset_univ _) K
    _ = containedMass D.family K := containedMassOn_univ D.family K
    _ ≤ Delta * volume (K : Set Space) := hKT K

/-- Actual ambient data bounds the genuine supremum of all owner-fibre
concentrations.  The scalar premise only converts the ENNReal product to the
requested NNReal `Delta`. -/
theorem ownerFiberDeltaMax_le_of_ambientFrostman
    {iota : Type u} [Fintype iota] [DecidableEq iota]
    {ownerIndex : Type v} [DecidableEq ownerIndex]
    {a b Delta : NNReal} (D : ShadedConvexPlankFamily iota a b)
    (owner : iota → ownerIndex) {CF A : ENNReal}
    (hF : IsFrostmanIn CF D.family D.ambient)
    (hbase : containedMass D.family D.ambient ≤
      A * volume (D.ambient : Set Space))
    (hDelta : CF * A ≤ (Delta : ENNReal)) :
    ownerFiberDeltaMax D owner ≤ (Delta : ENNReal) := by
  have hglobal : IsKatzTao (Delta : ENNReal) D.family :=
    (isKatzTao_of_isFrostmanIn_of_ambientMass hF hbase).mono hDelta
  unfold ownerFiberDeltaMax
  apply iSup_le
  intro p
  exact
    Family6PlankKatzTaoFrostmanActualAdaptersV1.isKatzTao_iff_maximalConcentration_le.mp
      (isKatzTao_ownerFiberFamily_of_global D owner hglobal p)

#print axioms isKatzTao_of_isFrostmanIn_of_ambientMass
#print axioms isKatzTao_ownerFiberFamily_of_global
#print axioms ownerFiberDeltaMax_le_of_ambientFrostman

end

end Family8OwnerFiberKatzTaoFromAmbientFrostmanV2
