import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstProvenanceV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000

open Set

namespace FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstExactCProvenanceV2

open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open FamilyStickyCinematicL32ActualTubeCoefficientDistancesV1
open FamilyStickyCinematicL32FiniteMetricMaximalCoverV1
open FamilyStickyCinematicL32Prop41ActualGlobalNormCoarseFiberRandomSamplingV1
open FamilyStickyCinematicL32Prop41ActualY1ExactCFiberPairSelectionV1
open FamilyStickyCinematicL32Prop41ActualY1RetainedThreeShiftPerturbationReadyV1
open FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeSamplingBridgeV1
open FamilyStickyCinematicL32Prop41CanonicalMaximizerNonconcentrationV1
open FamilyStickyCinematicL32Prop41CoarseRectangleIncidenceDataV1
open FamilyStickyCinematicL32Prop41FiniteRandomSamplingExtractionV1
open FamilyStickyCinematicL32Prop41FiniteRandomSamplingSubfamilyExtractionV1
open FamilyStickyCinematicL32Prop41SeparatedCoefficientBallPairV1
open FamilyStickyCinematicL32TubePairTraceV1
open FamilyStickyWZ2TubeCarrierCoordinateAdapterV1

noncomputable section

universe u v

/-!
# Exact-C label-first G-prime sampling

This is an independent V2 carrier.  Its rectangle coordinate is a genuine
retained pair consisting of a fine label and an exact graph-C value.
Both sampled sides are restricted to that same cell before sampling.
Consequently every selected pair has a common fine label and literal common
graph-C value by construction.  No assertion that the whole ambient
global-norm family has fixed graph-C is used.

The quantitative boundary is honest: nonemptiness of the bilateral exact-C
cell support is not inferred from common-coarse incidence.  A separate
label-first separated-pair mass producer must supply it.
-/

/-- Fine-label/exact-C cells occupied by the retained incidence relation. -/
noncomputable def actualGPrimeRetainedFineExactCCells
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    {fineLabel : Type v} [DecidableEq fineLabel]
    (D : CoarseRectangleIncidenceData (point := Real × Real)
      (radius := radius) (iota := iota) fineLabel)
    (keep : iota -> fineLabel -> Prop) : Finset (fineLabel × Real) := by
  classical
  exact (D.retainedGoodPairs keep).image fun p =>
    (p.2, tubeGraphC (D.fine.tubes p.1))

@[simp]
theorem mem_actualGPrimeRetainedFineExactCCells_iff
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    {fineLabel : Type v} [DecidableEq fineLabel]
    (D : CoarseRectangleIncidenceData (point := Real × Real)
      (radius := radius) (iota := iota) fineLabel)
    (keep : iota -> fineLabel -> Prop) (r : fineLabel) (c : Real) :
    (r, c) ∈ actualGPrimeRetainedFineExactCCells D keep ↔
      ∃ i, (i, r) ∈ D.retainedGoodPairs keep ∧
        tubeGraphC (D.fine.tubes i) = c := by
  classical
  constructor
  · intro hcell
    obtain ⟨⟨i, s⟩, his, hEq⟩ :=
      Finset.mem_image.mp hcell
    have hsr : s = r := congrArg Prod.fst hEq
    have hc : tubeGraphC (D.fine.tubes i) = c :=
      congrArg Prod.snd hEq
    subst s
    exact ⟨i, his, hc⟩
  · rintro ⟨i, hi, hc⟩
    apply Finset.mem_image.mpr
    exact ⟨(i, r), hi, by simp [hc]⟩

/-- One occupied exact-C fine cell, restricted to one canonical metric ball. -/
noncomputable def actualGPrimeRetainedFineExactCMetricNeighbors
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    {fineLabel : Type v} [DecidableEq fineLabel]
    (N : CanonicalNormNonconcentrationData iota)
    (D : CoarseRectangleIncidenceData (point := Real × Real)
      (radius := radius) (iota := iota) fineLabel)
    (keep : iota -> fineLabel -> Prop) (center : iota)
    (ballRadius : Real) (r : fineLabel) (c : Real) : Finset N.family :=
  ambientSubtypeRestriction N.family
    ((retainedY1ExactCFiberAtFine D keep r c).filter fun i =>
      N.distance i center <= ballRadius)

@[simp]
theorem mem_actualGPrimeRetainedFineExactCMetricNeighbors_iff
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    {fineLabel : Type v} [DecidableEq fineLabel]
    (N : CanonicalNormNonconcentrationData iota)
    (D : CoarseRectangleIncidenceData (point := Real × Real)
      (radius := radius) (iota := iota) fineLabel)
    (keep : iota -> fineLabel -> Prop) (center : iota)
    (ballRadius : Real) (r : fineLabel) (c : Real) (i : N.family) :
    i ∈ actualGPrimeRetainedFineExactCMetricNeighbors
        N D keep center ballRadius r c ↔
      (i.1, r) ∈ D.retainedGoodPairs keep ∧
        tubeGraphC (D.fine.tubes i.1) = c ∧
          N.distance i.1 center <= ballRadius := by
  rw [actualGPrimeRetainedFineExactCMetricNeighbors,
    mem_ambientSubtypeRestriction_iff]
  simp only [Finset.mem_filter, mem_retainedY1ExactCFiberAtFine_iff]
  tauto

/-- Occupied exact-C fine cells which meet both separated metric balls. -/
noncomputable def actualGPrimeBilateralRetainedFineExactCCells
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    {fineLabel : Type v} [DecidableEq fineLabel]
    (N : CanonicalNormNonconcentrationData iota)
    (D : CoarseRectangleIncidenceData (point := Real × Real)
      (radius := radius) (iota := iota) fineLabel)
    (keep : iota -> fineLabel -> Prop) (left right : iota)
    (ballRadius : Real) : Finset (fineLabel × Real) := by
  classical
  exact (actualGPrimeRetainedFineExactCCells D keep).filter fun cell =>
    (actualGPrimeRetainedFineExactCMetricNeighbors N D keep left ballRadius
      cell.1 cell.2).Nonempty ∧
    (actualGPrimeRetainedFineExactCMetricNeighbors N D keep right ballRadius
      cell.1 cell.2).Nonempty

@[simp]
theorem mem_actualGPrimeBilateralRetainedFineExactCCells_iff
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    {fineLabel : Type v} [DecidableEq fineLabel]
    (N : CanonicalNormNonconcentrationData iota)
    (D : CoarseRectangleIncidenceData (point := Real × Real)
      (radius := radius) (iota := iota) fineLabel)
    (keep : iota -> fineLabel -> Prop) (left right : iota)
    (ballRadius : Real) (cell : fineLabel × Real) :
    cell ∈ actualGPrimeBilateralRetainedFineExactCCells
        N D keep left right ballRadius ↔
      cell ∈ actualGPrimeRetainedFineExactCCells D keep ∧
        (actualGPrimeRetainedFineExactCMetricNeighbors N D keep left
          ballRadius cell.1 cell.2).Nonempty ∧
        (actualGPrimeRetainedFineExactCMetricNeighbors N D keep right
          ballRadius cell.1 cell.2).Nonempty := by
  classical
  simp [actualGPrimeBilateralRetainedFineExactCCells]

/-- Exact-C label-first survivor type. -/
abbrev ActualGPrimeLabelFirstExactCSurvivor
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    {fineLabel : Type v} [DecidableEq fineLabel]
    (N : CanonicalNormNonconcentrationData iota)
    (D : CoarseRectangleIncidenceData (point := Real × Real)
      (radius := radius) (iota := iota) fineLabel)
    (keep : iota -> fineLabel -> Prop) (left right : iota)
    (ballRadius : Real)
    (omega : (N.family -> Fin 1) × (N.family -> Fin 1)) :=
  TwoSidedZeroColorSurvivor 1 1
    (fun cell : actualGPrimeBilateralRetainedFineExactCCells
        N D keep left right ballRadius =>
      actualGPrimeRetainedFineExactCMetricNeighbors
        N D keep left ballRadius cell.1.1 cell.1.2)
    (fun cell : actualGPrimeBilateralRetainedFineExactCCells
        N D keep left right ballRadius =>
      actualGPrimeRetainedFineExactCMetricNeighbors
        N D keep right ballRadius cell.1.1 cell.1.2)
    omega

def actualGPrimeLabelFirstExactCLabel
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    {fineLabel : Type v} [DecidableEq fineLabel]
    (N : CanonicalNormNonconcentrationData iota)
    (D : CoarseRectangleIncidenceData (point := Real × Real)
      (radius := radius) (iota := iota) fineLabel)
    (keep : iota -> fineLabel -> Prop) (left right : iota)
    (ballRadius : Real)
    (omega : (N.family -> Fin 1) × (N.family -> Fin 1)) :
    ActualGPrimeLabelFirstExactCSurvivor
      N D keep left right ballRadius omega -> fineLabel :=
  fun S => S.1.1.1

def actualGPrimeLabelFirstExactCValue
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    {fineLabel : Type v} [DecidableEq fineLabel]
    (N : CanonicalNormNonconcentrationData iota)
    (D : CoarseRectangleIncidenceData (point := Real × Real)
      (radius := radius) (iota := iota) fineLabel)
    (keep : iota -> fineLabel -> Prop) (left right : iota)
    (ballRadius : Real)
    (omega : (N.family -> Fin 1) × (N.family -> Fin 1)) :
    ActualGPrimeLabelFirstExactCSurvivor
      N D keep left right ballRadius omega -> Real :=
  fun S => S.1.1.2

noncomputable def actualGPrimeLabelFirstExactCLeftIndex
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    {fineLabel : Type v} [DecidableEq fineLabel]
    (N : CanonicalNormNonconcentrationData iota)
    (D : CoarseRectangleIncidenceData (point := Real × Real)
      (radius := radius) (iota := iota) fineLabel)
    (keep : iota -> fineLabel -> Prop) (left right : iota)
    (ballRadius : Real)
    (omega : (N.family -> Fin 1) × (N.family -> Fin 1)) :
    ActualGPrimeLabelFirstExactCSurvivor
      N D keep left right ballRadius omega -> iota :=
  fun S => (survivorLeftHitWitness 1 1
    (fun cell : actualGPrimeBilateralRetainedFineExactCCells
        N D keep left right ballRadius =>
      actualGPrimeRetainedFineExactCMetricNeighbors
        N D keep left ballRadius cell.1.1 cell.1.2)
    (fun cell : actualGPrimeBilateralRetainedFineExactCCells
        N D keep left right ballRadius =>
      actualGPrimeRetainedFineExactCMetricNeighbors
        N D keep right ballRadius cell.1.1 cell.1.2)
    omega S).1.1

noncomputable def actualGPrimeLabelFirstExactCRightIndex
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    {fineLabel : Type v} [DecidableEq fineLabel]
    (N : CanonicalNormNonconcentrationData iota)
    (D : CoarseRectangleIncidenceData (point := Real × Real)
      (radius := radius) (iota := iota) fineLabel)
    (keep : iota -> fineLabel -> Prop) (left right : iota)
    (ballRadius : Real)
    (omega : (N.family -> Fin 1) × (N.family -> Fin 1)) :
    ActualGPrimeLabelFirstExactCSurvivor
      N D keep left right ballRadius omega -> iota :=
  fun S => (survivorRightHitWitness 1 1
    (fun cell : actualGPrimeBilateralRetainedFineExactCCells
        N D keep left right ballRadius =>
      actualGPrimeRetainedFineExactCMetricNeighbors
        N D keep left ballRadius cell.1.1 cell.1.2)
    (fun cell : actualGPrimeBilateralRetainedFineExactCCells
        N D keep left right ballRadius =>
      actualGPrimeRetainedFineExactCMetricNeighbors
        N D keep right ballRadius cell.1.1 cell.1.2)
    omega S).1.1

structure ActualGPrimeLabelFirstExactCSampledOutcome
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    {fineLabel : Type v} [DecidableEq fineLabel]
    (N : CanonicalNormNonconcentrationData iota)
    (D : CoarseRectangleIncidenceData (point := Real × Real)
      (radius := radius) (iota := iota) fineLabel)
    (keep : iota -> fineLabel -> Prop) (left right : iota)
    (ballRadius : Real)
    (omega : (N.family -> Fin 1) × (N.family -> Fin 1)) : Prop where
  survival :
    ((actualGPrimeBilateralRetainedFineExactCCells
      N D keep left right ballRadius).card : Real) / 8 <=
      ((twoSidedZeroColorSurvivors 1 1
        (fun cell : actualGPrimeBilateralRetainedFineExactCCells
            N D keep left right ballRadius =>
          actualGPrimeRetainedFineExactCMetricNeighbors
            N D keep left ballRadius cell.1.1 cell.1.2)
        (fun cell : actualGPrimeBilateralRetainedFineExactCCells
            N D keep left right ballRadius =>
          actualGPrimeRetainedFineExactCMetricNeighbors
            N D keep right ballRadius cell.1.1 cell.1.2)
        omega).card : Real)
  load : twoSidedZeroColorLoad 1 1 omega <=
    7 * ((N.family.card : Real) / (1 : Real) +
      (N.family.card : Real) / (1 : Real))
  retained_tube_card_le_load :
    ((survivorRetainedPairTubeFamily 1 1
      (fun cell : actualGPrimeBilateralRetainedFineExactCCells
          N D keep left right ballRadius =>
        actualGPrimeRetainedFineExactCMetricNeighbors
          N D keep left ballRadius cell.1.1 cell.1.2)
      (fun cell : actualGPrimeBilateralRetainedFineExactCCells
          N D keep left right ballRadius =>
        actualGPrimeRetainedFineExactCMetricNeighbors
          N D keep right ballRadius cell.1.1 cell.1.2)
      omega (fun i : N.family => D.fine.tubes i.1)
        (fun i : N.family => D.fine.tubes i.1)).card : Real) <=
      twoSidedZeroColorLoad 1 1 omega

theorem exists_actualGPrimeLabelFirstExactCSampledOutcome
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    {fineLabel : Type v} [DecidableEq fineLabel]
    (N : CanonicalNormNonconcentrationData iota)
    (D : CoarseRectangleIncidenceData (point := Real × Real)
      (radius := radius) (iota := iota) fineLabel)
    (keep : iota -> fineLabel -> Prop) (left right : iota)
    (ballRadius : Real) :
    exists omega : (N.family -> Fin 1) × (N.family -> Fin 1),
      ActualGPrimeLabelFirstExactCSampledOutcome
        N D keep left right ballRadius omega := by
  classical
  let cells := actualGPrimeBilateralRetainedFineExactCCells
    N D keep left right ballRadius
  let leftNeighbors : cells -> Finset N.family := fun cell =>
    actualGPrimeRetainedFineExactCMetricNeighbors
      N D keep left ballRadius cell.1.1 cell.1.2
  let rightNeighbors : cells -> Finset N.family := fun cell =>
    actualGPrimeRetainedFineExactCMetricNeighbors
      N D keep right ballRadius cell.1.1 cell.1.2
  have hleft : forall cell : cells, 1 <= (leftNeighbors cell).card := by
    intro cell
    apply Finset.one_le_card.mpr
    exact ((mem_actualGPrimeBilateralRetainedFineExactCCells_iff
      N D keep left right ballRadius cell.1).mp cell.2).2.1
  have hright : forall cell : cells, 1 <= (rightNeighbors cell).card := by
    intro cell
    apply Finset.one_le_card.mpr
    exact ((mem_actualGPrimeBilateralRetainedFineExactCCells_iff
      N D keep left right ballRadius cell.1).mp cell.2).2.2
  obtain ⟨omega, hsurvival, hload⟩ :=
    exists_twoSidedZeroColor_sample_with_eighth_survival_and_sevenfold_load
      (Rectangle := cells) (alpha := N.family) (beta := N.family)
      1 1 leftNeighbors rightNeighbors hleft hright
  refine ⟨omega, {
    survival := ?_
    load := ?_
    retained_tube_card_le_load := ?_ }⟩
  · simpa only [cells, leftNeighbors, rightNeighbors,
      Fintype.card_coe, Nat.cast_one] using hsurvival
  · simpa only [Nat.cast_one, Fintype.card_coe] using hload
  · exact survivorRetainedPairTubeFamily_card_cast_le_load 1 1
      leftNeighbors rightNeighbors omega
      (fun i : N.family => D.fine.tubes i.1)
      (fun i : N.family => D.fine.tubes i.1)

theorem actualGPrimeLabelFirstExactC_actualRetainedY1PairSelection
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    {fineLabel : Type v} [DecidableEq fineLabel]
    (N : CanonicalNormNonconcentrationData iota)
    (D : CoarseRectangleIncidenceData (point := Real × Real)
      (radius := radius) (iota := iota) fineLabel)
    (keep : iota -> fineLabel -> Prop) (left right : iota)
    (ballRadius : Real)
    (hdistance : forall i j, N.distance i j =
      projectedTubePairCoefficientDistance
        (D.fine.tubes i) (D.fine.tubes j))
    (hcross : FiniteFamiliesCrossSeparated N.distance (8 * ballRadius)
      (finiteFamilyMetricBall N.family N.distance ballRadius left)
      (finiteFamilyMetricBall N.family N.distance ballRadius right))
    (omega : (N.family -> Fin 1) × (N.family -> Fin 1)) :
    ActualRetainedY1PairSelection D
      (Finset.univ : Finset
        (ActualGPrimeLabelFirstExactCSurvivor
          N D keep left right ballRadius omega))
      (actualGPrimeLabelFirstExactCLeftIndex
        N D keep left right ballRadius omega)
      (actualGPrimeLabelFirstExactCRightIndex
        N D keep left right ballRadius omega)
      (actualGPrimeLabelFirstExactCLabel
        N D keep left right ballRadius omega)
      keep (4 * ballRadius) := by
  classical
  let cells := actualGPrimeBilateralRetainedFineExactCCells
    N D keep left right ballRadius
  let leftNeighbors : cells -> Finset N.family := fun cell =>
    actualGPrimeRetainedFineExactCMetricNeighbors
      N D keep left ballRadius cell.1.1 cell.1.2
  let rightNeighbors : cells -> Finset N.family := fun cell =>
    actualGPrimeRetainedFineExactCMetricNeighbors
      N D keep right ballRadius cell.1.1 cell.1.2
  constructor
  · intro S _hS
    have hmem := (survivorLeftHitWitness 1 1 leftNeighbors rightNeighbors
      omega S).2.1
    exact (mem_actualGPrimeRetainedFineExactCMetricNeighbors_iff
      N D keep left ballRadius S.1.1.1 S.1.1.2
        (survivorLeftHitWitness 1 1 leftNeighbors rightNeighbors omega S).1).mp
          hmem |>.1
  · intro S _hS
    have hmem := (survivorRightHitWitness 1 1 leftNeighbors rightNeighbors
      omega S).2.1
    exact (mem_actualGPrimeRetainedFineExactCMetricNeighbors_iff
      N D keep right ballRadius S.1.1.1 S.1.1.2
        (survivorRightHitWitness 1 1 leftNeighbors rightNeighbors omega S).1).mp
          hmem |>.1
  · intro S _hS
    have hleftData :=
      (mem_actualGPrimeRetainedFineExactCMetricNeighbors_iff
        N D keep left ballRadius S.1.1.1 S.1.1.2
          (survivorLeftHitWitness 1 1 leftNeighbors rightNeighbors omega S).1).mp
            (survivorLeftHitWitness 1 1 leftNeighbors rightNeighbors omega S).2.1
    have hrightData :=
      (mem_actualGPrimeRetainedFineExactCMetricNeighbors_iff
        N D keep right ballRadius S.1.1.1 S.1.1.2
          (survivorRightHitWitness 1 1 leftNeighbors rightNeighbors omega S).1).mp
            (survivorRightHitWitness 1 1 leftNeighbors rightNeighbors omega S).2.1
    exact hleftData.2.1.trans hrightData.2.1.symm
  · intro S _hS
    let leftHit := survivorLeftHitWitness 1 1
      leftNeighbors rightNeighbors omega S
    let rightHit := survivorRightHitWitness 1 1
      leftNeighbors rightNeighbors omega S
    have hleftData :=
      (mem_actualGPrimeRetainedFineExactCMetricNeighbors_iff
        N D keep left ballRadius S.1.1.1 S.1.1.2 leftHit.1).mp leftHit.2.1
    have hrightData :=
      (mem_actualGPrimeRetainedFineExactCMetricNeighbors_iff
        N D keep right ballRadius S.1.1.1 S.1.1.2 rightHit.1).mp rightHit.2.1
    have hleftBall : leftHit.1.1 ∈
        finiteFamilyMetricBall N.family N.distance ballRadius left := by
      exact Finset.mem_filter.mpr ⟨leftHit.1.2, hleftData.2.2⟩
    have hrightBall : rightHit.1.1 ∈
        finiteFamilyMetricBall N.family N.distance ballRadius right := by
      exact Finset.mem_filter.mpr ⟨rightHit.1.2, hrightData.2.2⟩
    have hsep := hcross leftHit.1.1 hleftBall rightHit.1.1 hrightBall
    calc
      2 * (4 * ballRadius) = 8 * ballRadius := by ring
      _ <= N.distance leftHit.1.1 rightHit.1.1 := hsep
      _ = projectedTubePairCoefficientDistance
          (D.fine.tubes leftHit.1.1) (D.fine.tubes rightHit.1.1) :=
        hdistance _ _
      _ = tubePairCoefficientDistance
          (D.fine.tubes leftHit.1.1) (D.fine.tubes rightHit.1.1) :=
        (tubePairCoefficientDistance_eq_projectedTubePairCoefficientDistance
          (D.fine.tubes leftHit.1.1) (D.fine.tubes rightHit.1.1)).symm

theorem ActualGPrimeLabelFirstExactCSampledOutcome.survivors_nonempty
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    {fineLabel : Type v} [DecidableEq fineLabel]
    (N : CanonicalNormNonconcentrationData iota)
    (D : CoarseRectangleIncidenceData (point := Real × Real)
      (radius := radius) (iota := iota) fineLabel)
    (keep : iota -> fineLabel -> Prop) (left right : iota)
    (ballRadius : Real)
    (omega : (N.family -> Fin 1) × (N.family -> Fin 1))
    (O : ActualGPrimeLabelFirstExactCSampledOutcome
      N D keep left right ballRadius omega)
    (hcells : (actualGPrimeBilateralRetainedFineExactCCells
      N D keep left right ballRadius).Nonempty) :
    (Finset.univ : Finset (ActualGPrimeLabelFirstExactCSurvivor
      N D keep left right ballRadius omega)).Nonempty := by
  classical
  have hcellsPos : 0 < (actualGPrimeBilateralRetainedFineExactCCells
      N D keep left right ballRadius).card := Finset.card_pos.mpr hcells
  have hcellsReal : (0 : Real) <
      (actualGPrimeBilateralRetainedFineExactCCells
        N D keep left right ballRadius).card := by exact_mod_cast hcellsPos
  have hsurvival := O.survival
  have hsurvivors : (twoSidedZeroColorSurvivors 1 1
      (fun cell : actualGPrimeBilateralRetainedFineExactCCells
          N D keep left right ballRadius =>
        actualGPrimeRetainedFineExactCMetricNeighbors
          N D keep left ballRadius cell.1.1 cell.1.2)
      (fun cell : actualGPrimeBilateralRetainedFineExactCCells
          N D keep left right ballRadius =>
        actualGPrimeRetainedFineExactCMetricNeighbors
          N D keep right ballRadius cell.1.1 cell.1.2)
      omega).Nonempty := by
    by_contra hnot
    have hempty := Finset.not_nonempty_iff_eq_empty.mp hnot
    rw [hempty] at hsurvival
    norm_num at hsurvival
    linarith
  obtain ⟨cell, hcell⟩ := hsurvivors
  exact ⟨⟨cell, hcell⟩, Finset.mem_univ _⟩

#print axioms mem_actualGPrimeRetainedFineExactCCells_iff
#print axioms mem_actualGPrimeRetainedFineExactCMetricNeighbors_iff
#print axioms mem_actualGPrimeBilateralRetainedFineExactCCells_iff
#print axioms exists_actualGPrimeLabelFirstExactCSampledOutcome
#print axioms actualGPrimeLabelFirstExactC_actualRetainedY1PairSelection
#print axioms ActualGPrimeLabelFirstExactCSampledOutcome.survivors_nonempty

end

end FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstExactCProvenanceV2
