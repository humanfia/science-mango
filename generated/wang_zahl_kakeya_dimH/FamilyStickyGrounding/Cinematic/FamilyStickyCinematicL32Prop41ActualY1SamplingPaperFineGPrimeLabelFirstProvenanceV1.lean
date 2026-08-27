import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeSharpBudgetSampleConnectorV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41ActualY1PaperFineThreeShiftScaleProducerV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000

namespace FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstProvenanceV1

open Set
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open FamilyStickyCinematicL32ActualTubeCoefficientDistancesV1
open FamilyStickyCinematicL32CurvilinearRectanglePointMultiplicityV1
open FamilyStickyCinematicL32FiniteMetricMaximalCoverV1
open FamilyStickyCinematicL32FiniteProjectedShadingMultiplicitySliceV1
open FamilyStickyCinematicL32Prop41ActualGlobalNormCoarseFiberV1
open FamilyStickyCinematicL32Prop41ActualGlobalNormCoarseFiberRandomSamplingV1
open FamilyStickyCinematicL32Prop41ActualY1ExactCFiberPairSelectionV1
open FamilyStickyCinematicL32Prop41ActualY1FixedCommonCSelectionConnectorV1
open FamilyStickyCinematicL32Prop41ActualY1RetainedThreeShiftPerturbationReadyV1
open FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeSamplingBridgeV1
open FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeSharpBudgetSampleConnectorV1
open FamilyStickyCinematicL32Prop41CanonicalMaximizerNonconcentrationV1
open FamilyStickyCinematicL32Prop41CoarseRectangleIncidenceDataV1
open FamilyStickyCinematicL32Prop41FiniteRandomSamplingExtractionV1
open FamilyStickyCinematicL32Prop41FiniteRandomSamplingSubfamilyExtractionV1
open FamilyStickyCinematicL32Prop41SeparatedCoefficientBallPairV1
open FamilyStickyCinematicL32TubePairTraceV1

noncomputable section

universe u v

/-!
# Label-first G-prime sampling provenance

The existing common-coarse sampler chooses the left and right tube hits
independently.  Its incidence theorem therefore produces two fine labels,
which need not agree.  This is not enough to construct
`ActualSharedGlobalSurvivorCommonFineRefinement`.

This module records the minimal honest repair.  It first bins by a retained
fine label and samples the two tube sides inside that single bin.  The generic
two-colour sampler then retains exactly the same constants: one eighth of the
eligible fine-label bins and seven times the expected tube load.  A selected
item carries its common fine label by construction.  For a G-prime pair, the
cross-separation of the two coefficient balls gives the required lower bound
at `pairScale = 4 * ballRadius` for every selected item.
-/

/-- Retained incidences at one fine label, restricted to one canonical
coefficient ball and retyped into the canonical ambient family. -/
noncomputable def actualGPrimeRetainedFineMetricNeighbors
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    {fineLabel : Type v} [DecidableEq fineLabel]
    (N : CanonicalNormNonconcentrationData iota)
    (D : CoarseRectangleIncidenceData (point := Real × Real)
      (radius := radius) (iota := iota) fineLabel)
    (keep : iota -> fineLabel -> Prop) (center : iota)
    (ballRadius : Real) (r : fineLabel) : Finset N.family :=
  ambientSubtypeRestriction N.family
    ((retainedY1IndicesAtFine D keep r).filter fun i =>
      N.distance i center <= ballRadius)

@[simp]
theorem mem_actualGPrimeRetainedFineMetricNeighbors_iff
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    {fineLabel : Type v} [DecidableEq fineLabel]
    (N : CanonicalNormNonconcentrationData iota)
    (D : CoarseRectangleIncidenceData (point := Real × Real)
      (radius := radius) (iota := iota) fineLabel)
    (keep : iota -> fineLabel -> Prop) (center : iota)
    (ballRadius : Real) (r : fineLabel) (i : N.family) :
    i ∈ actualGPrimeRetainedFineMetricNeighbors N D keep center ballRadius r ↔
      (i.1, r) ∈ D.retainedGoodPairs keep ∧
        N.distance i.1 center <= ballRadius := by
  rw [actualGPrimeRetainedFineMetricNeighbors,
    mem_ambientSubtypeRestriction_iff]
  simp only [Finset.mem_filter,
    mem_retainedY1IndicesAtFine_iff]

/-- Fine labels which have at least one retained incidence in each of the two
selected G-prime balls.  This is the exact support on which a common-label
sampler can honestly run. -/
noncomputable def actualGPrimeBilateralRetainedFineLabels
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    {fineLabel : Type v} [DecidableEq fineLabel]
    (N : CanonicalNormNonconcentrationData iota)
    (D : CoarseRectangleIncidenceData (point := Real × Real)
      (radius := radius) (iota := iota) fineLabel)
    (keep : iota -> fineLabel -> Prop) (left right : iota)
    (ballRadius : Real) : Finset fineLabel := by
  classical
  exact D.fineLabels.filter fun r =>
    (actualGPrimeRetainedFineMetricNeighbors
      N D keep left ballRadius r).Nonempty ∧
    (actualGPrimeRetainedFineMetricNeighbors
      N D keep right ballRadius r).Nonempty

@[simp]
theorem mem_actualGPrimeBilateralRetainedFineLabels_iff
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    {fineLabel : Type v} [DecidableEq fineLabel]
    (N : CanonicalNormNonconcentrationData iota)
    (D : CoarseRectangleIncidenceData (point := Real × Real)
      (radius := radius) (iota := iota) fineLabel)
    (keep : iota -> fineLabel -> Prop) (left right : iota)
    (ballRadius : Real) (r : fineLabel) :
    r ∈ actualGPrimeBilateralRetainedFineLabels
        N D keep left right ballRadius ↔
      r ∈ D.fineLabels ∧
        (actualGPrimeRetainedFineMetricNeighbors
          N D keep left ballRadius r).Nonempty ∧
        (actualGPrimeRetainedFineMetricNeighbors
          N D keep right ballRadius r).Nonempty := by
  classical
  simp [actualGPrimeBilateralRetainedFineLabels]

/-- A label-first survivor.  Its rectangle coordinate is literally an
eligible retained fine label, so both selected hits have the same label. -/
abbrev ActualGPrimeLabelFirstSurvivor
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    {fineLabel : Type v} [DecidableEq fineLabel]
    (N : CanonicalNormNonconcentrationData iota)
    (D : CoarseRectangleIncidenceData (point := Real × Real)
      (radius := radius) (iota := iota) fineLabel)
    (keep : iota -> fineLabel -> Prop) (left right : iota)
    (ballRadius : Real)
    (omega : (N.family -> Fin 1) × (N.family -> Fin 1)) :=
  TwoSidedZeroColorSurvivor 1 1
    (fun r : actualGPrimeBilateralRetainedFineLabels
        N D keep left right ballRadius =>
      actualGPrimeRetainedFineMetricNeighbors
        N D keep left ballRadius r.1)
    (fun r : actualGPrimeBilateralRetainedFineLabels
        N D keep left right ballRadius =>
      actualGPrimeRetainedFineMetricNeighbors
        N D keep right ballRadius r.1)
    omega

/-- Common retained fine label of a label-first survivor. -/
def actualGPrimeLabelFirstLabel
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    {fineLabel : Type v} [DecidableEq fineLabel]
    (N : CanonicalNormNonconcentrationData iota)
    (D : CoarseRectangleIncidenceData (point := Real × Real)
      (radius := radius) (iota := iota) fineLabel)
    (keep : iota -> fineLabel -> Prop) (left right : iota)
    (ballRadius : Real)
    (omega : (N.family -> Fin 1) × (N.family -> Fin 1)) :
    ActualGPrimeLabelFirstSurvivor N D keep left right ballRadius omega ->
      fineLabel :=
  fun S => S.1.1

/-- Actual left index selected in a label-first survivor. -/
noncomputable def actualGPrimeLabelFirstLeftIndex
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    {fineLabel : Type v} [DecidableEq fineLabel]
    (N : CanonicalNormNonconcentrationData iota)
    (D : CoarseRectangleIncidenceData (point := Real × Real)
      (radius := radius) (iota := iota) fineLabel)
    (keep : iota -> fineLabel -> Prop) (left right : iota)
    (ballRadius : Real)
    (omega : (N.family -> Fin 1) × (N.family -> Fin 1)) :
    ActualGPrimeLabelFirstSurvivor N D keep left right ballRadius omega ->
      iota :=
  fun S => (survivorLeftHitWitness 1 1
    (fun r : actualGPrimeBilateralRetainedFineLabels
        N D keep left right ballRadius =>
      actualGPrimeRetainedFineMetricNeighbors
        N D keep left ballRadius r.1)
    (fun r : actualGPrimeBilateralRetainedFineLabels
        N D keep left right ballRadius =>
      actualGPrimeRetainedFineMetricNeighbors
        N D keep right ballRadius r.1)
    omega S).1.1

/-- Actual right index selected in a label-first survivor. -/
noncomputable def actualGPrimeLabelFirstRightIndex
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    {fineLabel : Type v} [DecidableEq fineLabel]
    (N : CanonicalNormNonconcentrationData iota)
    (D : CoarseRectangleIncidenceData (point := Real × Real)
      (radius := radius) (iota := iota) fineLabel)
    (keep : iota -> fineLabel -> Prop) (left right : iota)
    (ballRadius : Real)
    (omega : (N.family -> Fin 1) × (N.family -> Fin 1)) :
    ActualGPrimeLabelFirstSurvivor N D keep left right ballRadius omega ->
      iota :=
  fun S => (survivorRightHitWitness 1 1
    (fun r : actualGPrimeBilateralRetainedFineLabels
        N D keep left right ballRadius =>
      actualGPrimeRetainedFineMetricNeighbors
        N D keep left ballRadius r.1)
    (fun r : actualGPrimeBilateralRetainedFineLabels
        N D keep left right ballRadius =>
      actualGPrimeRetainedFineMetricNeighbors
        N D keep right ballRadius r.1)
    omega S).1.1

/-! ## The unchanged random-sampling constants -/

/-- A label-first sample with the same one-eighth survival and sevenfold load
as the original common-coarse sampler. -/
structure ActualGPrimeLabelFirstSampledOutcome
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    {fineLabel : Type v} [DecidableEq fineLabel]
    (N : CanonicalNormNonconcentrationData iota)
    (D : CoarseRectangleIncidenceData (point := Real × Real)
      (radius := radius) (iota := iota) fineLabel)
    (keep : iota -> fineLabel -> Prop) (left right : iota)
    (ballRadius : Real)
    (omega : (N.family -> Fin 1) × (N.family -> Fin 1)) : Prop where
  survival :
    ((actualGPrimeBilateralRetainedFineLabels
      N D keep left right ballRadius).card : Real) / 8 <=
      ((twoSidedZeroColorSurvivors 1 1
        (fun r : actualGPrimeBilateralRetainedFineLabels
            N D keep left right ballRadius =>
          actualGPrimeRetainedFineMetricNeighbors
            N D keep left ballRadius r.1)
        (fun r : actualGPrimeBilateralRetainedFineLabels
            N D keep left right ballRadius =>
          actualGPrimeRetainedFineMetricNeighbors
            N D keep right ballRadius r.1)
        omega).card : Real)
  load : twoSidedZeroColorLoad 1 1 omega <=
    7 * ((N.family.card : Real) / (1 : Real) +
      (N.family.card : Real) / (1 : Real))
  retained_tube_card_le_load :
    ((survivorRetainedPairTubeFamily 1 1
      (fun r : actualGPrimeBilateralRetainedFineLabels
          N D keep left right ballRadius =>
        actualGPrimeRetainedFineMetricNeighbors
          N D keep left ballRadius r.1)
      (fun r : actualGPrimeBilateralRetainedFineLabels
          N D keep left right ballRadius =>
        actualGPrimeRetainedFineMetricNeighbors
          N D keep right ballRadius r.1)
      omega (fun i : N.family => D.fine.tubes i.1)
        (fun i : N.family => D.fine.tubes i.1)).card : Real) <=
      twoSidedZeroColorLoad 1 1 omega

/-- Run the generic sampler after the common-fine-label binning.  No
common-label witness is an input. -/
theorem exists_actualGPrimeLabelFirstSampledOutcome
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    {fineLabel : Type v} [DecidableEq fineLabel]
    (N : CanonicalNormNonconcentrationData iota)
    (D : CoarseRectangleIncidenceData (point := Real × Real)
      (radius := radius) (iota := iota) fineLabel)
    (keep : iota -> fineLabel -> Prop) (left right : iota)
    (ballRadius : Real) :
    exists omega : (N.family -> Fin 1) × (N.family -> Fin 1),
      ActualGPrimeLabelFirstSampledOutcome
        N D keep left right ballRadius omega := by
  classical
  let labels := actualGPrimeBilateralRetainedFineLabels
    N D keep left right ballRadius
  let leftNeighbors : labels -> Finset N.family := fun r =>
    actualGPrimeRetainedFineMetricNeighbors
      N D keep left ballRadius r.1
  let rightNeighbors : labels -> Finset N.family := fun r =>
    actualGPrimeRetainedFineMetricNeighbors
      N D keep right ballRadius r.1
  have hleft : forall r : labels, 1 <= (leftNeighbors r).card := by
    intro r
    apply Finset.one_le_card.mpr
    exact ((mem_actualGPrimeBilateralRetainedFineLabels_iff
      N D keep left right ballRadius r.1).mp r.2).2.1
  have hright : forall r : labels, 1 <= (rightNeighbors r).card := by
    intro r
    apply Finset.one_le_card.mpr
    exact ((mem_actualGPrimeBilateralRetainedFineLabels_iff
      N D keep left right ballRadius r.1).mp r.2).2.2
  obtain ⟨omega, hsurvival, hload⟩ :=
    exists_twoSidedZeroColor_sample_with_eighth_survival_and_sevenfold_load
      (Rectangle := labels) (alpha := N.family) (beta := N.family)
      1 1 leftNeighbors rightNeighbors hleft hright
  refine ⟨omega, {
    survival := ?_
    load := ?_
    retained_tube_card_le_load := ?_ }⟩
  · simpa only [labels, leftNeighbors, rightNeighbors,
      Fintype.card_coe, Nat.cast_one] using hsurvival
  · simpa only [Nat.cast_one, Fintype.card_coe] using hload
  · exact survivorRetainedPairTubeFamily_card_cast_le_load 1 1
      leftNeighbors rightNeighbors omega
      (fun i : N.family => D.fine.tubes i.1)
      (fun i : N.family => D.fine.tubes i.1)

/-! ## Automatic common label and coefficient separation -/

/-- The old common-coarse carrier already gets coefficient separation from
the G-prime bridge.  This removes the second upstream input without changing
that carrier, at the forced scale `4 * ballRadius`. -/
theorem ActualConcreteGPrimeCommonCoarseSharpSamplingOutcome.sharedGlobalSurvivor_coefficientLower
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    {fineLabel : Type v} [DecidableEq fineLabel]
    (fine : UniformTubeFamily radius iota)
    (physical : FiniteProjectedShading (Real × Real) iota)
    (globalScale : Real) (globalCenter : Tube radius)
    (N : CanonicalNormNonconcentrationData iota)
    (D : CoarseRectangleIncidenceData (point := Real × Real)
      (radius := radius) (iota := iota) fineLabel)
    (ballRadius : Real) (bucket : Nat)
    (keep : iota -> fineLabel -> Prop) (left right : iota)
    (rectangles : Finset C2GraphRectangle)
    (O : ActualConcreteGPrimeCommonCoarseSharpSamplingOutcome fine physical
      globalScale globalCenter N D ballRadius bucket keep left right rectangles)
    (omega :
      (actualGlobalNormIndexFamily fine physical globalScale globalCenter ->
          Fin 1) ×
        (actualGlobalNormIndexFamily fine physical globalScale globalCenter ->
          Fin 1))
    (S : ActualSharedGlobalSurvivorItem fine physical globalScale globalCenter
      D keep rectangles (D.fine.tubes left) (D.fine.tubes right) ballRadius
        1 1 omega) :
    2 * (4 * ballRadius) <= tubePairCoefficientDistance
      (D.fine.tubes (actualSharedGlobalSurvivorLeftIndex fine physical
        globalScale globalCenter D keep rectangles (D.fine.tubes left)
          (D.fine.tubes right) ballRadius 1 1 omega S))
      (D.fine.tubes (actualSharedGlobalSurvivorRightIndex fine physical
        globalScale globalCenter D keep rectangles (D.fine.tubes left)
          (D.fine.tubes right) ballRadius 1 1 omega S)) := by
  have hrectangles := O.rectangles_eq
  subst rectangles
  exact O.bridge.survivor_pair_separated omega S

/-- Label-first survivor pairs form an `ActualRetainedY1PairSelection`.
Common-label membership is definitional, common `c` comes from the existing
fixed global fibre, and coefficient separation comes from the two G-prime
balls.  Neither of the two pointwise provenance inputs of the old uniform
package appears. -/
theorem actualGPrimeLabelFirst_actualRetainedY1PairSelection
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    {fineLabel : Type v} [DecidableEq fineLabel]
    (fine : UniformTubeFamily radius iota)
    (physical : FiniteProjectedShading (Real × Real) iota)
    (globalScale : Real) (globalCenter : Tube radius)
    (N : CanonicalNormNonconcentrationData iota)
    (D : CoarseRectangleIncidenceData (point := Real × Real)
      (radius := radius) (iota := iota) fineLabel)
    (keep : iota -> fineLabel -> Prop) (left right : iota)
    (ballRadius : Real)
    (hfamily : N.family =
      actualGlobalNormIndexFamily fine physical globalScale globalCenter)
    (hdistance : forall i j, N.distance i j =
      projectedTubePairCoefficientDistance
        (D.fine.tubes i) (D.fine.tubes j))
    (hcross : FiniteFamiliesCrossSeparated N.distance (8 * ballRadius)
      (finiteFamilyMetricBall N.family N.distance ballRadius left)
      (finiteFamilyMetricBall N.family N.distance ballRadius right))
    (commonC : Real)
    (C : ActualGlobalNormIndexFamilyFixedCProvenance fine physical globalScale
      globalCenter D commonC)
    (omega : (N.family -> Fin 1) × (N.family -> Fin 1)) :
    ActualRetainedY1PairSelection D
      (Finset.univ : Finset
        (ActualGPrimeLabelFirstSurvivor
          N D keep left right ballRadius omega))
      (actualGPrimeLabelFirstLeftIndex
        N D keep left right ballRadius omega)
      (actualGPrimeLabelFirstRightIndex
        N D keep left right ballRadius omega)
      (actualGPrimeLabelFirstLabel
        N D keep left right ballRadius omega)
      keep (4 * ballRadius) := by
  classical
  let labels := actualGPrimeBilateralRetainedFineLabels
    N D keep left right ballRadius
  let leftNeighbors : labels -> Finset N.family := fun r =>
    actualGPrimeRetainedFineMetricNeighbors
      N D keep left ballRadius r.1
  let rightNeighbors : labels -> Finset N.family := fun r =>
    actualGPrimeRetainedFineMetricNeighbors
      N D keep right ballRadius r.1
  constructor
  · intro S _hS
    have hmem := (survivorLeftHitWitness 1 1 leftNeighbors rightNeighbors
      omega S).2.1
    exact (mem_actualGPrimeRetainedFineMetricNeighbors_iff
      N D keep left ballRadius S.1.1
        (survivorLeftHitWitness 1 1 leftNeighbors rightNeighbors omega S).1).mp
          hmem |>.1
  · intro S _hS
    have hmem := (survivorRightHitWitness 1 1 leftNeighbors rightNeighbors
      omega S).2.1
    exact (mem_actualGPrimeRetainedFineMetricNeighbors_iff
      N D keep right ballRadius S.1.1
        (survivorRightHitWitness 1 1 leftNeighbors rightNeighbors omega S).1).mp
          hmem |>.1
  · intro S _hS
    have hleftN : actualGPrimeLabelFirstLeftIndex
        N D keep left right ballRadius omega S ∈ N.family :=
      (survivorLeftHitWitness 1 1 leftNeighbors rightNeighbors omega S).1.2
    have hrightN : actualGPrimeLabelFirstRightIndex
        N D keep left right ballRadius omega S ∈ N.family :=
      (survivorRightHitWitness 1 1 leftNeighbors rightNeighbors omega S).1.2
    have hleftC := C.fixed_c _ (by rw [← hfamily]; exact hleftN)
    have hrightC := C.fixed_c _ (by rw [← hfamily]; exact hrightN)
    exact hleftC.trans hrightC.symm
  · intro S _hS
    let leftHit := survivorLeftHitWitness 1 1
      leftNeighbors rightNeighbors omega S
    let rightHit := survivorRightHitWitness 1 1
      leftNeighbors rightNeighbors omega S
    have hleftData :=
      (mem_actualGPrimeRetainedFineMetricNeighbors_iff
        N D keep left ballRadius S.1.1 leftHit.1).mp leftHit.2.1
    have hrightData :=
      (mem_actualGPrimeRetainedFineMetricNeighbors_iff
        N D keep right ballRadius S.1.1 rightHit.1).mp rightHit.2.1
    have hleftBall : leftHit.1.1 ∈
        finiteFamilyMetricBall N.family N.distance ballRadius left := by
      exact Finset.mem_filter.mpr ⟨leftHit.1.2, hleftData.2⟩
    have hrightBall : rightHit.1.1 ∈
        finiteFamilyMetricBall N.family N.distance ballRadius right := by
      exact Finset.mem_filter.mpr ⟨rightHit.1.2, hrightData.2⟩
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

/-- Positive eligible-label support and the one-eighth survival inequality
force a nonempty label-first survivor family. -/
theorem ActualGPrimeLabelFirstSampledOutcome.survivors_nonempty
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    {fineLabel : Type v} [DecidableEq fineLabel]
    (N : CanonicalNormNonconcentrationData iota)
    (D : CoarseRectangleIncidenceData (point := Real × Real)
      (radius := radius) (iota := iota) fineLabel)
    (keep : iota -> fineLabel -> Prop) (left right : iota)
    (ballRadius : Real)
    (omega : (N.family -> Fin 1) × (N.family -> Fin 1))
    (O : ActualGPrimeLabelFirstSampledOutcome
      N D keep left right ballRadius omega)
    (hlabels : (actualGPrimeBilateralRetainedFineLabels
      N D keep left right ballRadius).Nonempty) :
    (Finset.univ : Finset (ActualGPrimeLabelFirstSurvivor
      N D keep left right ballRadius omega)).Nonempty := by
  classical
  have hlabelsPos : 0 < (actualGPrimeBilateralRetainedFineLabels
      N D keep left right ballRadius).card := Finset.card_pos.mpr hlabels
  have hlabelsReal : (0 : Real) <
      (actualGPrimeBilateralRetainedFineLabels
        N D keep left right ballRadius).card := by exact_mod_cast hlabelsPos
  have hsurvival := O.survival
  have hsurvivors : (twoSidedZeroColorSurvivors 1 1
      (fun r : actualGPrimeBilateralRetainedFineLabels
          N D keep left right ballRadius =>
        actualGPrimeRetainedFineMetricNeighbors
          N D keep left ballRadius r.1)
      (fun r : actualGPrimeBilateralRetainedFineLabels
          N D keep left right ballRadius =>
        actualGPrimeRetainedFineMetricNeighbors
          N D keep right ballRadius r.1)
      omega).Nonempty := by
    by_contra hnot
    have hempty := Finset.not_nonempty_iff_eq_empty.mp hnot
    rw [hempty] at hsurvival
    norm_num at hsurvival
    linarith
  obtain ⟨r, hr⟩ := hsurvivors
  exact ⟨⟨r, hr⟩, Finset.mem_univ _⟩

#print axioms mem_actualGPrimeRetainedFineMetricNeighbors_iff
#print axioms mem_actualGPrimeBilateralRetainedFineLabels_iff
#print axioms exists_actualGPrimeLabelFirstSampledOutcome
#print axioms ActualConcreteGPrimeCommonCoarseSharpSamplingOutcome.sharedGlobalSurvivor_coefficientLower
#print axioms actualGPrimeLabelFirst_actualRetainedY1PairSelection
#print axioms ActualGPrimeLabelFirstSampledOutcome.survivors_nonempty

end

end FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstProvenanceV1
