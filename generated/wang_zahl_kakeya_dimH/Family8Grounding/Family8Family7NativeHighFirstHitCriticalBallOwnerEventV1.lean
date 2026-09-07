import Family8Grounding.Family8Family7NativeHighFirstHitTubeOccurrenceNativeV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Lemma55E2FineRectangleFirstHitY2V1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8Family7NativeHighFirstHitCriticalBallOwnerEventV1

open Family8Family7NativeHighFirstHitTubeOccurrenceNativeV1
open Family8Family7NativeHighWeightedCriticalBallV1
open FamilyStickyCinematicL32FiniteProjectedPositiveMultiplicityDyadicV1
open FamilyStickyCinematicL32Lemma55E2FineRectangleFirstHitY2V1
open FamilyStickyCinematicL32Prop41ActualGPrimeLabelFirstFineSeparatedPairMassProducerV1
open FamilyStickyCinematicL32Prop41ActualPositiveCenterHighPayloadWeightedFullyActualConnectorV1
open FamilyStickyCinematicL32Prop41ActualY1E2SpatialFirstHitWeightedGPrimeSamplingConnectorV1
open FamilyStickyCinematicL32Prop41CoarseRectangleIncidenceDataV1
open FamilyStickyCinematicL32Prop41CanonicalMaximizerNonconcentrationV1
open FamilyStickyCinematicL32PyzActualNormFirstAllCenterHighConcreteQPRetentionV4
open FamilyStickyCinematicL32PyzActualNormFirstAllCenterMassWeightedBranchTypesV5C
open FamilyStickyCinematicL32PyzLowMultiplicityRestrictedThreeHalfV1

noncomputable section

universe u v

/-!
# A literal first-hit owner event on the weighted critical ball

Every fine label chooses one genuine retained tube occurrence.  The full
first-hit label mass is charged to that owner.  Maximizing these owner
weights therefore selects a critical ball together with an actual measurable
union of whole first-hit pieces.  Its volume is exactly the selected ball's
weight, and each point comes with an owner in that very ball and the same
critical centre/scale.
-/

/-- Producer data for a genuine owner of every retained first-hit label. -/
structure ActualGPrimeE2FirstHitOwnerData
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    {fineLabel : Type v} [DecidableEq fineLabel]
    (N : CanonicalNormNonconcentrationData iota)
    (D : CoarseRectangleIncidenceData (point := Real × Real)
      (radius := radius) (iota := iota) fineLabel)
    (label : Int) : Prop where
  fiber_nonempty : ∀ r, r ∈ D.fineLabels →
    (actualGPrimeRetainedFineActiveFiber
      N D (fun _ _ => True) r).Nonempty

namespace ActualGPrimeE2FirstHitOwnerData

variable {radius : NNReal} {iota : Type u} [DecidableEq iota]
variable {fineLabel : Type v} [DecidableEq fineLabel]
variable {N : CanonicalNormNonconcentrationData iota}
variable {D : CoarseRectangleIncidenceData (point := Real × Real)
  (radius := radius) (iota := iota) fineLabel}
variable {label : Int}

/-- One actual retained tube occurrence for a fine label.  Outside the
literal finite label carrier an arbitrary norm-family element is used. -/
noncomputable def owner (P : ActualGPrimeE2FirstHitOwnerData N D label)
    (r : fineLabel) : iota :=
  if hr : r ∈ D.fineLabels then Classical.choose (P.fiber_nonempty r hr)
  else Classical.choose N.family_nonempty

theorem owner_mem_fiber
    (P : ActualGPrimeE2FirstHitOwnerData N D label)
    {r : fineLabel} (hr : r ∈ D.fineLabels) :
    P.owner r ∈ actualGPrimeRetainedFineActiveFiber
      N D (fun _ _ => True) r := by
  rw [owner, dif_pos hr]
  exact Classical.choose_spec (P.fiber_nonempty r hr)

theorem owner_mem_family
    (P : ActualGPrimeE2FirstHitOwnerData N D label)
    {r : fineLabel} (hr : r ∈ D.fineLabels) :
    P.owner r ∈ N.family := by
  exact (Finset.mem_inter.mp (P.owner_mem_fiber hr)).2

/-- Whole-label first-hit weight charged to its genuine owner tube. -/
noncomputable def ownerWeight
    (P : ActualGPrimeE2FirstHitOwnerData N D label) (i : iota) : ENNReal :=
  ∑ r ∈ D.fineLabels,
    if P.owner r = i then actualGPrimeE2FirstHitLabelWeight D label r else 0

theorem ownerWeight_support
    (P : ActualGPrimeE2FirstHitOwnerData N D label)
    {i : iota} (hi : P.ownerWeight i ≠ 0) : i ∈ N.family := by
  by_contra hiFamily
  apply hi
  unfold ownerWeight
  apply Finset.sum_eq_zero
  intro r hr
  have hne : P.owner r ≠ i := by
    intro h
    apply hiFamily
    rw [← h]
    exact P.owner_mem_family hr
  simp [hne]

theorem sum_ownerWeight_eq_labelWeight
    (P : ActualGPrimeE2FirstHitOwnerData N D label) :
    (∑ i ∈ N.family, P.ownerWeight i) =
      ∑ r ∈ D.fineLabels,
        actualGPrimeE2FirstHitLabelWeight D label r := by
  classical
  unfold ownerWeight
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r hr
  simp [P.owner_mem_family hr]

/-- The canonical weighted selector for the literal whole-label owner
charge. -/
noncomputable def weightedNormData
    (P : ActualGPrimeE2FirstHitOwnerData N D label) :
    WeightedCanonicalNormBallData iota where
  family := N.family
  distance := N.distance
  weight := P.ownerWeight
  delta := N.delta
  ceiling := N.ceiling
  exponent := N.exponent
  family_nonempty := N.family_nonempty
  self_le_delta := N.self_le_delta
  delta_pos := N.delta_pos
  delta_le_ceiling := N.delta_le_ceiling
  exponent_nonneg := N.exponent_nonneg

/-- Fine labels whose actual owner belongs to the selected weighted ball. -/
noncomputable def criticalOwnerLabels
    (P : ActualGPrimeE2FirstHitOwnerData N D label) : Finset fineLabel :=
  D.fineLabels.filter fun r =>
    P.owner r ∈ P.weightedNormData.criticalBall

/-- Literal measurable union of whole first-hit pieces selected by the same
weighted critical ball. -/
noncomputable def criticalOwnerEvent
    (P : ActualGPrimeE2FirstHitOwnerData N D label) : Set (Real × Real) :=
  ⋃ r ∈ (P.criticalOwnerLabels : Set fineLabel),
    firstHitFineRectangleY2
      (projectedPositiveMultiplicityDyadicCell D.shading label)
      D.fineLabels D.fineRectangleAt (radius : Real) r

theorem measurableSet_criticalOwnerEvent
    (P : ActualGPrimeE2FirstHitOwnerData N D label) :
    MeasurableSet P.criticalOwnerEvent := by
  unfold criticalOwnerEvent
  apply FamilyStickyCinematicL32Lemma55FiniteMeasurableFirstHitPartitionV1.measurableSet_finiteBiUnion
  intro r _hr
  exact measurableSet_firstHitFineRectangleY2 _ _ _ _
    (measurableSet_projectedPositiveMultiplicityDyadicCell D.shading label) r

/-- Every selected-event point has a literal fine label and owner in the
very same weighted critical ball. -/
theorem mem_criticalOwnerEvent_owner_mem_criticalBall
    (P : ActualGPrimeE2FirstHitOwnerData N D label)
    {x : Real × Real} (hx : x ∈ P.criticalOwnerEvent) :
    ∃ r, r ∈ D.fineLabels ∧
      P.owner r ∈ P.weightedNormData.criticalBall ∧
      x ∈ firstHitFineRectangleY2
        (projectedPositiveMultiplicityDyadicCell D.shading label)
        D.fineLabels D.fineRectangleAt (radius : Real) r := by
  unfold criticalOwnerEvent at hx
  simp only [Set.mem_iUnion] at hx
  obtain ⟨r, hrSelected, hxr⟩ := hx
  have hrData := Finset.mem_filter.mp hrSelected
  exact ⟨r, hrData.1, hrData.2, hxr⟩

/-- Pointwise selected owner lies within the selected scale of the same
critical centre. -/
theorem mem_criticalOwnerEvent_owner_distance_to_center
    (P : ActualGPrimeE2FirstHitOwnerData N D label)
    {x : Real × Real} (hx : x ∈ P.criticalOwnerEvent) :
    ∃ r, r ∈ D.fineLabels ∧
      x ∈ firstHitFineRectangleY2
        (projectedPositiveMultiplicityDyadicCell D.shading label)
        D.fineLabels D.fineRectangleAt (radius : Real) r ∧
      N.distance (P.owner r) P.weightedNormData.criticalCenter ≤
        P.weightedNormData.criticalScale := by
  obtain ⟨r, hr, howner, hxr⟩ :=
    P.mem_criticalOwnerEvent_owner_mem_criticalBall hx
  exact ⟨r, hr, hxr,
    P.weightedNormData.criticalBall_distance_to_center howner⟩

theorem sum_ownerWeight_criticalBall_eq_selectedLabelWeight
    (P : ActualGPrimeE2FirstHitOwnerData N D label) :
    (∑ i ∈ P.weightedNormData.criticalBall, P.ownerWeight i) =
      ∑ r ∈ P.criticalOwnerLabels,
        actualGPrimeE2FirstHitLabelWeight D label r := by
  classical
  unfold ownerWeight criticalOwnerLabels
  rw [Finset.sum_comm, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro r hr
  by_cases howner : P.owner r ∈ P.weightedNormData.criticalBall
  · simp [howner]
  · simp [howner]

theorem volume_criticalOwnerEvent_eq_criticalBallWeight
    (P : ActualGPrimeE2FirstHitOwnerData N D label) :
    volume P.criticalOwnerEvent =
      ∑ i ∈ P.weightedNormData.criticalBall, P.ownerWeight i := by
  have hmeasurable : ∀ r, r ∈ P.criticalOwnerLabels →
      MeasurableSet (firstHitFineRectangleY2
        (projectedPositiveMultiplicityDyadicCell D.shading label)
        D.fineLabels D.fineRectangleAt (radius : Real) r) := by
    intro r _hr
    exact measurableSet_firstHitFineRectangleY2 _ _ _ _
      (measurableSet_projectedPositiveMultiplicityDyadicCell D.shading label) r
  have hdisjoint : Set.PairwiseDisjoint
      (P.criticalOwnerLabels : Set fineLabel)
      (firstHitFineRectangleY2
        (projectedPositiveMultiplicityDyadicCell D.shading label)
        D.fineLabels D.fineRectangleAt (radius : Real)) := by
    intro r hr s hs hrs
    exact (firstHitFineRectangleY2_pairwiseDisjoint
      (projectedPositiveMultiplicityDyadicCell D.shading label)
      D.fineLabels D.fineRectangleAt (radius : Real))
        (Finset.filter_subset _ _ hr) (Finset.filter_subset _ _ hs) hrs
  have hmeasure :
      volume (⋃ r ∈ (P.criticalOwnerLabels : Set fineLabel),
        firstHitFineRectangleY2
          (projectedPositiveMultiplicityDyadicCell D.shading label)
          D.fineLabels D.fineRectangleAt (radius : Real) r) =
        ∑ r ∈ P.criticalOwnerLabels,
          volume (firstHitFineRectangleY2
            (projectedPositiveMultiplicityDyadicCell D.shading label)
            D.fineLabels D.fineRectangleAt (radius : Real) r) :=
    measure_biUnion_finset hdisjoint hmeasurable
  unfold criticalOwnerEvent
  rw [hmeasure]
  exact P.sum_ownerWeight_criticalBall_eq_selectedLabelWeight.symm

end ActualGPrimeE2FirstHitOwnerData

universe w

/-- The callback-free owner data at one actual native high centre. -/
theorem nativeHighFirstHitOwnerData
    {radius : NNReal} {iota : Type w} [Fintype iota] [DecidableEq iota]
    (D : NativeBranchCore radius iota) (G : NativeHighGeometry D)
    (c : D.HighCenter) :
    ActualGPrimeE2FirstHitOwnerData
      (nativeHighFirstHitNormData D c)
      (nativeHighFirstHitIncidenceData D G c)
      (D.chosenHighPayloadAt c).payload.finalLabel where
  fiber_nonempty := nativeHighFirstHitRetainedFiber_nonempty D G c

/-- Total whole-label owner weight is the literal projected E2 mass. -/
theorem sum_nativeHighFirstHitOwnerWeight_eq_E2Mass
    {radius : NNReal} {iota : Type w} [Fintype iota] [DecidableEq iota]
    (D : NativeBranchCore radius iota) (G : NativeHighGeometry D)
    (c : D.HighCenter)
    (h : PositiveCenterHighPayloadBaseWeightedGlobalSampledLensConclusion
      (D.highBase c) (D.highBase_measurable c) D.S.family D.physical
      D.f D.f1 D.f2 D.outerA D.outerB D.hOuter D.hf D.hf1 D.globalScale
        c.1.1 D.tangencyExponent D.normExponent D.logCount
          (D.chosenHighPayloadAt c) (G.mesh c) (G.ballRadius c)) :
    let H := D.chosenHighPayloadAt c
    let N := nativeHighFirstHitNormData D c
    let R := nativeHighFirstHitIncidenceData D G c
    let P := nativeHighFirstHitOwnerData D G c
    (∑ i ∈ N.family, P.ownerWeight i) =
      volume (projectedPositiveMultiplicityDyadicCell
        R.shading H.payload.finalLabel) := by
  let H := D.chosenHighPayloadAt c
  let N := nativeHighFirstHitNormData D c
  let R := nativeHighFirstHitIncidenceData D G c
  let P := nativeHighFirstHitOwnerData D G c
  let Q := positiveCenterHighPayload_baseConcreteQ
    (D.highBase c) (D.highBase_measurable c) D.S.family D.physical
      D.f D.f1 D.f2 D.outerA D.outerB D.hOuter D.hf D.hf1 D.globalScale
        c.1.1 D.tangencyExponent D.normExponent D.logCount H (G.mesh c)
          (G.ballRadius c) h
  change (∑ i ∈ N.family, P.ownerWeight i) =
    volume (projectedPositiveMultiplicityDyadicCell
      R.shading H.payload.finalLabel)
  rw [P.sum_ownerWeight_eq_labelWeight]
  exact Q.firstHit_mass_eq

#print axioms ActualGPrimeE2FirstHitOwnerData.owner
#print axioms ActualGPrimeE2FirstHitOwnerData.owner_mem_fiber
#print axioms ActualGPrimeE2FirstHitOwnerData.ownerWeight
#print axioms ActualGPrimeE2FirstHitOwnerData.sum_ownerWeight_eq_labelWeight
#print axioms ActualGPrimeE2FirstHitOwnerData.weightedNormData
#print axioms ActualGPrimeE2FirstHitOwnerData.criticalOwnerEvent
#print axioms ActualGPrimeE2FirstHitOwnerData.measurableSet_criticalOwnerEvent
#print axioms ActualGPrimeE2FirstHitOwnerData.mem_criticalOwnerEvent_owner_distance_to_center
#print axioms ActualGPrimeE2FirstHitOwnerData.volume_criticalOwnerEvent_eq_criticalBallWeight
#print axioms nativeHighFirstHitOwnerData
#print axioms sum_nativeHighFirstHitOwnerWeight_eq_E2Mass

end

end Family8Family7NativeHighFirstHitCriticalBallOwnerEventV1
