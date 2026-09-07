import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32PyzActualNormFirstAllCenterHighConcreteQPFirstHitRichPairSumV9
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41ActualGPrimeLabelFirstWeightedFineSeparatedPairMassProducerV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace FamilyStickyCinematicL32PyzActualNormFirstAllCenterHighPreMaxFirstHitPairMassV2

open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open FamilyStickyCinematicL32FiniteProjectedPositiveMultiplicityDyadicV1
open FamilyStickyCinematicL32PyzE2DyadicDegreeWindowV1
open FamilyStickyCinematicL32PyzActualAllCenterBinUniformityV1
open FamilyStickyCinematicL32PyzActualNormFirstAllCenterPayloadDichotomyFinalCleanV2
open FamilyStickyCinematicL32Lemma57DyadicCeilBucketV1
open FamilyStickyCinematicL32Prop41ActualGPrimeDegreeRichMassProducerV1
open FamilyStickyCinematicL32Prop41ActualGPrimeLabelFirstFineSeparatedPairE2ConnectorV1
open FamilyStickyCinematicL32Prop41ActualGPrimeLabelFirstFineSeparatedPairMassProducerV1
open FamilyStickyCinematicL32Prop41ActualGPrimeLabelFirstWeightedFineSeparatedPairMassProducerV1
open FamilyStickyCinematicL32Prop41CanonicalMaximizerNonconcentrationV1
open FamilyStickyCinematicL32Prop41CoarseRectangleIncidenceDataV1
open FamilyStickyCinematicL32Prop41ActualY1E2SpatialActivePatternFloorCoverV1
open FamilyStickyCinematicL32Prop41ActualY1SharpFineScaleTangencyV1
open FamilyStickyCinematicL32ActualTubeCoefficientDistancesV1
open FamilyStickyCinematicL32Prop41ActualPositiveCenterHighPayloadWeightedFullyActualConnectorV1
open FamilyStickyCinematicL32Prop41ActualY1E2SpatialFirstHitWeightedGPrimeSamplingConnectorV1
open FamilyStickyCinematicL32Prop41ActualY1E2ToLabelFirstSelectedMassV1
open FamilyStickyCinematicL32Prop41ActualY1E2ToLabelFirstSelectedMassTopV1
open FamilyStickyCinematicL32Prop41ActualY1FineCoarseRectangleProducerV1
open FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstProvenanceV1
open FamilyStickyCinematicL32PyzActualAllCenterCanonicalPayloadFinalV5
open FamilyStickyCinematicL32PyzActualNormFirstAllCenterHighConcreteQPFirstHitRichPairSumV9
open FamilyStickyCinematicL32PyzActualNormFirstAllCenterHighConcreteQPOutcomeV4
open FamilyStickyCinematicL32PyzActualNormFirstAllCenterHighConcreteQPRetentionV4
open FamilyStickyCinematicL32PyzActualNormFirstAllCenterHighConcreteQPWeightedGeometricSumV2
open FamilyStickyCinematicL32PyzActualNormFirstAllCenterMassWeightedBranchTypesV5C

noncomputable section

universe u v

/-!
# The actual first-hit pair mass before centre-pair maximization

The selected-pair endpoint repeats one selected first-hit mass once for every
admissible centre pair.  That expression is useful for a crude cardinal cap,
but it hides the incidence structure needed for a sharp packing argument.

Here the first-hit weight is inserted before centre-pair maximization.  The
local quantity is definitionally the fine-label-first sum

`sum_r firstHitWeight(r) * #(separated pairs incident to r)`.

The proof below generates its per-label pair lower bound from the actual E2
degree and canonical near-neighbour cap.  It introduces no packing, ambient
cardinality, wide-cap, or desired-conclusion premise.
-/

/-- Generic weighted degree-gap lower bound before selecting a centre pair. -/
theorem fineLabelWeightSum_mul_degreeGap_le_centerPairMass
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    {fineLabel : Type v} [DecidableEq fineLabel]
    (N : CanonicalNormNonconcentrationData iota)
    (R : CoarseRectangleIncidenceData (point := Real × Real)
      (radius := radius) (iota := iota) fineLabel)
    (keep : iota -> fineLabel -> Prop) (ballRadius : Real)
    (degreeLower : Nat) (labelWeight : fineLabel -> ENNReal)
    (hdegree : forall r, r ∈ R.fineLabels ->
      degreeLower <=
        (actualGPrimeRetainedFineActiveFiber N R keep r).card)
    (hsymm : forall x y, N.distance x y = N.distance y x)
    (hnearRadiusLower : N.delta <= 10 * ballRadius)
    (hnearRadiusUpper : 10 * ballRadius <= N.ceiling) :
    (∑ r ∈ R.fineLabels, labelWeight r) *
        ((degreeLower *
          (degreeLower - automaticCanonicalNearCap N ballRadius) : Nat) :
            ENNReal) <=
      actualGPrimeWeightedFineSeparatedCenterPairMass
        N R keep ballRadius labelWeight := by
  let pairLower : Nat := degreeLower *
    (degreeLower - automaticCanonicalNearCap N ballRadius)
  have hperLabel : forall r, r ∈ R.fineLabels ->
      pairLower <=
        (actualGPrimeFineSeparatedPairsAt N R keep ballRadius r).card := by
    intro r hr
    have hcap : forall left,
        left ∈ actualGPrimeRetainedFineActiveFiber N R keep r ->
        (actualGPrimeFineNearRightFiber
          N R keep ballRadius r left).card <=
          automaticCanonicalNearCap N ballRadius := by
      intro left hleft
      exact actualGPrimeFineNearRightFiber_card_le_automatic
        N R keep ballRadius r hsymm hnearRadiusLower hnearRadiusUpper
          left hleft
    exact (Nat.mul_le_mul (hdegree r hr)
      (Nat.sub_le_sub_right (hdegree r hr)
        (automaticCanonicalNearCap N ballRadius))).trans
      (actualGPrimeFineActive_card_mul_tsub_nearCap_le_separated_card
        N R keep ballRadius r
          (automaticCanonicalNearCap N ballRadius) hcap)
  rw [← actualGPrimeWeightedFineSeparatedPairMass_eq_centerPairMass]
  exact fineLabelWeightSum_mul_pairLower_le_weightedSeparatedPairMass
    N R keep ballRadius labelWeight pairLower hperLabel

/-- The actual centre-pair total at one high centre.  Unlike the selected
pair mass, this is the entire pre-max Fubini sum. -/
noncomputable def nativeHighPreMaxFirstHitCenterPairMass
    {radius : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    (D : NativeBranchCore radius iota) (G : NativeHighGeometry D)
    (c : D.HighCenter) : ENNReal :=
  let H := D.chosenHighPayloadAt c
  let E_t := positiveCenterTangencyCell (D.highBase c) D.S.family D.physical
    D.f D.f1 D.f2 D.outerA D.outerB D.hOuter D.hf D.hf1 D.globalScale
      c.1.1 D.tangencyExponent H.payload.tangencyLabel
  let hEt : MeasurableSet E_t := measurableSet_positiveCenterTangencyCell
    (D.highBase c) (D.highBase_measurable c) D.S.family D.physical
      D.f D.f1 D.f2 D.outerA D.outerB D.hOuter D.hf D.hf1 D.globalScale
        c.1.1 D.tangencyExponent H.payload.tangencyLabel
  let globalDelta := dyadicCeilUpper H.payload.tangencyLabel
  let N := positiveCenterHighPayloadGlobalNormData H
  let R := actualCenteredHalfPaperFineE2SpatialIncidenceData E_t hEt
    D.S.family D.physical H.payload.finalLabel (G.mesh c) D.f D.f1 D.f2
      D.outerA D.outerB D.hOuter D.hf D.hf1 D.globalScale globalDelta c.1.1
        (36 * D.globalScale) D.tangencyExponent
  actualGPrimeWeightedFineSeparatedCenterPairMass
    N R (fun _ _ => True) (G.ballRadius c)
      (actualGPrimeE2FirstHitLabelWeight R H.payload.finalLabel)

/-- The preceding centre-first quantity is literally the fine-label-first
weighted incidence sum. -/
theorem nativeHighPreMaxFirstHitCenterPairMass_eq_labelFirst
    {radius : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    (D : NativeBranchCore radius iota) (G : NativeHighGeometry D)
    (c : D.HighCenter) :
    let H := D.chosenHighPayloadAt c
    let E_t := positiveCenterTangencyCell (D.highBase c) D.S.family D.physical
      D.f D.f1 D.f2 D.outerA D.outerB D.hOuter D.hf D.hf1 D.globalScale
        c.1.1 D.tangencyExponent H.payload.tangencyLabel
    let hEt : MeasurableSet E_t := measurableSet_positiveCenterTangencyCell
      (D.highBase c) (D.highBase_measurable c) D.S.family D.physical
        D.f D.f1 D.f2 D.outerA D.outerB D.hOuter D.hf D.hf1 D.globalScale
          c.1.1 D.tangencyExponent H.payload.tangencyLabel
    let globalDelta := dyadicCeilUpper H.payload.tangencyLabel
    let N := positiveCenterHighPayloadGlobalNormData H
    let R := actualCenteredHalfPaperFineE2SpatialIncidenceData E_t hEt
      D.S.family D.physical H.payload.finalLabel (G.mesh c) D.f D.f1 D.f2
        D.outerA D.outerB D.hOuter D.hf D.hf1 D.globalScale globalDelta c.1.1
          (36 * D.globalScale) D.tangencyExponent
    nativeHighPreMaxFirstHitCenterPairMass D G c =
      actualGPrimeWeightedFineSeparatedPairMass
        N R (fun _ _ => True) (G.ballRadius c)
          (actualGPrimeE2FirstHitLabelWeight R H.payload.finalLabel) := by
  dsimp only [nativeHighPreMaxFirstHitCenterPairMass]
  exact (actualGPrimeWeightedFineSeparatedPairMass_eq_centerPairMass
    _ _ _ _ _).symm

/-- The actual E2 mass times its degree gap is bounded by the full pre-max
first-hit pair mass.  The local concrete conclusion is used only for its
already-proved first-hit mass identity; no selected-pair inequality is used. -/
theorem paperFineE2_mul_degreeGap_le_preMaxFirstHitCenterPairMass
    {radius : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    (D : NativeBranchCore radius iota) (G : NativeHighGeometry D)
    (c : D.HighCenter)
    (h : PositiveCenterHighPayloadBaseWeightedGlobalSampledLensConclusion
      (D.highBase c) (D.highBase_measurable c) D.S.family D.physical
      D.f D.f1 D.f2 D.outerA D.outerB D.hOuter D.hf D.hf1 D.globalScale
        c.1.1 D.tangencyExponent D.normExponent D.logCount
          (D.chosenHighPayloadAt c) (G.mesh c) (G.ballRadius c)) :
    let H := D.chosenHighPayloadAt c
    let E_t := positiveCenterTangencyCell (D.highBase c) D.S.family D.physical
      D.f D.f1 D.f2 D.outerA D.outerB D.hOuter D.hf D.hf1 D.globalScale
        c.1.1 D.tangencyExponent H.payload.tangencyLabel
    let hEt : MeasurableSet E_t := measurableSet_positiveCenterTangencyCell
      (D.highBase c) (D.highBase_measurable c) D.S.family D.physical
        D.f D.f1 D.f2 D.outerA D.outerB D.hOuter D.hf D.hf1 D.globalScale
          c.1.1 D.tangencyExponent H.payload.tangencyLabel
    let globalDelta := dyadicCeilUpper H.payload.tangencyLabel
    volume (actualCenteredHalfPaperFineE2 E_t hEt D.S.family D.physical
        H.payload.finalLabel D.f D.f1 D.f2 D.outerA D.outerB D.hOuter
          D.hf D.hf1 D.globalScale c.1.1 (36 * D.globalScale)
            D.tangencyExponent globalDelta) *
        nativeHighConcreteDegreeGap D G c <=
      nativeHighPreMaxFirstHitCenterPairMass D G c := by
  dsimp only
  let H := D.chosenHighPayloadAt c
  let E_t := positiveCenterTangencyCell (D.highBase c) D.S.family D.physical
    D.f D.f1 D.f2 D.outerA D.outerB D.hOuter D.hf D.hf1 D.globalScale
      c.1.1 D.tangencyExponent H.payload.tangencyLabel
  let hEt : MeasurableSet E_t := measurableSet_positiveCenterTangencyCell
    (D.highBase c) (D.highBase_measurable c) D.S.family D.physical
      D.f D.f1 D.f2 D.outerA D.outerB D.hOuter D.hf D.hf1 D.globalScale
        c.1.1 D.tangencyExponent H.payload.tangencyLabel
  let globalDelta := dyadicCeilUpper H.payload.tangencyLabel
  let N := positiveCenterHighPayloadGlobalNormData H
  let R := actualCenteredHalfPaperFineE2SpatialIncidenceData E_t hEt
    D.S.family D.physical H.payload.finalLabel (G.mesh c) D.f D.f1 D.f2
      D.outerA D.outerB D.hOuter D.hf D.hf1 D.globalScale globalDelta c.1.1
        (36 * D.globalScale) D.tangencyExponent
  let Y1 := actualCenteredHalfPaperFineY1 E_t hEt D.S.family D.physical
    D.f D.f1 D.f2 D.outerA D.outerB D.hOuter D.hf D.hf1 D.globalScale
      c.1.1 (36 * D.globalScale) D.tangencyExponent globalDelta
  let source := actualCenteredHalfPaperFineE2 E_t hEt D.S.family D.physical
    H.payload.finalLabel D.f D.f1 D.f2 D.outerA D.outerB D.hOuter D.hf
      D.hf1 D.globalScale c.1.1 (36 * D.globalScale)
        D.tangencyExponent globalDelta
  let patternAt := D.physical.activeAtPoint
  let fineLabels : Finset
      (ActualCenteredHalfPaperFineE2SpatialLabel E_t hEt D.S.family
        D.physical H.payload.finalLabel (G.mesh c) D.f D.f1 D.f2 D.outerA
          D.outerB D.hOuter D.hf D.hf1 D.globalScale c.1.1
            (36 * D.globalScale) D.tangencyExponent globalDelta) :=
    Finset.univ
  let pointAt := spatialActivePatternRepresentative D.physical.ambient
    patternAt source (G.mesh c)
  let fineT := prop41Y1PaperFineT (radius : Real) globalDelta D.globalScale
  have hspatialLabels : R.fineLabels = fineLabels := by rfl
  have hpointAt : R.pointAt = pointAt := by rfl
  have hshading : R.shading = Y1 := by rfl
  obtain ⟨_hlabel, _hq, _hmass, _hEtPos, _hEtSubset, _hbin, _hE2Pos,
      _hE2Measurable, _hE2Subset, hactivePayload⟩ := H.payload.certificate
  have hactiveSource : forall q, q ∈ source ->
      (Y1.activeAtPoint q).Nonempty := by
    intro q hqSource
    have hqPositive : q ∈ positiveCenterE2 (D.highBase c)
        (D.highBase_measurable c) D.S.family D.physical D.f D.f1 D.f2
          D.outerA D.outerB D.hOuter D.hf D.hf1 D.globalScale c.1.1
            D.tangencyExponent H.payload.tangencyLabel
              H.payload.finalLabel := by
      simpa only [source, Y1, actualCenteredHalfPaperFineE2,
        actualCenteredHalfPaperFineY1, positiveCenterE2, positiveCenterY1,
        positiveCenterTangencyCell, E_t, hEt, globalDelta] using hqSource
    obtain ⟨i, hi⟩ := hactivePayload q hqPositive
    refine ⟨i, ?_⟩
    simpa only [Y1, actualCenteredHalfPaperFineY1, positiveCenterY1,
      positiveCenterTangencyCell, E_t, hEt, globalDelta] using hi
  have hcell : forall r, r ∈ R.fineLabels ->
      R.pointAt r ∈ projectedPositiveMultiplicityDyadicCell
        R.shading H.payload.finalLabel := by
    intro r _hr
    rw [hpointAt, hshading]
    exact (spatialActivePatternRepresentative_spec D.physical.ambient
      patternAt source (G.mesh c) r).1
  have hactiveR : forall r, r ∈ R.fineLabels ->
      (R.shading.activeAtPoint (R.pointAt r)).Nonempty := by
    intro r hr
    rw [hpointAt, hshading]
    exact hactiveSource (pointAt r) (hcell r hr)
  have hRactual : R = actualCenteredHalfY1FineCoarseRectangleData E_t hEt
      D.S.family D.physical fineLabels pointAt D.f D.f1 D.f2 D.outerA
        D.outerB D.hOuter D.hf D.hf1 D.globalScale c.1.1
          (36 * D.globalScale) D.tangencyExponent globalDelta fineT
            globalDelta D.globalScale := by rfl
  have hsubsetR : forall r, r ∈ R.fineLabels ->
      R.shading.activeAtPoint (R.pointAt r) ⊆ N.family := by
    intro r hr
    rw [positiveCenterHighPayloadGlobalNormData_family, hRactual]
    exact actualCenteredHalfY1_activeAtFine_subset_globalNormIndexFamily
      E_t hEt D.S.family D.physical fineLabels pointAt D.f D.f1 D.f2
      D.outerA D.outerB D.hOuter D.hf D.hf1 D.globalScale c.1.1
      (36 * D.globalScale) D.tangencyExponent globalDelta fineT
      globalDelta D.globalScale r (by simpa only [hspatialLabels] using hr)
  have hdegree : forall r, r ∈ R.fineLabels ->
      pyzE2DegreeLower H.payload.finalLabel <=
        (actualGPrimeRetainedFineActiveFiber
          N R (fun _ _ => True) r).card := by
    intro r hr
    exact pyzE2DegreeLower_le_actualGPrimeRetainedFineActiveFiber_true
      N R H.payload.finalLabel r hr (hcell r hr) (hactiveR r hr)
        (hsubsetR r hr)
  have hsymm : forall x y, N.distance x y = N.distance y x := by
    intro x y
    exact projectedTubePairCoefficientDistance_comm _ _
  let Q := positiveCenterHighPayload_baseConcreteQ
    (D.highBase c) (D.highBase_measurable c) D.S.family D.physical
      D.f D.f1 D.f2 D.outerA D.outerB D.hOuter D.hf D.hf1 D.globalScale
        c.1.1 D.tangencyExponent D.normExponent D.logCount H (G.mesh c)
          (G.ballRadius c) h
  have hmass :
      (∑ r ∈ R.fineLabels,
          actualGPrimeE2FirstHitLabelWeight R H.payload.finalLabel r) =
        volume (projectedPositiveMultiplicityDyadicCell
          R.shading H.payload.finalLabel) := Q.firstHit_mass_eq
  have hpair := fineLabelWeightSum_mul_degreeGap_le_centerPairMass
    N R (fun _ _ => True) (G.ballRadius c)
      (pyzE2DegreeLower H.payload.finalLabel)
      (actualGPrimeE2FirstHitLabelWeight R H.payload.finalLabel)
      hdegree hsymm (G.hnearRadiusLower c) (G.hnearRadiusUpper c)
  rw [hmass] at hpair
  simpa only [R, actualCenteredHalfPaperFineE2SpatialIncidenceData,
    actualCenteredHalfProjectedE2SpatialIncidenceData,
    y1FineCoarseRectangleData, actualCenteredHalfPaperFineY1,
    actualCenteredHalfPaperFineE2, nativeHighConcreteDegreeGap,
    nativeHighPreMaxFirstHitCenterPairMass] using hpair

/-- The local high-base inequality with the full pre-max pair mass. -/
theorem highBase_mul_degreeGap_le_binLoss_mul_preMaxFirstHitCenterPairMass
    {radius : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    (D : NativeBranchCore radius iota) (G : NativeHighGeometry D)
    (c : D.HighCenter)
    (h : PositiveCenterHighPayloadBaseWeightedGlobalSampledLensConclusion
      (D.highBase c) (D.highBase_measurable c) D.S.family D.physical
      D.f D.f1 D.f2 D.outerA D.outerB D.hOuter D.hf D.hf1 D.globalScale
        c.1.1 D.tangencyExponent D.normExponent D.logCount
          (D.chosenHighPayloadAt c) (G.mesh c) (G.ballRadius c)) :
    volume (D.highBase c) * nativeHighConcreteDegreeGap D G c <=
      actualAllCenterPostNormBinLoss radius D.globalScale
          D.physical.ambient.card *
        nativeHighPreMaxFirstHitCenterPairMass D G c := by
  let H := D.chosenHighPayloadAt c
  let E_t := positiveCenterTangencyCell (D.highBase c) D.S.family D.physical
    D.f D.f1 D.f2 D.outerA D.outerB D.hOuter D.hf D.hf1 D.globalScale
      c.1.1 D.tangencyExponent H.payload.tangencyLabel
  let hEt : MeasurableSet E_t := measurableSet_positiveCenterTangencyCell
    (D.highBase c) (D.highBase_measurable c) D.S.family D.physical
      D.f D.f1 D.f2 D.outerA D.outerB D.hOuter D.hf D.hf1 D.globalScale
        c.1.1 D.tangencyExponent H.payload.tangencyLabel
  let globalDelta := dyadicCeilUpper H.payload.tangencyLabel
  exact positiveCenterHighPayload_base_mul_degree_le_binLoss_mul_of_E2_mul_le
    (D.highBase c) (D.highBase_measurable c) D.S.family D.physical
      D.f D.f1 D.f2 D.outerA D.outerB D.hOuter D.hf D.hf1 D.globalScale
        c.1.1 D.tangencyExponent D.normExponent D.logCount H
          (nativeHighConcreteDegreeGap D G c)
          (nativeHighPreMaxFirstHitCenterPairMass D G c)
          (paperFineE2_mul_degreeGap_le_preMaxFirstHitCenterPairMass
            D G c h)

/-- Sum of the full first-hit pair-incidence mass over all actual high
centres. -/
noncomputable def nativeHighPreMaxFirstHitPairMassBudget
    {radius : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    {D : NativeBranchCore radius iota} (G : NativeHighGeometry D) : ENNReal :=
  ∑ c : D.HighCenter, nativeHighPreMaxFirstHitCenterPairMass D G c

/-- Honest all-centre endpoint before any centre-pair maximization.  The
remaining theorem is now precisely a packing upper bound for the same
fine-label-first incidence sum. -/
theorem NativeHighConcreteQPOutcome.sourceMass_half_le_binLoss_mul_preMaxFirstHitPairMassBudget
    {radius : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    {D : NativeBranchCore radius iota} {G : NativeHighGeometry D}
    (hout : NativeHighConcreteQPOutcome D G)
    (hhalf : D.sourceMass / 2 <=
      ∑ c ∈ D.high, volume (D.cell c.1)) :
    D.sourceMass / 2 <=
      actualAllCenterPostNormBinLoss radius D.globalScale
          D.physical.ambient.card *
        nativeHighPreMaxFirstHitPairMassBudget G := by
  classical
  have hbaseSum :
      (∑ c : D.HighCenter, volume (D.highBase c)) =
        ∑ c ∈ D.high, volume (D.cell c.1) := by
    simpa only [NativeBranchCore.highBase,
      NativeBranchCore.positiveBase, Finset.univ_eq_attach] using
        Finset.sum_attach D.high (fun c => volume (D.cell c.1))
  have hhalf' : D.sourceMass / 2 <=
      ∑ c : D.HighCenter, volume (D.highBase c) :=
    hhalf.trans_eq hbaseSum.symm
  have hhalfUniv : D.sourceMass / 2 <=
      ∑ c ∈ (Finset.univ : Finset D.HighCenter),
        volume (D.highBase c) := by
    simpa only [Finset.sum_filter, Finset.mem_univ, if_true] using hhalf'
  have hsum := half_sourceMass_le_sum_rhs_of_degreeGap
    (high := (Finset.univ : Finset D.HighCenter))
    (weight := fun c => volume (D.highBase c))
    (rhs := fun c =>
      actualAllCenterPostNormBinLoss radius D.globalScale
          D.physical.ambient.card *
        nativeHighPreMaxFirstHitCenterPairMass D G c)
    (degreeGap := fun c =>
      pyzE2DegreeLower (D.chosenHighPayloadAt c).payload.finalLabel *
        (pyzE2DegreeLower (D.chosenHighPayloadAt c).payload.finalLabel -
          automaticCanonicalNearCap
            (positiveCenterHighPayloadGlobalNormData
              (D.chosenHighPayloadAt c)) (G.ballRadius c)))
    D.sourceMass hhalfUniv
    (by
      intro c _hc
      have hc := G.hroom c
      have hd : 1 <=
          pyzE2DegreeLower (D.chosenHighPayloadAt c).payload.finalLabel := by
        omega
      have hdiff : 1 <=
          pyzE2DegreeLower (D.chosenHighPayloadAt c).payload.finalLabel -
            automaticCanonicalNearCap
              (positiveCenterHighPayloadGlobalNormData
                (D.chosenHighPayloadAt c)) (G.ballRadius c) := by
        omega
      calc
        1 = 1 * 1 := by norm_num
        _ <= pyzE2DegreeLower
              (D.chosenHighPayloadAt c).payload.finalLabel *
            (pyzE2DegreeLower
                (D.chosenHighPayloadAt c).payload.finalLabel -
              automaticCanonicalNearCap
                (positiveCenterHighPayloadGlobalNormData
                  (D.chosenHighPayloadAt c)) (G.ballRadius c)) :=
          Nat.mul_le_mul hd hdiff)
    (by
      intro c _hc
      simpa only [nativeHighConcreteDegreeGap] using
        highBase_mul_degreeGap_le_binLoss_mul_preMaxFirstHitCenterPairMass
          D G c (nativeHighConcreteQPLocalAt hout c))
  calc
    D.sourceMass / 2 <=
        ∑ c ∈ (Finset.univ : Finset D.HighCenter),
          actualAllCenterPostNormBinLoss radius D.globalScale
              D.physical.ambient.card *
            nativeHighPreMaxFirstHitCenterPairMass D G c := hsum
    _ = actualAllCenterPostNormBinLoss radius D.globalScale
          D.physical.ambient.card *
        nativeHighPreMaxFirstHitPairMassBudget G := by
      simp only [nativeHighPreMaxFirstHitPairMassBudget, Finset.mul_sum]

#print axioms fineLabelWeightSum_mul_degreeGap_le_centerPairMass
#print axioms nativeHighPreMaxFirstHitCenterPairMass
#print axioms nativeHighPreMaxFirstHitCenterPairMass_eq_labelFirst
#print axioms paperFineE2_mul_degreeGap_le_preMaxFirstHitCenterPairMass
#print axioms highBase_mul_degreeGap_le_binLoss_mul_preMaxFirstHitCenterPairMass
#print axioms nativeHighPreMaxFirstHitPairMassBudget
#print axioms NativeHighConcreteQPOutcome.sourceMass_half_le_binLoss_mul_preMaxFirstHitPairMassBudget

end

end FamilyStickyCinematicL32PyzActualNormFirstAllCenterHighPreMaxFirstHitPairMassV2
