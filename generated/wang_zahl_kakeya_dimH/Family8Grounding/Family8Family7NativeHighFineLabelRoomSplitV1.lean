import Family8Grounding.Family8Family7NativeHighFineLabelNormalizedMassV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32PyzActualNormFirstHighDyadicPairMassUpperV3
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8Family7NativeHighFineLabelRoomSplitV1

open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open FamilyStickyCinematicL32FiniteProjectedPositiveMultiplicityDyadicV1
open FamilyStickyCinematicL32PyzE2DyadicDegreeWindowV1
open FamilyStickyCinematicL32PyzActualAllCenterBinUniformityV1
open FamilyStickyCinematicL32Lemma57DyadicCeilBucketV1
open FamilyStickyCinematicL32Prop41ActualGPrimeDegreeRichMassProducerV1
open FamilyStickyCinematicL32Prop41ActualGPrimeLabelFirstFineSeparatedPairMassProducerV1
open FamilyStickyCinematicL32Prop41ActualGPrimeLabelFirstWeightedFineSeparatedPairMassProducerV1
open FamilyStickyCinematicL32Prop41ActualGPrimeSynchronizedActualPairIncidenceV2
open FamilyStickyCinematicL32Prop41ActualPositiveCenterHighPayloadWeightedFullyActualConnectorV1
open FamilyStickyCinematicL32Prop41ActualY1E2SpatialFirstHitWeightedGPrimeSamplingConnectorV1
open FamilyStickyCinematicL32Prop41ActualY1E2ToLabelFirstSelectedMassTopV1
open FamilyStickyCinematicL32Prop41CanonicalMaximizerNonconcentrationV1
open FamilyStickyCinematicL32Prop41CanonicalRichSeparatedPairConsumerV1
open FamilyStickyCinematicL32Prop41CoarseRectangleIncidenceDataV1
open FamilyStickyCinematicL32Prop41FiniteRichSeparatedPairSelectionV1
open FamilyStickyCinematicL32PyzActualAllCenterCanonicalPayloadFinalV5
open FamilyStickyCinematicL32PyzActualNormFirstAllCenterHighConcreteQPFirstHitRichPairSumV9
open FamilyStickyCinematicL32PyzActualNormFirstAllCenterHighConcreteQPOutcomeV4
open FamilyStickyCinematicL32PyzActualNormFirstAllCenterHighConcreteQPWeightedGeometricSumV2
open FamilyStickyCinematicL32PyzActualNormFirstAllCenterHighPreMaxFirstHitGlobalMassV2
open FamilyStickyCinematicL32PyzActualNormFirstAllCenterHighPreMaxFirstHitPairMassV2
open FamilyStickyCinematicL32PyzActualNormFirstAllCenterMassWeightedBranchTypesV5C
open FamilyStickyCinematicL32PyzActualNormFirstHighDyadicPairMassUpperV3
open Family8Family7NativeHighFineLabelNormalizedMassV1

noncomputable section

universe u v

/-!
# Fractional degree-room split for the normalized native-high mass

The strict room currently stored by `NativeHighGeometry` permits the degree
gap to be only one.  This file makes the exact missing quantitative split:

* on centres with `2 * nearCap <= degreeLower`, the fine-label pair
  multiplicity divided by the degree gap is at most the absolute constant
  `8`;
* every complementary centre satisfies
  `degreeLower < 2 * nearCap`, so the unresolved branch is an actual
  near-saturation statement about the canonical norm ball.

No desired-conclusion scalar or packing callback is added.
-/

/-- Increasing the separation radius can only remove fine endpoint pairs. -/
theorem actualGPrimeFineSeparatedPairsAt_anti_ballRadius
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    {fineLabel : Type v} [DecidableEq fineLabel]
    (N : CanonicalNormNonconcentrationData iota)
    (D : CoarseRectangleIncidenceData (point := Real × Real)
      (radius := radius) (iota := iota) fineLabel)
    (keep : iota -> fineLabel -> Prop) {smallRadius largeRadius : Real}
    (hRadius : smallRadius <= largeRadius) (r : fineLabel) :
    actualGPrimeFineSeparatedPairsAt N D keep largeRadius r ⊆
      actualGPrimeFineSeparatedPairsAt N D keep smallRadius r := by
  classical
  intro pair hpair
  simp only [actualGPrimeFineSeparatedPairsAt, Finset.mem_filter,
    Finset.mem_product] at hpair ⊢
  refine ⟨hpair.1, ?_⟩
  unfold canonicalTenRadiusSeparated at hpair ⊢
  exact (mul_le_mul_of_nonneg_left hRadius (by norm_num)).trans hpair.2

/-- The weighted fine-label pair mass has the same radius monotonicity. -/
theorem actualGPrimeWeightedFineSeparatedPairMass_anti_ballRadius
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    {fineLabel : Type v} [DecidableEq fineLabel]
    (N : CanonicalNormNonconcentrationData iota)
    (D : CoarseRectangleIncidenceData (point := Real × Real)
      (radius := radius) (iota := iota) fineLabel)
    (keep : iota -> fineLabel -> Prop) {smallRadius largeRadius : Real}
    (hRadius : smallRadius <= largeRadius)
    (labelWeight : fineLabel -> ENNReal) :
    actualGPrimeWeightedFineSeparatedPairMass N D keep largeRadius
        labelWeight <=
      actualGPrimeWeightedFineSeparatedPairMass N D keep smallRadius
        labelWeight := by
  classical
  unfold actualGPrimeWeightedFineSeparatedPairMass
  apply Finset.sum_le_sum
  intro r hr
  gcongr
  exact actualGPrimeFineSeparatedPairsAt_anti_ballRadius
    N D keep hRadius r

theorem actualGPrimeSurvivorSeparationRadius_le
    {ballRadius : Real} (hballRadius : 0 <= ballRadius) :
    actualGPrimeSurvivorSeparationRadius ballRadius <= ballRadius := by
  unfold actualGPrimeSurvivorSeparationRadius
  linarith

/-- Before any synchronization or sharing cap, the literal native pre-max
pair mass costs only the square of its actual dyadic degree upper endpoint. -/
theorem nativeHighPreMaxFirstHitCenterPairMass_le_degreeUpper_sq_mul_labelMass
    {radius : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    (D : NativeBranchCore radius iota) (G : NativeHighGeometry D)
    (c : D.HighCenter) :
    nativeHighPreMaxFirstHitCenterPairMass D G c <=
      (((pyzE2DegreeUpper
          (D.chosenHighPayloadAt c).payload.finalLabel *
        pyzE2DegreeUpper
          (D.chosenHighPayloadAt c).payload.finalLabel : Nat) : ENNReal) *
        nativeHighPreMaxFirstHitLabelMass D G c) := by
  let H := D.chosenHighPayloadAt c
  let N := positiveCenterHighPayloadGlobalNormData H
  have hball : 0 <= G.ballRadius c :=
    N.delta_pos.le.trans (G.hballRadiusLower c)
  rw [nativeHighPreMaxFirstHitCenterPairMass_eq_labelFirst]
  calc
    _ <= actualGPrimeWeightedFineSeparatedPairMass
        N
        (let E_t := positiveCenterTangencyCell (D.highBase c) D.S.family
            D.physical D.f D.f1 D.f2 D.outerA D.outerB D.hOuter D.hf D.hf1
              D.globalScale c.1.1 D.tangencyExponent H.payload.tangencyLabel
         let hEt : MeasurableSet E_t := measurableSet_positiveCenterTangencyCell
            (D.highBase c) (D.highBase_measurable c) D.S.family D.physical
              D.f D.f1 D.f2 D.outerA D.outerB D.hOuter D.hf D.hf1
                D.globalScale c.1.1 D.tangencyExponent
                  H.payload.tangencyLabel
         actualCenteredHalfPaperFineE2SpatialIncidenceData E_t hEt D.S.family
            D.physical H.payload.finalLabel (G.mesh c) D.f D.f1 D.f2 D.outerA
              D.outerB D.hOuter D.hf D.hf1 D.globalScale
                (dyadicCeilUpper H.payload.tangencyLabel) c.1.1
                  (36 * D.globalScale) D.tangencyExponent)
        (fun _ _ => True)
        (actualGPrimeSurvivorSeparationRadius (G.ballRadius c))
        (let E_t := positiveCenterTangencyCell (D.highBase c) D.S.family
            D.physical D.f D.f1 D.f2 D.outerA D.outerB D.hOuter D.hf D.hf1
              D.globalScale c.1.1 D.tangencyExponent H.payload.tangencyLabel
         let hEt : MeasurableSet E_t := measurableSet_positiveCenterTangencyCell
            (D.highBase c) (D.highBase_measurable c) D.S.family D.physical
              D.f D.f1 D.f2 D.outerA D.outerB D.hOuter D.hf D.hf1
                D.globalScale c.1.1 D.tangencyExponent
                  H.payload.tangencyLabel
         let R := actualCenteredHalfPaperFineE2SpatialIncidenceData E_t hEt
            D.S.family D.physical H.payload.finalLabel (G.mesh c) D.f D.f1 D.f2
              D.outerA D.outerB D.hOuter D.hf D.hf1 D.globalScale
                (dyadicCeilUpper H.payload.tangencyLabel) c.1.1
                  (36 * D.globalScale) D.tangencyExponent
         actualGPrimeE2FirstHitLabelWeight R H.payload.finalLabel) := by
      apply actualGPrimeWeightedFineSeparatedPairMass_anti_ballRadius
      exact actualGPrimeSurvivorSeparationRadius_le hball
    _ <= _ := by
      simpa only [H, N] using
        nativeHighWeightedFineSeparatedPairMass_le_degreeUpper_sq_mul_labelMass
          D G c

/-- Elementary numerical cancellation: a half-room degree gap absorbs both
dyadic degree-upper factors up to the constant eight. -/
theorem degreeUpper_sq_le_eight_mul_degreeGap_of_halfRoom
    (label : Int) (nearCap : Nat)
    (hhalfRoom : 2 * nearCap <= pyzE2DegreeLower label) :
    pyzE2DegreeUpper label * pyzE2DegreeUpper label <=
      8 * (pyzE2DegreeLower label *
        (pyzE2DegreeLower label - nearCap)) := by
  let lower := pyzE2DegreeLower label
  let upper := pyzE2DegreeUpper label
  have hupper : upper <= 2 * lower := by
    exact pyzE2DegreeUpper_le_two_mul_lower label
  have hgap : lower <= 2 * (lower - nearCap) := by
    dsimp only [lower] at hhalfRoom ⊢
    omega
  calc
    upper * upper <= (2 * lower) * (2 * lower) :=
      Nat.mul_le_mul hupper hupper
    _ = 4 * (lower * lower) := by ring
    _ <= 8 * (lower * (lower - nearCap)) := by
      nlinarith [Nat.mul_le_mul_left (4 * lower) hgap]

/-- The exact degree-gap-normalized first-hit pair mass is constant-loss at
every centre with half-room. -/
theorem normalizedCenterPairMass_le_eight_mul_labelMass_of_halfRoom
    {radius : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    (D : NativeBranchCore radius iota) (G : NativeHighGeometry D)
    (c : D.HighCenter)
    (hhalfRoom :
      2 * automaticCanonicalNearCap
          (positiveCenterHighPayloadGlobalNormData
            (D.chosenHighPayloadAt c)) (G.ballRadius c) <=
        pyzE2DegreeLower
          (D.chosenHighPayloadAt c).payload.finalLabel) :
    nativeHighPreMaxFirstHitCenterPairMass D G c /
        nativeHighConcreteDegreeGap D G c <=
      8 * nativeHighPreMaxFirstHitLabelMass D G c := by
  apply (ENNReal.div_le_iff
    (nativeHighConcreteDegreeGap_ne_zero D G c)
    (nativeHighConcreteDegreeGap_ne_top D G c)).2
  have hpre :=
    nativeHighPreMaxFirstHitCenterPairMass_le_degreeUpper_sq_mul_labelMass
      D G c
  have hscalarNat := degreeUpper_sq_le_eight_mul_degreeGap_of_halfRoom
    (D.chosenHighPayloadAt c).payload.finalLabel
    (automaticCanonicalNearCap
      (positiveCenterHighPayloadGlobalNormData
        (D.chosenHighPayloadAt c)) (G.ballRadius c)) hhalfRoom
  have hscalar :
      ((pyzE2DegreeUpper
          (D.chosenHighPayloadAt c).payload.finalLabel *
        pyzE2DegreeUpper
          (D.chosenHighPayloadAt c).payload.finalLabel : Nat) : ENNReal) <=
        8 * nativeHighConcreteDegreeGap D G c := by
    unfold nativeHighConcreteDegreeGap
    exact_mod_cast hscalarNat
  calc
    nativeHighPreMaxFirstHitCenterPairMass D G c <=
        (((pyzE2DegreeUpper
            (D.chosenHighPayloadAt c).payload.finalLabel *
          pyzE2DegreeUpper
            (D.chosenHighPayloadAt c).payload.finalLabel : Nat) : ENNReal) *
          nativeHighPreMaxFirstHitLabelMass D G c) := hpre
    _ <= (8 * nativeHighConcreteDegreeGap D G c) *
          nativeHighPreMaxFirstHitLabelMass D G c :=
      mul_le_mul' hscalar le_rfl
    _ = (8 * nativeHighPreMaxFirstHitLabelMass D G c) *
          nativeHighConcreteDegreeGap D G c := by ring

/-- Centres with a genuine fractional reserve in the degree subtraction. -/
noncomputable def nativeHighHalfRoomCenters
    {radius : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    (D : NativeBranchCore radius iota) (G : NativeHighGeometry D) :
    Finset D.HighCenter :=
  Finset.univ.filter fun c =>
    2 * automaticCanonicalNearCap
        (positiveCenterHighPayloadGlobalNormData (D.chosenHighPayloadAt c))
          (G.ballRadius c) <=
      pyzE2DegreeLower (D.chosenHighPayloadAt c).payload.finalLabel

/-- The complementary centres, where the canonical near cap is comparable
to the selected dyadic degree. -/
noncomputable def nativeHighNearSaturatedCenters
    {radius : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    (D : NativeBranchCore radius iota) (G : NativeHighGeometry D) :
    Finset D.HighCenter :=
  Finset.univ.filter fun c =>
    ¬2 * automaticCanonicalNearCap
        (positiveCenterHighPayloadGlobalNormData (D.chosenHighPayloadAt c))
          (G.ballRadius c) <=
      pyzE2DegreeLower (D.chosenHighPayloadAt c).payload.finalLabel

noncomputable def nativeHighHalfRoomMass
    {radius : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    (D : NativeBranchCore radius iota) (G : NativeHighGeometry D) : ENNReal :=
  ∑ c ∈ nativeHighHalfRoomCenters D G, volume (D.highBase c)

noncomputable def nativeHighNearSaturatedMass
    {radius : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    (D : NativeBranchCore radius iota) (G : NativeHighGeometry D) : ENNReal :=
  ∑ c ∈ nativeHighNearSaturatedCenters D G, volume (D.highBase c)

theorem nativeHighHalfRoomMass_add_nearSaturatedMass
    {radius : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    (D : NativeBranchCore radius iota) (G : NativeHighGeometry D) :
    nativeHighHalfRoomMass D G + nativeHighNearSaturatedMass D G =
      ∑ c : D.HighCenter, volume (D.highBase c) := by
  classical
  simpa [nativeHighHalfRoomMass, nativeHighNearSaturatedMass,
    nativeHighHalfRoomCenters, nativeHighNearSaturatedCenters] using
      (Finset.sum_filter_add_sum_filter_not (Finset.univ : Finset D.HighCenter)
        (fun c =>
          2 * automaticCanonicalNearCap
              (positiveCenterHighPayloadGlobalNormData
                (D.chosenHighPayloadAt c)) (G.ballRadius c) <=
            pyzE2DegreeLower
              (D.chosenHighPayloadAt c).payload.finalLabel)
        (fun c => volume (D.highBase c)))

theorem nativeHighNearSaturated_degree_lt_two_mul_nearCap
    {radius : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    (D : NativeBranchCore radius iota) (G : NativeHighGeometry D)
    {c : D.HighCenter} (hc : c ∈ nativeHighNearSaturatedCenters D G) :
    pyzE2DegreeLower (D.chosenHighPayloadAt c).payload.finalLabel <
      2 * automaticCanonicalNearCap
        (positiveCenterHighPayloadGlobalNormData (D.chosenHighPayloadAt c))
          (G.ballRadius c) := by
  have hnot := (Finset.mem_filter.mp hc).2
  omega

/-- Any high-half splits automatically into a half-room quarter or a genuine
near-saturated quarter. -/
theorem sourceMass_quarter_le_halfRoomMass_or_nearSaturatedMass
    {radius : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    (D : NativeBranchCore radius iota) (G : NativeHighGeometry D)
    (hhalf : D.sourceMass / 2 <=
      ∑ c ∈ D.high, volume (D.cell c.1)) :
    D.sourceMass / 4 <= nativeHighHalfRoomMass D G ∨
      D.sourceMass / 4 <= nativeHighNearSaturatedMass D G := by
  have hbaseSum :
      (∑ c : D.HighCenter, volume (D.highBase c)) =
        ∑ c ∈ D.high, volume (D.cell c.1) := by
    simpa only [NativeBranchCore.highBase,
      NativeBranchCore.positiveBase, Finset.univ_eq_attach] using
        Finset.sum_attach D.high (fun c => volume (D.cell c.1))
  have htotal : D.sourceMass / 2 <=
      nativeHighHalfRoomMass D G + nativeHighNearSaturatedMass D G := by
    calc
      D.sourceMass / 2 <= ∑ c : D.HighCenter, volume (D.highBase c) :=
        hhalf.trans_eq hbaseSum.symm
      _ = nativeHighHalfRoomMass D G +
          nativeHighNearSaturatedMass D G :=
        (nativeHighHalfRoomMass_add_nearSaturatedMass D G).symm
  rcases le_total (nativeHighHalfRoomMass D G)
      (nativeHighNearSaturatedMass D G) with hle | hle
  · right
    apply (ENNReal.div_le_iff (by norm_num) (by norm_num)).2
    have hs : D.sourceMass / 2 <=
        nativeHighNearSaturatedMass D G +
          nativeHighNearSaturatedMass D G :=
      htotal.trans (add_le_add hle le_rfl)
    have hs' := (ENNReal.div_le_iff (by norm_num) (by norm_num)).1 hs
    calc
      D.sourceMass <=
          (nativeHighNearSaturatedMass D G +
            nativeHighNearSaturatedMass D G) * 2 := hs'
      _ = nativeHighNearSaturatedMass D G * 4 := by ring
  · left
    apply (ENNReal.div_le_iff (by norm_num) (by norm_num)).2
    have hs : D.sourceMass / 2 <=
        nativeHighHalfRoomMass D G + nativeHighHalfRoomMass D G :=
      htotal.trans (add_le_add le_rfl hle)
    have hs' := (ENNReal.div_le_iff (by norm_num) (by norm_num)).1 hs
    calc
      D.sourceMass <=
          (nativeHighHalfRoomMass D G +
            nativeHighHalfRoomMass D G) * 2 := hs'
      _ = nativeHighHalfRoomMass D G * 4 := by ring

/-- If the half-room side carries a quarter of the source, all exact
first-hit/fine-label cancellation closes with constant eight. -/
theorem sourceMass_quarter_le_eight_binLoss_mul_sourceMass_of_halfRoom
    {radius : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    (D : NativeBranchCore radius iota) (G : NativeHighGeometry D)
    (hhalf : D.sourceMass / 2 <=
      ∑ c ∈ D.high, volume (D.cell c.1))
    (hroomQuarter : D.sourceMass / 4 <= nativeHighHalfRoomMass D G) :
    D.sourceMass / 4 <=
      (actualAllCenterPostNormBinLoss radius D.globalScale
          D.physical.ambient.card * 8) * D.sourceMass := by
  classical
  let hout := nativeHighConcreteQPOutcome_of_half D G hhalf
  let binLoss := actualAllCenterPostNormBinLoss radius D.globalScale
    D.physical.ambient.card
  calc
    D.sourceMass / 4 <= nativeHighHalfRoomMass D G := hroomQuarter
    _ <= ∑ c ∈ nativeHighHalfRoomCenters D G,
        binLoss * (nativeHighPreMaxFirstHitCenterPairMass D G c /
          nativeHighConcreteDegreeGap D G c) := by
      unfold nativeHighHalfRoomMass
      apply Finset.sum_le_sum
      intro c _hc
      exact highBase_le_binLoss_mul_normalizedCenterPairMass D G c
        (nativeHighConcreteQPLocalAt hout c)
    _ <= ∑ c ∈ nativeHighHalfRoomCenters D G,
        binLoss * (8 * nativeHighPreMaxFirstHitLabelMass D G c) := by
      apply Finset.sum_le_sum
      intro c hc
      exact mul_le_mul' le_rfl
        (normalizedCenterPairMass_le_eight_mul_labelMass_of_halfRoom D G c
          (Finset.mem_filter.mp hc).2)
    _ = (binLoss * 8) *
        ∑ c ∈ nativeHighHalfRoomCenters D G,
          nativeHighPreMaxFirstHitLabelMass D G c := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro c _hc
      ring
    _ <= (binLoss * 8) * nativeHighPreMaxFirstHitLabelMassBudget G := by
      exact mul_le_mul' le_rfl (by
        unfold nativeHighPreMaxFirstHitLabelMassBudget
        exact Finset.sum_le_sum_of_subset (Finset.subset_univ _))
    _ <= (binLoss * 8) * D.sourceMass := by
      exact mul_le_mul' le_rfl
        (NativeHighConcreteQPOutcome.preMaxFirstHitLabelMassBudget_le_sourceMass
          hout)

/-- Fully automatic no-callback endpoint: either the normalized native-high
coefficient is constant eight, or a quarter of the source lies on centres
whose canonical near cap is at least half the selected degree. -/
theorem sourceMass_quarter_le_eight_binLoss_mul_sourceMass_or_nearSaturated
    {radius : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    (D : NativeBranchCore radius iota) (G : NativeHighGeometry D)
    (hhalf : D.sourceMass / 2 <=
      ∑ c ∈ D.high, volume (D.cell c.1)) :
    D.sourceMass / 4 <=
        (actualAllCenterPostNormBinLoss radius D.globalScale
          D.physical.ambient.card * 8) * D.sourceMass ∨
      D.sourceMass / 4 <= nativeHighNearSaturatedMass D G := by
  rcases sourceMass_quarter_le_halfRoomMass_or_nearSaturatedMass D G hhalf with
    hroom | hsaturated
  · exact Or.inl
      (sourceMass_quarter_le_eight_binLoss_mul_sourceMass_of_halfRoom
        D G hhalf hroom)
  · exact Or.inr hsaturated

#print axioms actualGPrimeFineSeparatedPairsAt_anti_ballRadius
#print axioms actualGPrimeWeightedFineSeparatedPairMass_anti_ballRadius
#print axioms nativeHighPreMaxFirstHitCenterPairMass_le_degreeUpper_sq_mul_labelMass
#print axioms degreeUpper_sq_le_eight_mul_degreeGap_of_halfRoom
#print axioms normalizedCenterPairMass_le_eight_mul_labelMass_of_halfRoom
#print axioms nativeHighHalfRoomMass_add_nearSaturatedMass
#print axioms nativeHighNearSaturated_degree_lt_two_mul_nearCap
#print axioms sourceMass_quarter_le_halfRoomMass_or_nearSaturatedMass
#print axioms sourceMass_quarter_le_eight_binLoss_mul_sourceMass_of_halfRoom
#print axioms sourceMass_quarter_le_eight_binLoss_mul_sourceMass_or_nearSaturated

end

end Family8Family7NativeHighFineLabelRoomSplitV1
