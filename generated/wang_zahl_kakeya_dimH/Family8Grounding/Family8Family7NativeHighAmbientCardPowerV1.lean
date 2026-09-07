import Family8Grounding.Family8Family7NativeHighDyadicPairMassSumV1
import FamilyStickyGrounding.FamilyStickyPyzActualPositiveCenterHighPairCarrierV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8Family7NativeHighAmbientCardPowerV1

open FamilyStickyCinematicL32ContinuumCriticalSingleDyadicSelectionV1
open FamilyStickyCinematicL32ContinuumActualCriticalScaleMapV1
open FamilyStickyCinematicL32FiniteMetricMaximalCoverV1
open FamilyStickyCinematicL32FiniteNormCriticalBallV1
open FamilyStickyCinematicL32FiniteProjectedShadingMultiplicitySliceV1
open FamilyStickyCinematicL32Lemma57DyadicCeilBucketV1
open FamilyStickyCinematicL32Prop41ActualGPrimeCanonicalSharingCapV3
open FamilyStickyCinematicL32Prop41ActualGPrimeDegreeRichMassProducerV1
open FamilyStickyCinematicL32Prop41ActualPositiveCenterHighPayloadWeightedFullyActualConnectorV1
open FamilyStickyCinematicL32Prop41CanonicalMaximizerNonconcentrationV1
open FamilyStickyCinematicL32PyzActualAllCenterCanonicalPayloadFinalV5
open FamilyStickyCinematicL32PyzActualAllCenterBinUniformityV1
open FamilyStickyCinematicL32PyzActualNormFirstAllCenterMassWeightedBranchTypesV5C
open FamilyStickyCinematicL32PyzE2DyadicDegreeWindowV1
open FamilyStickyPyzActualPositiveCenterHighPairCarrierV1
open Family8Family7NativeHighDyadicPairMassSumV1

noncomputable section

universe u

/-!
# Ambient-card envelope for the native-high Family 7 loss

The literal high-branch geometry already says that the canonical radius-`R`
sharing cap is smaller than the selected `E₂` degree.  The selected degree,
in turn, is at most twice the cardinality of the literal active fibre and
hence at most twice the retained ambient cardinality.  This file records that
chain without inserting a small-power callback.

The remaining post-normalization bin factor is deliberately left exact.  A
radius-power estimate therefore still needs a genuine upstream packing bound
for the retained ambient family.
-/

/-- The radius-`R` sharing ceiling is no larger than the radius-`10R`
near-pair ceiling used by the high-room hypothesis. -/
theorem automaticCanonicalCenterSharingNatCap_le_nearCap
    {iota : Type u} [DecidableEq iota]
    (N : CanonicalNormNonconcentrationData iota) {ballRadius : Real}
    (hballRadiusLower : N.delta <= ballRadius) :
    automaticCanonicalCenterSharingNatCap N ballRadius <=
      automaticCanonicalNearCap N ballRadius := by
  have hballRadiusPos : 0 < ballRadius := N.delta_pos.trans_le hballRadiusLower
  have hcriticalScaleLower : N.delta <= N.criticalScale := by
    exact (finiteCriticalMaximizerScale_bounds N.family N.distance
      N.family_nonempty N.delta_le_ceiling).1
  have hcriticalScalePos : 0 < N.criticalScale :=
    N.delta_pos.trans_le hcriticalScaleLower
  have hratioNonneg : 0 <= ballRadius / N.criticalScale := by positivity
  have hratioLe : ballRadius / N.criticalScale <=
      (10 * ballRadius) / N.criticalScale := by
    apply (div_le_div_iff_of_pos_right hcriticalScalePos).2
    nlinarith
  have hrpow :
      (ballRadius / N.criticalScale) ^ N.exponent <=
        ((10 * ballRadius) / N.criticalScale) ^ N.exponent := by
    exact Real.rpow_le_rpow hratioNonneg hratioLe N.exponent_nonneg
  unfold automaticCanonicalCenterSharingNatCap automaticCanonicalNearCap
  apply Nat.ceil_mono
  exact mul_le_mul_of_nonneg_right hrpow (by positivity)

/-- At every literal high centre, the canonical sharing cap is bounded by
the selected dyadic degree upper endpoint. -/
theorem nativeHigh_sharingCap_le_degreeUpper
    {radius : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    (D : NativeBranchCore radius iota) (G : NativeHighGeometry D)
    (c : D.HighCenter) :
    automaticCanonicalCenterSharingNatCap
        (positiveCenterHighPayloadGlobalNormData (D.chosenHighPayloadAt c))
        (G.ballRadius c) <=
      pyzE2DegreeUpper (D.chosenHighPayloadAt c).payload.finalLabel := by
  let H := D.chosenHighPayloadAt c
  let N := positiveCenterHighPayloadGlobalNormData H
  have hshareNear : automaticCanonicalCenterSharingNatCap N
      (G.ballRadius c) <= automaticCanonicalNearCap N (G.ballRadius c) := by
    exact automaticCanonicalCenterSharingNatCap_le_nearCap N
      (G.hballRadiusLower c)
  have hnearLower : automaticCanonicalNearCap N (G.ballRadius c) <
      pyzE2DegreeLower H.payload.finalLabel := by
    simpa only [H, N] using G.hroom c
  have hlowerUpper : pyzE2DegreeLower H.payload.finalLabel <=
      pyzE2DegreeUpper H.payload.finalLabel := by
    unfold pyzE2DegreeLower pyzE2DegreeUpper
    apply Nat.ceil_mono
    have hupperPos : 0 < dyadicCeilUpper H.payload.finalLabel :=
      Real.rpow_pos_of_pos (by norm_num) _
    linarith
  exact (hshareNear.trans hnearLower.le).trans hlowerUpper

/-- The selected dyadic degree is at most twice the retained ambient
cardinality. -/
theorem nativeHigh_degreeUpper_le_two_mul_ambientCard
    {radius : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    (D : NativeBranchCore radius iota) (c : D.HighCenter) :
    pyzE2DegreeUpper (D.chosenHighPayloadAt c).payload.finalLabel <=
      2 * D.physical.ambient.card := by
  let H := D.chosenHighPayloadAt c
  let Y1 := positiveCenterY1 (D.highBase c) (D.highBase_measurable c)
    D.S.family D.physical D.f D.f1 D.f2 D.outerA D.outerB D.hOuter D.hf
    D.hf1 D.globalScale c.1.1 D.tangencyExponent H.payload.tangencyLabel
  have hlowerActive : pyzE2DegreeLower H.payload.finalLabel <=
      (Y1.activeAtPoint H.payload.q).card := by
    simpa only [H, Y1] using
      degreeLower_le_payload_active_card volume (D.highBase c)
        (D.highBase_measurable c) D.S.family D.physical D.f D.f1 D.f2
        D.outerA D.outerB D.hOuter D.hf D.hf1 D.globalScale c.1.1
        D.tangencyExponent H.payload
  have hactiveAmbient : (Y1.activeAtPoint H.payload.q).card <=
      D.physical.ambient.card := by
    have hambientEq : Y1.ambient = D.physical.ambient := by
      dsimp only [Y1]
      exact actualProjectedCenteredHalfTangencyY1_ambient_eq
        (D.highBase c) (D.highBase_measurable c) D.S.family D.physical
        D.f D.f1 D.f2 D.outerA D.outerB D.hOuter D.hf D.hf1
        D.globalScale c.1.1 (36 * D.globalScale) D.tangencyExponent
        (dyadicCeilUpper H.payload.tangencyLabel)
    apply Finset.card_le_card
    intro i hi
    have hiY1 : i ∈ Y1.ambient := (Y1.mem_activeAtPoint H.payload.q i).mp hi |>.1
    exact hambientEq.le hiY1
  exact (pyzE2DegreeUpper_le_two_mul_lower H.payload.finalLabel).trans
    (Nat.mul_le_mul_left 2 (hlowerActive.trans hactiveAmbient))

/-- The complete local pair coefficient is bounded by the fourth power of
twice the actual retained ambient cardinality. -/
theorem nativeHighLocalDyadicPairLoss_le_ambientCardFourth
    {radius : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    (D : NativeBranchCore radius iota) (G : NativeHighGeometry D)
    (c : D.HighCenter) :
    nativeHighLocalDyadicPairLoss D G c <=
      648 * (((2 * D.physical.ambient.card) ^ 4 : Nat) : ENNReal) := by
  let H := D.chosenHighPayloadAt c
  let share := automaticCanonicalCenterSharingNatCap
    (positiveCenterHighPayloadGlobalNormData H) (G.ballRadius c)
  let degree := pyzE2DegreeUpper H.payload.finalLabel
  have hshare : share <= degree := by
    simpa only [H, share, degree] using nativeHigh_sharingCap_le_degreeUpper D G c
  have hdegree : degree <= 2 * D.physical.ambient.card := by
    simpa only [H, degree] using
      nativeHigh_degreeUpper_le_two_mul_ambientCard D c
  have hnat : share * share * (degree * degree) <=
      (2 * D.physical.ambient.card) ^ 4 := by
    calc
      share * share * (degree * degree) <=
          degree * degree * (degree * degree) :=
        Nat.mul_le_mul (Nat.mul_le_mul hshare hshare)
          (Nat.mul_le_mul le_rfl le_rfl)
      _ <= (2 * D.physical.ambient.card) *
          (2 * D.physical.ambient.card) *
            ((2 * D.physical.ambient.card) *
              (2 * D.physical.ambient.card)) :=
        Nat.mul_le_mul (Nat.mul_le_mul hdegree hdegree)
          (Nat.mul_le_mul hdegree hdegree)
      _ = (2 * D.physical.ambient.card) ^ 4 := by ring
  unfold nativeHighLocalDyadicPairLoss
  dsimp only [H, share, degree]
  apply mul_le_mul' le_rfl
  exact_mod_cast hnat

/-- The finite supremum over high centres obeys the same ambient-card
fourth-power envelope. -/
theorem nativeHighDyadicPairLossMax_le_ambientCardFourth
    {radius : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    (D : NativeBranchCore radius iota) (G : NativeHighGeometry D) :
    nativeHighDyadicPairLossMax D G <=
      648 * (((2 * D.physical.ambient.card) ^ 4 : Nat) : ENNReal) := by
  classical
  unfold nativeHighDyadicPairLossMax
  apply Finset.sup_le
  intro c hc
  exact nativeHighLocalDyadicPairLoss_le_ambientCardFourth D G c

/-- The exact scalar obstruction after native-high aggregation, now reduced
to the literal ambient cardinality and the one remaining dyadic-bin factor. -/
theorem postNormBinLoss_mul_nativeHighDyadicPairLossMax_le_ambientEnvelope
    {radius : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    (D : NativeBranchCore radius iota) (G : NativeHighGeometry D) :
    actualAllCenterPostNormBinLoss radius D.globalScale
        D.physical.ambient.card * nativeHighDyadicPairLossMax D G <=
      actualAllCenterPostNormBinLoss radius D.globalScale
          D.physical.ambient.card *
        (648 * (((2 * D.physical.ambient.card) ^ 4 : Nat) : ENNReal)) := by
  exact mul_le_mul' le_rfl
    (nativeHighDyadicPairLossMax_le_ambientCardFourth D G)

#print axioms automaticCanonicalCenterSharingNatCap_le_nearCap
#print axioms nativeHigh_sharingCap_le_degreeUpper
#print axioms nativeHigh_degreeUpper_le_two_mul_ambientCard
#print axioms nativeHighLocalDyadicPairLoss_le_ambientCardFourth
#print axioms nativeHighDyadicPairLossMax_le_ambientCardFourth
#print axioms postNormBinLoss_mul_nativeHighDyadicPairLossMax_le_ambientEnvelope

end
end Family8Family7NativeHighAmbientCardPowerV1
