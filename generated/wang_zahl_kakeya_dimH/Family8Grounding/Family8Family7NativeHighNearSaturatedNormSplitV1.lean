import Family8Grounding.Family8Family7NativeHighFineLabelRoomSplitV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8Family7NativeHighNearSaturatedNormSplitV1

open FamilyStickyCinematicL32ContinuumActualCriticalScaleMapV1
open FamilyStickyCinematicL32Prop41ActualGPrimeDegreeRichMassProducerV1
open FamilyStickyCinematicL32Prop41ActualPositiveCenterHighPayloadWeightedFullyActualConnectorV1
open FamilyStickyCinematicL32Prop41CanonicalMaximizerNonconcentrationV1
open FamilyStickyCinematicL32PyzActualAllCenterBinUniformityV1
open FamilyStickyCinematicL32PyzActualNormFirstAllCenterMassWeightedBranchTypesV5C
open Family8Family7NativeHighFineLabelRoomSplitV1

noncomputable section

universe u

/-!
# The genuine canonical-norm split inside the near-saturated high branch

For a near-saturated high centre, the high-degree threshold forces the
canonical near-cap above `12 * logCount`.  Expanding the canonical ceiling
then gives a lower bound for the actual maximizer ball, weighted at radius
`10 * ballRadius`.

There are only two ways this can happen:

* the canonical critical scale is already below `10 * ballRadius`, which is
  the honest scale-restart branch; or
* the scale ratio is at most one, in which case the literal critical ball has
  more than `12 * logCount` members.

This file records that split before any induction or rescaling theorem is
inserted.  It has no conclusion-valued callback.
-/

/-- The strict high threshold and near saturation force a logarithmically
large canonical near cap. -/
theorem nativeHighNearSaturated_nearCap_gt_twelve_logCount
    {radius : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    (D : NativeBranchCore radius iota) (G : NativeHighGeometry D)
    {c : D.HighCenter} (hc : c ∈ nativeHighNearSaturatedCenters D G) :
    12 * D.logCount <
      automaticCanonicalNearCap
        (positiveCenterHighPayloadGlobalNormData (D.chosenHighPayloadAt c))
          (G.ballRadius c) := by
  have hhigh := (D.chosenHighPayloadAt c).high
  have hsaturated :=
    nativeHighNearSaturated_degree_lt_two_mul_nearCap D G hc
  omega

/-- Ceiling elimination exposes the actual weighted critical-ball quantity
which is large on every near-saturated centre. -/
theorem nativeHighNearSaturated_weightedCriticalBall_gt_twelve_logCount
    {radius : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    (D : NativeBranchCore radius iota) (G : NativeHighGeometry D)
    {c : D.HighCenter} (hc : c ∈ nativeHighNearSaturatedCenters D G) :
    ((12 * D.logCount : Nat) : Real) <
      (((10 * G.ballRadius c) /
          (positiveCenterHighPayloadGlobalNormData
            (D.chosenHighPayloadAt c)).criticalScale) ^
        (positiveCenterHighPayloadGlobalNormData
          (D.chosenHighPayloadAt c)).exponent *
        (((positiveCenterHighPayloadGlobalNormData
          (D.chosenHighPayloadAt c)).criticalBall.card : Nat) : Real)) := by
  have hcap :=
    nativeHighNearSaturated_nearCap_gt_twelve_logCount D G hc
  unfold automaticCanonicalNearCap at hcap
  exact Nat.lt_ceil.mp hcap

/-- Near-saturated centres whose selected critical norm scale is already
below the separation scale. -/
noncomputable def nativeHighNearSaturatedScaleRestartCenters
    {radius : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    (D : NativeBranchCore radius iota) (G : NativeHighGeometry D) :
    Finset D.HighCenter :=
  (nativeHighNearSaturatedCenters D G).filter fun c =>
    (positiveCenterHighPayloadGlobalNormData
      (D.chosenHighPayloadAt c)).criticalScale < 10 * G.ballRadius c

/-- The complementary near-saturated centres.  On these centres the scale
ratio in the canonical near cap is at most one. -/
noncomputable def nativeHighNearSaturatedCriticalBallRichCenters
    {radius : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    (D : NativeBranchCore radius iota) (G : NativeHighGeometry D) :
    Finset D.HighCenter :=
  (nativeHighNearSaturatedCenters D G).filter fun c =>
    ¬(positiveCenterHighPayloadGlobalNormData
      (D.chosenHighPayloadAt c)).criticalScale < 10 * G.ballRadius c

noncomputable def nativeHighNearSaturatedScaleRestartMass
    {radius : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    (D : NativeBranchCore radius iota) (G : NativeHighGeometry D) : ENNReal :=
  ∑ c ∈ nativeHighNearSaturatedScaleRestartCenters D G,
    volume (D.highBase c)

noncomputable def nativeHighNearSaturatedCriticalBallRichMass
    {radius : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    (D : NativeBranchCore radius iota) (G : NativeHighGeometry D) : ENNReal :=
  ∑ c ∈ nativeHighNearSaturatedCriticalBallRichCenters D G,
    volume (D.highBase c)

/-- On the complementary scale branch, the literal canonical critical ball
has more than `12 * logCount` actual indices. -/
theorem nativeHighNearSaturatedCriticalBallRich_card_gt_twelve_logCount
    {radius : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    (D : NativeBranchCore radius iota) (G : NativeHighGeometry D)
    {c : D.HighCenter}
    (hc : c ∈ nativeHighNearSaturatedCriticalBallRichCenters D G) :
    12 * D.logCount <
      (positiveCenterHighPayloadGlobalNormData
        (D.chosenHighPayloadAt c)).criticalBall.card := by
  let N := positiveCenterHighPayloadGlobalNormData (D.chosenHighPayloadAt c)
  have hcData := Finset.mem_filter.mp hc
  have hweighted : ((12 * D.logCount : Nat) : Real) <
      ((10 * G.ballRadius c) / N.criticalScale) ^ N.exponent *
        ((N.criticalBall.card : Nat) : Real) := by
    simpa only [N] using
      nativeHighNearSaturated_weightedCriticalBall_gt_twelve_logCount
        D G hcData.1
  have htenLe : 10 * G.ballRadius c <= N.criticalScale := by
    simpa only [N] using le_of_not_gt hcData.2
  have hcriticalScaleLower : N.delta <= N.criticalScale := by
    exact (finiteCriticalMaximizerScale_bounds N.family N.distance
      N.family_nonempty N.delta_le_ceiling).1
  have hcriticalScalePos : 0 < N.criticalScale :=
    N.delta_pos.trans_le hcriticalScaleLower
  have hballRadiusPos : 0 < G.ballRadius c :=
    N.delta_pos.trans_le (by simpa only [N] using G.hballRadiusLower c)
  have hratioNonneg : 0 <= (10 * G.ballRadius c) / N.criticalScale := by
    positivity
  have hratioLeOne :
      (10 * G.ballRadius c) / N.criticalScale <= 1 :=
    (div_le_one hcriticalScalePos).2 htenLe
  have hrpowLeOne :
      ((10 * G.ballRadius c) / N.criticalScale) ^ N.exponent <= 1 :=
    Real.rpow_le_one hratioNonneg hratioLeOne N.exponent_nonneg
  have hweightedLe :
      ((10 * G.ballRadius c) / N.criticalScale) ^ N.exponent *
          ((N.criticalBall.card : Nat) : Real) <=
        ((N.criticalBall.card : Nat) : Real) := by
    calc
      _ <= 1 * ((N.criticalBall.card : Nat) : Real) :=
        mul_le_mul_of_nonneg_right hrpowLeOne (by positivity)
      _ = _ := one_mul _
  have hcardReal : ((12 * D.logCount : Nat) : Real) <
      ((N.criticalBall.card : Nat) : Real) :=
    hweighted.trans_le hweightedLe
  exact_mod_cast hcardReal

/-- The two canonical-norm subbranches exactly partition the unresolved
near-saturated mass. -/
theorem nativeHighNearSaturatedScaleRestartMass_add_criticalBallRichMass
    {radius : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    (D : NativeBranchCore radius iota) (G : NativeHighGeometry D) :
    nativeHighNearSaturatedScaleRestartMass D G +
        nativeHighNearSaturatedCriticalBallRichMass D G =
      nativeHighNearSaturatedMass D G := by
  classical
  unfold nativeHighNearSaturatedScaleRestartMass
    nativeHighNearSaturatedCriticalBallRichMass
    nativeHighNearSaturatedScaleRestartCenters
    nativeHighNearSaturatedCriticalBallRichCenters
    nativeHighNearSaturatedMass
  simpa using
    (Finset.sum_filter_add_sum_filter_not
      (nativeHighNearSaturatedCenters D G)
      (fun c =>
        (positiveCenterHighPayloadGlobalNormData
          (D.chosenHighPayloadAt c)).criticalScale < 10 * G.ballRadius c)
      (fun c => volume (D.highBase c)))

/-- If the near-saturated side carries a quarter of the source, one of its
two genuine norm subbranches carries an eighth. -/
theorem sourceMass_eighth_le_scaleRestartMass_or_criticalBallRichMass
    {radius : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    (D : NativeBranchCore radius iota) (G : NativeHighGeometry D)
    (hnear : D.sourceMass / 4 <= nativeHighNearSaturatedMass D G) :
    D.sourceMass / 8 <= nativeHighNearSaturatedScaleRestartMass D G ∨
      D.sourceMass / 8 <=
        nativeHighNearSaturatedCriticalBallRichMass D G := by
  have hsum : D.sourceMass / 4 <=
      nativeHighNearSaturatedScaleRestartMass D G +
        nativeHighNearSaturatedCriticalBallRichMass D G := by
    rw [nativeHighNearSaturatedScaleRestartMass_add_criticalBallRichMass]
    exact hnear
  rcases le_total (nativeHighNearSaturatedScaleRestartMass D G)
      (nativeHighNearSaturatedCriticalBallRichMass D G) with hle | hle
  · right
    apply (ENNReal.div_le_iff (by norm_num) (by norm_num)).2
    have hs : D.sourceMass / 4 <=
        nativeHighNearSaturatedCriticalBallRichMass D G +
          nativeHighNearSaturatedCriticalBallRichMass D G :=
      hsum.trans (add_le_add hle le_rfl)
    have hs' := (ENNReal.div_le_iff (by norm_num) (by norm_num)).1 hs
    calc
      D.sourceMass <=
          (nativeHighNearSaturatedCriticalBallRichMass D G +
            nativeHighNearSaturatedCriticalBallRichMass D G) * 4 := hs'
      _ = nativeHighNearSaturatedCriticalBallRichMass D G * 8 := by ring
  · left
    apply (ENNReal.div_le_iff (by norm_num) (by norm_num)).2
    have hs : D.sourceMass / 4 <=
        nativeHighNearSaturatedScaleRestartMass D G +
          nativeHighNearSaturatedScaleRestartMass D G :=
      hsum.trans (add_le_add le_rfl hle)
    have hs' := (ENNReal.div_le_iff (by norm_num) (by norm_num)).1 hs
    calc
      D.sourceMass <=
          (nativeHighNearSaturatedScaleRestartMass D G +
            nativeHighNearSaturatedScaleRestartMass D G) * 4 := hs'
      _ = nativeHighNearSaturatedScaleRestartMass D G * 8 := by ring

/-- Callback-free three-way endpoint after fine-label cancellation.  The
only remaining nonconstant branches are now the actual critical-scale restart
and an actually rich canonical critical ball. -/
theorem sourceMass_nativeHigh_constant_or_scaleRestart_or_criticalBallRich
    {radius : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    (D : NativeBranchCore radius iota) (G : NativeHighGeometry D)
    (hhalf : D.sourceMass / 2 <=
      ∑ c ∈ D.high, volume (D.cell c.1)) :
    D.sourceMass / 4 <=
        (actualAllCenterPostNormBinLoss radius D.globalScale
          D.physical.ambient.card * 8) * D.sourceMass ∨
      D.sourceMass / 8 <=
          nativeHighNearSaturatedScaleRestartMass D G ∨
        D.sourceMass / 8 <=
          nativeHighNearSaturatedCriticalBallRichMass D G := by
  rcases sourceMass_quarter_le_eight_binLoss_mul_sourceMass_or_nearSaturated
      D G hhalf with hconstant | hnear
  · exact Or.inl hconstant
  · exact Or.inr
      (sourceMass_eighth_le_scaleRestartMass_or_criticalBallRichMass D G hnear)

#print axioms nativeHighNearSaturated_nearCap_gt_twelve_logCount
#print axioms nativeHighNearSaturated_weightedCriticalBall_gt_twelve_logCount
#print axioms nativeHighNearSaturatedCriticalBallRich_card_gt_twelve_logCount
#print axioms
  nativeHighNearSaturatedScaleRestartMass_add_criticalBallRichMass
#print axioms sourceMass_eighth_le_scaleRestartMass_or_criticalBallRichMass
#print axioms
  sourceMass_nativeHigh_constant_or_scaleRestart_or_criticalBallRich

end

end Family8Family7NativeHighNearSaturatedNormSplitV1
