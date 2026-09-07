import Family8Grounding.Family8OwnerFiberKatzTaoFromAmbientFrostmanV2
import Family8Grounding.Family8SelectedOccurrenceNormalizedOuterDatumV1
import Mathlib.Tactic

/-!
# Global-owner Equation (45) control for the normalized selected outer family

When the owner-fibre concentration bound is obtained from one global ambient
Frostman certificate, splitting the family into geometric owner fibres gives
no better `Delta`: the proof first obtains a global Katz--Tao estimate and
then restricts it to every owner fibre.  A constant `PUnit` owner therefore
gives the same coefficient and makes unique ownership tautological.

This is the deliberately weak Eq. (45) interface needed by the normalized
selected-occurrence route.  It uses no sticky-parent thickening containment,
no raw plank datum, and no memberwise or all-label callback.
-/

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8SelectedOccurrenceNormalizedGlobalOwnerEq45ControlV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
open Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
open Submission.Kakeya.Uniformity
open Family6AffineConvexVolumeCoreV1
open Family6AffinePlankAnalyticHypothesesStableV1
open Family8GreedyWinnerAutomaticJohnSideBucketV1
open Family8OwnerFiberKatzTaoFromAmbientFrostmanV2
open Family8SelectedOccurrenceDensityFrostmanV1
open Family8SelectedOccurrenceMaxOwnerHullCommonScaleDatumV1
open Family8SelectedOccurrenceNormalizedOuterDatumV1
open Family8SelectedParentAffineShadingTransportV4
open Family8SelectedParentJohnPlankSideWidthBridgeV7
open Family8SelectedParentJohnPlankSideWidthBridgeV8
open Family8UniqueOwnerLocalDeltaMaxThickControlV1

noncomputable section

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5000000

local instance (p : Prop) : Decidable p := Classical.propDecidable p

universe u

/-! ## Generic constant-owner route -/

/-- A global ambient Frostman estimate gives Family 6 thick-plank control
through the constant `PUnit` owner.  The coefficient inequality is kept in
its natural weak direction; no equality or canonical numerical choice is
required. -/
theorem frostmanThickenedPlankControl_of_globalAmbientFrostman
    {index : Type u} [Fintype index] [DecidableEq index]
    {a b Delta : NNReal}
    (D : ShadedConvexPlankFamily index a b)
    {CF A : ENNReal}
    (hF : IsFrostmanIn CF D.family D.ambient)
    (hbase : containedMass D.family D.ambient <=
      A * volume (D.ambient : Set Space))
    (hDelta : CF * A <= (Delta : ENNReal)) :
    FrostmanThickenedPlankControl D
      (uniqueOwnerLocalDeltaThickM
        D.comparisonConstant Delta a b) := by
  let owner : index -> Unit := fun _ => ()
  apply frostmanThickenedPlankControl_of_uniqueOwner_localDeltaMax D owner
  · intro _theta _hthetaLower _hthetaUpper _i _j _hj
    rfl
  · exact ownerFiberDeltaMax_le_of_ambientFrostman
      D owner hF hbase hDelta

/-! ## Exact selected-occurrence normalized outer specialization -/

variable {delta : NNReal} {iota : Type u}
  [Fintype iota] [DecidableEq iota]
  {fine : UniformTubeFamily delta iota}
  {active : Finset iota}

variable
  (P : GreedyDensityPartition fine.bodyFamily
    (hullCandidates active) (hullContainer fine.bodyFamily) active)

/-- The exact normalized selected outer datum inherits the constant-owner
global-Delta control from its raw ambient Frostman and ambient-mass bounds.
Both bounds are transported by the same scalar affine equivalence, so the
coefficient `A` and the inequality `CF * A <= Delta` are unchanged. -/
theorem selectedOccurrenceNormalizedOuter_frostmanThickenedPlankControl_of_globalAmbient
    (Y : Shading fine.bodyFamily)
    (hdelta : 0 < delta)
    (labelOuter : Fin 3 -> Int)
    (Rside : Finset (Fin (blocks fine.bodyFamily P).length))
    (hlabel : forall k, k ∈ Rside ->
      sideShapeLabel (winnerLongSide P hdelta k) = labelOuter)
    (ambient : ConvexBody Space)
    (ambientComparisonConstant : NNReal)
    (ambient_is_unit_scale : IsPlank ambientComparisonConstant 1 1
      (affineImageConvexBody
        (selectedOccurrenceNormalizedOuterAffineEquiv labelOuter) ambient))
    {CF A : ENNReal}
    (hF : IsFrostmanIn CF
      (selectedOccurrenceOuterFamily P Rside) ambient)
    (hbase : containedMass
        (selectedOccurrenceOuterFamily P Rside) ambient <=
      A * volume (ambient : Set Space))
    {Delta : NNReal}
    (hDelta : CF * A <= (Delta : ENNReal)) :
    FrostmanThickenedPlankControl
      (selectedOccurrenceNormalizedOuterDatum P Y hdelta labelOuter Rside
        hlabel ambient ambientComparisonConstant ambient_is_unit_scale
        hF.family_subset)
      (uniqueOwnerLocalDeltaThickM 576 Delta
        (bucketShortA labelOuter) (bucketShortB labelOuter)) := by
  let e := selectedOccurrenceNormalizedOuterAffineEquiv labelOuter
  let D := selectedOccurrenceNormalizedOuterDatum P Y hdelta labelOuter Rside
    hlabel ambient ambientComparisonConstant ambient_is_unit_scale
    hF.family_subset
  have hFNormalized : IsFrostmanIn CF
      (selectedOccurrenceNormalizedOuterFamily P labelOuter Rside)
      (affineImageConvexBody e ambient) := by
    simpa only [e] using
      (selectedOccurrenceNormalizedOuterFamily_isFrostmanIn
        P labelOuter Rside ambient hF)
  have hbaseNormalized :
      containedMass
          (selectedOccurrenceNormalizedOuterFamily P labelOuter Rside)
          (affineImageConvexBody e ambient) <=
        A * volume (affineImageConvexBody e ambient : Set Space) := by
    change containedMass
        (affineImageFamily e (selectedOccurrenceOuterFamily P Rside))
        (affineImageConvexBody e ambient) <=
      A * volume (affineImageConvexBody e ambient : Set Space)
    rw [containedMass_affineImageFamily,
      affinePreimageConvexBody_affineImageConvexBody,
      volume_affineImageConvexBody]
    calc
      affineJacobian e *
          containedMass (selectedOccurrenceOuterFamily P Rside) ambient <=
        affineJacobian e * (A * volume (ambient : Set Space)) :=
          mul_le_mul' le_rfl hbase
      _ = A * (affineJacobian e * volume (ambient : Set Space)) := by
        ac_rfl
  exact frostmanThickenedPlankControl_of_globalAmbientFrostman
    D hFNormalized hbaseNormalized hDelta

#print axioms frostmanThickenedPlankControl_of_globalAmbientFrostman
#print axioms
  selectedOccurrenceNormalizedOuter_frostmanThickenedPlankControl_of_globalAmbient

end

end Family8SelectedOccurrenceNormalizedGlobalOwnerEq45ControlV1
