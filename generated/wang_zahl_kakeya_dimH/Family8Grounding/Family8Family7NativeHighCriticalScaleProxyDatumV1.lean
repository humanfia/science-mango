import Family8Grounding.Family8Family7NativeHighCriticalScaleProxyGeometryV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

open Set MeasureTheory
open scoped ENNReal NNReal

namespace Family8Family7NativeHighCriticalScaleProxyDatumV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Family8Family7NativeHighCriticalBallDatumV1
open Family8Family7NativeHighCriticalBallRestrictedSourceV1
open Family8Family7NativeHighCriticalBallAffineProxyV1
open Family8Family7NativeHighCriticalScaleProxyGeometryV1
open Family8Family7NativeHighNearSaturatedNormSplitV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8SelectedParentAffineShadingTransportV4
open Family6AffineConvexVolumeCoreV1
open FamilyStickyCinematicL32Prop41ActualPositiveCenterHighPayloadWeightedFullyActualConnectorV1
open FamilyStickyCinematicL32PyzActualNormFirstAllCenterMassWeightedBranchTypesV5C

noncomputable section

universe u

/-!
# Consumer-ready critical-scale proxy datum

This packages the concrete geometry as the actual `WZL3` source and
mass-retaining `ActualTubeDatum` already expected by downstream consumers.
-/

theorem nativeHighCriticalScaleProxyGeometry
    {radius : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    (D : NativeBranchCore radius iota) (G : NativeHighGeometry D)
    (c : D.HighCenter) (datum : NativeHighCriticalBallDatum D c)
    (hambientSource : D.ambient ⊆ D.S.source) :
    NativeHighCriticalBallAffineProxyGeometry
      (criticalScaleProxyRadius radius
        (positiveCenterHighPayloadGlobalNormData
          (D.chosenHighPayloadAt c)).criticalScale
        (nativeHighCriticalScale_pos D c))
      (nativeHighCriticalScaleAffineEquiv D c) D c :=
  nativeHighCriticalScaleAffineProxyGeometry
    D G c datum hambientSource

/-- The literal critical-ball proxy as a source in the post-normalization
absolute `L_3` chart. -/
def nativeHighCriticalScaleProxyWZL3Source
    {radius : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    (D : NativeBranchCore radius iota) (G : NativeHighGeometry D)
    (c : D.HighCenter) (datum : NativeHighCriticalBallDatum D c)
    (hambientSource : D.ambient ⊆ D.S.source) :=
  nativeHighCriticalBallAffineProxyWZL3Source
    (criticalScaleProxyRadius radius
      (positiveCenterHighPayloadGlobalNormData
        (D.chosenHighPayloadAt c)).criticalScale
      (nativeHighCriticalScale_pos D c))
    (nativeHighCriticalScaleAffineEquiv D c) D c
    (nativeHighCriticalScaleProxyGeometry D G c datum hambientSource)

/-- The transported shading on the concrete critical-scale proxy family. -/
def nativeHighCriticalScaleProxyShading
    {radius : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    (D : NativeBranchCore radius iota) (G : NativeHighGeometry D)
    (c : D.HighCenter) (datum : NativeHighCriticalBallDatum D c)
    (hambientSource : D.ambient ⊆ D.S.source)
    (Y : Shading D.S.family.bodyFamily) :=
  nativeHighCriticalBallAffineProxyShading
    (criticalScaleProxyRadius radius
      (positiveCenterHighPayloadGlobalNormData
        (D.chosenHighPayloadAt c)).criticalScale
      (nativeHighCriticalScale_pos D c))
    (nativeHighCriticalScaleAffineEquiv D c) D c Y
    (nativeHighCriticalScaleProxyGeometry D G c datum hambientSource)

/-- Universe-zero specialization as an actual tube datum. -/
def nativeHighCriticalScaleProxyDatum
    {radius : NNReal} {iota : Type} [Fintype iota] [DecidableEq iota]
    (D : NativeBranchCore radius iota) (G : NativeHighGeometry D)
    (c : D.HighCenter) (datum : NativeHighCriticalBallDatum D c)
    (hambientSource : D.ambient ⊆ D.S.source)
    (Y : Shading D.S.family.bodyFamily) :
    ActualTubeDatum
      (criticalScaleProxyRadius radius
        (positiveCenterHighPayloadGlobalNormData
          (D.chosenHighPayloadAt c)).criticalScale
        (nativeHighCriticalScale_pos D c))
      (NativeHighCriticalBallIndex D c) :=
  nativeHighCriticalBallAffineProxyDatum
    (criticalScaleProxyRadius radius
      (positiveCenterHighPayloadGlobalNormData
        (D.chosenHighPayloadAt c)).criticalScale
      (nativeHighCriticalScale_pos D c))
    (nativeHighCriticalScaleAffineEquiv D c) D c Y
    (nativeHighCriticalScaleProxyGeometry D G c datum hambientSource)

theorem nativeHighCriticalScaleProxyShading_shadingMass
    {radius : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    (D : NativeBranchCore radius iota) (G : NativeHighGeometry D)
    (c : D.HighCenter) (datum : NativeHighCriticalBallDatum D c)
    (hambientSource : D.ambient ⊆ D.S.source)
    (Y : Shading D.S.family.bodyFamily) :
    (nativeHighCriticalScaleProxyShading D G c datum hambientSource Y).shadingMass =
      affineJacobian (nativeHighCriticalScaleAffineEquiv D c) *
        (nativeHighCriticalBallShading D c Y).shadingMass := by
  exact nativeHighCriticalBallAffineProxyShading_shadingMass
    (criticalScaleProxyRadius radius
      (positiveCenterHighPayloadGlobalNormData
        (D.chosenHighPayloadAt c)).criticalScale
      (nativeHighCriticalScale_pos D c))
    (nativeHighCriticalScaleAffineEquiv D c) D c Y
    (nativeHighCriticalScaleProxyGeometry D G c datum hambientSource)

theorem nativeHighCriticalScaleProxyShading_shadedUnion_volume
    {radius : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    (D : NativeBranchCore radius iota) (G : NativeHighGeometry D)
    (c : D.HighCenter) (datum : NativeHighCriticalBallDatum D c)
    (hambientSource : D.ambient ⊆ D.S.source)
    (Y : Shading D.S.family.bodyFamily) :
    volume
        (nativeHighCriticalScaleProxyShading D G c datum hambientSource Y).shadedUnion =
      affineJacobian (nativeHighCriticalScaleAffineEquiv D c) *
        volume (nativeHighCriticalBallShading D c Y).shadedUnion := by
  exact nativeHighCriticalBallAffineProxyShading_shadedUnion_volume
    (criticalScaleProxyRadius radius
      (positiveCenterHighPayloadGlobalNormData
        (D.chosenHighPayloadAt c)).criticalScale
      (nativeHighCriticalScale_pos D c))
    (nativeHighCriticalScaleAffineEquiv D c) D c Y
    (nativeHighCriticalScaleProxyGeometry D G c datum hambientSource)

theorem nativeHighCriticalScaleProxyShading_averageMultiplicity
    {radius : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    (D : NativeBranchCore radius iota) (G : NativeHighGeometry D)
    (c : D.HighCenter) (datum : NativeHighCriticalBallDatum D c)
    (hambientSource : D.ambient ⊆ D.S.source)
    (Y : Shading D.S.family.bodyFamily) :
    (nativeHighCriticalScaleProxyShading D G c datum
        hambientSource Y).averageMultiplicity =
      (nativeHighCriticalBallShading D c Y).averageMultiplicity := by
  exact nativeHighCriticalBallAffineProxyShading_averageMultiplicity
    (criticalScaleProxyRadius radius
      (positiveCenterHighPayloadGlobalNormData
        (D.chosenHighPayloadAt c)).criticalScale
      (nativeHighCriticalScale_pos D c))
    (nativeHighCriticalScaleAffineEquiv D c) D c Y
    (nativeHighCriticalScaleProxyGeometry D G c datum hambientSource)

theorem nativeHighCriticalScaleProxyDatum_radius_le_one_fifth_of_richCenter
    {radius : NNReal} {iota : Type} [Fintype iota] [DecidableEq iota]
    (D : NativeBranchCore radius iota) (G : NativeHighGeometry D)
    {c : D.HighCenter}
    (hc : c ∈ nativeHighNearSaturatedCriticalBallRichCenters D G) :
    criticalScaleProxyRadius radius
      (positiveCenterHighPayloadGlobalNormData
        (D.chosenHighPayloadAt c)).criticalScale
      (nativeHighCriticalScale_pos D c) ≤ (1 / 5 : NNReal) :=
  nativeHighCriticalScaleProxyRadius_le_one_fifth_of_richCenter D G hc

#print axioms nativeHighCriticalScaleProxyGeometry
#print axioms nativeHighCriticalScaleProxyWZL3Source
#print axioms nativeHighCriticalScaleProxyShading
#print axioms nativeHighCriticalScaleProxyDatum
#print axioms nativeHighCriticalScaleProxyShading_shadingMass
#print axioms nativeHighCriticalScaleProxyShading_shadedUnion_volume
#print axioms nativeHighCriticalScaleProxyShading_averageMultiplicity
#print axioms nativeHighCriticalScaleProxyDatum_radius_le_one_fifth_of_richCenter

end

end Family8Family7NativeHighCriticalScaleProxyDatumV1
