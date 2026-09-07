import Family8Grounding.Family8Family7GenericNativeHighWeightedCriticalBallSupportV1
import Family8Grounding.Family8Family7NativeHighCriticalScaleProxyDatumV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8Family7GenericNativeHighArbitraryWeightedProxyDefinitionsV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open Family8ContractedJohnActualTubeProxyV1
open Family8Family7GenericNativeHighGeometryV1
open Family8Family7GenericNativeHighWeightedCriticalBallSupportV1
open Family8Family7GenericNativeHighWeightedNormDataV1
open Family8Family7NativeHighCriticalScaleAffineMapV1
open Family8Family7NativeHighCriticalScaleProxyGeometryV1
open Family8SelectedParentPlankFineProxyDatumV1
open Family8ShadingAwareGenericNativeBranchCoreV2
open FamilyStickyCinematicL32ActualTubeCoefficientDistancesV1
open FamilyStickyCinematicL32FiniteProjectedShadingMultiplicitySliceV1
open FamilyStickyCinematicL32WZL3UniformTubeSourceV1

noncomputable section

universe u

/-!
# Arbitrary weighted critical-scale proxy definitions over a generic core

This layer contains only synchronized definitions and their literal mass and
support projections.  Geometry, unit-ball support, and greedy admissibility
are intentionally deferred to separate successors.
-/

structure GenericNativeHighArbitraryWeightedProxyInput
    {radius : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    {S : WZL3UniformTubeSource radius iota}
    {physical : FiniteProjectedShading (Real × Real) iota}
    {f : Real → Real} {hfContinuous : Continuous f}
    (D : GenericNativeBranchCore radius iota S physical f hfContinuous) where
  geometry : GenericNativeHighGeometry D
  center : D.HighCenter
  weight : iota → ENNReal

abbrev GenericNativeHighArbitraryWeightedCriticalBallIndex
    {radius : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    {S : WZL3UniformTubeSource radius iota}
    {physical : FiniteProjectedShading (Real × Real) iota}
    {f : Real → Real} {hfContinuous : Continuous f}
    (D : GenericNativeBranchCore radius iota S physical f hfContinuous)
    (P : GenericNativeHighArbitraryWeightedProxyInput D) :=
  {i // i ∈ (genericNativeHighWeightedNormData
    D P.center P.weight).criticalBall}

def genericNativeHighArbitraryWeightedCriticalBallFamily
    {radius : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    {S : WZL3UniformTubeSource radius iota}
    {physical : FiniteProjectedShading (Real × Real) iota}
    {f : Real → Real} {hfContinuous : Continuous f}
    (D : GenericNativeBranchCore radius iota S physical f hfContinuous)
    (P : GenericNativeHighArbitraryWeightedProxyInput D) :
    UniformTubeFamily radius
      (GenericNativeHighArbitraryWeightedCriticalBallIndex D P) :=
  S.family.restrictTo
    (genericNativeHighWeightedNormData D P.center P.weight).criticalBall

@[simp] theorem genericNativeHighArbitraryWeightedCriticalBallFamily_tubes
    {radius : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    {S : WZL3UniformTubeSource radius iota}
    {physical : FiniteProjectedShading (Real × Real) iota}
    {f : Real → Real} {hfContinuous : Continuous f}
    (D : GenericNativeBranchCore radius iota S physical f hfContinuous)
    (P : GenericNativeHighArbitraryWeightedProxyInput D)
    (i : GenericNativeHighArbitraryWeightedCriticalBallIndex D P) :
    (genericNativeHighArbitraryWeightedCriticalBallFamily D P).tubes i =
      S.family.tubes i.1 :=
  rfl

def genericNativeHighArbitraryWeightedCriticalBallShading
    {radius : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    {S : WZL3UniformTubeSource radius iota}
    {physical : FiniteProjectedShading (Real × Real) iota}
    {f : Real → Real} {hfContinuous : Continuous f}
    (D : GenericNativeBranchCore radius iota S physical f hfContinuous)
    (P : GenericNativeHighArbitraryWeightedProxyInput D)
    (Y : Shading S.family.bodyFamily) :
    Shading
      (genericNativeHighArbitraryWeightedCriticalBallFamily D P).bodyFamily where
  carrier i := Y.carrier i.1
  measurable_carrier i := Y.measurable_carrier i.1
  carrier_subset i := Y.carrier_subset i.1

@[simp] theorem genericNativeHighArbitraryWeightedCriticalBallShading_carrier
    {radius : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    {S : WZL3UniformTubeSource radius iota}
    {physical : FiniteProjectedShading (Real × Real) iota}
    {f : Real → Real} {hfContinuous : Continuous f}
    (D : GenericNativeBranchCore radius iota S physical f hfContinuous)
    (P : GenericNativeHighArbitraryWeightedProxyInput D)
    (Y : Shading S.family.bodyFamily)
    (i : GenericNativeHighArbitraryWeightedCriticalBallIndex D P) :
    (genericNativeHighArbitraryWeightedCriticalBallShading
      D P Y).carrier i = Y.carrier i.1 :=
  rfl

theorem genericNativeHighArbitraryWeightedCriticalBallShading_shadingMass
    {radius : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    {S : WZL3UniformTubeSource radius iota}
    {physical : FiniteProjectedShading (Real × Real) iota}
    {f : Real → Real} {hfContinuous : Continuous f}
    (D : GenericNativeBranchCore radius iota S physical f hfContinuous)
    (P : GenericNativeHighArbitraryWeightedProxyInput D)
    (Y : Shading S.family.bodyFamily) :
    (genericNativeHighArbitraryWeightedCriticalBallShading
      D P Y).shadingMass =
      ∑ i ∈ (genericNativeHighWeightedNormData
        D P.center P.weight).criticalBall,
        volume (Y.carrier i) := by
  unfold Shading.shadingMass
  simpa only [
    genericNativeHighArbitraryWeightedCriticalBallShading_carrier,
    Finset.univ_eq_attach] using
      Finset.sum_attach
        (genericNativeHighWeightedNormData
          D P.center P.weight).criticalBall
        (fun i => volume (Y.carrier i))

theorem genericNativeHighArbitraryWeightedCriticalBall_subset_physicalAmbient
    {radius : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    {S : WZL3UniformTubeSource radius iota}
    {physical : FiniteProjectedShading (Real × Real) iota}
    {f : Real → Real} {hfContinuous : Continuous f}
    (D : GenericNativeBranchCore radius iota S physical f hfContinuous)
    (P : GenericNativeHighArbitraryWeightedProxyInput D) :
    (genericNativeHighWeightedNormData
      D P.center P.weight).criticalBall ⊆ physical.ambient :=
  genericNativeHighWeightedCriticalBall_subset_physicalAmbient
    D P.center P.weight

theorem genericNativeHighArbitraryWeightedCriticalScale_pos
    {radius : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    {S : WZL3UniformTubeSource radius iota}
    {physical : FiniteProjectedShading (Real × Real) iota}
    {f : Real → Real} {hfContinuous : Continuous f}
    (D : GenericNativeBranchCore radius iota S physical f hfContinuous)
    (P : GenericNativeHighArbitraryWeightedProxyInput D) :
    0 < (genericNativeHighWeightedNormData
      D P.center P.weight).criticalScale :=
  (genericNativeHighWeightedNormData
    D P.center P.weight).delta_pos.trans_le
      (genericNativeHighWeightedNormData
        D P.center P.weight).criticalScale_bounds.1

def genericNativeHighArbitraryWeightedCriticalScaleAffineEquiv
    {radius : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    {S : WZL3UniformTubeSource radius iota}
    {physical : FiniteProjectedShading (Real × Real) iota}
    {f : Real → Real} {hfContinuous : Continuous f}
    (D : GenericNativeBranchCore radius iota S physical f hfContinuous)
    (P : GenericNativeHighArbitraryWeightedProxyInput D) :
    Space ≃ᵃ[Real] Space :=
  let W := genericNativeHighWeightedNormData D P.center P.weight
  let T0 := S.family.tubes W.criticalCenter
  criticalScaleAffineEquiv W.criticalScale
    (genericNativeHighArbitraryWeightedCriticalScale_pos D P)
    (projectedTubeGraphA T0) (projectedTubeGraphB T0)
    (projectedTubeGraphC T0) (projectedTubeGraphD T0)

def genericNativeHighArbitraryWeightedCriticalScaleProxyFamily
    {radius : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    {S : WZL3UniformTubeSource radius iota}
    {physical : FiniteProjectedShading (Real × Real) iota}
    {f : Real → Real} {hfContinuous : Continuous f}
    (D : GenericNativeBranchCore radius iota S physical f hfContinuous)
    (P : GenericNativeHighArbitraryWeightedProxyInput D) :
    UniformTubeFamily
      (criticalScaleProxyRadius radius
        (genericNativeHighWeightedNormData D P.center P.weight).criticalScale
        (genericNativeHighArbitraryWeightedCriticalScale_pos D P))
      (GenericNativeHighArbitraryWeightedCriticalBallIndex D P) where
  tubes i := affineAxisProxyTube
    (criticalScaleProxyRadius radius
      (genericNativeHighWeightedNormData D P.center P.weight).criticalScale
      (genericNativeHighArbitraryWeightedCriticalScale_pos D P))
    (genericNativeHighArbitraryWeightedCriticalScaleAffineEquiv D P)
    (S.family.tubes i.1)
  refinement := UniformRefinement.ofFinset Finset.univ

@[simp] theorem genericNativeHighArbitraryWeightedCriticalScaleProxyFamily_tubes
    {radius : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    {S : WZL3UniformTubeSource radius iota}
    {physical : FiniteProjectedShading (Real × Real) iota}
    {f : Real → Real} {hfContinuous : Continuous f}
    (D : GenericNativeBranchCore radius iota S physical f hfContinuous)
    (P : GenericNativeHighArbitraryWeightedProxyInput D)
    (i : GenericNativeHighArbitraryWeightedCriticalBallIndex D P) :
    (genericNativeHighArbitraryWeightedCriticalScaleProxyFamily D P).tubes i =
      affineAxisProxyTube
        (criticalScaleProxyRadius radius
          (genericNativeHighWeightedNormData
            D P.center P.weight).criticalScale
          (genericNativeHighArbitraryWeightedCriticalScale_pos D P))
        (genericNativeHighArbitraryWeightedCriticalScaleAffineEquiv D P)
        (S.family.tubes i.1) :=
  rfl

#print axioms GenericNativeHighArbitraryWeightedProxyInput
#print axioms genericNativeHighArbitraryWeightedCriticalBallFamily
#print axioms genericNativeHighArbitraryWeightedCriticalBallShading
#print axioms
  genericNativeHighArbitraryWeightedCriticalBallShading_shadingMass
#print axioms
  genericNativeHighArbitraryWeightedCriticalBall_subset_physicalAmbient
#print axioms genericNativeHighArbitraryWeightedCriticalScale_pos
#print axioms genericNativeHighArbitraryWeightedCriticalScaleAffineEquiv
#print axioms genericNativeHighArbitraryWeightedCriticalScaleProxyFamily

end

end Family8Family7GenericNativeHighArbitraryWeightedProxyDefinitionsV1
