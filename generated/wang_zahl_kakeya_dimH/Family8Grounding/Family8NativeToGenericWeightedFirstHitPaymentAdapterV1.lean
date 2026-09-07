import Family8Grounding.Family8ShadingAwareGenericNativeBranchCoreV2
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32PyzActualNormFirstAllCenterHighConcreteQPFirstHitRichPairSumV9
import Mathlib.Tactic

/-!
# Native-to-generic transport retaining the weighted first-hit payment

The first-hit outcome is dependent on the old `NativeBranchCore`.  Its
projected physical datum is nevertheless a literal parameter of the newer
`GenericNativeBranchCore`.  This file performs only that definitional
transport and keeps the same dependent `hout`; it does not replace the
selected first-hit mass by a source-mass envelope.
-/

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 5000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8NativeToGenericWeightedFirstHitPaymentAdapterV1

open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open Family8ShadingAwareGenericNativeBranchCoreV2
open FamilyStickyCinematicL32PyzActualAllCenterBinUniformityV1
open FamilyStickyCinematicL32PyzActualNormFirstAllCenterHighConcreteQPFirstHitRichPairSumV9
open FamilyStickyCinematicL32PyzActualNormFirstAllCenterHighConcreteQPOutcomeV4
open FamilyStickyCinematicL32PyzActualNormFirstAllCenterMassWeightedBranchTypesV5C
open FamilyStickyCinematicL32WZL3UniformTubeSourceV1

noncomputable section

universe u

/-- Forget only the presentation of the old projected physical datum.  Every
geometric field, cell, and localization proof is reused literally. -/
def nativeToGenericCore
    {radius : NNReal} {iota : Type u}
    [Fintype iota] [DecidableEq iota]
    (D : NativeBranchCore radius iota) :
    GenericNativeBranchCore radius iota D.S D.physical D.f D.hfContinuous where
  f1 := D.f1
  f2 := D.f2
  outerA := D.outerA
  outerB := D.outerB
  hOuter := D.hOuter
  hf := D.hf
  hf1 := D.hf1
  globalScale := D.globalScale
  hglobalScale := D.hglobalScale
  cell := D.cell
  tangencyExponent := D.tangencyExponent
  normExponent := D.normExponent
  logCount := D.logCount
  hradius := D.hradius
  hradiusSixteen := D.hradiusSixteen
  hradiusTangency := D.hradiusTangency
  hnormExponent := D.hnormExponent
  hcellMeasurable := D.hcellMeasurable
  hlocalized := D.hlocalized

@[simp]
theorem nativeToGenericCore_physicalDatum
    {radius : NNReal} {iota : Type u}
    [Fintype iota] [DecidableEq iota]
    (D : NativeBranchCore radius iota) :
    (nativeToGenericCore D).physicalDatum = D.physical := by
  rfl

/-- The generic core computes the same literal cell sum that the old core
stored together with `hsourceMass`. -/
theorem nativeToGenericCore_sourceMass_eq
    {radius : NNReal} {iota : Type u}
    [Fintype iota] [DecidableEq iota]
    (D : NativeBranchCore radius iota) :
    (nativeToGenericCore D).sourceMass = D.sourceMass := by
  change (∑ center ∈ D.centers, volume (D.cell center)) = D.sourceMass
  exact D.hsourceMass.symm

/-- The honest V9 weighted first-hit payment, stated on the generic view of
the same core.  The dependent outcome `hout` is not reconstructed or
reselected. -/
theorem sourceMass_half_le_binLoss_mul_weightedFirstHitRichPairBudget_generic
    {radius : NNReal} {iota : Type u}
    [Fintype iota] [DecidableEq iota]
    {D : NativeBranchCore radius iota} {G : NativeHighGeometry D}
    (hout : NativeHighConcreteQPOutcome D G)
    (hhalf : D.sourceMass / 2 <=
      ∑ c ∈ D.high, volume (D.cell c.1)) :
    (nativeToGenericCore D).sourceMass / 2 <=
      actualAllCenterPostNormBinLoss radius D.globalScale
          D.physical.ambient.card *
        (72 * nativeHighConcreteWeightedFirstHitRichPairBudget hout) := by
  rw [nativeToGenericCore_sourceMass_eq]
  exact
    NativeHighConcreteQPOutcome.sourceMass_half_le_binLoss_mul_weightedFirstHitRichPairBudget
      hout hhalf

#print axioms nativeToGenericCore
#print axioms nativeToGenericCore_physicalDatum
#print axioms nativeToGenericCore_sourceMass_eq
#print axioms sourceMass_half_le_binLoss_mul_weightedFirstHitRichPairBudget_generic

end
end Family8NativeToGenericWeightedFirstHitPaymentAdapterV1
