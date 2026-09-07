import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32PyzActualNormFirstAllCenterMassWeightedBranchTypesV5C
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace FamilyStickyCinematicL32PyzActualNormFirstAllCenterMassWeightedBranchLowV5D

open FamilyStickyCinematicL32PyzActualNormFirstAllCenterLowHalfMomentV4
open FamilyStickyCinematicL32PyzActualNormFirstAllCenterMassWeightedBranchConnectorV5
open FamilyStickyCinematicL32PyzActualNormFirstAllCenterMassWeightedBranchTypesV5C

noncomputable section

universe u

/-- The low branch is a direct V4 call on V2's literal complementary
finset.  Its sole branch-specific premise is the low-half mass inequality. -/
theorem nativeLowOutcome_of_half
    {radius : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    (D : NativeBranchCore radius iota) (L : NativeLowGeometry D)
    (hhalf : D.sourceMass / 2 <=
      ∑ a ∈ D.low, volume (D.cell a.1)) : L.Outcome := by
  classical
  unfold NativeLowGeometry.Outcome
  exact actualLowPayloadHalfMoment_sum L.Q D.S D.ambient L.hambient L.hunit
    D.physicalBase D.hphysicalBase D.f D.hfContinuous D.f1 D.f2 D.outerA
    D.outerB D.hOuter D.hf D.hf1 L.hparameter L.halpha L.halphaOne
    L.hfun L.hfun1 D.globalScale D.hglobalScale D.low (fun a => a.1)
    Subtype.val_injective (fun a _ha => (Finset.mem_filter.mp a.2).1)
    D.positiveBase D.positiveBase_measurable L.hbaseSubset D.normExponent
    D.tangencyExponent D.logCount L.lower L.upper L.multiplicity D.hradius
    D.hradiusSixteen D.hradiusTangency D.hnormExponent
    L.htangencyExponent L.hbaseBand D.payloadAt L.hpairAmbient L.hpairAt
    L.hactiveCapAt L.hfamilyAt L.hnormBallSubsetAt L.hnormScaleLowerAt
    (fun a ha => by
      have hnot : ¬ 24 * D.logCount <= D.degree a :=
        (Finset.mem_filter.mp ha).2
      exact lt_of_not_ge hnot)
    D.sourceMass hhalf

#print axioms nativeLowOutcome_of_half

end
end FamilyStickyCinematicL32PyzActualNormFirstAllCenterMassWeightedBranchLowV5D
