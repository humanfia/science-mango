import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32PyzActualNormFirstAllCenterMassWeightedBranchTypesV5C
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace FamilyStickyCinematicL32PyzActualNormFirstAllCenterMassWeightedBranchHighV5D

open FamilyStickyCinematicL32PyzActualNormFirstAllCenterHighHalfSampledLensV3
open FamilyStickyCinematicL32PyzActualNormFirstAllCenterMassWeightedBranchTypesV5C

noncomputable section

universe u

/-- The high branch is a direct V3 call on the literal subtype selected by
V2.  Its sole branch-specific premise is the high-half mass inequality. -/
theorem nativeHighOutcome_of_half
    {radius : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    (D : NativeBranchCore radius iota) (G : NativeHighGeometry D)
    (hhalf : D.sourceMass / 2 <=
      ∑ c ∈ D.high, volume (D.cell c.1)) : G.Outcome := by
  classical
  have hsum :
      (∑ c : D.HighCenter, volume (D.highBase c)) =
        ∑ c ∈ D.high, volume (D.cell c.1) := by
    simpa only [NativeBranchCore.highBase,
      NativeBranchCore.positiveBase, Finset.univ_eq_attach] using
        Finset.sum_attach D.high (fun c => volume (D.cell c.1))
  have hhalf' : D.sourceMass / 2 <=
      ∑ c : D.HighCenter, volume (D.highBase c) :=
    hhalf.trans_eq hsum.symm
  unfold NativeHighGeometry.Outcome
  exact exists_actualAllHighCenters_baseSampledLens_sum
    D.highBase D.highBase_measurable D.S.family D.ambient D.physicalBase
      D.hphysicalBase D.f D.hfContinuous D.f1 D.f2 D.outerA D.outerB
      D.hOuter D.hf D.hf1 D.globalScale D.hglobalScale (fun c => c.1.1)
      (fun c => (Finset.mem_filter.mp c.1.2).1) G.bucket G.hbucket
      D.tangencyExponent D.normExponent D.logCount D.chosenHighPayloadAt
      G.mesh G.ballRadius G.hmesh G.hparameter G.sharp G.hft G.hf1Lower
      G.hf1Upper G.hf2 G.hf2Continuous G.hmeshBase G.hroom
      G.hnearRadiusLower G.hnearRadiusUpper G.hballRadiusLower
      G.hballRadiusUpper G.hsmall G.hcount D.sourceMass hhalf'

#print axioms nativeHighOutcome_of_half

end
end FamilyStickyCinematicL32PyzActualNormFirstAllCenterMassWeightedBranchHighV5D
