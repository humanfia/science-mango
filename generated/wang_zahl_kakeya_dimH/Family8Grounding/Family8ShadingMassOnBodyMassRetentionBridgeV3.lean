import Family8Grounding.Family8StickyShadingAwareLogBucketSelectionV1

/-!
# From retained shading mass to retained tube-body mass, V3

The shading-aware selector records the mass that is relevant to source
multiplicity.  Every shading carrier lies in its tube body, so this retention
feeds the existing body-mass fine-card budget with no additional loss.
-/

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8ShadingMassOnBodyMassRetentionBridgeV3

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.JointTubeFactoring
open Submission.Kakeya.Uniformity
open Family8StickyShadingAwareLogBucketSelectionV1

noncomputable section

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false

variable {delta : NNReal} {index : Type*}
  [Fintype index] [DecidableEq index]
  {fine : UniformTubeFamily delta index}

/-- On every finite index set, actual shading mass is bounded by the mass of
the corresponding tube bodies. -/
theorem shadingMassOn_le_bodyMassOn
    (Y : Shading fine.bodyFamily) (s : Finset index) :
    shadingMassOn Y s ≤ bodyMassOn fine.bodyFamily s := by
  unfold shadingMassOn bodyMassOn
  exact Finset.sum_le_sum fun i _hi => measure_mono (Y.carrier_subset i)

/-- A `WithinFactor` shading-retention statement can be consumed directly by
the existing body-mass fine-card budget. -/
theorem withinFactor_bodyMassOn_of_shadingMassOn
    (Y : Shading fine.bodyFamily) (s : Finset index)
    (sourceMass : ENNReal) (retainLoss : Nat)
    (hretain : WithinFactor retainLoss sourceMass (shadingMassOn Y s)) :
    WithinFactor retainLoss sourceMass (bodyMassOn fine.bodyFamily s) := by
  unfold WithinFactor at hretain ⊢
  exact hretain.trans
    (nsmul_le_nsmul_right (shadingMassOn_le_bodyMassOn Y s) retainLoss)

#print axioms shadingMassOn_le_bodyMassOn
#print axioms withinFactor_bodyMassOn_of_shadingMassOn

end
end Family8ShadingMassOnBodyMassRetentionBridgeV3
