import Family8Grounding.Family8ShadingMassOnBodyMassRetentionBridgeV3
import Submission.Kakeya.ConvexFactoring.InducedShadingDensityAlgebra
import Submission.Kakeya.ConvexFactoring.HeavyParentSelection

/-!
# Density retention for a literal selected coarse subtype, V3

V1 and V2 are failed drafts and are not imported.  V1 omitted the direct\nHeavyParentSelection import; V2 was mathematically complete but failed the\nunused-section-variable linter.\n\nThese two generic identities isolate the measure algebra needed by the
first-crossing chart and graph-bucket selections.  They use the literal
selected subtype throughout.  In particular, the contained-mass identity
does not cancel a possibly zero or infinite scalar: finiteness and the
zero-volume case are already handled by
`shadingDensity_mul_familyVolume`.
-/

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8SelectedCoarseShadingDensityRetentionV3

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.InducedShadingDensityAlgebra
open Submission.Kakeya.ConvexFactoring.HeavyParentSelection
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

/-- A literal finite subtype that retains shading mass up to `loss` retains
the corresponding selected-subtype shading density up to the same loss.
No positivity or finiteness hypothesis on `loss` is needed. -/
theorem selectedCoarseShading_density_div_loss_le
    (Y : Shading fine.bodyFamily) {s t : Finset index} (loss : ENNReal)
    (hst : s ⊆ t)
    (hretained : shadingMassOn Y t ≤ loss * shadingMassOn Y s) :
    (selectedCoarseShading Y t).shadingDensity / loss ≤
      (selectedCoarseShading Y s).shadingDensity := by
  let source := selectedCoarseShading Y t
  let target := selectedCoarseShading Y s
  have hfamily :
      familyVolume (selectedCoarseFamily fine.bodyFamily s) ≤
        familyVolume (selectedCoarseFamily fine.bodyFamily t) := by
    rw [selectedCoarseFamily_volume, selectedCoarseFamily_volume]
    exact Finset.sum_le_sum_of_subset hst
  have hmass : source.shadingMass ≤ loss * target.shadingMass := by
    simpa only [source, target, selectedCoarseShading_mass, shadingMassOn]
      using hretained
  have hdensity : source.shadingDensity ≤
      loss * target.shadingDensity := by
    by_cases hzero :
        familyVolume (selectedCoarseFamily fine.bodyFamily t) = 0
    · have hsourceMass : source.shadingMass = 0 :=
        nonpos_iff_eq_zero.mp
          (source.shadingMass_le_familyVolume.trans_eq hzero)
      simp [Shading.shadingDensity, source, hzero, hsourceMass]
    · rw [← ENNReal.mul_le_mul_iff_right hzero
        (familyVolume_ne_top
          (selectedCoarseFamily fine.bodyFamily t))]
      calc
        familyVolume (selectedCoarseFamily fine.bodyFamily t) *
            source.shadingDensity = source.shadingMass := by
          rw [mul_comm, shadingDensity_mul_familyVolume]
        _ ≤ loss * target.shadingMass := hmass
        _ = loss *
            (target.shadingDensity *
              familyVolume (selectedCoarseFamily fine.bodyFamily s)) := by
          rw [shadingDensity_mul_familyVolume]
        _ ≤ loss *
            (target.shadingDensity *
              familyVolume (selectedCoarseFamily fine.bodyFamily t)) := by
          exact mul_le_mul' le_rfl (mul_le_mul' le_rfl hfamily)
        _ = familyVolume (selectedCoarseFamily fine.bodyFamily t) *
            (loss * target.shadingDensity) := by ac_rfl
  exact ENNReal.div_le_of_le_mul' hdensity

/-- If every selected body lies in `K`, selected density times the literal
contained body mass is exactly the selected shading mass.  This statement is
valid even when the selected family has zero total volume; no cancellation is
used. -/
theorem selectedCoarseShading_density_mul_containedMassOn
    (Y : Shading fine.bodyFamily) (t : Finset index)
    (K : ConvexBody Space)
    (hcontained : ∀ i ∈ t,
      (fine.bodyFamily i : Set Space) ⊆ (K : Set Space)) :
    (selectedCoarseShading Y t).shadingDensity *
        containedMassOn fine.bodyFamily t K = shadingMassOn Y t := by
  calc
    (selectedCoarseShading Y t).shadingDensity *
        containedMassOn fine.bodyFamily t K =
        (selectedCoarseShading Y t).shadingDensity *
          bodyMassOn fine.bodyFamily t := by
      rw [containedMassOn_eq_bodyMassOn_of_contained
        fine.bodyFamily t K hcontained]
    _ = (selectedCoarseShading Y t).shadingDensity *
        familyVolume (selectedCoarseFamily fine.bodyFamily t) := by
      rw [bodyMassOn, selectedCoarseFamily_volume]
    _ = (selectedCoarseShading Y t).shadingMass :=
      shadingDensity_mul_familyVolume (selectedCoarseShading Y t)
    _ = shadingMassOn Y t := by
      rw [selectedCoarseShading_mass]
      rfl

#print axioms selectedCoarseShading_density_div_loss_le
#print axioms selectedCoarseShading_density_mul_containedMassOn

end
end Family8SelectedCoarseShadingDensityRetentionV3
