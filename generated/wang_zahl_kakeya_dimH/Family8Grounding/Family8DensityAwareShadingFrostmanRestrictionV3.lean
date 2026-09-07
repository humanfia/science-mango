import Family8Grounding.Family8Prop51SelectedOccurrenceSourceFrostmanV1
import Family8Grounding.Family8ShadingMassOnBodyMassRetentionBridgeV3
import Submission.Kakeya.Uniformity.TubeFamily

/-!
# Density-aware restriction of an active Frostman family, V3

V1 and V2 are failed drafts and are not imported.  V1 omitted the\nUniformity namespace; V2 used an unavailable multiplication monotonicity\nalias.\n\nThis is the same-object alternative to cardinality restriction.  A lower
density bound converts ambient contained tube mass into actual shading mass;
a shading-retention inequality then pays only the reciprocal density and the
literal mass-selection loss.  The selected shading is automatically bounded
by selected contained tube mass because `IsFrostmanOn` already records that
all active tube bodies lie in its ambient convex body.
-/

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8DensityAwareShadingFrostmanRestrictionV3

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.JointTubeFactoring
open Submission.Kakeya.Uniformity
open Family8Prop51SelectedOccurrenceSourceFrostmanV1
open Family8ShadingMassOnBodyMassRetentionBridgeV3
open Family8StickyShadingAwareLogBucketSelectionV1

noncomputable section

set_option autoImplicit false
set_option warningAsError true

variable {delta : NNReal} {index : Type*}
  [Fintype index] [DecidableEq index]
  {fine : UniformTubeFamily delta index}

/-- Restrict an active Frostman theorem along the same shading-mass
selection.  The exact loss is `d⁻¹ * L`; no cardinal comparison and no
source Katz--Tao hypothesis is used. -/
theorem isFrostmanOn_subset_of_density_shading_retention
    {s t : Finset index} {C d L : ENNReal} {K : ConvexBody Space}
    (Y : Shading fine.bodyFamily)
    (hst : s ⊆ t)
    (hfull : IsFrostmanOn C fine.bodyFamily t K)
    (hd0 : d ≠ 0) (hdtop : d ≠ ∞)
    (hdensity :
      d * containedMassOn fine.bodyFamily t K ≤ shadingMassOn Y t)
    (hshadingRetained : shadingMassOn Y t ≤ L * shadingMassOn Y s) :
    IsFrostmanOn (C * (d⁻¹ * L)) fine.bodyFamily s K := by
  have hcontained : ∀ i ∈ s,
      (fine.bodyFamily i : Set Space) ⊆ (K : Set Space) := by
    intro i hi
    exact hfull.1 i (hst hi)
  have hshadingContained :
      shadingMassOn Y s ≤ containedMassOn fine.bodyFamily s K := by
    exact (shadingMassOn_le_bodyMassOn Y s).trans_eq
      (containedMassOn_eq_bodyMassOn_of_contained
        fine.bodyFamily s K hcontained).symm
  have hscaled :
      d * containedMassOn fine.bodyFamily t K ≤
        L * containedMassOn fine.bodyFamily s K :=
    hdensity.trans <| hshadingRetained.trans <|
      mul_le_mul' le_rfl hshadingContained
  have hretained :
      containedMassOn fine.bodyFamily t K ≤
        (d⁻¹ * L) * containedMassOn fine.bodyFamily s K := by
    have hdiv :
        containedMassOn fine.bodyFamily t K ≤
          (L * containedMassOn fine.bodyFamily s K) / d := by
      apply (ENNReal.le_div_iff_mul_le (Or.inl hd0) (Or.inl hdtop)).2
      simpa only [mul_comm] using hscaled
    simpa only [ENNReal.div_eq_inv_mul, mul_assoc] using hdiv
  exact isFrostmanOn_subset_of_ambientMass_retention
    hst hfull hretained

end
end Family8DensityAwareShadingFrostmanRestrictionV3
