import Family8Grounding.Family8RestrictedActualDatumMassBridgeV1
import Submission.Kakeya.ConvexFactoring.InducedShadingDensityAlgebra

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8RestrictedActualDatumDensityRetentionV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8KatzTaoFrostmanPropertiesV1
open Family8GeneralizedKatzTaoMultiplicityV1
open Family8RestrictedActualDatumMassBridgeV1
open Submission.Kakeya.ConvexFactoring.InducedShadingDensityAlgebra
open FamilyStickyCinematicL32Prop41FiniteRandomSamplingExtractionV1

noncomputable section

set_option autoImplicit false
set_option warningAsError true

/-!
# Density retention for an actual sampled subtype

The randomized generalized Katz--Tao step retains a weighted portion of the
source shading and then applies `KatzTaoProperty` to the literal restricted
datum.  These lemmas supply the deterministic denominator comparison needed
to transport the source density to that datum.
-/

/-- The actual family volume of a selected subtype is its literal selected
subsum in the source index type. -/
theorem restrictActualTubeDatum_actualFamilyVolume
    {delta : NNReal} {iota : Type} [Fintype iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota) (selected : Finset iota) :
    (restrictActualTubeDatum D selected).actualFamilyVolume =
      ∑ i ∈ selected, volume (D.family.bodyFamily i : Set Space) := by
  classical
  unfold ActualTubeDatum.actualFamilyVolume familyVolume
  simp_rw [restrictActualTubeDatum_bodyFamily_apply]
  rw [← Finset.attach_eq_univ]
  exact Finset.sum_attach selected
    (fun i => volume (D.family.bodyFamily i : Set Space))

/-- Restricting the actual index family cannot increase its summed tube
volume. -/
theorem restrictActualTubeDatum_actualFamilyVolume_le
    {delta : NNReal} {iota : Type} [Fintype iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota) (selected : Finset iota) :
    (restrictActualTubeDatum D selected).actualFamilyVolume ≤
      D.actualFamilyVolume := by
  rw [restrictActualTubeDatum_actualFamilyVolume]
  calc
    (∑ i ∈ selected, volume (D.family.bodyFamily i : Set Space)) ≤
        ∑ i ∈ (Finset.univ : Finset iota),
          volume (D.family.bodyFamily i : Set Space) :=
      Finset.sum_le_sum_of_subset (Finset.subset_univ _)
    _ = D.actualFamilyVolume := by
      simp [ActualTubeDatum.actualFamilyVolume, familyVolume]

/-- If the source mass is at most `loss` times the selected mass, then the
selected actual datum loses at most the same factor in shading density. -/
theorem source_shadingDensity_div_loss_le_restrictActualTubeDatum
    {delta : NNReal} {iota : Type} [Fintype iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota) (selected : Finset iota)
    (loss : ENNReal)
    (hretained : D.shading.shadingMass ≤
      loss * (restrictActualTubeDatum D selected).shading.shadingMass) :
    D.shading.shadingDensity / loss ≤
      (restrictActualTubeDatum D selected).shading.shadingDensity := by
  let Z := restrictActualTubeDatum D selected
  have hfamily :
      familyVolume Z.family.bodyFamily ≤ familyVolume D.family.bodyFamily := by
    exact restrictActualTubeDatum_actualFamilyVolume_le D selected
  have hsource : D.shading.shadingDensity ≤ loss * Z.shading.shadingDensity := by
    by_cases hzero : familyVolume D.family.bodyFamily = 0
    · have hmass : D.shading.shadingMass = 0 :=
        nonpos_iff_eq_zero.mp
          (D.shading.shadingMass_le_familyVolume.trans_eq hzero)
      simp [Shading.shadingDensity, hzero, hmass]
    · rw [← ENNReal.mul_le_mul_iff_right hzero
        (familyVolume_ne_top D.family.bodyFamily)]
      calc
        familyVolume D.family.bodyFamily * D.shading.shadingDensity =
            D.shading.shadingMass := by
          rw [mul_comm, shadingDensity_mul_familyVolume]
        _ ≤ loss * Z.shading.shadingMass := hretained
        _ = loss *
            (Z.shading.shadingDensity * familyVolume Z.family.bodyFamily) := by
          rw [shadingDensity_mul_familyVolume]
        _ ≤ loss *
            (Z.shading.shadingDensity * familyVolume D.family.bodyFamily) := by
          gcongr
        _ = familyVolume D.family.bodyFamily *
            (loss * Z.shading.shadingDensity) := by ac_rfl
  exact ENNReal.div_le_of_le_mul' hsource

/-- Zero-colour specialization used by the simultaneous sampling consumer. -/
theorem source_shadingDensity_div_loss_le_zeroColorActualDatum
    {delta : NNReal} {iota : Type} [Fintype iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota) (k : Nat) [NeZero k]
    (omega : iota → Fin k) (loss : ENNReal)
    (hretained : D.shading.shadingMass ≤
      loss * (zeroColorActualDatum D k omega).shading.shadingMass) :
    D.shading.shadingDensity / loss ≤
      (zeroColorActualDatum D k omega).shading.shadingDensity := by
  exact source_shadingDensity_div_loss_le_restrictActualTubeDatum
    D (zeroColorSample k omega) loss hretained

#print axioms restrictActualTubeDatum_actualFamilyVolume
#print axioms restrictActualTubeDatum_actualFamilyVolume_le
#print axioms source_shadingDensity_div_loss_le_restrictActualTubeDatum
#print axioms source_shadingDensity_div_loss_le_zeroColorActualDatum

end
end Family8RestrictedActualDatumDensityRetentionV1
