import Family8Grounding.Family8PlankLongTubeGlobalKatzTaoV3
import FamilyStickyGrounding.FamilyStickyFiniteFamilyMaximalConcentrationV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8PlankLongTubeCanonicalGlobalKatzTaoBoundV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Family6AffinePlankAnalyticHypothesesStableV1
open Family6CanonicalFrostmanConstantCoreV1
open Family8AmbientFamilyVolumeDensityV2
open Family8PlankCertificateLongTubeCoverV2
open Family8PlankLongTubeFrostmanTransferV3
open Family8PlankLongTubeThickenedAmbientFrostmanV3
open Family8PlankLongTubeGlobalKatzTaoV3
open FamilyStickyFiniteFamilyMaximalConcentrationV1
open FamilyStickyAdjacentTestBodyGeometryV1

noncomputable section

universe u

variable {iota : Type u} [Fintype iota] [DecidableEq iota]
variable {a b : NNReal}

/-- The indexed volume of the genuine long-tube cover costs at most the
same memberwise plank-to-tube copy loss. -/
theorem plankLongTubeCover_familyVolume_le_copyLoss_mul
    (D : ShadedConvexPlankFamily iota a b)
    (hb : b ≤ (2 : NNReal)⁻¹) :
    familyVolume (plankLongTubeCoverFamily D).bodyFamily ≤
      plankLongTubeFrostmanCopyLoss D.comparisonConstant a b *
        familyVolume D.family := by
  unfold familyVolume
  calc
    (∑ i, volume ((plankLongTubeCoverFamily D).bodyFamily i : Set Space)) ≤
        ∑ i, plankLongTubeFrostmanCopyLoss D.comparisonConstant a b *
          volume (D.family i : Set Space) := by
      apply Finset.sum_le_sum
      intro i _hi
      exact longTubeCover_volume_le_copyLoss_mul_source D hb i
    _ = plankLongTubeFrostmanCopyLoss D.comparisonConstant a b *
        ∑ i, volume (D.family i : Set Space) := by
      rw [Finset.mul_sum]

/-- For the canonical source Frostman constant, all ambient-volume and
family-volume normalizations cancel.  Thus the global Katz--Tao constant of
the genuine long-tube cover is uniformly bounded by two geometric copy
losses times the actual maximal concentration of the source family. -/
theorem plankLongTubeGlobalKatzTaoConstant_canonical_le
    (D : ShadedConvexPlankFamily iota a b)
    (hb : b ≤ (2 : NNReal)⁻¹)
    (hfamily0 : familyVolume D.family ≠ 0) :
    plankLongTubeGlobalKatzTaoConstant D
        (canonicalFrostmanConstant D.family D.ambient) ≤
      plankLongTubeFrostmanCopyLoss D.comparisonConstant a b ^ 2 *
        maximalConcentration D.family := by
  let R := plankLongTubeFrostmanCopyLoss D.comparisonConstant a b
  let sourceMass := familyVolume D.family
  let coverMass := familyVolume (plankLongTubeCoverFamily D).bodyFamily
  let ambientVolume := volume (D.ambient : Set Space)
  let thickVolume := volume (closedThickeningBody D.ambient 1 : Set Space)
  let Delta := maximalConcentration D.family
  have hsourceTop : sourceMass ≠ ∞ := by
    exact (familyVolume_lt_top D.family).ne
  have hambient0 : ambientVolume ≠ 0 := by
    exact ne_of_gt D.ambient_is_unit_scale.volume_pos
  have hambientTop : ambientVolume ≠ ∞ := by
    exact D.ambient.isCompact.measure_lt_top.ne
  have hthick0 : thickVolume ≠ 0 := by
    exact closedThickening_sourceAmbient_volume_ne_zero D
  have hthickTop : thickVolume ≠ ∞ := by
    exact closedThickening_sourceAmbient_volume_ne_top D
  have hcollapse :
      plankLongTubeGlobalKatzTaoConstant D
          (canonicalFrostmanConstant D.family D.ambient) * sourceMass =
        R * Delta * coverMass := by
    unfold plankLongTubeGlobalKatzTaoConstant
    unfold plankLongTubeThickenedAmbientLoss
    unfold canonicalFrostmanConstant
    unfold ambientFamilyVolumeDensity
    rw [containedMass_eq_familyVolume_of_contained
      D.family D.ambient D.contained_in_ambient]
    change
      (R * ((thickVolume / ambientVolume) *
          ((Delta * ambientVolume) / sourceMass)) *
        (coverMass / thickVolume)) * sourceMass =
        R * Delta * coverMass
    rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv]
    calc
      (R *
            (thickVolume * ambientVolume⁻¹ *
              (Delta * ambientVolume * sourceMass⁻¹)) *
          (coverMass * thickVolume⁻¹)) *
          sourceMass =
        R * Delta * coverMass *
          (ambientVolume⁻¹ * ambientVolume) *
          (sourceMass⁻¹ * sourceMass) *
          (thickVolume * thickVolume⁻¹) := by
        ac_rfl
      _ = R * Delta * coverMass := by
        rw [ENNReal.inv_mul_cancel hambient0 hambientTop,
          ENNReal.inv_mul_cancel hfamily0 hsourceTop,
          ENNReal.mul_inv_cancel hthick0 hthickTop]
        simp
  have hcover : coverMass ≤ R * sourceMass := by
    exact plankLongTubeCover_familyVolume_le_copyLoss_mul D hb
  have hscaled :
      plankLongTubeGlobalKatzTaoConstant D
          (canonicalFrostmanConstant D.family D.ambient) * sourceMass ≤
        (R ^ 2 * Delta) * sourceMass := by
    rw [hcollapse]
    calc
      R * Delta * coverMass ≤ R * Delta * (R * sourceMass) := by
        exact mul_le_mul' le_rfl hcover
      _ = (R ^ 2 * Delta) * sourceMass := by
        simp only [pow_two]
        ac_rfl
  have hscaled' :
      sourceMass * plankLongTubeGlobalKatzTaoConstant D
          (canonicalFrostmanConstant D.family D.ambient) ≤
        sourceMass * (R ^ 2 * Delta) := by
    simpa only [mul_comm] using hscaled
  exact (ENNReal.mul_le_mul_iff_right hfamily0 hsourceTop).mp hscaled'

#print axioms plankLongTubeCover_familyVolume_le_copyLoss_mul
#print axioms plankLongTubeGlobalKatzTaoConstant_canonical_le

end

end Family8PlankLongTubeCanonicalGlobalKatzTaoBoundV1
