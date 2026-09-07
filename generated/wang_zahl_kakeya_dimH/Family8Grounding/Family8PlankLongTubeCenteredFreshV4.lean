import Family8Grounding.Family8PlankLongTubeGlobalKatzTaoV3
import Family8Grounding.Family8PlankLongTubeAmbientB2SupportV3
import Family8Grounding.Family8B2NormalizedConflictKatzTaoCapV6
import Family8Grounding.Family8FiniteRandomRigidMotionPaperFixedJohnCopyTransportCoreV1
import Family8Grounding.Family8FiniteRandomRigidMotionPaperFixedJohnFreshSelectionV2
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 5000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8PlankLongTubeCenteredFreshV4

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family6AffinePlankAnalyticHypothesesStableV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8GeneralizedFrostmanMultiplicityV1
open Family8GeneralizedKatzTaoMultiplicityV1
open Family8FiniteRandomRigidMotionIncidenceV1
open Family8FiniteRandomRigidMotionB2NormalizedDatumV1
open Family8FiniteRandomRigidMotionB2FreshGreedyV1
open Family8FiniteRandomRigidMotionPaperFixedJohnCopyTransportCoreV1
open Family8FiniteRandomRigidMotionPaperFixedJohnFreshSelectionV2
open Family8B2NormalizedConflictKatzTaoCapV6
open Family8PlankCertificateLongTubeCoverV2
open Family8PlankLongTubeAmbientB2SupportV3
open Family8PlankLongTubeFrostmanTransferV3
open Family8PlankLongTubeThickenedAmbientFrostmanV3
open Family8PlankLongTubeGlobalKatzTaoV3
open Family8AmbientFamilyVolumeDensityV2
open FamilyStickyAdjacentTestBodyGeometryV1

noncomputable section

variable {iota : Type} [Fintype iota] [Nonempty iota] [DecidableEq iota]
variable {a b : NNReal}

/-!
# Centered fresh long-tube datum from actual plank Frostman data

The source plank shading is first retyped against its genuine long-tube
cover. A single actual translation moves the common B2 center to the origin.
The callback-free global Katz--Tao estimate then controls the normalized
conflict graph, and fresh greedy selection manufactures pairwise essential
distinctness on one retained subtype. No source admissibility is assumed.

V1--V3 were failed drafts and are not imported.
-/

/-- The genuine same-index long-tube cover packaged as an actual datum. -/
def plankLongTubeActualDatum
    (D : ShadedConvexPlankFamily iota a b) : ActualTubeDatum b iota where
  family := plankLongTubeCoverFamily D
  shading := plankLongTubeCoverShading D

/-- One translated copy, centered at the selected unit-scale ambient box. -/
def centeredPlankLongTubeActualDatum
    (D : ShadedConvexPlankFamily iota a b) :
    ActualTubeDatum b (Unit × iota) :=
  indexedRigidCopyDatum
    (fun _ : Unit ↦
      translationRigidMotion (-(ambientPlankCertificate D).box.center))
    (plankLongTubeActualDatum D)

/-- The centered source datum has the B2 support required by the canonical
eighth-normalization. -/
theorem centeredPlankLongTubeActualDatum_B2
    (D : ShadedConvexPlankFamily iota a b)
    (hb : b ≤ (2 : NNReal)⁻¹) :
    ∀ p : Unit × iota,
      ((centeredPlankLongTubeActualDatum D).family.tubes p).carrier ⊆
        Metric.closedBall (0 : Space) 2 := by
  intro p x hx
  let R := translationRigidMotion (-(ambientPlankCertificate D).box.center)
  change x ∈
    (rigidTube R ((plankLongTubeCoverFamily D).tubes p.2)).carrier at hx
  rw [rigidTube_carrier] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  have hraw :=
    longTubeCover_subset_closedBall_ambientCenter_two D hb p.2 hy
  rw [Metric.mem_closedBall] at hraw ⊢
  simpa [R, translationRigidMotion_apply, dist_eq_norm, sub_eq_add_neg,
    add_comm, add_left_comm, add_assoc] using hraw

/-- The explicit global long-tube Katz--Tao constant is finite whenever the
source Frostman constant is finite. -/
theorem plankLongTubeGlobalKatzTaoConstant_ne_top
    (D : ShadedConvexPlankFamily iota a b) {C : ENNReal}
    (hCfinite : C ≠ ∞) :
    plankLongTubeGlobalKatzTaoConstant D C ≠ ∞ := by
  have hsourceVolume0 : volume (D.ambient : Set Space) ≠ 0 :=
    ne_of_gt D.ambient_is_unit_scale.volume_pos
  have hcopyLoss :
      plankLongTubeFrostmanCopyLoss D.comparisonConstant a b ≠ ∞ := by
    unfold plankLongTubeFrostmanCopyLoss
    exact ENNReal.coe_ne_top
  have hthickLoss : plankLongTubeThickenedAmbientLoss D ≠ ∞ := by
    unfold plankLongTubeThickenedAmbientLoss
    exact ENNReal.div_ne_top
      (closedThickening_sourceAmbient_volume_ne_top D)
      hsourceVolume0
  have hambientDensity :
      ambientFamilyVolumeDensity
        (plankLongTubeCoverFamily D).bodyFamily
        (closedThickeningBody D.ambient 1) ≠ ∞ :=
    ambientFamilyVolumeDensity_ne_top _ _
      (closedThickening_sourceAmbient_volume_ne_zero D)
  unfold plankLongTubeGlobalKatzTaoConstant
  exact ENNReal.mul_ne_top
    (ENNReal.mul_ne_top hcopyLoss
      (ENNReal.mul_ne_top hthickLoss hCfinite))
    hambientDensity

/-- The global Katz--Tao estimate transports exactly through the single
centering translation. -/
theorem centeredPlankLongTubeActualDatum_isKatzTao
    (D : ShadedConvexPlankFamily iota a b)
    (hb : b ≤ (2 : NNReal)⁻¹) {C : ENNReal}
    (hF : IsFrostmanIn C D.family D.ambient) :
    IsKatzTao (plankLongTubeGlobalKatzTaoConstant D C)
      (centeredPlankLongTubeActualDatum D).family.bodyFamily := by
  let motion : Unit → RigidMotion := fun _ ↦
    translationRigidMotion (-(ambientPlankCertificate D).box.center)
  have hsource :
      IsKatzTao (plankLongTubeGlobalKatzTaoConstant D C)
        (plankLongTubeActualDatum D).family.bodyFamily := by
    simpa only [plankLongTubeActualDatum] using
      plankLongTubeCover_isKatzTao D hb hF
  have hcopy := indexedRigidCopyTubeFamily_isKatzTao_card_mul
    motion (plankLongTubeActualDatum D).family hsource
  change IsKatzTao (plankLongTubeGlobalKatzTaoConstant D C)
    (indexedRigidCopyTubeFamily motion
      (plankLongTubeActualDatum D).family).bodyFamily
  simpa only [Fintype.card_unit, Nat.cast_one, one_mul] using hcopy

/-- Fresh admissible normalized subtype on the same centered datum. The
output retains the exact greedy card, mass, Katz--Tao, and source-average
inequalities used downstream. -/
theorem exists_centeredPlankLongTube_fresh_admissible
    (D : ShadedConvexPlankFamily iota a b)
    (hbPos : 0 < b) (hbHalf : b ≤ (2 : NNReal)⁻¹)
    {C : ENNReal} (hCfinite : C ≠ ∞)
    (hF : IsFrostmanIn C D.family D.ambient) :
    let source := centeredPlankLongTubeActualDatum D
    let Csource := plankLongTubeGlobalKatzTaoConstant D C
    let threshold := Nat.ceil ((480000 * (128 * Csource) : ENNReal).toReal)
    ∃ selected : Finset (Unit × iota),
      selected.Nonempty ∧
      (restrictActualTubeDatum
        (eighthNormalizedDatum source) selected).IsAdmissible ∧
      (Fintype.card (Unit × iota) : ENNReal) ≤
        (threshold + 1 : Nat) * (selected.card : ENNReal) ∧
      (eighthNormalizedDatum source).shading.shadingMass ≤
        (threshold + 1 : Nat) *
          (restrictActualTubeDatum
            (eighthNormalizedDatum source) selected).shading.shadingMass ∧
      IsKatzTao (128 * Csource)
        (restrictActualTubeDatum
          (eighthNormalizedDatum source) selected).family.bodyFamily ∧
      D.shading.averageMultiplicity ≤
        (threshold + 1 : Nat) *
          (restrictActualTubeDatum
            (eighthNormalizedDatum source) selected).shading.averageMultiplicity := by
  dsimp only
  let source := centeredPlankLongTubeActualDatum D
  let Csource := plankLongTubeGlobalKatzTaoConstant D C
  let threshold := Nat.ceil ((480000 * (128 * Csource) : ENNReal).toReal)
  have hCsourceFinite : Csource ≠ ∞ :=
    plankLongTubeGlobalKatzTaoConstant_ne_top D hCfinite
  have hsourceKT : IsKatzTao Csource source.family.bodyFamily := by
    exact centeredPlankLongTubeActualDatum_isKatzTao D hbHalf hF
  have hconflict : ∀ p,
      (normalizedConflictIndices source p).card ≤ threshold := by
    intro p
    exact normalizedConflictIndices_card_le_sourceFixedKatzTaoNatCap
      source hbPos hbHalf hCsourceFinite hsourceKT p
  obtain ⟨selected, hselected, hadmissible, hcard, hmass,
      hselectedKT, hcenteredAverage⟩ :=
    exists_normalized_refinement_admissible_isKatzTao_of_scale_B2
      source hbPos hbHalf
      (centeredPlankLongTubeActualDatum_B2 D hbHalf)
      hconflict hsourceKT
  refine ⟨selected, hselected, hadmissible, hcard, hmass,
    hselectedKT, ?_⟩
  have hsourceCentered :
      D.shading.averageMultiplicity ≤ source.shading.averageMultiplicity := by
    let motion : Unit → RigidMotion := fun _ ↦
      translationRigidMotion (-(ambientPlankCertificate D).box.center)
    have hcopy := source_averageMultiplicity_le_indexedRigidCopy
      motion (plankLongTubeActualDatum D).family
        (plankLongTubeActualDatum D).shading
    simpa only [source, centeredPlankLongTubeActualDatum,
      indexedRigidCopyDatum, plankLongTubeActualDatum,
      plankLongTubeCoverShading_averageMultiplicity] using hcopy
  exact hsourceCentered.trans hcenteredAverage

#print axioms centeredPlankLongTubeActualDatum_B2
#print axioms plankLongTubeGlobalKatzTaoConstant_ne_top
#print axioms centeredPlankLongTubeActualDatum_isKatzTao
#print axioms exists_centeredPlankLongTube_fresh_admissible

end
end Family8PlankLongTubeCenteredFreshV4
