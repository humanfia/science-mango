import Family8Grounding.Family8PlankLongTubeFrostmanTransferV3
import Family8Grounding.Family8FrostmanAmbientEnlargementV1
import FamilyStickyGrounding.FamilyStickyAdjacentTestBodyGeometryV1
import Submission.Kakeya.ConvexFactoring.BufferedHomotheticCore
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 5000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal InnerProductSpace

namespace Family8PlankLongTubeThickenedAmbientFrostmanV3

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.BufferedHomotheticCore
open Submission.Kakeya.Uniformity
open Family6AffinePlankAnalyticHypothesesStableV1
open Family8PlankThickControlCanonicalSeedNormalizationV3
open Family8PlankCertificateLongTubeCoverV2
open Family8PlankLongTubeFrostmanTransferV3
open Family8FrostmanAmbientEnlargementV1
open FamilyStickyAdjacentTestBodyGeometryV1

noncomputable section

universe u

variable {iota : Type u} [Fintype iota] [DecidableEq iota]
variable {a b : NNReal}

/-!
# Genuine long tubes in a common thickened ambient

The center of each certified source plank belongs to the source ambient.
Every point of its long axis is at distance at most `1/2` from that center,
and every point of the radius-`b` cover tube is a further distance at most
`b <= 1/2`. Hence the entire cover lives in the literal radius-one closed
thickening of the original ambient. This avoids any unproved ambient
monotonicity or abstract enlargement callback.

V1 and V2 were failed drafts and are not imported.
-/

/-- Every genuine long-tube cover member lies in the radius-one closed
thickening of the original ambient body. -/
theorem longTubeCover_subset_closedThickening_sourceAmbient
    (D : ShadedConvexPlankFamily iota a b)
    (hb : b ≤ (2 : NNReal)⁻¹) (i : iota) :
    ((plankLongTubeCoverFamily D).bodyFamily i : Set Space) ⊆
      (closedThickeningBody D.ambient 1 : Set Space) := by
  intro x hx
  let T := (plankLongTubeCoverFamily D).tubes i
  rw [UniformTubeFamily.bodyFamily, Tube.coe_body, Tube.carrier,
    T.axis.isCompact_carrier.cthickening_eq_biUnion_closedBall
      (show 0 ≤ (b : Real) by positivity)] at hx
  simp only [mem_iUnion, Metric.mem_closedBall] at hx
  obtain ⟨y, hyAxis, hxy⟩ := hx
  rw [T.axis.carrier_eq_image] at hyAxis
  obtain ⟨t, ht, rfl⟩ := hyAxis
  have htAbs : |t - (2 : Real)⁻¹| ≤ (2 : Real)⁻¹ := by
    rw [abs_le]
    constructor <;> norm_num at * <;> linarith [ht.1, ht.2]
  let cert := plankSeedCertificate D i
  have haxisVec :
      (T.axis.base + t • T.axis.direction) - cert.box.center =
        (t - (2 : Real)⁻¹) • cert.box.frame 2 := by
    simp only [T, plankLongTubeCoverFamily_tubes,
      plankCertificateLongTube, plankCertificateLongAxis, cert]
    module
  have hyCenter :
      dist (T.axis.base + t • T.axis.direction) cert.box.center ≤
        (2 : Real)⁻¹ := by
    rw [dist_eq_norm, haxisVec, norm_smul, cert.box.frame.norm_eq_one,
      mul_one]
    exact htAbs
  have hcenterSource : cert.box.center ∈ (D.family i : Set Space) := by
    exact certificateCenter_mem_body
      (plankSeedCertificate D i).toBoxDimensionsCertificate
  have hcenterAmbient : cert.box.center ∈ (D.ambient : Set Space) :=
    D.contained_in_ambient i hcenterSource
  have hxCenter : dist x cert.box.center ≤ 1 := by
    calc
      dist x cert.box.center ≤
          dist x (T.axis.base + t • T.axis.direction) +
            dist (T.axis.base + t • T.axis.direction) cert.box.center :=
        dist_triangle _ _ _
      _ ≤ (b : Real) + (2 : Real)⁻¹ := add_le_add hxy hyCenter
      _ ≤ 1 := by
        have hbR : (b : Real) ≤ (2 : Real)⁻¹ := by exact_mod_cast hb
        linarith
  simpa only [coe_closedThickening] using
    Metric.mem_cthickening_of_dist_le x cert.box.center
      ((1 : NNReal) : Real) (D.ambient : Set Space) hcenterAmbient hxCenter

/-- Exact loss for enlarging the source ambient to its radius-one closed
thickening. -/
def plankLongTubeThickenedAmbientLoss
    (D : ShadedConvexPlankFamily iota a b) : ENNReal :=
  volume (closedThickeningBody D.ambient 1 : Set Space) /
    volume (D.ambient : Set Space)

theorem thickenedAmbient_volume_le_loss_mul_sourceAmbient
    (D : ShadedConvexPlankFamily iota a b) :
    volume (closedThickeningBody D.ambient 1 : Set Space) ≤
      plankLongTubeThickenedAmbientLoss D *
        volume (D.ambient : Set Space) := by
  have hvolume0 : volume (D.ambient : Set Space) ≠ 0 :=
    ne_of_gt D.ambient_is_unit_scale.volume_pos
  have hvolumeTop : volume (D.ambient : Set Space) ≠ ∞ :=
    D.ambient.isCompact.measure_lt_top.ne
  rw [plankLongTubeThickenedAmbientLoss,
    ENNReal.div_mul_cancel hvolume0 hvolumeTop]

/-- The source Frostman certificate in the literal common thickened ambient. -/
theorem source_isFrostmanIn_closedThickening_sourceAmbient
    (D : ShadedConvexPlankFamily iota a b) {C : ENNReal}
    (hF : IsFrostmanIn C D.family D.ambient) :
    IsFrostmanIn (plankLongTubeThickenedAmbientLoss D * C)
      D.family (closedThickeningBody D.ambient 1) := by
  exact isFrostmanIn_enlarge_ambient hF
    (subset_closedThickening D.ambient 1)
    (thickenedAmbient_volume_le_loss_mul_sourceAmbient D)

/-- Callback-free Frostman certificate for the genuine long-tube cover in
the literal common thickened ambient. -/
theorem plankLongTubeCover_isFrostmanIn_thickenedAmbient
    (D : ShadedConvexPlankFamily iota a b)
    (hb : b ≤ (2 : NNReal)⁻¹) {C : ENNReal}
    (hF : IsFrostmanIn C D.family D.ambient) :
    IsFrostmanIn
      (plankLongTubeFrostmanCopyLoss D.comparisonConstant a b *
        (plankLongTubeThickenedAmbientLoss D * C))
      (plankLongTubeCoverFamily D).bodyFamily
      (closedThickeningBody D.ambient 1) := by
  exact isFrostmanIn_bodyCover
    (source_isFrostmanIn_closedThickening_sourceAmbient D hF)
    (sourcePlank_subset_longTubeCover D)
    (longTubeCover_volume_le_copyLoss_mul_source D hb)
    (longTubeCover_subset_closedThickening_sourceAmbient D hb)

#print axioms longTubeCover_subset_closedThickening_sourceAmbient
#print axioms thickenedAmbient_volume_le_loss_mul_sourceAmbient
#print axioms source_isFrostmanIn_closedThickening_sourceAmbient
#print axioms plankLongTubeCover_isFrostmanIn_thickenedAmbient

end
end Family8PlankLongTubeThickenedAmbientFrostmanV3
