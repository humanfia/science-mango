import Family8Grounding.Family8PlankLongTubeThickenedAmbientFrostmanV3
import Family8Grounding.Family8AmbientFamilyVolumeDensityV2
import Mathlib.Tactic

/-!
# Global Katz--Tao control for the genuine long-tube cover

The callback-free Frostman certificate in the actual thickened source
ambient is combined with its literal family-volume density.  This produces
the raw global Katz--Tao estimate consumed by normalized conflict counting
and fresh greedy extraction.  V1 and V2 were mechanical drafts and are not
imported.
-/

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8PlankLongTubeGlobalKatzTaoV3

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.BufferedHomotheticCore
open Family6AffinePlankAnalyticHypothesesStableV1
open Family8AmbientFamilyVolumeDensityV2
open Family8PlankCertificateLongTubeCoverV2
open Family8PlankLongTubeFrostmanTransferV3
open Family8PlankLongTubeThickenedAmbientFrostmanV3
open FamilyStickyAdjacentTestBodyGeometryV1

noncomputable section

set_option autoImplicit false
set_option warningAsError true

universe u

variable {iota : Type u} [Fintype iota] [DecidableEq iota]
variable {a b : NNReal}

theorem closedThickening_sourceAmbient_volume_ne_zero
    (D : ShadedConvexPlankFamily iota a b) :
    volume (closedThickeningBody D.ambient 1 : Set Space) ≠ 0 := by
  have hmono : volume (D.ambient : Set Space) ≤
      volume (closedThickeningBody D.ambient 1 : Set Space) :=
    measure_mono (subset_closedThickening D.ambient 1)
  exact ne_of_gt (D.ambient_is_unit_scale.volume_pos.trans_le hmono)

theorem closedThickening_sourceAmbient_volume_ne_top
    (D : ShadedConvexPlankFamily iota a b) :
    volume (closedThickeningBody D.ambient 1 : Set Space) ≠ ∞ :=
  (closedThickeningBody D.ambient 1).isCompact.measure_lt_top.ne

def plankLongTubeGlobalKatzTaoConstant
    (D : ShadedConvexPlankFamily iota a b) (C : ENNReal) : ENNReal :=
  (plankLongTubeFrostmanCopyLoss D.comparisonConstant a b *
      (plankLongTubeThickenedAmbientLoss D * C)) *
    ambientFamilyVolumeDensity
      (plankLongTubeCoverFamily D).bodyFamily
      (closedThickeningBody D.ambient 1)

/-- Actual ambient Frostman data produces global Katz--Tao control of the
same genuine long-tube cover, without an ambient-mass premise. -/
theorem plankLongTubeCover_isKatzTao
    (D : ShadedConvexPlankFamily iota a b)
    (hb : b ≤ (2 : NNReal)⁻¹) {C : ENNReal}
    (hF : IsFrostmanIn C D.family D.ambient) :
    IsKatzTao (plankLongTubeGlobalKatzTaoConstant D C)
      (plankLongTubeCoverFamily D).bodyFamily := by
  unfold plankLongTubeGlobalKatzTaoConstant
  exact isKatzTao_of_isFrostmanIn_familyVolumeDensity
    (plankLongTubeCover_isFrostmanIn_thickenedAmbient D hb hF)
    (closedThickening_sourceAmbient_volume_ne_zero D)
    (closedThickening_sourceAmbient_volume_ne_top D)

#print axioms closedThickening_sourceAmbient_volume_ne_zero
#print axioms closedThickening_sourceAmbient_volume_ne_top
#print axioms plankLongTubeCover_isKatzTao

end

end Family8PlankLongTubeGlobalKatzTaoV3
