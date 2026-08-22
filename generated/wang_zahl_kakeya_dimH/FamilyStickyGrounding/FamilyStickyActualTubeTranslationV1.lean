import Submission.Kakeya.ConvexGeometry.Tube
import Mathlib.Topology.MetricSpace.HausdorffDistance

open Set MeasureTheory
open scoped ENNReal NNReal Pointwise

namespace FamilyStickyActualTubeTranslationV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry

noncomputable section

/-!
# Actual translations of the repository's tube geometry

These definitions provide the geometric action used by the finite
translation-grid model.  Translation preserves the exact tube radius,
carrier, convex body, and Euclidean volume.
-/

/-- Translate the base point of a unit segment while keeping its direction. -/
def translateUnitSegment (S : UnitSegment) (v : Space) : UnitSegment where
  base := v + S.base
  direction := S.direction
  norm_direction := S.norm_direction

@[simp] theorem translateUnitSegment_base (S : UnitSegment) (v : Space) :
    (translateUnitSegment S v).base = v + S.base := rfl

@[simp] theorem translateUnitSegment_direction (S : UnitSegment) (v : Space) :
    (translateUnitSegment S v).direction = S.direction := rfl

@[simp] theorem translateUnitSegment_endpoint (S : UnitSegment) (v : Space) :
    (translateUnitSegment S v).endpoint = v + S.endpoint := by
  simp [translateUnitSegment, UnitSegment.endpoint, add_assoc]

/-- The translated segment carrier is the literal image under addition. -/
theorem translateUnitSegment_carrier (S : UnitSegment) (v : Space) :
    (translateUnitSegment S v).carrier = (fun x => v + x) '' S.carrier := by
  simpa [UnitSegment.carrier, translateUnitSegment_endpoint] using
    (segment_translate_image ℝ v S.base S.endpoint).symm

/-- Closed metric thickening commutes with translation by an ambient vector. -/
theorem cthickening_translate (s : Set Space) (v : Space) (r : Real) :
    Metric.cthickening r ((fun x => v + x) '' s) =
      (fun x => v + x) '' Metric.cthickening r s := by
  change Metric.cthickening r (v +ᵥ s) =
    v +ᵥ Metric.cthickening r s
  ext x
  rw [Metric.mem_cthickening_iff,
    Set.mem_vadd_set_iff_neg_vadd_mem,
    Metric.mem_cthickening_iff]
  simp only [← Metric.infEDist_vadd v (-v +ᵥ x) s,
    vadd_vadd, add_neg_cancel, zero_vadd]

/-- Translate a tube without changing its radius or direction. -/
def translateTube {delta : NNReal} (T : Tube delta) (v : Space) :
    Tube delta where
  axis := translateUnitSegment T.axis v

/-- The actual translated tube carrier is the image of the original carrier. -/
theorem translateTube_carrier {delta : NNReal} (T : Tube delta) (v : Space) :
    (translateTube T v).carrier = (fun x => v + x) '' T.carrier := by
  unfold Tube.carrier translateTube
  rw [translateUnitSegment_carrier]
  exact cthickening_translate T.axis.carrier v delta

/-- Translation also transports the associated convex body exactly. -/
theorem translateTube_coe_body {delta : NNReal} (T : Tube delta) (v : Space) :
    ((translateTube T v).body : Set Space) = (fun x => v + x) '' T.carrier := by
  rw [Tube.coe_body, translateTube_carrier]

/-- Euclidean volume of an actual tube is translation invariant. -/
theorem translateTube_volume {delta : NNReal} (T : Tube delta) (v : Space) :
    volume (translateTube T v).carrier = volume T.carrier := by
  rw [translateTube_carrier]
  change volume (v +ᵥ T.carrier) = volume T.carrier
  exact MeasureTheory.measure_vadd volume v T.carrier

#print axioms translateUnitSegment_carrier
#print axioms cthickening_translate
#print axioms translateTube_carrier
#print axioms translateTube_coe_body
#print axioms translateTube_volume

end

end FamilyStickyActualTubeTranslationV1
