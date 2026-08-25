import FamilyStickyGrounding.FamilyStickySharedTranslationPackingExistenceV1

open Set
open scoped NNReal

namespace FamilyStickySharedTranslationPackingNonemptyV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexGeometry.FrameBoxInducedCoveringGrowth

noncomputable section

/-!
# Nonemptiness of the canonical shared packing outcome type

The motion ball contains its center.  Therefore the maximal-net cover has at
least one center, and the subtype of packing centers used as the translation
outcome type has a genuine `Nonempty` instance.  This closes the small typeclass
bridge needed by the finite product-probability/Chernoff endpoint.
-/

theorem motionBallPackingCertificate_centers_nonempty
    {motionRadius mesh : NNReal}
    (C : PackingCertificate
      (Metric.closedBall (0 : Space) (motionRadius : Real)) mesh) :
    (↑C.centers : Set Space).Nonempty := by
  apply C.cover.nonempty
  exact ⟨0, by simp⟩

/-- The literal packing-center subtype is inhabited. -/
theorem motionBallPackingCertificate_translation_nonempty
    {motionRadius mesh : NNReal}
    (C : PackingCertificate
      (Metric.closedBall (0 : Space) (motionRadius : Real)) mesh) :
    Nonempty (↥C.centers) := by
  obtain ⟨v, hv⟩ := motionBallPackingCertificate_centers_nonempty C
  exact ⟨⟨v, hv⟩⟩

#print axioms motionBallPackingCertificate_centers_nonempty
#print axioms motionBallPackingCertificate_translation_nonempty

end


end FamilyStickySharedTranslationPackingNonemptyV1
