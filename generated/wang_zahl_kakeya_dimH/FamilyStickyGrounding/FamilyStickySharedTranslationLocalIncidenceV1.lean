import FamilyStickyGrounding.FamilyStickySharedTranslationPackingIncidenceV1
import FamilyStickyGrounding.FamilyStickyFrameBoxAxialThickeningV1

open Set MeasureTheory
open scoped ENNReal NNReal

namespace FamilyStickySharedTranslationLocalIncidenceV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexGeometry.FrameBoxInducedCoveringGrowth
open FamilyStickyActualTubeTranslationGridV1
open FamilyStickySharedTranslationPackingIncidenceV1.ActualTubeTranslationGrid
open FamilyStickySharedTranslationPackingIncidenceV1.ActualTubeTranslationGrid.IsSharedTranslationPacking
open FamilyStickyFrameBoxAxialThickeningV1.FrameBox

noncomputable section

/-!
# Local incidence for one shared translation packing

For the shared random vector of GWZ Appendix Section 7, every landed reference
point `gridVector g + x` lies in `closedBall x rho`.  Combining that literal
fact with the two-short-axis window gives the packing estimate

`#hits * vol(B_mesh) <= (side0+2mesh)(side1+2mesh) 2(rho+mesh)`.

This is the local `k_1 k_2 rho` geometry needed by the paper.  It is strictly
sharper in the long direction than the earlier full widened-box experiment.
-/

variable {delta : NNReal} {translation tubeIndex : Type*}
  [Fintype translation] [DecidableEq translation]
  [DecidableEq tubeIndex]
  {G : ActualTubeTranslationGrid delta translation tubeIndex}
  {mesh motionRadius : NNReal}

/-- Every landed point of a shared hit lies in the motion ball centered at
the untranslated reference point. -/
theorem pointHitCenters_subset_motionBall
    (P : IsSharedTranslationPacking G mesh motionRadius)
    (A : Set Space) (x : Space) :
    (↑(P.pointHitCenters A x) : Set Space) ⊆
      Metric.closedBall x (motionRadius : Real) := by
  intro y hy
  change y ∈ P.pointHitCenters A x at hy
  obtain ⟨g, _hg, rfl⟩ := Finset.mem_image.mp hy
  rw [Metric.mem_closedBall]
  simpa [dist_eq_norm] using P.gridVector_norm_le g

/-- Faithful local incidence estimate: the first two axes come from the test
box, while the third is truncated by the one shared motion ball. -/
theorem card_pointHits_nsmul_ballVolume_le_axialCap
    (P : IsSharedTranslationPacking G mesh motionRadius)
    (A : Set Space) (B : FrameBox) (hA : A ⊆ B.carrier) (x : Space) :
    (P.pointHits A x).card •
        volume (Metric.ball (0 : Space) (mesh : Real)) ≤
      ((B.side 0 : ENNReal) + 2 * (mesh : ENNReal)) *
        ((B.side 1 : ENNReal) + 2 * (mesh : ENNReal)) *
          (2 * ((motionRadius : ENNReal) + (mesh : ENNReal))) := by
  let C := P.pointHitPackingCertificate A x
  calc
    (P.pointHits A x).card •
        volume (Metric.ball (0 : Space) (mesh : Real)) =
      C.centers.card •
        volume (Metric.ball (0 : Space) (mesh : Real)) := by
          rw [show C.centers.card = (P.pointHits A x).card by
            exact P.card_pointHitCenters A x]
    _ ≤ volume (Metric.thickening (mesh : Real)
        (↑(P.pointHitCenters A x) : Set Space)) :=
      C.card_smul_ballVolume_le_thickening
    _ ≤ ((B.side 0 : ENNReal) + 2 * (mesh : ENNReal)) *
          ((B.side 1 : ENNReal) + 2 * (mesh : ENNReal)) *
            (2 * ((motionRadius : ENNReal) + (mesh : ENNReal))) :=
      volume_thickening_le_axialCap B
        (↑(P.pointHitCenters A x) : Set Space) x motionRadius mesh
        (P.pointHitCenters_subset hA x)
        (pointHitCenters_subset_motionBall P A x)

#print axioms pointHitCenters_subset_motionBall
#print axioms card_pointHits_nsmul_ballVolume_le_axialCap

end


end FamilyStickySharedTranslationLocalIncidenceV1
