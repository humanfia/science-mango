import FamilyStickyGrounding.FamilyStickyActualTubeTranslationGridV1
import Submission.Kakeya.ConvexFactoring.FrameBoxInducedCoveringGrowth
import Submission.Kakeya.ConvexFactoring.FrameBoxThickening

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace FamilyStickySharedTranslationPackingIncidenceV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexGeometry.FrameBoxInducedCoveringGrowth
open FamilyStickyActualTubeTranslationGridV1

noncomputable section

/-!
# One shared finite translation packing

Faithful source provenance: in GWZ `lemrandommotion` (Section 7, lines
1490--1498 of the pinned source) each repetition is one translation vector
chosen from `B_rho`.  In the appendix proof (lines 2655--2710), the same
translation is tested against every tube and every convex test set; those
tests enter only through a union bound.  They do not contribute separate
translation coordinates.

Accordingly this module uses one finite outcome type.  Its vectors lie in the
motion ball, are separated at scale `2 * mesh`, and cover that same ball at
scale `2 * mesh`.  For a fixed target subset of a `FrameBox`, the hit vectors
remain separated.  Disjoint mesh-balls and the proved FrameBox thickening
volume bound give the literal incidence inequality

`#hits • volume(B_mesh) <= prod_i (side_i + 2*mesh)`.

No test-indexed product grid and no probability conclusion occur here.
-/

namespace ActualTubeTranslationGrid

variable {delta : NNReal} {translation tubeIndex : Type*}
  [Fintype translation] [DecidableEq translation]
  [DecidableEq tubeIndex]

/-- Geometric certificate for one shared finite net in the motion ball. -/
structure IsSharedTranslationPacking
    (G : ActualTubeTranslationGrid delta translation tubeIndex)
    (mesh motionRadius : NNReal) : Prop where
  mesh_pos : 0 < mesh
  gridVector_injective : Function.Injective G.gridVector
  gridVector_norm_le : forall g, ‖G.gridVector g‖ <= (motionRadius : Real)
  separated : forall {g h : translation}, g ≠ h ->
    ((2 * mesh : NNReal) : ENNReal) < edist (G.gridVector g) (G.gridVector h)
  cover_motionBall : Metric.IsCover (2 * mesh)
    (Metric.closedBall (0 : Space) (motionRadius : Real))
    (Set.range G.gridVector)

namespace IsSharedTranslationPacking

variable {G : ActualTubeTranslationGrid delta translation tubeIndex}
  {mesh motionRadius : NNReal}

/-- The finite shared grid centers. -/
def gridCenters
    (_P : IsSharedTranslationPacking G mesh motionRadius) : Finset Space :=
  Finset.univ.image G.gridVector

theorem card_gridCenters
    (P : IsSharedTranslationPacking G mesh motionRadius) :
    P.gridCenters.card = Fintype.card translation := by
  rw [gridCenters, Finset.card_image_of_injective _ P.gridVector_injective]
  simp

/-- The shared net itself is a packing certificate for the motion ball. -/
def motionBallPackingCertificate
    (P : IsSharedTranslationPacking G mesh motionRadius) :
    PackingCertificate
      (Metric.closedBall (0 : Space) (motionRadius : Real)) mesh where
  centers := P.gridCenters
  centers_subset := by
    intro v hv
    change v ∈ P.gridCenters at hv
    obtain ⟨g, _hg, rfl⟩ := Finset.mem_image.mp hv
    rw [Metric.mem_closedBall, dist_zero_right]
    exact P.gridVector_norm_le g
  separated := by
    intro v hv w hw hvw
    change v ∈ P.gridCenters at hv
    change w ∈ P.gridCenters at hw
    obtain ⟨g, _hg, rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨h, _hh, rfl⟩ := Finset.mem_image.mp hw
    apply P.separated
    intro hgh
    apply hvw
    exact congrArg G.gridVector hgh
  cover := by
    simpa only [gridCenters, Finset.coe_image, Finset.coe_univ,
      Set.image_univ] using P.cover_motionBall

/-- A finite `2*mesh` cover yields the needed lower bound on the number of
shared outcomes, with open balls of radius `3*mesh`. -/
theorem volume_motionBall_le_card_smul_ballVolume_three
    (P : IsSharedTranslationPacking G mesh motionRadius) :
    volume (Metric.closedBall (0 : Space) (motionRadius : Real)) <=
      Fintype.card translation •
        volume (Metric.ball (0 : Space) ((3 * mesh : NNReal) : Real)) := by
  let C := P.motionBallPackingCertificate
  calc
    volume (Metric.closedBall (0 : Space) (motionRadius : Real)) <=
        volume (⋃ v ∈ C.centers,
          Metric.ball v ((3 * mesh : NNReal) : Real)) :=
      measure_mono (C.subset_iUnion_largeBalls P.mesh_pos)
    _ <= ∑ v ∈ C.centers,
        volume (Metric.ball v ((3 * mesh : NNReal) : Real)) :=
      measure_biUnion_finset_le C.centers _
    _ = C.centers.card •
        volume (Metric.ball (0 : Space) ((3 * mesh : NNReal) : Real)) := by
      simp [InnerProductSpace.volume_ball]
    _ = Fintype.card translation •
        volume (Metric.ball (0 : Space) ((3 * mesh : NNReal) : Real)) := by
      rw [show C.centers.card = Fintype.card translation by
        exact P.card_gridCenters]

/-- Outcomes whose translated reference point lands in `A`. -/
def pointHits
    (_P : IsSharedTranslationPacking G mesh motionRadius)
    (A : Set Space) (x : Space) : Finset translation := by
  classical
  exact Finset.univ.filter fun g => G.gridVector g + x ∈ A

/-- Actual landed points of the hit outcomes. -/
def pointHitCenters
    (P : IsSharedTranslationPacking G mesh motionRadius)
    (A : Set Space) (x : Space) : Finset Space :=
  (P.pointHits A x).image fun g => G.gridVector g + x

theorem card_pointHitCenters
    (P : IsSharedTranslationPacking G mesh motionRadius)
    (A : Set Space) (x : Space) :
    (P.pointHitCenters A x).card = (P.pointHits A x).card := by
  rw [pointHitCenters]
  apply Finset.card_image_of_injective
  intro g h hgh
  apply P.gridVector_injective
  exact add_right_cancel hgh

/-- The landed hit points form a packing certificate for their own finite
set.  The cover field is tautological; separation is inherited from the one
shared grid. -/
def pointHitPackingCertificate
    (P : IsSharedTranslationPacking G mesh motionRadius)
    (A : Set Space) (x : Space) :
    PackingCertificate (↑(P.pointHitCenters A x) : Set Space) mesh where
  centers := P.pointHitCenters A x
  centers_subset := fun _ hv => hv
  separated := by
    intro v hv w hw hvw
    change v ∈ P.pointHitCenters A x at hv
    change w ∈ P.pointHitCenters A x at hw
    obtain ⟨g, _hg, rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨h, _hh, rfl⟩ := Finset.mem_image.mp hw
    rw [edist_add_right]
    apply P.separated
    intro hgh
    apply hvw
    rw [hgh]
  cover := by
    rw [Metric.isCover_iff_subset_iUnion_closedBall]
    intro v hv
    exact Set.mem_iUnion.mpr ⟨v,
      Set.mem_iUnion.mpr ⟨hv, by simp⟩⟩

theorem pointHitCenters_subset
    (P : IsSharedTranslationPacking G mesh motionRadius)
    {A : Set Space} {B : FrameBox} (hA : A ⊆ B.carrier) (x : Space) :
    (↑(P.pointHitCenters A x) : Set Space) ⊆ B.carrier := by
  intro v hv
  change v ∈ P.pointHitCenters A x at hv
  obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp hv
  have hgA : G.gridVector g + x ∈ A := by
    classical
    simpa [pointHits] using hg
  exact hA hgA

/-- Shared-grid incidence bound for an arbitrary target inside one actual
oriented box. -/
theorem card_pointHits_nsmul_ballVolume_le_widenedBox
    (P : IsSharedTranslationPacking G mesh motionRadius)
    (A : Set Space) (B : FrameBox) (hA : A ⊆ B.carrier) (x : Space) :
    (P.pointHits A x).card •
        volume (Metric.ball (0 : Space) (mesh : Real)) <=
      ∏ i, ((B.side i : ENNReal) + 2 * (mesh : ENNReal)) := by
  let C := P.pointHitPackingCertificate A x
  calc
    (P.pointHits A x).card •
        volume (Metric.ball (0 : Space) (mesh : Real)) =
      C.centers.card •
        volume (Metric.ball (0 : Space) (mesh : Real)) := by
          rw [show C.centers.card = (P.pointHits A x).card by
            exact P.card_pointHitCenters A x]
    _ <= volume (Metric.thickening (mesh : Real)
        (↑(P.pointHitCenters A x) : Set Space)) :=
      C.card_smul_ballVolume_le_thickening
    _ <= ∏ i, ((B.side i : ENNReal) + 2 * (mesh : ENNReal)) :=
      B.volume_thickening_le_prod_side_add_two_mul _
        (P.pointHitCenters_subset hA x) mesh

#print axioms card_gridCenters
#print axioms motionBallPackingCertificate
#print axioms volume_motionBall_le_card_smul_ballVolume_three
#print axioms card_pointHitCenters
#print axioms pointHitPackingCertificate
#print axioms card_pointHits_nsmul_ballVolume_le_widenedBox

end IsSharedTranslationPacking

end ActualTubeTranslationGrid

end

end FamilyStickySharedTranslationPackingIncidenceV1
