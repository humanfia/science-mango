import FamilyStickyGrounding.FamilyStickySharedTranslationPackingIncidenceV1

open Set
open scoped ENNReal NNReal

namespace FamilyStickySharedTranslationPackingExistenceV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexGeometry.FrameBoxInducedCoveringGrowth
open FamilyStickyActualTubeTranslationGridV1
open FamilyStickySharedTranslationPackingIncidenceV1
open FamilyStickySharedTranslationPackingIncidenceV1.ActualTubeTranslationGrid

noncomputable section

/-!
# A canonical finite shared packing of the motion ball

Faithful source provenance: the random vector in GWZ Section 7,
`lemrandommotion` (pinned source lines 1490--1498), is sampled from one ball
`B_rho`; Appendix lines 2655--2710 reuse that same vector for all tests.  This
module replaces that one continuous ball by a single finite maximal separated
set.  It does not make a test-indexed product of translation grids.

Mathlib's `maximalSeparatedSet` supplies all four geometric facts needed by
the finite model: finiteness, containment in `B_rho`, `2 * mesh` separation,
and a closed `2 * mesh` cover.  The adapter below changes only the translation
type of an existing actual grid; its tubes and test bodies are preserved
definitionally.  No incidence or probability conclusion is assumed here.
-/

/-- Total boundedness of a Euclidean closed ball makes its packing number
finite at every positive mesh. -/
theorem motionBall_packingNumber_two_mul_ne_top
    (motionRadius mesh : NNReal) (hmesh : 0 < mesh) :
    Metric.packingNumber (2 * mesh)
        (Metric.closedBall (0 : Space) (motionRadius : Real)) ≠ ⊤ := by
  have htot : TotallyBounded
      (Metric.closedBall (0 : Space) (motionRadius : Real)) :=
    (isCompact_closedBall (0 : Space) (motionRadius : Real)).totallyBounded
  obtain ⟨N, _hNsub, hNfinite, hNcover⟩ :=
    Metric.exists_finite_isCover_of_totallyBounded
      (ε := mesh) hmesh.ne' htot
  have hext_lt_top :
      Metric.externalCoveringNumber mesh
          (Metric.closedBall (0 : Space) (motionRadius : Real)) < ⊤ :=
    hNcover.externalCoveringNumber_le_encard.trans_lt
      hNfinite.encard_lt_top
  exact
    ((Metric.packingNumber_two_mul_le_externalCoveringNumber mesh
      (Metric.closedBall (0 : Space) (motionRadius : Real))).trans_lt
        hext_lt_top).ne

/-- The actual finite maximal packing/net of the motion ball. -/
theorem exists_motionBallPackingCertificate
    (motionRadius mesh : NNReal) (hmesh : 0 < mesh) :
    Nonempty
      (PackingCertificate
        (Metric.closedBall (0 : Space) (motionRadius : Real)) mesh) := by
  have hpack : Metric.packingNumber (2 * mesh)
      (Metric.closedBall (0 : Space) (motionRadius : Real)) ≠ ⊤ :=
    motionBall_packingNumber_two_mul_ne_top motionRadius mesh hmesh
  let S : Set Space := Metric.maximalSeparatedSet (2 * mesh)
    (Metric.closedBall (0 : Space) (motionRadius : Real))
  have hSfinite : S.Finite := by
    rw [← Set.encard_lt_top_iff]
    rw [show S.encard = Metric.packingNumber (2 * mesh)
        (Metric.closedBall (0 : Space) (motionRadius : Real)) by
      simpa [S] using Metric.encard_maximalSeparatedSet hpack]
    exact hpack.lt_top
  refine ⟨{
    centers := hSfinite.toFinset
    centers_subset := ?_
    separated := ?_
    cover := ?_ }⟩
  · simpa [S] using
      (Metric.maximalSeparatedSet_subset :
        Metric.maximalSeparatedSet (2 * mesh)
            (Metric.closedBall (0 : Space) (motionRadius : Real)) ⊆
          Metric.closedBall (0 : Space) (motionRadius : Real))
  · simpa [S] using
      (Metric.isSeparated_maximalSeparatedSet :
        Metric.IsSeparated (2 * mesh)
          (Metric.maximalSeparatedSet (2 * mesh)
            (Metric.closedBall (0 : Space) (motionRadius : Real)) :
              Set Space))
  · simpa [S] using Metric.isCover_maximalSeparatedSet hpack

namespace ActualTubeTranslationGrid

variable {delta : NNReal} {oldTranslation tubeIndex : Type*}
  [Fintype oldTranslation] [DecidableEq oldTranslation]
  [DecidableEq tubeIndex]

/-- Replace an arbitrary old translation type by the literal centers of a
motion-ball packing.  The tube/test data are unchanged. -/
def ofMotionBallPackingCertificate
    (G : ActualTubeTranslationGrid delta oldTranslation tubeIndex)
    {motionRadius mesh : NNReal}
    (C : PackingCertificate
      (Metric.closedBall (0 : Space) (motionRadius : Real)) mesh) :
    ActualTubeTranslationGrid delta (↥C.centers) tubeIndex where
  gridVector g := g.1
  tubes := G.tubes
  tube := G.tube
  testCard := G.testCard
  testBody := G.testBody
  activeTests := G.activeTests

@[simp] theorem ofMotionBallPackingCertificate_tubes
    (G : ActualTubeTranslationGrid delta oldTranslation tubeIndex)
    {motionRadius mesh : NNReal}
    (C : PackingCertificate
      (Metric.closedBall (0 : Space) (motionRadius : Real)) mesh) :
    (ofMotionBallPackingCertificate G C).tubes = G.tubes := rfl

@[simp] theorem ofMotionBallPackingCertificate_testBody
    (G : ActualTubeTranslationGrid delta oldTranslation tubeIndex)
    {motionRadius mesh : NNReal}
    (C : PackingCertificate
      (Metric.closedBall (0 : Space) (motionRadius : Real)) mesh)
    (K : Fin G.testCard) :
    (ofMotionBallPackingCertificate G C).testBody K = G.testBody K := rfl

/-- The packing-center adapter satisfies the complete shared-grid geometry
interface: positive mesh, injectivity, motion radius, separation, and cover. -/
theorem ofMotionBallPackingCertificate_isSharedTranslationPacking
    (G : ActualTubeTranslationGrid delta oldTranslation tubeIndex)
    {motionRadius mesh : NNReal} (hmesh : 0 < mesh)
    (C : PackingCertificate
      (Metric.closedBall (0 : Space) (motionRadius : Real)) mesh) :
    IsSharedTranslationPacking (ofMotionBallPackingCertificate G C)
      mesh motionRadius := by
  refine {
    mesh_pos := hmesh
    gridVector_injective := ?_
    gridVector_norm_le := ?_
    separated := ?_
    cover_motionBall := ?_ }
  · intro g h hgh
    exact Subtype.ext hgh
  · intro g
    change ‖(g.1 : Space)‖ <= (motionRadius : Real)
    have hg : (g.1 : Space) ∈
        Metric.closedBall (0 : Space) (motionRadius : Real) :=
      C.centers_subset g.2
    simpa [Metric.mem_closedBall, dist_zero_right] using hg
  · intro g h hgh
    apply C.separated g.2 h.2
    intro hval
    apply hgh
    exact Subtype.ext hval
  · have hrange :
        Set.range
            (ofMotionBallPackingCertificate G C).gridVector =
          (↑C.centers : Set Space) := by
      ext v
      constructor
      · rintro ⟨g, rfl⟩
        exact g.2
      · intro hv
        exact ⟨⟨v, hv⟩, rfl⟩
    rw [hrange]
    exact C.cover

/-- End-to-end producer for a finite actual grid representing one shared
translation sampled from the motion ball. -/
theorem exists_sharedTranslationPackingGrid
    (G : ActualTubeTranslationGrid delta oldTranslation tubeIndex)
    (motionRadius mesh : NNReal) (hmesh : 0 < mesh) :
    ∃ C : PackingCertificate
        (Metric.closedBall (0 : Space) (motionRadius : Real)) mesh,
      IsSharedTranslationPacking (ofMotionBallPackingCertificate G C)
        mesh motionRadius := by
  let C := Classical.choice
    (exists_motionBallPackingCertificate motionRadius mesh hmesh)
  exact ⟨C,
    ofMotionBallPackingCertificate_isSharedTranslationPacking G hmesh C⟩

#print axioms motionBall_packingNumber_two_mul_ne_top
#print axioms exists_motionBallPackingCertificate
#print axioms ofMotionBallPackingCertificate_isSharedTranslationPacking
#print axioms exists_sharedTranslationPackingGrid

end ActualTubeTranslationGrid

end

end FamilyStickySharedTranslationPackingExistenceV1
