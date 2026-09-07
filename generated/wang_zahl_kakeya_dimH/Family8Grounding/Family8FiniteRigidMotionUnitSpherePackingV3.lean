import Family8Grounding.Family8FiniteRigidMotionDirectionTranslationSupportV1
import Family8Grounding.Family8SphereDirectionPackingV1
import FamilyStickyGrounding.FamilyStickySharedTranslationPackingExistenceV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators InnerProductSpace

namespace Family8FiniteRigidMotionUnitSpherePackingV3

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexGeometry.FrameBoxInducedCoveringGrowth
open Family8SphereDirectionPackingV1

noncomputable section

/-!
# A genuine finite direction law on the unit sphere

The fixed-John construction needs rotations as well as translations.  This
module supplies the direction component without a conclusion-valued callback:
it is the literal maximal separated set on the Euclidean unit sphere.  Its
centres are unit vectors, are separated at twice the mesh, and cover every
unit direction at that scale.  The existing sphere-volume argument gives the
correct dimension-two upper cardinality.
-/

def unitDirectionSphere : Set Space :=
  Metric.sphere (0 : Space) 1

theorem mem_unitDirectionSphere_iff_norm_eq_one (v : Space) :
    v ∈ unitDirectionSphere ↔ ‖v‖ = 1 := by
  simp [unitDirectionSphere]

theorem unitDirectionSphere_packingNumber_two_mul_ne_top
    (mesh : NNReal) (hmesh : 0 < mesh) :
    Metric.packingNumber (2 * mesh) unitDirectionSphere ≠ ⊤ := by
  have htot : TotallyBounded unitDirectionSphere :=
    (isCompact_sphere (0 : Space) 1).totallyBounded
  obtain ⟨N, _hNsub, hNfinite, hNcover⟩ :=
    Metric.exists_finite_isCover_of_totallyBounded
      (ε := mesh) hmesh.ne' htot
  have hext_lt_top :
      Metric.externalCoveringNumber mesh unitDirectionSphere < ⊤ :=
    hNcover.externalCoveringNumber_le_encard.trans_lt
      hNfinite.encard_lt_top
  exact
    ((Metric.packingNumber_two_mul_le_externalCoveringNumber mesh
      unitDirectionSphere).trans_lt hext_lt_top).ne

theorem exists_unitDirectionSpherePackingCertificate
    (mesh : NNReal) (hmesh : 0 < mesh) :
    Nonempty (PackingCertificate unitDirectionSphere mesh) := by
  have hpack : Metric.packingNumber (2 * mesh) unitDirectionSphere ≠ ⊤ :=
    unitDirectionSphere_packingNumber_two_mul_ne_top mesh hmesh
  let S : Set Space :=
    Metric.maximalSeparatedSet (2 * mesh) unitDirectionSphere
  have hSfinite : S.Finite := by
    rw [← Set.encard_lt_top_iff]
    rw [show S.encard =
        Metric.packingNumber (2 * mesh) unitDirectionSphere by
      simpa [S] using Metric.encard_maximalSeparatedSet hpack]
    exact hpack.lt_top
  refine ⟨{
    centers := hSfinite.toFinset
    centers_subset := ?_
    separated := ?_
    cover := ?_ }⟩
  · simpa [S] using
      (Metric.maximalSeparatedSet_subset :
        Metric.maximalSeparatedSet (2 * mesh) unitDirectionSphere ⊆
          unitDirectionSphere)
  · simpa [S] using
      (Metric.isSeparated_maximalSeparatedSet :
        Metric.IsSeparated (2 * mesh)
          (Metric.maximalSeparatedSet (2 * mesh)
            unitDirectionSphere : Set Space))
  · simpa [S] using Metric.isCover_maximalSeparatedSet hpack

def unitDirectionSpherePackingCertificate
    (mesh : NNReal) (hmesh : 0 < mesh) :
    PackingCertificate unitDirectionSphere mesh :=
  Classical.choice
    (exists_unitDirectionSpherePackingCertificate mesh hmesh)

abbrev UnitDirectionChoice (mesh : NNReal) (hmesh : 0 < mesh) :=
  ↥(unitDirectionSpherePackingCertificate mesh hmesh).centers

@[simp] theorem unitDirectionChoice_norm
    (mesh : NNReal) (hmesh : 0 < mesh)
    (g : UnitDirectionChoice mesh hmesh) :
    ‖(g.1 : Space)‖ = 1 := by
  apply (mem_unitDirectionSphere_iff_norm_eq_one g.1).mp
  exact (unitDirectionSpherePackingCertificate mesh hmesh).centers_subset g.2

theorem unitDirectionChoice_separated
    (mesh : NNReal) (hmesh : 0 < mesh)
    (g k : UnitDirectionChoice mesh hmesh) (hgk : g ≠ k) :
    ((2 * mesh : NNReal) : Real) < dist (g.1 : Space) (k.1 : Space) := by
  have hsep := (unitDirectionSpherePackingCertificate mesh hmesh).separated
    g.2 k.2 (fun h ↦ hgk (Subtype.ext h))
  have hsep' : ((2 * mesh : NNReal) : ENNReal) <
      ENNReal.ofReal (dist (g.1 : Space) (k.1 : Space)) := by
    simpa [edist_dist] using hsep
  simpa using ENNReal.coe_lt_ofReal.mp hsep'

theorem unitDirectionChoice_cover
    (mesh : NNReal) (hmesh : 0 < mesh)
    (u : Space) (hu : ‖u‖ = 1) :
    ∃ g : UnitDirectionChoice mesh hmesh,
      edist u (g.1 : Space) ≤ (2 * mesh : NNReal) := by
  have huSphere : u ∈ unitDirectionSphere :=
    (mem_unitDirectionSphere_iff_norm_eq_one u).2 hu
  obtain ⟨g, hg, hug⟩ :=
    (unitDirectionSpherePackingCertificate mesh hmesh).cover huSphere
  exact ⟨⟨g, hg⟩, hug⟩

noncomputable instance unitDirectionChoiceNonempty
    (mesh : NNReal) (hmesh : 0 < mesh) :
    Nonempty (UnitDirectionChoice mesh hmesh) := by
  let e : Space := EuclideanSpace.single (0 : Fin 3) (1 : Real)
  have he : ‖e‖ = 1 := by simp [e]
  obtain ⟨g, _hg⟩ := unitDirectionChoice_cover mesh hmesh e he
  exact ⟨g⟩

theorem unitDirectionChoice_card_mul_twoMesh_sq_le
    (mesh : NNReal) (hmesh : 0 < mesh) (hmeshOne : 2 * mesh ≤ 1) :
    (Fintype.card (UnitDirectionChoice mesh hmesh) : Real) *
        ((2 * mesh : NNReal) : Real) ^ 2 ≤ 32 := by
  let C := unitDirectionSpherePackingCertificate mesh hmesh
  have hunit : ∀ i ∈ C.centers, ‖(i : Space)‖ = 1 := by
    intro i hi
    apply (mem_unitDirectionSphere_iff_norm_eq_one i).mp
    exact C.centers_subset hi
  have hsep : ∀ i ∈ C.centers, ∀ j ∈ C.centers, i ≠ j →
      (((2 * mesh : NNReal) : Real)) ≤ dist i j := by
    intro i hi j hj hij
    have hsepRaw := C.separated hi hj hij
    have hsepENN : ((2 * mesh : NNReal) : ENNReal) <
        ENNReal.ofReal (dist i j) := by
      simpa [edist_dist] using hsepRaw
    have hdist : (((2 * mesh : NNReal) : Real)) < dist i j := by
      simpa using ENNReal.coe_lt_ofReal.mp hsepENN
    exact hdist.le
  simpa only [C, Fintype.card_coe] using
    directionFinset_card_mul_sq_le_thirtyTwo
      C.centers (fun i ↦ i) (2 * mesh)
      (mul_pos (by norm_num) hmesh) hmeshOne hunit hsep

#print axioms mem_unitDirectionSphere_iff_norm_eq_one
#print axioms unitDirectionSphere_packingNumber_two_mul_ne_top
#print axioms exists_unitDirectionSpherePackingCertificate
#print axioms unitDirectionChoice_norm
#print axioms unitDirectionChoice_separated
#print axioms unitDirectionChoice_cover
#print axioms unitDirectionChoice_card_mul_twoMesh_sq_le

end
end Family8FiniteRigidMotionUnitSpherePackingV3
