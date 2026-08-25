import Submission.Kakeya.ConvexGeometry.Tube
import Mathlib.Topology.MetricSpace.Cover
import Mathlib.Topology.MetricSpace.ProperSpace

open Set
open scoped NNReal

namespace FamilyStickyRandomProductCoordinatePackingV1

open LeanEval.Analysis.WangZahlKakeya

noncomputable section
set_option linter.unusedSectionVars false

/-!
# A finite packing core for basepoint--direction parameters

The WZ line cell is represented, after choosing one of the two orientations,
by a pair `(basepoint, direction)` in `Space x Space`.  This is a fixed
six-dimensional proper metric space.  We choose once and for all a finite
`1/4`-net of its closed ball of radius `1200`.  Any finite parameter family
in that ball with pairwise distance at least one injects into this net, so its
cardinality is bounded by one fixed natural number.

This is the product-coordinate packing kernel requested by the source audit.
It contains no tube geometry, scale, family, probability, or cardinal-bound
callback.  An explicit cubical grid could replace the chosen compactness net
without changing any downstream interface; the present finite producer keeps
the proof independent of coordinate-floor arithmetic.
-/

/-- Oriented basepoint together with oriented unit direction. -/
abbrev LineParameter := Space × Space

def normalizedParameterRadius : NNReal := 1200

def normalizedParameterMesh : NNReal := (4 : NNReal)⁻¹

theorem normalizedParameterMesh_ne_zero :
    normalizedParameterMesh ≠ 0 := by
  norm_num [normalizedParameterMesh]

/-- One produced finite net of the fixed normalized parameter ball. -/
structure ProductCoordinatePackingNet where
  centers : Finset LineParameter
  cover : Metric.IsCover normalizedParameterMesh
    (Metric.closedBall (0 : LineParameter)
      (normalizedParameterRadius : Real)) (centers : Set LineParameter)

theorem exists_productCoordinatePackingNet :
    Nonempty ProductCoordinatePackingNet := by
  obtain ⟨N, _hsubset, hfinite, hcover⟩ :=
    Metric.exists_finite_isCover_of_isCompact
      normalizedParameterMesh_ne_zero
      (isCompact_closedBall (0 : LineParameter)
        (normalizedParameterRadius : Real))
  refine ⟨{ centers := hfinite.toFinset, cover := ?_ }⟩
  simpa using hcover

def canonicalPackingNet : ProductCoordinatePackingNet :=
  Classical.choice exists_productCoordinatePackingNet

/-- Dimension-only constant controlling all normalized local line cells. -/
def productCoordinatePackingConstant : Nat :=
  canonicalPackingNet.centers.card

namespace ProductCoordinatePackingNet

variable (P : ProductCoordinatePackingNet)

theorem exists_center_edist_le (p : LineParameter)
    (hp : ‖p‖ <= (normalizedParameterRadius : Real)) :
    exists c, c ∈ P.centers ∧
      edist p c <= (normalizedParameterMesh : ENNReal) := by
  have hpBall : p ∈ Metric.closedBall (0 : LineParameter)
      (normalizedParameterRadius : Real) := by
    simpa [Metric.mem_closedBall, dist_zero_right] using hp
  exact P.cover hpBall

/-- Code a point in the normalized ball by one chosen covering center. -/
def code {index : Type*} (parameter : index -> LineParameter)
    (rangeBound : forall i,
      ‖parameter i‖ <= (normalizedParameterRadius : Real))
    (i : index) : {c // c ∈ P.centers} :=
  ⟨Classical.choose (P.exists_center_edist_le (parameter i) (rangeBound i)),
    (Classical.choose_spec
      (P.exists_center_edist_le (parameter i) (rangeBound i))).1⟩

theorem dist_parameter_code_le
    {index : Type*} (parameter : index -> LineParameter)
    (rangeBound : forall i,
      ‖parameter i‖ <= (normalizedParameterRadius : Real))
    (i : index) :
    dist (parameter i) (P.code parameter rangeBound i).1 <= (4 : Real)⁻¹ := by
  have h := (Classical.choose_spec
    (P.exists_center_edist_le (parameter i) (rangeBound i))).2
  rw [edist_dist] at h
  have hreal := ENNReal.toReal_mono ENNReal.coe_ne_top h
  simpa [code, normalizedParameterMesh] using hreal

theorem code_injective_of_one_separated
    {index : Type*} (parameter : index -> LineParameter)
    (rangeBound : forall i,
      ‖parameter i‖ <= (normalizedParameterRadius : Real))
    (separated : forall i j, i ≠ j ->
      1 <= ‖parameter i - parameter j‖) :
    Function.Injective (P.code parameter rangeBound) := by
  intro i j hcode
  by_contra hij
  have hsep : (1 : Real) <= dist (parameter i) (parameter j) := by
    simpa [dist_eq_norm] using separated i j hij
  have hnearI := P.dist_parameter_code_le parameter rangeBound i
  have hnearJ := P.dist_parameter_code_le parameter rangeBound j
  have hlt : dist (parameter i) (parameter j) < 1 := by
    calc
      dist (parameter i) (parameter j) <=
          dist (parameter i) (P.code parameter rangeBound i).1 +
            dist (P.code parameter rangeBound i).1 (parameter j) :=
        dist_triangle _ _ _
      _ = dist (parameter i) (P.code parameter rangeBound i).1 +
            dist (P.code parameter rangeBound j).1 (parameter j) := by
        rw [hcode]
      _ <= (4 : Real)⁻¹ + (4 : Real)⁻¹ := by
        exact add_le_add hnearI (by simpa [dist_comm] using hnearJ)
      _ < 1 := by norm_num
  exact (not_lt_of_ge hsep) hlt

end ProductCoordinatePackingNet

/-- Finite-index form used by the tube adapter.  Translation and rescaling of
the parameters are performed before this theorem is called. -/
theorem card_le_productCoordinatePackingConstant
    {index : Type*} [Fintype index]
    (parameter : index -> LineParameter)
    (rangeBound : forall i,
      ‖parameter i‖ <= (normalizedParameterRadius : Real))
    (separated : forall i j, i ≠ j ->
      1 <= ‖parameter i - parameter j‖) :
    Fintype.card index <= productCoordinatePackingConstant := by
  simpa [productCoordinatePackingConstant] using
    (Fintype.card_le_of_injective
      (canonicalPackingNet.code parameter rangeBound)
      (canonicalPackingNet.code_injective_of_one_separated
        parameter rangeBound separated))

/-- Finset form, retaining arbitrary ambient indices. -/
theorem finset_card_le_productCoordinatePackingConstant
    {index : Type*} [DecidableEq index] (indices : Finset index)
    (parameter : index -> LineParameter)
    (rangeBound : forall i, i ∈ indices ->
      ‖parameter i‖ <= (normalizedParameterRadius : Real))
    (separated : forall i, i ∈ indices -> forall j, j ∈ indices ->
      i ≠ j -> 1 <= ‖parameter i - parameter j‖) :
    indices.card <= productCoordinatePackingConstant := by
  let p : {i // i ∈ indices} -> LineParameter := fun i => parameter i.1
  have hrange : forall i, ‖p i‖ <= (normalizedParameterRadius : Real) :=
    fun i => rangeBound i.1 i.2
  have hsep : forall i j, i ≠ j -> 1 <= ‖p i - p j‖ := by
    intro i j hij
    apply separated i.1 i.2 j.1 j.2
    intro hval
    exact hij (Subtype.ext hval)
  simpa only [Fintype.card_coe] using
    card_le_productCoordinatePackingConstant p hrange hsep

#print axioms exists_productCoordinatePackingNet
#print axioms ProductCoordinatePackingNet.exists_center_edist_le
#print axioms ProductCoordinatePackingNet.dist_parameter_code_le
#print axioms ProductCoordinatePackingNet.code_injective_of_one_separated
#print axioms card_le_productCoordinatePackingConstant
#print axioms finset_card_le_productCoordinatePackingConstant

end
end FamilyStickyRandomProductCoordinatePackingV1
