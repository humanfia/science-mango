import Family8Grounding.Family8KatzTaoNegativeExponentObstructionV1
import Mathlib.Tactic

open scoped ENNReal NNReal BigOperators
open MeasureTheory Set

namespace Family8KatzTaoParallelTubeGridV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family4GlobalExtremalUpstream
open Family8KatzTaoFrostmanPropertiesV1
open Family8KatzTaoNegativeExponentObstructionV1

noncomputable section

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

/-!
# A literal separated grid of parallel tubes

The geometric lemmas in this file are independent of the later choice of
grid cardinality.  Parallel axes are centred in the first coordinate and
translated in the second coordinate.  A transverse gap strictly larger than
twice the tube radius makes the closed tube carriers disjoint.
-/

/-- The first coordinate unit vector in the ambient three-space. -/
def parallelDirection : Space :=
  EuclideanSpace.single (0 : Fin 3) (1 : Real)

/-- A unit axis centred in the first coordinate and translated transversely
by the real offset `a`. -/
def parallelAxis (a : Real) : UnitSegment where
  base := (-1 / 2 : Real) • parallelDirection +
    a • EuclideanSpace.single (1 : Fin 3) (1 : Real)
  direction := parallelDirection
  norm_direction := by
    simp [parallelDirection, PiLp.norm_single]

/-- The corresponding radius-`delta` tube. -/
def parallelTube (delta : NNReal) (a : Real) : Tube delta where
  axis := parallelAxis a

@[simp] theorem parallelAxis_direction (a : Real) :
    (parallelAxis a).direction = parallelDirection := rfl

@[simp] theorem parallelAxis_base (a : Real) :
    (parallelAxis a).base =
      (-1 / 2 : Real) • parallelDirection +
        a • EuclideanSpace.single (1 : Fin 3) (1 : Real) := rfl

@[simp] theorem parallelTube_axis (delta : NNReal) (a : Real) :
    (parallelTube delta a).axis = parallelAxis a := rfl

@[simp] theorem parallelAxis_point_apply_one (a t : Real) :
    ((parallelAxis a).base + t • (parallelAxis a).direction) (1 : Fin 3) = a := by
  simp [parallelAxis, parallelDirection]

/-- Every point of a closed tube has an axis parameter within the radius. -/
theorem exists_parallelAxis_parameter_dist_le_of_mem
    {delta : NNReal} {a : Real} {x : Space}
    (hx : x ∈ (parallelTube delta a).carrier) :
    ∃ t ∈ Set.Icc (0 : Real) 1,
      dist x ((parallelAxis a).base + t • (parallelAxis a).direction) ≤
        (delta : Real) := by
  change x ∈ Metric.cthickening (delta : Real) (parallelAxis a).carrier at hx
  rw [
    (parallelAxis a).isCompact_carrier.cthickening_eq_biUnion_closedBall
      (show 0 ≤ (delta : Real) by positivity)] at hx
  simp only [Set.mem_iUnion, Metric.mem_closedBall] at hx
  obtain ⟨y, hyAxis, hdist⟩ := hx
  rw [(parallelAxis a).carrier_eq_image] at hyAxis
  obtain ⟨t, ht, rfl⟩ := hyAxis
  exact ⟨t, ht, hdist⟩

/-- A transverse gap larger than twice the radius makes two parallel tube
carriers literally disjoint. -/
theorem parallelTube_carrier_disjoint_of_two_mul_lt_abs_sub
    {delta : NNReal} {a b : Real}
    (hgap : 2 * (delta : Real) < |a - b|) :
    Disjoint (parallelTube delta a).carrier (parallelTube delta b).carrier := by
  rw [Set.disjoint_left]
  intro x hxa hxb
  obtain ⟨s, _hs, hxs⟩ :=
    exists_parallelAxis_parameter_dist_le_of_mem hxa
  obtain ⟨t, _ht, hxt⟩ :=
    exists_parallelAxis_parameter_dist_le_of_mem hxb
  let p : Space := (parallelAxis a).base + s • (parallelAxis a).direction
  let q : Space := (parallelAxis b).base + t • (parallelAxis b).direction
  have hpq : dist p q ≤ 2 * (delta : Real) := by
    calc
      dist p q ≤ dist p x + dist x q := dist_triangle p x q
      _ ≤ (delta : Real) + (delta : Real) := by
        exact add_le_add (by simpa [p, dist_comm] using hxs)
          (by simpa [q] using hxt)
      _ = 2 * (delta : Real) := by ring
  have hcoord :
      |(p - q) (1 : Fin 3)| ≤ ‖p - q‖ := by
    simpa only [Real.norm_eq_abs] using
      PiLp.norm_apply_le (p - q) (1 : Fin 3)
  have hcoordinate : (p - q) (1 : Fin 3) = a - b := by
    simp [p, q, parallelAxis, parallelDirection]
  have hab : |a - b| ≤ dist p q := by
    calc
      |a - b| = |(p - q) (1 : Fin 3)| := by rw [hcoordinate]
      _ ≤ ‖p - q‖ := hcoord
      _ = dist p q := by rw [dist_eq_norm]
  exact (not_le_of_gt hgap) (hab.trans hpq)

/-- If the transverse offset and radius are both at most one quarter, the
whole tube lies in the normalized unit ball. -/
theorem parallelTube_carrier_subset_unitBall
    {delta : NNReal} {a : Real}
    (ha : |a| ≤ (1 / 4 : Real))
    (hdelta : delta ≤ (1 / 4 : NNReal)) :
    (parallelTube delta a).carrier ⊆ Metric.closedBall (0 : Space) 1 := by
  have haxis :
      (parallelAxis a).carrier ⊆
        Metric.closedBall (0 : Space) (3 / 4 : Real) := by
    intro x hx
    rw [UnitSegment.carrier_eq_image] at hx
    obtain ⟨t, ht, rfl⟩ := hx
    rw [Metric.mem_closedBall, dist_zero_right]
    have htabs : |t - 1 / 2| ≤ (1 / 2 : Real) := by
      rw [abs_le]
      constructor <;> linarith [ht.1, ht.2]
    have hpoint :
        (parallelAxis a).base + t • (parallelAxis a).direction =
          (t - 1 / 2 : Real) • parallelDirection +
            a • EuclideanSpace.single (1 : Fin 3) (1 : Real) := by
      simp only [parallelAxis_base, parallelAxis_direction]
      module
    change ‖(parallelAxis a).base +
      t • (parallelAxis a).direction‖ ≤ (3 / 4 : Real)
    rw [hpoint]
    calc
      ‖(t - 1 / 2 : Real) • parallelDirection +
          a • EuclideanSpace.single (1 : Fin 3) (1 : Real)‖ ≤
          ‖(t - 1 / 2 : Real) • parallelDirection‖ +
            ‖a • EuclideanSpace.single (1 : Fin 3) (1 : Real)‖ :=
        norm_add_le _ _
      _ = |t - 1 / 2| + |a| := by
        simp [parallelDirection, norm_smul, PiLp.norm_single, Real.norm_eq_abs]
      _ ≤ (1 / 2 : Real) + (1 / 4 : Real) := add_le_add htabs ha
      _ = (3 / 4 : Real) := by norm_num
  have hdeltaReal : (delta : Real) ≤ (1 / 4 : Real) := by
    exact_mod_cast hdelta
  change Metric.cthickening (delta : Real) (parallelAxis a).carrier ⊆
    Metric.closedBall (0 : Space) 1
  refine (Metric.cthickening_subset_of_subset _ haxis).trans ?_
  rw [cthickening_closedBall (by positivity) (by norm_num)]
  exact Metric.closedBall_subset_closedBall (by linarith)

/-- Literal carrier disjointness is stronger than the project's
half-overlap notion of essential distinctness. -/
theorem essentiallyDistinct_of_carrier_disjoint
    {delta : NNReal} {T U : Tube delta}
    (hdisjoint : Disjoint T.carrier U.carrier) :
    EssentiallyDistinct T U := by
  unfold EssentiallyDistinct
  rw [hdisjoint.inter_eq]
  simp

#print axioms exists_parallelAxis_parameter_dist_le_of_mem
#print axioms parallelTube_carrier_disjoint_of_two_mul_lt_abs_sub
#print axioms parallelTube_carrier_subset_unitBall
#print axioms essentiallyDistinct_of_carrier_disjoint

end
end Family8KatzTaoParallelTubeGridV1
