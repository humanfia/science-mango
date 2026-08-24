import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32CurvilinearRectangleCarrierV1
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Tactic.Linarith

set_option autoImplicit false

open Set MeasureTheory

namespace FamilyStickyCinematicL32CurvilinearRectangleVolumeV1

open FamilyStickyCinematicL32CurvilinearRectangleCarrierV1
open FamilyStickyCinematicL32RectangleTangencyV1

noncomputable section

/-!
# Lebesgue area of a curvilinear graph rectangle

This is the area computation used in Pramanik--Yang--Zahl,
arXiv:2207.02259v3, Lemma 3.15.  For each parameter, the vertical section
of a `delta`-thick graph rectangle is the interval
`[f(theta)-delta,f(theta)+delta]`.  The symmetric product-measure formula
therefore gives exact area `2*delta*baseLength`, independently of the graph.
-/

/-- A graph rectangle with measurable center graph has a measurable
carrier. -/
theorem measurableSet_graphRectangle_carrier
    (R : GraphRectangle) (delta : Real) (hgraph : Measurable R.graph) :
    MeasurableSet (R.carrier delta) := by
  unfold GraphRectangle.carrier cinematicVerticalNeighborhood
  exact (measurableSet_Icc.preimage measurable_snd).inter
    (measurableSet_Iic.preimage
      ((measurable_fst.sub (hgraph.comp measurable_snd)).abs))

/-- Exact Lebesgue area of a measurable curvilinear graph rectangle. -/
theorem volume_graphRectangle_carrier
    (R : GraphRectangle) {delta : Real}
    (hgraph : Measurable R.graph) :
    volume (R.carrier delta) =
      ENNReal.ofReal (2 * delta) *
        ENNReal.ofReal (R.right - R.left) := by
  classical
  have hmeasurable := measurableSet_graphRectangle_carrier R delta hgraph
  have hsection : forall theta : Real,
      volume ((fun value : Real => (value, theta)) ⁻¹' R.carrier delta) =
        R.base.indicator
          (fun _ => ENNReal.ofReal (2 * delta)) theta := by
    intro theta
    rw [Set.indicator_apply]
    by_cases htheta : theta ∈ R.base
    · rw [if_pos htheta]
      have hset :
          (fun value : Real => (value, theta)) ⁻¹' R.carrier delta =
            Icc (R.graph theta - delta) (R.graph theta + delta) := by
        ext value
        simp only [GraphRectangle.carrier, cinematicVerticalNeighborhood,
          Set.mem_preimage, Set.mem_ofPred_eq,
          htheta, true_and, mem_Icc]
        rw [abs_le]
        constructor <;> intro h <;> constructor <;> linarith
      rw [hset, Real.volume_Icc]
      congr 1
      ring
    · rw [if_neg htheta]
      have hset :
          (fun value : Real => (value, theta)) ⁻¹' R.carrier delta = ∅ := by
        ext value
        simp [GraphRectangle.carrier, cinematicVerticalNeighborhood, htheta]
      rw [hset, measure_empty]
  change ((volume : Measure Real).prod (volume : Measure Real))
      (R.carrier delta) = _
  rw [Measure.prod_apply_symm hmeasurable]
  simp_rw [hsection]
  rw [GraphRectangle.base]
  rw [lintegral_indicator_const measurableSet_Icc]
  rw [Real.volume_Icc]

#print axioms measurableSet_graphRectangle_carrier
#print axioms volume_graphRectangle_carrier

end

end FamilyStickyCinematicL32CurvilinearRectangleVolumeV1
