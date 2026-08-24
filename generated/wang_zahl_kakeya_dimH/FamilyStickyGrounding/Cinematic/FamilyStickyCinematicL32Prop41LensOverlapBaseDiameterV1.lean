import Mathlib.Topology.MetricSpace.Pseudo.Real
import Mathlib.Tactic.Linarith

set_option autoImplicit false

open Set

namespace FamilyStickyCinematicL32Prop41LensOverlapBaseDiameterV1

/-!
# PYZ Lemma 4.7: lens overlap localizes two rectangle bases

This is the metric core of the overlap-to-comparability argument.  Each
lens support and its associated rectangle base are localized near the same
critical parameter.  If the two lens supports meet, the two critical
parameters are close; consequently the union of the two rectangle bases
has controlled diameter.

The analytic producer of the four localization hypotheses is deliberately
separate.  No comparability or lens-counting conclusion is assumed.
-/

/-- Two lens supports localized at respective critical parameters and
sharing a parameter force the associated base union to have diameter at
most four localization radii. -/
theorem base_union_diameter_le_four_mul_of_lensSupport_overlap
    (base1 base2 lensSupport1 lensSupport2 : Set Real)
    (critical1 critical2 radius : Real) (hradius : 0 <= radius)
    (hbase1 : forall x, x ∈ base1 -> dist x critical1 <= radius)
    (hbase2 : forall x, x ∈ base2 -> dist x critical2 <= radius)
    (hlens1 : forall x, x ∈ lensSupport1 ->
      dist x critical1 <= radius)
    (hlens2 : forall x, x ∈ lensSupport2 ->
      dist x critical2 <= radius)
    (hoverlap : (lensSupport1 ∩ lensSupport2).Nonempty) :
    forall x, x ∈ base1 ∪ base2 -> forall y, y ∈ base1 ∪ base2 ->
      dist x y <= 4 * radius := by
  rcases hoverlap with ⟨z, hz1, hz2⟩
  have hzCritical1 : dist critical1 z <= radius := by
    simpa [dist_comm] using hlens1 z hz1
  have hzCritical2 : dist z critical2 <= radius := hlens2 z hz2
  have hcritical : dist critical1 critical2 <= 2 * radius := by
    have htriangle := dist_triangle critical1 z critical2
    linarith
  intro x hx y hy
  rcases hx with hx1 | hx2
  · rcases hy with hy1 | hy2
    · have hxBound := hbase1 x hx1
      have hyBound : dist critical1 y <= radius := by
        simpa [dist_comm] using hbase1 y hy1
      have htriangle := dist_triangle x critical1 y
      linarith
    · have hxBound := hbase1 x hx1
      have hyBound : dist critical2 y <= radius := by
        simpa [dist_comm] using hbase2 y hy2
      have htriangle1 := dist_triangle x critical1 y
      have htriangle2 := dist_triangle critical1 critical2 y
      linarith
  · rcases hy with hy1 | hy2
    · have hxBound := hbase2 x hx2
      have hyBound : dist critical1 y <= radius := by
        simpa [dist_comm] using hbase1 y hy1
      have hcritical' : dist critical2 critical1 <= 2 * radius := by
        simpa [dist_comm] using hcritical
      have htriangle1 := dist_triangle x critical2 y
      have htriangle2 := dist_triangle critical2 critical1 y
      linarith
    · have hxBound := hbase2 x hx2
      have hyBound : dist critical2 y <= radius := by
        simpa [dist_comm] using hbase2 y hy2
      have htriangle := dist_triangle x critical2 y
      linarith

#print axioms base_union_diameter_le_four_mul_of_lensSupport_overlap

end FamilyStickyCinematicL32Prop41LensOverlapBaseDiameterV1
