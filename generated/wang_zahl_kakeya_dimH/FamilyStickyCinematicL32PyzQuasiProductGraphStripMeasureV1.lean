import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Prod

set_option autoImplicit false

open Set MeasureTheory
open scoped ENNReal

namespace FamilyStickyCinematicL32PyzQuasiProductGraphStripMeasureV1

noncomputable section

/-!
# A faithful quasi-product graph-strip estimate

PYZ (5.37) uses only the defining one-dimensional Frostman estimates of the
outer set and every vertical fibre of a quasi-product.  This module records
that source structure and derives the two-dimensional graph-strip estimate
by product-measure disintegration.

The source fields are literal measurable fibre decomposition and
one-dimensional interval estimates.  No two-dimensional rectangle or final
`M` bound is a structure field.
-/

/-- One-dimensional interval non-concentration with an explicit bound
function. -/
def IsPyzIntervalFrostman
    (A : Set Real) (bound : Real -> Real -> ENNReal) : Prop :=
  MeasurableSet A ∧
    forall a b, volume (A ∩ Icc a b) <= bound a b

/-- A measurable fibre product whose outer set and all vertical fibres obey
the same one-dimensional interval bound. -/
structure PyzQuasiProduct
    (E : Set (Real × Real)) (bound : Real -> Real -> ENNReal) where
  outer : Set Real
  fiber : Real -> Set Real
  measurable_E : MeasurableSet E
  slice_eq_of_mem : forall theta, theta ∈ outer ->
    Prod.mk theta ⁻¹' E = fiber theta
  slice_eq_of_not_mem : forall theta, theta ∉ outer ->
    Prod.mk theta ⁻¹' E = ∅
  outer_frostman : IsPyzIntervalFrostman outer bound
  fiber_frostman : forall theta,
    IsPyzIntervalFrostman (fiber theta) bound

/-- A graph strip over `[a,b]` with vertical half-width `width`. -/
def pyzGraphStrip
    (a b : Real) (g : Real -> Real) (width : Real) :
    Set (Real × Real) :=
  {p | p.1 ∈ Icc a b ∧
    p.2 ∈ Icc (g p.1 - width) (g p.1 + width)}

theorem measurableSet_pyzGraphStrip
    {a b width : Real} {g : Real -> Real} (hg : Measurable g) :
    MeasurableSet (pyzGraphStrip a b g width) := by
  simpa [pyzGraphStrip] using
    (measurableSet_region_between_cc
      (hg.sub_const width) (hg.add_const width) measurableSet_Icc)

/-- The exact vertical slice of a quasi-product intersected with a graph
strip. -/
theorem mk_preimage_inter_pyzGraphStrip
    {E : Set (Real × Real)} {bound : Real -> Real -> ENNReal}
    (Q : PyzQuasiProduct E bound)
    (a b : Real) (g : Real -> Real) (width theta : Real) :
    Prod.mk theta ⁻¹' (E ∩ pyzGraphStrip a b g width) =
      {y | theta ∈ Q.outer ∩ Icc a b ∧
        y ∈ Q.fiber theta ∩ Icc (g theta - width) (g theta + width)} := by
  ext y
  rw [Set.mem_preimage, Set.mem_inter_iff]
  change ((theta, y) ∈ E ∧
      theta ∈ Icc a b ∧ y ∈ Icc (g theta - width) (g theta + width)) ↔ _
  by_cases houter : theta ∈ Q.outer
  · have hslice := Set.ext_iff.mp (Q.slice_eq_of_mem theta houter) y
    change (theta, y) ∈ E ↔ y ∈ Q.fiber theta at hslice
    rw [hslice]
    simp [houter, and_assoc, and_left_comm]
  · have hslice := Set.ext_iff.mp (Q.slice_eq_of_not_mem theta houter) y
    change (theta, y) ∈ E ↔ y ∈ (∅ : Set Real) at hslice
    rw [hslice]
    simp [houter]

/-- Product-measure disintegration turns the two one-dimensional Frostman
inputs into the graph-strip mass bound.  `verticalBound` only upper-bounds
the already specified one-dimensional interval-bound function on the
particular moving vertical intervals. -/
theorem volume_inter_pyzGraphStrip_le
    {E : Set (Real × Real)} {bound : Real -> Real -> ENNReal}
    (Q : PyzQuasiProduct E bound)
    {a b width : Real} {g : Real -> Real}
    (hg : Measurable g) (verticalBound : ENNReal)
    (hvertical : forall theta, theta ∈ Q.outer ∩ Icc a b ->
      bound (g theta - width) (g theta + width) <= verticalBound) :
    volume (E ∩ pyzGraphStrip a b g width) <=
      verticalBound * bound a b := by
  have hstrip : MeasurableSet (pyzGraphStrip a b g width) :=
    measurableSet_pyzGraphStrip hg
  have hinter : MeasurableSet (E ∩ pyzGraphStrip a b g width) :=
    Q.measurable_E.inter hstrip
  have houterBase : MeasurableSet (Q.outer ∩ Icc a b) :=
    Q.outer_frostman.1.inter measurableSet_Icc
  rw [Measure.volume_eq_prod, Measure.prod_apply hinter]
  calc
    (∫⁻ theta, volume
        (Prod.mk theta ⁻¹' (E ∩ pyzGraphStrip a b g width)) ∂volume) <=
        ∫⁻ theta, (Q.outer ∩ Icc a b).indicator
          (fun _ => verticalBound) theta ∂volume := by
      apply lintegral_mono
      intro theta
      change volume
          (Prod.mk theta ⁻¹' (E ∩ pyzGraphStrip a b g width)) <= _
      rw [mk_preimage_inter_pyzGraphStrip Q a b g width theta]
      by_cases htheta : theta ∈ Q.outer ∩ Icc a b
      · have hset :
            {y | theta ∈ Q.outer ∩ Icc a b ∧
              y ∈ Q.fiber theta ∩
                Icc (g theta - width) (g theta + width)} =
              Q.fiber theta ∩ Icc
                (g theta - width) (g theta + width) := by
          ext y
          change (theta ∈ Q.outer ∩ Icc a b ∧ (y ∈ Q.fiber theta ∧ y ∈ Icc (g theta - width) (g theta + width))) ↔ (y ∈ Q.fiber theta ∧ y ∈ Icc (g theta - width) (g theta + width))
          exact and_iff_right htheta
        rw [hset, Set.indicator_of_mem htheta]
        exact (Q.fiber_frostman theta).2
          (g theta - width) (g theta + width) |>.trans
            (hvertical theta htheta)
      · have hset :
            {y | theta ∈ Q.outer ∩ Icc a b ∧
              y ∈ Q.fiber theta ∩
                Icc (g theta - width) (g theta + width)} = ∅ := by
          ext y
          simp [htheta]
        rw [hset, measure_empty, Set.indicator_of_notMem htheta]
    _ = verticalBound * volume (Q.outer ∩ Icc a b) := by
      exact lintegral_indicator_const houterBase verticalBound
    _ <= verticalBound * bound a b := by
      exact mul_le_mul' le_rfl (Q.outer_frostman.2 a b)

#print axioms IsPyzIntervalFrostman
#print axioms PyzQuasiProduct
#print axioms pyzGraphStrip
#print axioms measurableSet_pyzGraphStrip
#print axioms mk_preimage_inter_pyzGraphStrip
#print axioms volume_inter_pyzGraphStrip_le

end

end FamilyStickyCinematicL32PyzQuasiProductGraphStripMeasureV1
