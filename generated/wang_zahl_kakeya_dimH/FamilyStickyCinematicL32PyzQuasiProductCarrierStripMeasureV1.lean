import FamilyStickyCinematicL32PyzQuasiProductFrostmanBoundV1

set_option autoImplicit false

open Set MeasureTheory
open scoped ENNReal

namespace FamilyStickyCinematicL32PyzQuasiProductCarrierStripMeasureV1

open FamilyStickyCinematicL32PyzQuasiProductGraphStripMeasureV1
open FamilyStickyCinematicL32PyzQuasiProductFrostmanBoundV1

noncomputable section

/-!
# Quasi-product strips in the project's carrier coordinate order

The cinematic rectangle API stores a point as `(vertical, parameter)`;
thus its base coordinate is `.2`.  This is the coordinate-symmetric Tonelli
form of the PYZ quasi-product estimate, using `prod_apply_symm`.  It is the
version intended for actual rectangle carriers.
-/

/-- A measurable quasi-product written in the project's `(y, theta)` order. -/
structure PyzCarrierQuasiProduct
    (E : Set (Real × Real)) (bound : Real -> Real -> ENNReal) where
  outer : Set Real
  fiber : Real -> Set Real
  measurable_E : MeasurableSet E
  slice_eq_of_mem : forall theta, theta ∈ outer ->
    (fun y => (y, theta)) ⁻¹' E = fiber theta
  slice_eq_of_not_mem : forall theta, theta ∉ outer ->
    (fun y => (y, theta)) ⁻¹' E = ∅
  outer_frostman : IsPyzIntervalFrostman outer bound
  fiber_frostman : forall theta,
    IsPyzIntervalFrostman (fiber theta) bound

/-- Carrier-coordinate graph strip: `.2` is the parameter and `.1` is the
vertical graph value. -/
def pyzCarrierGraphStrip
    (a b : Real) (g : Real -> Real) (width : Real) :
    Set (Real × Real) :=
  {q | q.2 ∈ Icc a b ∧
    q.1 ∈ Icc (g q.2 - width) (g q.2 + width)}

theorem measurableSet_pyzCarrierGraphStrip
    {a b width : Real} {g : Real -> Real} (hg : Measurable g) :
    MeasurableSet (pyzCarrierGraphStrip a b g width) := by
  have hstandard : MeasurableSet
      {p : Real × Real | p.1 ∈ Icc a b ∧
        p.2 ∈ Icc (g p.1 - width) (g p.1 + width)} := by
    simpa only [Set.mem_ofPred_eq] using
      (measurableSet_region_between_cc
        (hg.sub_const width) (hg.add_const width) measurableSet_Icc)
  simpa only [pyzCarrierGraphStrip, Prod.swap,
    Set.preimage_ofPred_eq] using measurable_swap hstandard

theorem vertical_preimage_inter_pyzCarrierGraphStrip
    {E : Set (Real × Real)} {bound : Real -> Real -> ENNReal}
    (Q : PyzCarrierQuasiProduct E bound)
    (a b : Real) (g : Real -> Real) (width theta : Real) :
    (fun y => (y, theta)) ⁻¹'
        (E ∩ pyzCarrierGraphStrip a b g width) =
      {y | theta ∈ Q.outer ∩ Icc a b ∧
        y ∈ Q.fiber theta ∩ Icc (g theta - width) (g theta + width)} := by
  ext y
  rw [Set.mem_preimage, Set.mem_inter_iff]
  change ((y, theta) ∈ E ∧
      theta ∈ Icc a b ∧ y ∈ Icc (g theta - width) (g theta + width)) ↔ _
  by_cases houter : theta ∈ Q.outer
  · have hslice := Set.ext_iff.mp (Q.slice_eq_of_mem theta houter) y
    change (y, theta) ∈ E ↔ y ∈ Q.fiber theta at hslice
    rw [hslice]
    simp [houter, and_assoc, and_left_comm]
  · have hslice := Set.ext_iff.mp (Q.slice_eq_of_not_mem theta houter) y
    change (y, theta) ∈ E ↔ y ∈ (∅ : Set Real) at hslice
    rw [hslice]
    simp [houter]

/-- Symmetric Tonelli form of the abstract quasi-product strip estimate. -/
theorem volume_inter_pyzCarrierGraphStrip_le
    {E : Set (Real × Real)} {bound : Real -> Real -> ENNReal}
    (Q : PyzCarrierQuasiProduct E bound)
    {a b width : Real} {g : Real -> Real}
    (hg : Measurable g) (verticalBound : ENNReal)
    (hvertical : forall theta, theta ∈ Q.outer ∩ Icc a b ->
      bound (g theta - width) (g theta + width) <= verticalBound) :
    volume (E ∩ pyzCarrierGraphStrip a b g width) <=
      verticalBound * bound a b := by
  have hstrip : MeasurableSet (pyzCarrierGraphStrip a b g width) :=
    measurableSet_pyzCarrierGraphStrip hg
  have hinter : MeasurableSet (E ∩ pyzCarrierGraphStrip a b g width) :=
    Q.measurable_E.inter hstrip
  have houterBase : MeasurableSet (Q.outer ∩ Icc a b) :=
    Q.outer_frostman.1.inter measurableSet_Icc
  rw [Measure.volume_eq_prod, Measure.prod_apply_symm hinter]
  calc
    (∫⁻ theta, volume
        ((fun y => (y, theta)) ⁻¹'
          (E ∩ pyzCarrierGraphStrip a b g width)) ∂volume) <=
        ∫⁻ theta, (Q.outer ∩ Icc a b).indicator
          (fun _ => verticalBound) theta ∂volume := by
      apply lintegral_mono
      intro theta
      change volume ((fun y => (y, theta)) ⁻¹'
          (E ∩ pyzCarrierGraphStrip a b g width)) <= _
      rw [vertical_preimage_inter_pyzCarrierGraphStrip
        Q a b g width theta]
      by_cases htheta : theta ∈ Q.outer ∩ Icc a b
      · have hset :
            {y | theta ∈ Q.outer ∩ Icc a b ∧
              y ∈ Q.fiber theta ∩
                Icc (g theta - width) (g theta + width)} =
              Q.fiber theta ∩ Icc
                (g theta - width) (g theta + width) := by
          ext y
          change (theta ∈ Q.outer ∩ Icc a b ∧
            (y ∈ Q.fiber theta ∧
              y ∈ Icc (g theta - width) (g theta + width))) ↔
            (y ∈ Q.fiber theta ∧
              y ∈ Icc (g theta - width) (g theta + width))
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

/-- The explicit `(delta,alpha;C)_1 × (delta,alpha;C)_1` carrier-strip
bound in the actual coordinate order. -/
theorem volume_inter_pyzCarrierGraphStrip_le_frostmanProduct
    {E : Set (Real × Real)}
    {delta alpha : Real} {C : ENNReal}
    (Q : PyzCarrierQuasiProduct E
      (pyzFrostmanIntervalBound delta alpha C))
    {a b width : Real} {g : Real -> Real}
    (hg : Measurable g) :
    volume (E ∩ pyzCarrierGraphStrip a b g width) <=
      (C * (ENNReal.ofReal delta) ^ (1 - alpha) *
          (ENNReal.ofReal (2 * width)) ^ alpha) *
        (C * (ENNReal.ofReal delta) ^ (1 - alpha) *
          (ENNReal.ofReal (b - a)) ^ alpha) := by
  have hvertical : forall theta, theta ∈ Q.outer ∩ Icc a b ->
      pyzFrostmanIntervalBound delta alpha C
          (g theta - width) (g theta + width) <=
        C * (ENNReal.ofReal delta) ^ (1 - alpha) *
          (ENNReal.ofReal (2 * width)) ^ alpha := by
    intro theta _htheta
    simp only [pyzFrostmanIntervalBound]
    have hlength : (g theta + width) - (g theta - width) =
        2 * width := by ring
    rw [hlength]
  simpa [pyzFrostmanIntervalBound] using
    (volume_inter_pyzCarrierGraphStrip_le Q hg
      (C * (ENNReal.ofReal delta) ^ (1 - alpha) *
        (ENNReal.ofReal (2 * width)) ^ alpha) hvertical)

#print axioms PyzCarrierQuasiProduct
#print axioms pyzCarrierGraphStrip
#print axioms measurableSet_pyzCarrierGraphStrip
#print axioms vertical_preimage_inter_pyzCarrierGraphStrip
#print axioms volume_inter_pyzCarrierGraphStrip_le
#print axioms volume_inter_pyzCarrierGraphStrip_le_frostmanProduct

end

end FamilyStickyCinematicL32PyzQuasiProductCarrierStripMeasureV1
