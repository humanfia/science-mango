import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41RectangularSkirtJordanSourceV1
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Separation.Hausdorff

set_option autoImplicit false
set_option linter.style.haveILetI false

open Function Set

namespace FamilyStickyCinematicL32Prop41CircleLiftEmbeddingV1

open FamilyStickyCinematicL32Prop41RectangularSkirtJordanSourceV1

noncomputable section

/-!
# A compact-circle lift bridge for the PYZ rectangular skirt

This module contains no skirt geometry.  It converts a continuous loop on a
closed fundamental interval, injective on the associated half-open interval,
into an actual embedding of the Euclidean unit circle.  Thus later modules
only have to verify explicit piecewise-linear/graph facts about the literal
skirt parametrization.
-/

/-- Complex unit-circle coordinates are homeomorphic to the real-coordinate
unit circle used by the PYZ Jordan source interface. -/
noncomputable def complexCircleEquivPlaneUnitCircle :
    Circle ≃ₜ PlaneUnitCircle :=
  Homeomorph.subtype Complex.equivRealProdCLM.toHomeomorph (by
    intro z
    constructor
    · intro hz
      change z ∈ Metric.sphere (0 : Complex) 1 at hz
      have hnorm : ‖z‖ = 1 := mem_sphere_zero_iff_norm.mp hz
      change z.re ^ 2 + z.im ^ 2 = 1
      calc
        z.re ^ 2 + z.im ^ 2 = Complex.normSq z := by
          simp [Complex.normSq_apply, pow_two]
        _ = ‖z‖ ^ 2 := Complex.normSq_eq_norm_sq z
        _ = 1 := by rw [hnorm]; norm_num
    · intro hz
      change z.re ^ 2 + z.im ^ 2 = 1 at hz
      change z ∈ Metric.sphere (0 : Complex) 1
      apply mem_sphere_zero_iff_norm.mpr
      have hsq : ‖z‖ ^ 2 = 1 := by
        rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
        simpa [pow_two] using hz
      nlinarith [norm_nonneg z])

/-- The real-coordinate unit circle, rescaled to an additive circle of any
positive period. -/
noncomputable def planeUnitCircleEquivAddCircle
    (p : Real) (hp : 0 < p) : PlaneUnitCircle ≃ₜ AddCircle p :=
  complexCircleEquivPlaneUnitCircle.symm.trans
    (AddCircle.homeomorphCircle hp.ne').symm

/-- Restricting a scalar loop to a half-open fundamental interval and lifting
it to the additive circle preserves injectivity. -/
theorem liftIco_injective_of_injOn
    {X : Type*} {p a : Real} [Fact (0 < p)] {loop : Real -> X}
    (hinj : Set.InjOn loop (Ico a (a + p))) :
    Function.Injective (AddCircle.liftIco p a loop) := by
  intro x y hxy
  apply (AddCircle.equivIco p a).injective
  apply Subtype.ext
  exact hinj (AddCircle.equivIco p a x).property
    (AddCircle.equivIco p a y).property hxy

/-- The range of the additive-circle lift is exactly the image of one
half-open fundamental interval. -/
theorem range_liftIco
    {X : Type*} {p a : Real} [Fact (0 < p)] (loop : Real -> X) :
    range (AddCircle.liftIco p a loop) =
      loop '' Ico a (a + p) := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨(AddCircle.equivIco p a x).1,
      (AddCircle.equivIco p a x).property, rfl⟩
  · rintro ⟨t, ht, rfl⟩
    refine ⟨(t : AddCircle p), ?_⟩
    exact AddCircle.liftIco_coe_apply ht

/-- Lift an explicit scalar loop to the Euclidean unit circle. -/
noncomputable def planeCircleLift
    {X : Type*} (p a : Real) (hp : 0 < p) (loop : Real -> X) :
    PlaneUnitCircle -> X := by
  haveI : Fact (0 < p) := ⟨hp⟩
  exact AddCircle.liftIco p a loop ∘ planeUnitCircleEquivAddCircle p hp

/-- Endpoint agreement plus interval continuity gives a continuous map from
the Euclidean unit circle. -/
theorem continuous_planeCircleLift
    {X : Type*} [TopologicalSpace X]
    {p a : Real} (hp : 0 < p) {loop : Real -> X}
    (hend : loop a = loop (a + p))
    (hcontinuous : ContinuousOn loop (Icc a (a + p))) :
    Continuous (planeCircleLift p a hp loop) := by
  haveI : Fact (0 < p) := ⟨hp⟩
  exact (AddCircle.liftIco_continuous hend hcontinuous).comp
    (planeUnitCircleEquivAddCircle p hp).continuous

/-- Half-open injectivity gives injectivity after the unit-circle lift. -/
theorem planeCircleLift_injective
    {X : Type*} {p a : Real} (hp : 0 < p) {loop : Real -> X}
    (hinj : Set.InjOn loop (Ico a (a + p))) :
    Function.Injective (planeCircleLift p a hp loop) := by
  haveI : Fact (0 < p) := ⟨hp⟩
  exact (liftIco_injective_of_injOn hinj).comp
    (planeUnitCircleEquivAddCircle p hp).injective

/-- The lifted unit-circle range is the image of the half-open scalar
fundamental interval. -/
theorem range_planeCircleLift
    {X : Type*} {p a : Real} (hp : 0 < p) (loop : Real -> X) :
    range (planeCircleLift p a hp loop) =
      loop '' Ico a (a + p) := by
  haveI : Fact (0 < p) := ⟨hp⟩
  rw [planeCircleLift, (planeUnitCircleEquivAddCircle p hp).surjective.range_comp]
  exact range_liftIco loop

/-- The compact-Hausdorff bridge used to discharge `Topology.IsEmbedding`.
No Jordan conclusion is assumed. -/
theorem planeCircleLift_isEmbedding
    {X : Type*} [TopologicalSpace X] [T2Space X]
    {p a : Real} (hp : 0 < p) {loop : Real -> X}
    (hend : loop a = loop (a + p))
    (hcontinuous : ContinuousOn loop (Icc a (a + p)))
    (hinj : Set.InjOn loop (Ico a (a + p))) :
    Topology.IsEmbedding (planeCircleLift p a hp loop) := by
  haveI : Fact (0 < p) := ⟨hp⟩
  have hlift : Topology.IsEmbedding (AddCircle.liftIco p a loop) :=
    ((AddCircle.liftIco_continuous hend hcontinuous).isClosedEmbedding
      (liftIco_injective_of_injOn hinj)).isEmbedding
  exact hlift.comp (planeUnitCircleEquivAddCircle p hp).isEmbedding

/-- A faithful scalar loop realization of a set gives a closed Jordan curve.
The hypotheses are the elementary continuity, half-open injectivity, and
literal range calculation that the skirt producer must prove. -/
theorem isClosedJordanCurve_of_loop
    {p a : Real} (hp : 0 < p) {loop : Real -> Real × Real}
    (hend : loop a = loop (a + p))
    (hcontinuous : ContinuousOn loop (Icc a (a + p)))
    (hinj : Set.InjOn loop (Ico a (a + p)))
    {E : Set (Real × Real)}
    (hrange : loop '' Ico a (a + p) = E) :
    IsClosedJordanCurve E := by
  refine ⟨planeCircleLift p a hp loop,
    planeCircleLift_isEmbedding hp hend hcontinuous hinj, ?_⟩
  exact (range_planeCircleLift hp loop).trans hrange

#print axioms complexCircleEquivPlaneUnitCircle
#print axioms planeUnitCircleEquivAddCircle
#print axioms liftIco_injective_of_injOn
#print axioms range_liftIco
#print axioms continuous_planeCircleLift
#print axioms planeCircleLift_injective
#print axioms range_planeCircleLift
#print axioms planeCircleLift_isEmbedding
#print axioms isClosedJordanCurve_of_loop

end

end FamilyStickyCinematicL32Prop41CircleLiftEmbeddingV1
