import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41ActualChoiceOfShiftPairLocalBridgeV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41FiniteGeneralPositionExactRootReproductionV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41WeightedThreeShiftPigeonholeV1

set_option autoImplicit false
set_option warningAsError true

open Set
open scoped BigOperators ENNReal

namespace FamilyStickyCinematicL32Prop41ActualChoiceOfShiftPairLocalWeightedBridgeV1

open Submission.Kakeya.ConvexGeometry
open FamilyStickyCinematicL32ActualTubeConstantShiftV1
open FamilyStickyCinematicL32CurvilinearRectangleCarrierV1
open FamilyStickyCinematicL32CurvilinearRectanglePointMultiplicityV1
open FamilyStickyCinematicL32Prop41ActualChoiceOfShiftPairLocalBridgeV1
open FamilyStickyCinematicL32Prop41FiniteGeneralPositionExactRootReproductionV1
open FamilyStickyCinematicL32Prop41PairLocalActualLensRectangleCoreV1
open FamilyStickyCinematicL32Prop41TangencyProductToScaleV1
open FamilyStickyCinematicL32Prop41ThreeShiftPigeonholeV1
open FamilyStickyCinematicL32Prop41WeightedThreeShiftPigeonholeV1

noncomputable section

universe u

/-!
# Weighted actual trace-shift selection

The geometric pointwise existence theorem is unchanged.  Only the final
finite pigeonhole choice is made using an arbitrary `ENNReal` weight.  A
singleton invocation of the existing actual bridge exposes the pointwise
valid shift without duplicating its analytic proof.
-/

/-- Weight-aware actual `choiceOfShift`: a common trace translation retains
at least one third of the prescribed mass and returns the same complete
pair-local data as the cardinal version. -/
theorem exists_uniform_threeShift_weighted_pairLocalActualLensRectangleData
    {alpha : Type u} [DecidableEq alpha] {radius : NNReal}
    (items : Finset alpha) (T U : alpha -> Tube radius)
    (rectangles : alpha -> C2GraphRectangle)
    (f f1 f2 : Real -> Real)
    {A B delta t rho q lambda : Real}
    (hitems : items.Nonempty)
    (hdelta : 0 < delta) (ht : 0 < t) (hq : 1 <= q)
    (hlambda : 0 < lambda) (hrhoLambda : rho <= lambda)
    (hshiftDominates : 10 * prop41TangencyScaleFactor q < lambda)
    (hstrengthenedScale :
      (10 * prop41TangencyScaleFactor q + lambda) * delta <
        t / 46080)
    (htraceRadius : 2 * (rho * delta) <= q * delta)
    (hwidth : (1 / 2 : Real) <= B - A)
    (hfDeriv : forall z, z ∈ Icc A B -> HasDerivAt f (f1 z) z)
    (hf1Deriv : forall z, z ∈ Icc A B -> HasDerivAt f1 (f2 z) z)
    (hparameter : forall z, z ∈ Icc A B -> |z| <= 1)
    (hft : forall z, z ∈ Icc A B -> |f z| <= 2)
    (hf1Lower : forall z, z ∈ Icc A B -> 1 <= |f1 z|)
    (hf1Upper : forall z, z ∈ Icc A B -> |f1 z| <= 2)
    (hf2 : forall z, z ∈ Icc A B -> |f2 z| <= 1 / 100)
    (hf2Continuous : ContinuousOn f2 (Icc A B))
    (data : forall i, i ∈ items ->
      ActualTwoFamilyRectangleTangencyData
        (T i) (U i) f (rectangles i) A B delta t rho)
    (weight : alpha -> ENNReal) :
    exists (k : Fin 3) (eta : Real) (fiber : Finset alpha)
      (_D : forall i, i ∈ fiber ->
        PairLocalActualLensRectangleData
          (traceTranslateTube (T i) (eta * (lambda * delta)))
          (U i) f (rectangles i) A B delta t lambda),
      eta = threeShiftValue k ∧
      eta ∈ ({(-1 : Real), 0, 1} : Set Real) ∧
      fiber.Nonempty ∧
      fiber ⊆ items ∧
      finiteENNRealWeight items weight <=
        3 * finiteENNRealWeight fiber weight := by
  let good : alpha -> Fin 3 -> Prop := fun i k =>
    Nonempty (PairLocalActualLensRectangleData
      (traceTranslateTube (T i) (threeShiftValue k * (lambda * delta)))
      (U i) f (rectangles i) A B delta t lambda)
  have hgood : forall i, i ∈ items -> exists k : Fin 3, good i k := by
    intro i hi
    have hsingleton : ({i} : Finset alpha).Nonempty := by simp
    have hsingletonData : forall j, j ∈ ({i} : Finset alpha) ->
        ActualTwoFamilyRectangleTangencyData
          (T j) (U j) f (rectangles j) A B delta t rho := by
      intro j hj
      have hji : j = i := Finset.mem_singleton.mp hj
      subst j
      exact data i hi
    obtain ⟨k, eta, fiber, P, heta, _hetaMem, hfiber,
        hfiberSubset, _hcard⟩ :=
      exists_uniform_threeShift_pairLocalActualLensRectangleData
        ({i} : Finset alpha) T U rectangles f f1 f2 hsingleton hdelta ht hq
          hlambda hrhoLambda hshiftDominates hstrengthenedScale htraceRadius
            hwidth hfDeriv hf1Deriv hparameter hft hf1Lower hf1Upper hf2
              hf2Continuous hsingletonData
    obtain ⟨j, hjFiber⟩ := hfiber
    have hji : j = i := Finset.mem_singleton.mp (hfiberSubset hjFiber)
    subst j
    refine ⟨k, ?_⟩
    dsimp only [good]
    exact ⟨by simpa only [heta] using P i hjFiber⟩
  obtain ⟨k, hfiber, hfiberSubset, hweight, hfiberGood⟩ :=
    exists_uniform_threeShift_weighted_fiber items good weight hitems hgood
  let fiber := threeShiftFiber items
    (chosenThreeShiftLabel items good hgood) k
  let D : forall i, i ∈ fiber ->
      PairLocalActualLensRectangleData
        (traceTranslateTube (T i)
          (threeShiftValue k * (lambda * delta)))
        (U i) f (rectangles i) A B delta t lambda := fun i hi => by
    have hi' : i ∈ threeShiftFiber items
        (chosenThreeShiftLabel items good hgood) k := by
      simpa only [fiber] using hi
    exact Classical.choice (hfiberGood i hi')
  refine ⟨k, threeShiftValue k, fiber, D, rfl, threeShiftValue_mem k,
    ?_, ?_, ?_⟩
  · simpa only [fiber] using hfiber
  · simpa only [fiber] using hfiberSubset
  · simpa only [fiber] using hweight


/-- Weight-aware strengthened actual choice of shift.  The selected common
shift retains at least one third of the prescribed mass and every survivor
keeps the strict root-interiority, coefficient, and tangency slack required
by the finite general-position perturbation. -/
theorem exists_uniform_threeShift_weighted_perturbationReadyPairLocalActualLensRectangleData
    {alpha : Type u} [DecidableEq alpha] {radius : NNReal}
    (items : Finset alpha) (T U : alpha -> Tube radius)
    (rectangles : alpha -> C2GraphRectangle)
    (f f1 f2 : Real -> Real)
    {A B delta t rho q lambda : Real}
    (hitems : items.Nonempty)
    (hdelta : 0 < delta) (ht : 0 < t) (hq : 1 <= q)
    (hlambda : 0 < lambda) (hrhoLambda : rho <= lambda)
    (hshiftDominates : 10 * prop41TangencyScaleFactor q < lambda)
    (hstrengthenedScale :
      (10 * prop41TangencyScaleFactor q + lambda) * delta <
        t / 46080)
    (htraceRadius : 2 * (rho * delta) <= q * delta)
    (hwidth : (1 / 2 : Real) <= B - A)
    (hfDeriv : forall z, z ∈ Icc A B -> HasDerivAt f (f1 z) z)
    (hf1Deriv : forall z, z ∈ Icc A B -> HasDerivAt f1 (f2 z) z)
    (hparameter : forall z, z ∈ Icc A B -> |z| <= 1)
    (hft : forall z, z ∈ Icc A B -> |f z| <= 2)
    (hf1Lower : forall z, z ∈ Icc A B -> 1 <= |f1 z|)
    (hf1Upper : forall z, z ∈ Icc A B -> |f1 z| <= 2)
    (hf2 : forall z, z ∈ Icc A B -> |f2 z| <= 1 / 100)
    (hf2Continuous : ContinuousOn f2 (Icc A B))
    (data : forall i, i ∈ items ->
      ActualTwoFamilyRectangleTangencyData
        (T i) (U i) f (rectangles i) A B delta t rho)
    (weight : alpha -> ENNReal) :
    exists (k : Fin 3) (eta : Real) (fiber : Finset alpha)
      (_P : forall i, i ∈ fiber ->
        PerturbationReadyPairLocalActualLensRectangleData
          (traceTranslateTube (T i) (eta * (lambda * delta)))
          (U i) f (rectangles i) A B delta t lambda (2 * lambda)),
      eta = threeShiftValue k ∧
      eta ∈ ({(-1 : Real), 0, 1} : Set Real) ∧
      fiber.Nonempty ∧
      fiber ⊆ items ∧
      finiteENNRealWeight items weight <=
        3 * finiteENNRealWeight fiber weight := by
  let good : alpha -> Fin 3 -> Prop := fun i k =>
    Nonempty (PerturbationReadyPairLocalActualLensRectangleData
      (traceTranslateTube (T i) (threeShiftValue k * (lambda * delta)))
      (U i) f (rectangles i) A B delta t lambda (2 * lambda))
  have hgood : forall i, i ∈ items -> exists k : Fin 3, good i k := by
    intro i hi
    have hsingleton : ({i} : Finset alpha).Nonempty := by simp
    have hsingletonData : forall j, j ∈ ({i} : Finset alpha) ->
        ActualTwoFamilyRectangleTangencyData
          (T j) (U j) f (rectangles j) A B delta t rho := by
      intro j hj
      have hji : j = i := Finset.mem_singleton.mp hj
      subst j
      exact data i hi
    obtain ⟨k, eta, fiber, P, heta, _hetaMem, hfiber,
        hfiberSubset, _hcard⟩ :=
      exists_uniform_threeShift_perturbationReadyPairLocalActualLensRectangleData
        ({i} : Finset alpha) T U rectangles f f1 f2 hsingleton hdelta ht hq
          hlambda hrhoLambda hshiftDominates hstrengthenedScale htraceRadius
            hwidth hfDeriv hf1Deriv hparameter hft hf1Lower hf1Upper hf2
              hf2Continuous hsingletonData
    obtain ⟨j, hjFiber⟩ := hfiber
    have hji : j = i := Finset.mem_singleton.mp (hfiberSubset hjFiber)
    subst j
    refine ⟨k, ?_⟩
    dsimp only [good]
    exact ⟨by simpa only [heta] using P i hjFiber⟩
  obtain ⟨k, hfiber, hfiberSubset, hweight, hfiberGood⟩ :=
    exists_uniform_threeShift_weighted_fiber items good weight hitems hgood
  let fiber := threeShiftFiber items
    (chosenThreeShiftLabel items good hgood) k
  let P : forall i, i ∈ fiber ->
      PerturbationReadyPairLocalActualLensRectangleData
        (traceTranslateTube (T i)
          (threeShiftValue k * (lambda * delta)))
        (U i) f (rectangles i) A B delta t lambda (2 * lambda) := fun i hi => by
    have hiFiber : i ∈ threeShiftFiber items
        (chosenThreeShiftLabel items good hgood) k := by
      simpa only [fiber] using hi
    exact Classical.choice (hfiberGood i hiFiber)
  refine ⟨k, threeShiftValue k, fiber, P, rfl, threeShiftValue_mem k,
    ?_, ?_, ?_⟩
  · simpa only [fiber] using hfiber
  · simpa only [fiber] using hfiberSubset
  · simpa only [fiber] using hweight

#print axioms exists_uniform_threeShift_weighted_pairLocalActualLensRectangleData
#print axioms exists_uniform_threeShift_weighted_perturbationReadyPairLocalActualLensRectangleData

end

end FamilyStickyCinematicL32Prop41ActualChoiceOfShiftPairLocalWeightedBridgeV1
