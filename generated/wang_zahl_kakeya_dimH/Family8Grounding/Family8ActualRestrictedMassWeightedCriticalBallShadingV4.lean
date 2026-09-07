import Family8Grounding.Family8Family7WeightedCriticalBallMassRetentionV2
import Family8Grounding.Family8WeightedCanonicalCriticalBallShadingUnionV1
import FamilyStickyGrounding.FamilyStickyWZ2AmbientRestrictedIntegralAdapterV1
import Mathlib.Tactic

/-!
# Actual restricted-mass weights and their literal critical-ball shading, V3

V1 omitted the namespace providing `Space`; V2 used a wrong qualification
for `restrictedMass`; V3 did not zeta the outer theorem-result lets.  This
clean successor imports no predecessor.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1400000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8ActualRestrictedMassWeightedCriticalBallShadingV4

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open Family8Family7NativeHighWeightedCriticalBallV1
open Family8Family7WeightedCriticalBallMassRetentionV2
open Family8WeightedCanonicalCriticalBallShadingUnionV1
open Family8WeightedCanonicalCriticalScaleProxyAverageV2
open FamilyStickyCinematicL32WZL3UniformTubeSourceV1
open FamilyStickyWZ2ShadingPopularityV2

noncomputable section

universe u

def restrictedShading
    {iota : Type u} {F : ConvexFamily iota}
    (Y : Shading F) (X : Set Space) (hX : MeasurableSet X) : Shading F where
  carrier i := Y.carrier i ∩ X
  measurable_carrier i := (Y.measurable_carrier i).inter hX
  carrier_subset i := inter_subset_left.trans (Y.carrier_subset i)

@[simp] theorem restrictedShading_carrier
    {iota : Type u} {F : ConvexFamily iota}
    (Y : Shading F) (X : Set Space) (hX : MeasurableSet X) (i : iota) :
    (restrictedShading Y X hX).carrier i = Y.carrier i ∩ X :=
  rfl

theorem restrictedShading_shadingMass
    {iota : Type u} [Fintype iota] {F : ConvexFamily iota}
    (Y : Shading F) (X : Set Space) (hX : MeasurableSet X) :
    (restrictedShading Y X hX).shadingMass =
      ∑ i, restrictedMass Y X i := by
  rfl

def actualRestrictedMassWeightedNormData
    {iota : Type u} (D : WeightedCanonicalNormBallData iota)
    {F : ConvexFamily iota} (Y : Shading F) (X : Set Space) :
    WeightedCanonicalNormBallData iota where
  family := D.family
  distance := D.distance
  weight := fun i => restrictedMass Y X i
  delta := D.delta
  ceiling := D.ceiling
  exponent := D.exponent
  family_nonempty := D.family_nonempty
  self_le_delta := D.self_le_delta
  delta_pos := D.delta_pos
  delta_le_ceiling := D.delta_le_ceiling
  exponent_nonneg := D.exponent_nonneg

@[simp] theorem actualRestrictedMassWeightedNormData_family
    {iota : Type u} (D : WeightedCanonicalNormBallData iota)
    {F : ConvexFamily iota} (Y : Shading F) (X : Set Space) :
    (actualRestrictedMassWeightedNormData D Y X).family = D.family :=
  rfl

@[simp] theorem actualRestrictedMassWeightedNormData_weight
    {iota : Type u} (D : WeightedCanonicalNormBallData iota)
    {F : ConvexFamily iota} (Y : Shading F) (X : Set Space) (i : iota) :
    (actualRestrictedMassWeightedNormData D Y X).weight i =
      restrictedMass Y X i :=
  rfl

theorem actualRestrictedMass_criticalBallShadingMass
    {radius : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    (S : WZL3UniformTubeSource radius iota)
    (D : WeightedCanonicalNormBallData iota)
    (Y : Shading S.family.bodyFamily)
    (X : Set Space) (hX : MeasurableSet X) :
    let W := actualRestrictedMassWeightedNormData D Y X
    (weightedCanonicalCriticalBallShading S W
      (restrictedShading Y X hX)).shadingMass =
        ∑ i ∈ W.criticalBall, W.weight i := by
  let W := actualRestrictedMassWeightedNormData D Y X
  unfold Shading.shadingMass
  simp only [weightedCanonicalCriticalBallShading, restrictedShading,
    actualRestrictedMassWeightedNormData, restrictedMass]
  symm
  exact Finset.sum_subtype _ (fun _i => Iff.rfl) _

theorem actualRestrictedMass_total_le_card_mul_criticalBallShadingMass
    {radius : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    (S : WZL3UniformTubeSource radius iota)
    (D : WeightedCanonicalNormBallData iota)
    (Y : Shading S.family.bodyFamily)
    (X : Set Space) (hX : MeasurableSet X) :
    let W := actualRestrictedMassWeightedNormData D Y X
    (∑ i ∈ W.family, restrictedMass Y X i) ≤
      (W.family.card : ENNReal) *
        (weightedCanonicalCriticalBallShading S W
          (restrictedShading Y X hX)).shadingMass := by
  dsimp only
  let W := actualRestrictedMassWeightedNormData D Y X
  have hretention := totalWeight_le_card_mul_criticalBallWeight W
  rw [actualRestrictedMass_criticalBallShadingMass S D Y X hX]
  simpa only [W, actualRestrictedMassWeightedNormData_weight] using hretention

theorem actualRestrictedMass_criticalBallShadedUnion_subset
    {radius : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    (S : WZL3UniformTubeSource radius iota)
    (D : WeightedCanonicalNormBallData iota)
    (Y : Shading S.family.bodyFamily)
    (X : Set Space) (hX : MeasurableSet X) :
    let W := actualRestrictedMassWeightedNormData D Y X
    (weightedCanonicalCriticalBallShading S W
      (restrictedShading Y X hX)).shadedUnion ⊆ Y.shadedUnion := by
  dsimp only
  let W := actualRestrictedMassWeightedNormData D Y X
  intro x hx
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
  exact Set.mem_iUnion.mpr ⟨i.1, hi.1⟩

#print axioms restrictedShading
#print axioms restrictedShading_shadingMass
#print axioms actualRestrictedMassWeightedNormData
#print axioms actualRestrictedMass_criticalBallShadingMass
#print axioms actualRestrictedMass_total_le_card_mul_criticalBallShadingMass
#print axioms actualRestrictedMass_criticalBallShadedUnion_subset

end
end Family8ActualRestrictedMassWeightedCriticalBallShadingV4
