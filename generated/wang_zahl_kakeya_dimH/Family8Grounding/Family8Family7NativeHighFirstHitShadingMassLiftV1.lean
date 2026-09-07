import Family8Grounding.Family8Family7NativeHighCriticalBallRestrictedSourceV1
import Family8Grounding.Family8FrostmanCinematicFirstHitMassDecompositionV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1500000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8Family7NativeHighFirstHitShadingMassLiftV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Family4GlobalExtremalUpstream
open Family8Family7NativeHighCriticalBallRestrictedSourceV1
open Family8FrostmanCinematicFirstHitMassDecompositionV1
open FamilyStickyWZ2ShadingPopularityV2
open FamilyStickyCinematicL32Lemma55FiniteMeasurableFirstHitPartitionV1
open FamilyStickyCinematicL32Prop41ActualPositiveCenterHighPayloadWeightedFullyActualConnectorV1
open FamilyStickyCinematicL32PyzActualNormFirstAllCenterMassWeightedBranchTypesV5C

noncomputable section

/-!
# Honest first-hit ownership lift to native critical-ball shading mass

This is the minimal 3D interface missing from the current E2 native branch.
A finite first-hit cover of the actual shaded union is accompanied only by a
pointwise ownership fact: if a shading occurrence lies in an owner's
first-hit cell, then its tube index lies in that owner's literal canonical
critical ball.  No mass lower bound or conclusion is stored as input.

The pointwise fact automatically yields a global mass charge and a finite
pigeonhole center whose restricted critical-ball shading retains the source
mass up to the number of owners.
-/

theorem firstHit_cellRestrictedShadingMass_le_nativeHighCriticalBallShadingMass
    {radius : NNReal} {iota : Type} [Fintype iota] [DecidableEq iota]
    {owner : Type} [DecidableEq owner]
    (D : NativeBranchCore radius iota) (Y : Shading D.S.family.bodyFamily)
    (cells : Finset owner) (event : owner → Set Space)
    (centerAt : owner → D.HighCenter) (o : owner)
    (howner : ∀ i p,
      p ∈ finiteFirstHitFiber Y.shadedUnion cells event o →
      p ∈ Y.carrier i →
      i ∈ (positiveCenterHighPayloadGlobalNormData
        (D.chosenHighPayloadAt (centerAt o))).criticalBall) :
    cellRestrictedShadingMass Y
        (finiteFirstHitFiber Y.shadedUnion cells event o) ≤
      (nativeHighCriticalBallShading D (centerAt o) Y).shadingMass := by
  classical
  let ball := (positiveCenterHighPayloadGlobalNormData
    (D.chosenHighPayloadAt (centerAt o))).criticalBall
  rw [nativeHighCriticalBallShading_shadingMass]
  unfold cellRestrictedShadingMass restrictedMass
  calc
    (∑ i, volume
        (Y.carrier i ∩ finiteFirstHitFiber Y.shadedUnion cells event o)) ≤
        ∑ i, if i ∈ ball then volume (Y.carrier i) else 0 := by
      apply Finset.sum_le_sum
      intro i _hi
      by_cases hiBall : i ∈ ball
      · simp only [hiBall, if_true]
        exact measure_mono Set.inter_subset_left
      · have hempty :
            Y.carrier i ∩ finiteFirstHitFiber Y.shadedUnion cells event o =
              ∅ := by
          ext p
          constructor
          · intro hp
            exact (hiBall (howner i p hp.2 hp.1)).elim
          · intro hp
            exact hp.elim
        rw [hempty, measure_empty]
        simp only [hiBall, if_false, le_refl]
    _ = ∑ i ∈ ball, volume (Y.carrier i) := by
      simp [ball]

theorem shadingMass_le_sum_nativeHighCriticalBallShadingMass_of_firstHitOwner
    {radius : NNReal} {iota : Type} [Fintype iota] [DecidableEq iota]
    {owner : Type} [DecidableEq owner]
    (D : NativeBranchCore radius iota) (Y : Shading D.S.family.bodyFamily)
    (cells : Finset owner) (event : owner → Set Space)
    (centerAt : owner → D.HighCenter)
    (hmeasurable : ∀ o, o ∈ cells → MeasurableSet (event o))
    (hcover : ∀ p, p ∈ Y.shadedUnion →
      ∃ o, o ∈ cells ∧ p ∈ event o)
    (howner : ∀ o, o ∈ cells → ∀ i p,
      p ∈ finiteFirstHitFiber Y.shadedUnion cells event o →
      p ∈ Y.carrier i →
      i ∈ (positiveCenterHighPayloadGlobalNormData
        (D.chosenHighPayloadAt (centerAt o))).criticalBall) :
    Y.shadingMass ≤
      ∑ o ∈ cells,
        (nativeHighCriticalBallShading D (centerAt o) Y).shadingMass := by
  calc
    Y.shadingMass =
        ∑ o ∈ cells, cellRestrictedShadingMass Y
          (finiteFirstHitFiber Y.shadedUnion cells event o) := by
      symm
      exact sum_firstHit_cellRestrictedShadingMass_eq_shadingMass
        Y cells event hmeasurable hcover
    _ ≤ ∑ o ∈ cells,
        (nativeHighCriticalBallShading D (centerAt o) Y).shadingMass := by
      exact Finset.sum_le_sum fun o ho =>
        firstHit_cellRestrictedShadingMass_le_nativeHighCriticalBallShadingMass
          D Y cells event centerAt o (howner o ho)

theorem exists_nativeHighCriticalBallShadingMass_charge_of_firstHitOwner
    {radius : NNReal} {iota : Type} [Fintype iota] [DecidableEq iota]
    {owner : Type} [DecidableEq owner]
    (D : NativeBranchCore radius iota) (Y : Shading D.S.family.bodyFamily)
    (cells : Finset owner) (event : owner → Set Space)
    (centerAt : owner → D.HighCenter) (hcells : cells.Nonempty)
    (hmeasurable : ∀ o, o ∈ cells → MeasurableSet (event o))
    (hcover : ∀ p, p ∈ Y.shadedUnion →
      ∃ o, o ∈ cells ∧ p ∈ event o)
    (howner : ∀ o, o ∈ cells → ∀ i p,
      p ∈ finiteFirstHitFiber Y.shadedUnion cells event o →
      p ∈ Y.carrier i →
      i ∈ (positiveCenterHighPayloadGlobalNormData
        (D.chosenHighPayloadAt (centerAt o))).criticalBall) :
    ∃ o, o ∈ cells ∧
      Y.shadingMass ≤ (cells.card : ENNReal) *
        (nativeHighCriticalBallShading D (centerAt o) Y).shadingMass := by
  classical
  let mass : owner → ENNReal := fun o =>
    (nativeHighCriticalBallShading D (centerAt o) Y).shadingMass
  obtain ⟨o, ho, hmax⟩ := Finset.exists_max_image cells mass hcells
  have hsum := Finset.sum_le_card_nsmul cells mass (mass o)
    (fun k hk => hmax k hk)
  refine ⟨o, ho, ?_⟩
  calc
    Y.shadingMass ≤ ∑ k ∈ cells,
        (nativeHighCriticalBallShading D (centerAt k) Y).shadingMass :=
      shadingMass_le_sum_nativeHighCriticalBallShadingMass_of_firstHitOwner
        D Y cells event centerAt hmeasurable hcover howner
    _ ≤ (cells.card : ENNReal) *
        (nativeHighCriticalBallShading D (centerAt o) Y).shadingMass := by
      simpa only [mass, nsmul_eq_mul] using hsum

theorem exists_nativeHighCriticalBallShadingMass_extremalCharge_of_firstHitOwner
    {radius : NNReal} {iota : Type} [Fintype iota] [DecidableEq iota]
    {owner : Type} [DecidableEq owner]
    (D : NativeBranchCore radius iota)
    {Y : Shading D.S.family.bodyFamily}
    {parallelLoss : Nat} {epsilon sigma : Real}
    (E : EpsilonExtremalTubeFamily D.S.family Y D.ambient parallelLoss
      epsilon sigma)
    (cells : Finset owner) (event : owner → Set Space)
    (centerAt : owner → D.HighCenter) (hcells : cells.Nonempty)
    (hmeasurable : ∀ o, o ∈ cells → MeasurableSet (event o))
    (hcover : ∀ p, p ∈ Y.shadedUnion →
      ∃ o, o ∈ cells ∧ p ∈ event o)
    (howner : ∀ o, o ∈ cells → ∀ i p,
      p ∈ finiteFirstHitFiber Y.shadedUnion cells event o →
      p ∈ Y.carrier i →
      i ∈ (positiveCenterHighPayloadGlobalNormData
        (D.chosenHighPayloadAt (centerAt o))).criticalBall) :
    ∃ o, o ∈ cells ∧
      (radius : ENNReal) ^ epsilon ≤ (cells.card : ENNReal) *
        (nativeHighCriticalBallShading D (centerAt o) Y).shadingMass := by
  obtain ⟨o, ho, hcharge⟩ :=
    exists_nativeHighCriticalBallShadingMass_charge_of_firstHitOwner
      D Y cells event centerAt hcells hmeasurable hcover howner
  exact ⟨o, ho, E.shading_mass_lower.trans hcharge⟩

#print axioms firstHit_cellRestrictedShadingMass_le_nativeHighCriticalBallShadingMass
#print axioms shadingMass_le_sum_nativeHighCriticalBallShadingMass_of_firstHitOwner
#print axioms exists_nativeHighCriticalBallShadingMass_charge_of_firstHitOwner
#print axioms exists_nativeHighCriticalBallShadingMass_extremalCharge_of_firstHitOwner

end

end Family8Family7NativeHighFirstHitShadingMassLiftV1
