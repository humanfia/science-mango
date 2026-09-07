import Family8Grounding.Family8Family7NativeHighCriticalBallRestrictedSourceV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8Family7NativeHighCriticalBallUnionMassV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Family4GlobalExtremalUpstream
open Family8Family7NativeHighCriticalBallRestrictedSourceV1
open FamilyStickyCinematicL32Prop41ActualPositiveCenterHighPayloadWeightedFullyActualConnectorV1
open FamilyStickyCinematicL32PyzActualNormFirstAllCenterMassWeightedBranchTypesV5C

noncomputable section

/-!
# Occurrence-correct mass charge for the union of native critical balls

A spatial first-hit partition assigns a point only once, but a point may lie
in several shading carriers.  The honest object to assign is therefore the
tube occurrence.  This file implements that assignment without a callback:
take the literal union of all canonical critical balls and sum the original
carrier masses on that union.

The union mass is bounded by the sum of the literal critical-ball shading
masses, hence by one maximal ball times the number of high centres.  To
identify the union mass with the original shading mass it is enough to prove
the pointwise support statement that every positive-mass carrier belongs to
some canonical critical ball.  This is the precise remaining producer
obligation; no desired mass conclusion is stored as input.
-/

/-- The literal union of all canonical critical balls at high centres. -/
noncomputable def nativeHighCriticalBallUnion
    {radius : NNReal} {iota : Type} [Fintype iota] [DecidableEq iota]
    (D : NativeBranchCore radius iota) : Finset iota :=
  Finset.univ.biUnion fun c : D.HighCenter =>
    (positiveCenterHighPayloadGlobalNormData
      (D.chosenHighPayloadAt c)).criticalBall

@[simp] theorem mem_nativeHighCriticalBallUnion
    {radius : NNReal} {iota : Type} [Fintype iota] [DecidableEq iota]
    (D : NativeBranchCore radius iota) (i : iota) :
    i ∈ nativeHighCriticalBallUnion D ↔
      ∃ c : D.HighCenter,
        i ∈ (positiveCenterHighPayloadGlobalNormData
          (D.chosenHighPayloadAt c)).criticalBall := by
  classical
  simp [nativeHighCriticalBallUnion]

/-- Original shading mass carried by the literal union of critical balls. -/
noncomputable def nativeHighCriticalBallUnionMass
    {radius : NNReal} {iota : Type} [Fintype iota] [DecidableEq iota]
    (D : NativeBranchCore radius iota)
    (Y : Shading D.S.family.bodyFamily) : ENNReal :=
  ∑ i ∈ nativeHighCriticalBallUnion D, volume (Y.carrier i)

private theorem sum_biUnion_le_sum_sum
    {owner item : Type} [DecidableEq owner] [DecidableEq item]
    (cells : Finset owner) (ball : owner → Finset item)
    (weight : item → ENNReal) :
    (∑ i ∈ cells.biUnion ball, weight i) ≤
      ∑ c ∈ cells, ∑ i ∈ ball c, weight i := by
  classical
  calc
    (∑ i ∈ cells.biUnion ball, weight i) ≤
        ∑ i ∈ cells.biUnion ball,
          ∑ c ∈ cells, if i ∈ ball c then weight i else 0 := by
      apply Finset.sum_le_sum
      intro i hi
      obtain ⟨c, hc, hic⟩ := Finset.mem_biUnion.mp hi
      have hsingle := Finset.single_le_sum
        (s := cells)
        (f := fun c => if i ∈ ball c then weight i else 0)
        (fun _ _ => show (0 : ENNReal) ≤ _ from bot_le) hc
      simpa only [hic, if_true] using hsingle
    _ = ∑ c ∈ cells,
        ∑ i ∈ cells.biUnion ball,
          if i ∈ ball c then weight i else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ c ∈ cells, ∑ i ∈ ball c, weight i := by
      apply Finset.sum_congr rfl
      intro c hc
      rw [← Finset.sum_filter]
      congr 1
      ext i
      simp only [Finset.mem_filter]
      constructor
      · exact fun hi => hi.2
      · intro hi
        exact ⟨Finset.mem_biUnion.mpr ⟨c, hc, hi⟩, hi⟩

/-- Counting occurrences rather than spatial points gives the exact robust
union-to-ball mass inequality, with arbitrary overlaps allowed. -/
theorem nativeHighCriticalBallUnionMass_le_sum_shadingMass
    {radius : NNReal} {iota : Type} [Fintype iota] [DecidableEq iota]
    (D : NativeBranchCore radius iota)
    (Y : Shading D.S.family.bodyFamily) :
    nativeHighCriticalBallUnionMass D Y ≤
      ∑ c : D.HighCenter,
        (nativeHighCriticalBallShading D c Y).shadingMass := by
  classical
  unfold nativeHighCriticalBallUnionMass nativeHighCriticalBallUnion
  calc
    (∑ i ∈ (Finset.univ : Finset D.HighCenter).biUnion
        (fun c => (positiveCenterHighPayloadGlobalNormData
          (D.chosenHighPayloadAt c)).criticalBall),
        volume (Y.carrier i)) ≤
      ∑ c ∈ (Finset.univ : Finset D.HighCenter),
        ∑ i ∈ (positiveCenterHighPayloadGlobalNormData
          (D.chosenHighPayloadAt c)).criticalBall,
          volume (Y.carrier i) :=
      sum_biUnion_le_sum_sum
        (Finset.univ : Finset D.HighCenter)
        (fun c => (positiveCenterHighPayloadGlobalNormData
          (D.chosenHighPayloadAt c)).criticalBall)
        (fun i => volume (Y.carrier i))
    _ = ∑ c : D.HighCenter,
        (nativeHighCriticalBallShading D c Y).shadingMass := by
      apply Finset.sum_congr rfl
      intro c _hc
      exact (nativeHighCriticalBallShading_shadingMass D c Y).symm

/-- A nonempty high-centre family contains one critical ball carrying the
union mass up to the exact number of high centres. -/
theorem exists_nativeHighCriticalBallShadingMass_charge_union
    {radius : NNReal} {iota : Type} [Fintype iota] [DecidableEq iota]
    (D : NativeBranchCore radius iota)
    (Y : Shading D.S.family.bodyFamily)
    (hcenters : Nonempty D.HighCenter) :
    ∃ c : D.HighCenter,
      nativeHighCriticalBallUnionMass D Y ≤
        (Fintype.card D.HighCenter : ENNReal) *
          (nativeHighCriticalBallShading D c Y).shadingMass := by
  classical
  let mass : D.HighCenter → ENNReal := fun c =>
    (nativeHighCriticalBallShading D c Y).shadingMass
  have huniv : (Finset.univ : Finset D.HighCenter).Nonempty :=
    Finset.univ_nonempty
  obtain ⟨c, _hc, hmax⟩ := Finset.exists_max_image Finset.univ mass huniv
  have hsum := Finset.sum_le_card_nsmul Finset.univ mass (mass c)
    (fun k hk => hmax k hk)
  refine ⟨c, (nativeHighCriticalBallUnionMass_le_sum_shadingMass D Y).trans ?_⟩
  simpa only [mass, Finset.card_univ, nsmul_eq_mul] using hsum

/-- Pointwise positive-mass support in the critical-ball union is exactly
what is needed to recover the full original shading mass. -/
theorem nativeHighCriticalBallUnionMass_eq_shadingMass_of_support
    {radius : NNReal} {iota : Type} [Fintype iota] [DecidableEq iota]
    (D : NativeBranchCore radius iota)
    (Y : Shading D.S.family.bodyFamily)
    (hsupport : ∀ i, volume (Y.carrier i) ≠ 0 →
      i ∈ nativeHighCriticalBallUnion D) :
    nativeHighCriticalBallUnionMass D Y = Y.shadingMass := by
  classical
  unfold nativeHighCriticalBallUnionMass Shading.shadingMass
  apply Finset.sum_subset (Finset.subset_univ _)
  intro i _hi hnot
  by_contra hne
  exact hnot (hsupport i hne)

/-- The occurrence-correct pointwise producer criterion gives a critical
ball with an extremal mass charge, without a mass-valued callback. -/
theorem exists_nativeHighCriticalBallShadingMass_extremalCharge_of_support
    {radius : NNReal} {iota : Type} [Fintype iota] [DecidableEq iota]
    (D : NativeBranchCore radius iota)
    {Y : Shading D.S.family.bodyFamily}
    {parallelLoss : Nat} {epsilon sigma : Real}
    (E : EpsilonExtremalTubeFamily D.S.family Y D.ambient parallelLoss
      epsilon sigma)
    (hcenters : Nonempty D.HighCenter)
    (hsupport : ∀ i, volume (Y.carrier i) ≠ 0 →
      i ∈ nativeHighCriticalBallUnion D) :
    ∃ c : D.HighCenter,
      (radius : ENNReal) ^ epsilon ≤
        (Fintype.card D.HighCenter : ENNReal) *
          (nativeHighCriticalBallShading D c Y).shadingMass := by
  obtain ⟨c, hcharge⟩ :=
    exists_nativeHighCriticalBallShadingMass_charge_union D Y hcenters
  refine ⟨c, E.shading_mass_lower.trans ?_⟩
  rw [← nativeHighCriticalBallUnionMass_eq_shadingMass_of_support
    D Y hsupport]
  exact hcharge

/-- A literal ambient index cover is a sufficient geometric producer for
the positive-mass support criterion, using the extremal support field. -/
theorem exists_nativeHighCriticalBallShadingMass_extremalCharge_of_ambientCover
    {radius : NNReal} {iota : Type} [Fintype iota] [DecidableEq iota]
    (D : NativeBranchCore radius iota)
    {Y : Shading D.S.family.bodyFamily}
    {parallelLoss : Nat} {epsilon sigma : Real}
    (E : EpsilonExtremalTubeFamily D.S.family Y D.ambient parallelLoss
      epsilon sigma)
    (hcenters : Nonempty D.HighCenter)
    (hcover : D.ambient ⊆ nativeHighCriticalBallUnion D) :
    ∃ c : D.HighCenter,
      (radius : ENNReal) ^ epsilon ≤
        (Fintype.card D.HighCenter : ENNReal) *
          (nativeHighCriticalBallShading D c Y).shadingMass := by
  apply exists_nativeHighCriticalBallShadingMass_extremalCharge_of_support
    D E hcenters
  intro i hmass
  by_cases hi : i ∈ D.ambient
  · exact hcover hi
  · rw [E.support i hi, measure_empty] at hmass
    exact (hmass rfl).elim

#print axioms nativeHighCriticalBallUnion
#print axioms nativeHighCriticalBallUnionMass_le_sum_shadingMass
#print axioms exists_nativeHighCriticalBallShadingMass_charge_union
#print axioms nativeHighCriticalBallUnionMass_eq_shadingMass_of_support
#print axioms
  exists_nativeHighCriticalBallShadingMass_extremalCharge_of_support
#print axioms
  exists_nativeHighCriticalBallShadingMass_extremalCharge_of_ambientCover

end

end Family8Family7NativeHighCriticalBallUnionMassV1
