import Family8Grounding.Family8Family7NativeHighCriticalBallDatumV1
import Submission.Kakeya.ConvexFactoring.TubeHierarchyInfrastructure
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8Family7NativeHighCriticalBallRestrictedSourceV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family4GlobalExtremalUpstream
open FamilyStickyCinematicL32Prop41ActualPositiveCenterHighPayloadWeightedFullyActualConnectorV1
open FamilyStickyCinematicL32Prop41CanonicalMaximizerNonconcentrationV1
open FamilyStickyCinematicL32PyzActualNormFirstAllCenterMassWeightedBranchTypesV5C
open FamilyStickyCinematicL32WZL3UniformTubeSourceV1
open Family8Family7NativeHighCriticalBallDatumV1

noncomputable section

universe u

/-!
# Literal restricted source on the native-high critical ball

This successor reindexes the actual canonical critical ball as a genuine
uniform tube family.  The fixed `L_3` chart, unit-ball containment,
essential distinctness, and all scale-cover bounds restrict from the actual
upstream extremal family.  The restricted shading has its literal finite
mass sum and a shaded union contained in the source union.

Consequently every epsilon-extremal field except the restricted shading-mass
lower bound is automatic.  The final theorem exposes precisely that one
remaining scalar premise; it contains no conclusion-valued callback.
-/

abbrev NativeHighCriticalBallIndex
    {radius : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    (D : NativeBranchCore radius iota) (c : D.HighCenter) :=
  {i // i ∈ (positiveCenterHighPayloadGlobalNormData
    (D.chosenHighPayloadAt c)).criticalBall}

/-- The literal critical-ball subfamily, with every subtype index active. -/
def nativeHighCriticalBallFamily
    {radius : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    (D : NativeBranchCore radius iota) (c : D.HighCenter) :
    UniformTubeFamily radius (NativeHighCriticalBallIndex D c) :=
  D.S.family.restrictTo
    (positiveCenterHighPayloadGlobalNormData
      (D.chosenHighPayloadAt c)).criticalBall

@[simp] theorem nativeHighCriticalBallFamily_tubes
    {radius : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    (D : NativeBranchCore radius iota) (c : D.HighCenter)
    (i : NativeHighCriticalBallIndex D c) :
    (nativeHighCriticalBallFamily D c).tubes i = D.S.family.tubes i.1 :=
  rfl

@[simp] theorem nativeHighCriticalBallFamily_refined
    {radius : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    (D : NativeBranchCore radius iota) (c : D.HighCenter) :
    (nativeHighCriticalBallFamily D c).refinement.refined = Finset.univ :=
  rfl

/-- Restricting the actual upstream shading to the critical-ball subtype. -/
def nativeHighCriticalBallShading
    {radius : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    (D : NativeBranchCore radius iota) (c : D.HighCenter)
    (Y : Shading D.S.family.bodyFamily) :
    Shading (nativeHighCriticalBallFamily D c).bodyFamily where
  carrier i := Y.carrier i.1
  measurable_carrier i := Y.measurable_carrier i.1
  carrier_subset i := Y.carrier_subset i.1

@[simp] theorem nativeHighCriticalBallShading_carrier
    {radius : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    (D : NativeBranchCore radius iota) (c : D.HighCenter)
    (Y : Shading D.S.family.bodyFamily)
    (i : NativeHighCriticalBallIndex D c) :
    (nativeHighCriticalBallShading D c Y).carrier i = Y.carrier i.1 :=
  rfl

/-- The restricted mass is exactly the literal finite sum on the canonical
critical ball. -/
theorem nativeHighCriticalBallShading_shadingMass
    {radius : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    (D : NativeBranchCore radius iota) (c : D.HighCenter)
    (Y : Shading D.S.family.bodyFamily) :
    (nativeHighCriticalBallShading D c Y).shadingMass =
      ∑ i ∈ (positiveCenterHighPayloadGlobalNormData
        (D.chosenHighPayloadAt c)).criticalBall,
          volume (Y.carrier i) := by
  unfold Shading.shadingMass
  simpa only [nativeHighCriticalBallShading_carrier,
    Finset.univ_eq_attach] using
      Finset.sum_attach
        (positiveCenterHighPayloadGlobalNormData
          (D.chosenHighPayloadAt c)).criticalBall
        (fun i => volume (Y.carrier i))

/-- The literal restricted union is contained in the original shaded union. -/
theorem nativeHighCriticalBallShading_shadedUnion_subset
    {radius : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    (D : NativeBranchCore radius iota) (c : D.HighCenter)
    (Y : Shading D.S.family.bodyFamily) :
    (nativeHighCriticalBallShading D c Y).shadedUnion ⊆ Y.shadedUnion := by
  intro x hx
  rcases Set.mem_iUnion.mp hx with ⟨i, hi⟩
  exact Set.mem_iUnion.mpr ⟨i.1, hi⟩

/-- Essential distinctness survives literal subtype restriction. -/
theorem nativeHighCriticalBallFamily_pairwise_essentiallyDistinct
    {radius : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    (D : NativeBranchCore radius iota) (c : D.HighCenter)
    (datum : NativeHighCriticalBallDatum D c) :
    Set.Pairwise (Set.univ : Set (NativeHighCriticalBallIndex D c))
      (fun i j => EssentiallyDistinct
        ((nativeHighCriticalBallFamily D c).tubes i)
        ((nativeHighCriticalBallFamily D c).tubes j)) := by
  intro i _hi j _hj hij
  exact datum.pairwise_essentiallyDistinct i.2 j.2
    (Subtype.coe_ne_coe.mpr hij)

/-- Unit-ball containment survives literal subtype restriction. -/
theorem nativeHighCriticalBallFamily_contained_in_unit_ball
    {radius : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    (D : NativeBranchCore radius iota) (c : D.HighCenter)
    (datum : NativeHighCriticalBallDatum D c) :
    ∀ i : NativeHighCriticalBallIndex D c,
      ((nativeHighCriticalBallFamily D c).tubes i).carrier ⊆
        Metric.closedBall (0 : Space) 1 := by
  intro i
  exact datum.contained_in_unit_ball i.1 i.2

/-- The original `L_3` chart restricts to the literal critical ball. -/
def nativeHighCriticalBallWZL3Source
    {radius : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    (D : NativeBranchCore radius iota) (c : D.HighCenter)
    (datum : NativeHighCriticalBallDatum D c)
    (hambientSource : D.ambient ⊆ D.S.source) :
    WZL3UniformTubeSource radius (NativeHighCriticalBallIndex D c) where
  family := nativeHighCriticalBallFamily D c
  source := Finset.univ
  source_direction_final_half := by
    intro i _hi
    apply D.S.source_direction_final_half i.1
    apply hambientSource
    exact datum.subset_physicalAmbient i.2

@[simp] theorem nativeHighCriticalBallWZL3Source_source
    {radius : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    (D : NativeBranchCore radius iota) (c : D.HighCenter)
    (datum : NativeHighCriticalBallDatum D c)
    (hambientSource : D.ambient ⊆ D.S.source) :
    (nativeHighCriticalBallWZL3Source D c datum hambientSource).source =
      Finset.univ :=
  rfl

/-- Every upstream extremal scale cover restricts to the critical-ball
subtype without increasing its parallel-cluster loss. -/
theorem exists_nativeHighCriticalBall_scaleCover
    {radius tau : NNReal} {iota : Type u}
    [Fintype iota] [DecidableEq iota]
    (D : NativeBranchCore radius iota) (c : D.HighCenter)
    {Y : Shading D.S.family.bodyFamily}
    {parallelLoss : Nat} {epsilon sigma : Real}
    (E : EpsilonExtremalTubeFamily D.S.family Y D.ambient parallelLoss
      epsilon sigma)
    (datum : NativeHighCriticalBallDatum D c)
    (hradiusTau : radius ≤ tau) (htauOne : tau ≤ 1) :
    ∃ C : @TubeScaleCover radius tau (NativeHighCriticalBallIndex D c) _
        (nativeHighCriticalBallFamily D c) Finset.univ,
      ∀ U : Tube tau, (C.parallelCluster U).card ≤ parallelLoss := by
  obtain ⟨C, hC⟩ := E.scale_covers tau hradiusTau htauOne
  let C' : @TubeScaleCover radius tau (NativeHighCriticalBallIndex D c) _
      (nativeHighCriticalBallFamily D c) Finset.univ :=
    { count := C.count
      tubes := C.tubes
      parent := fun i => C.parent i.1
      carrier_subset := by
        intro i _hi
        apply C.carrier_subset i.1
        exact datum.subset_physicalAmbient i.2 }
  refine ⟨C', ?_⟩
  intro U
  exact hC U

/-- All epsilon-extremal fields on the literal critical-ball restriction are
automatic except its actual shading-mass lower bound. -/
theorem nativeHighCriticalBall_epsilonExtremal_of_shadingMassLower
    {radius : NNReal} {iota : Type u}
    [Fintype iota] [DecidableEq iota]
    (D : NativeBranchCore radius iota) (c : D.HighCenter)
    {Y : Shading D.S.family.bodyFamily}
    {parallelLoss : Nat} {epsilon sigma : Real}
    (E : EpsilonExtremalTubeFamily D.S.family Y D.ambient parallelLoss
      epsilon sigma)
    (datum : NativeHighCriticalBallDatum D c)
    (hmass : (radius : ENNReal) ^ epsilon ≤
      (nativeHighCriticalBallShading D c Y).shadingMass) :
    EpsilonExtremalTubeFamily
      (nativeHighCriticalBallFamily D c)
      (nativeHighCriticalBallShading D c Y) Finset.univ parallelLoss
      epsilon sigma := by
  refine {
    delta_pos := E.delta_pos
    delta_le_half := E.delta_le_half
    epsilon_pos := E.epsilon_pos
    active_nonempty := ?_
    support := ?_
    contained_in_unit_ball := ?_
    essentially_distinct := ?_
    parallelLoss_rounds_power := E.parallelLoss_rounds_power
    scale_covers := ?_
    shading_mass_lower := hmass
    union_volume_upper := ?_ }
  · obtain ⟨i, hi⟩ := datum.nonempty
    exact ⟨⟨i, hi⟩, Finset.mem_univ _⟩
  · intro i hi
    exact (hi (Finset.mem_univ i)).elim
  · intro i _hi
    exact nativeHighCriticalBallFamily_contained_in_unit_ball D c datum i
  · simpa only [Finset.coe_univ] using
      nativeHighCriticalBallFamily_pairwise_essentiallyDistinct D c datum
  · intro tau hradiusTau htauOne
    exact exists_nativeHighCriticalBall_scaleCover D c E datum
      hradiusTau htauOne
  · exact (measure_mono
      (nativeHighCriticalBallShading_shadedUnion_subset D c Y)).trans
        E.union_volume_upper

#print axioms nativeHighCriticalBallFamily
#print axioms nativeHighCriticalBallShading_shadingMass
#print axioms nativeHighCriticalBallShading_shadedUnion_subset
#print axioms nativeHighCriticalBallFamily_pairwise_essentiallyDistinct
#print axioms nativeHighCriticalBallFamily_contained_in_unit_ball
#print axioms nativeHighCriticalBallWZL3Source
#print axioms exists_nativeHighCriticalBall_scaleCover
#print axioms nativeHighCriticalBall_epsilonExtremal_of_shadingMassLower

end

end Family8Family7NativeHighCriticalBallRestrictedSourceV1
