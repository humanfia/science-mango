import FamilyStickyGrounding.FamilyStickyHierarchyEndpointPrefixBridgeV1
import FamilyStickyGrounding.FamilyStickyParentFiberMassDecompositionV6
import FamilyStickyGrounding.FamilyStickyWZ2ProjectionSliceRetentionV1

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 3000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace FamilyStickyHierarchyEndpointPrefixShadingTransportV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyAdjacentScaleStepV2.StickyScaleCover
open FamilyStickyParentFiberMassDecompositionV6.StickyScaleCover
open FamilyStickyScaleChainArbitraryRadiusInterpolationV1
open FamilyStickyHierarchyEndpointPrefixBridgeV1
open FamilyStickyHierarchyEndpointPrefixBridgeV1.Identification
open FamilyStickyHierarchyPreMotionHullTestSupportV1
open FamilyStickyHierarchySuppliedPackingJointRandomMotionV1
open FamilyStickyWZ2ProjectionSliceRetentionV1

noncomputable section

/-!
# Endpoint-to-prefix coverage and shading transport

The endpoint-to-prefix bridge supplies an injective, body-preserving map of
indexed convex families.  This module records what that data really transports:

* family coverage and summed family volume move monotonically to the prefix;
* a shading extends by the empty set away from the embedded range, preserving
  its shaded union, shading mass, and every set-theoretic projection union;
* a `StickyScaleCover` aggregates active fine shading pieces inside their
  literal parents, preserving the shaded union and losing at most the actual
  parent-fibre cardinality in summed shading mass; and
* composing the two constructions gives an actual shading of the supplied
  hierarchy prefix, with no conclusion supplied as a field.

The final section isolates the exact remaining issue.  An embedding need not
exhaust the prefix indices, so it cannot preserve the denominator
`familyVolume` or a shading-density lower bound.  Exhaustion is sufficient,
and the empty-to-singleton example proves it is not automatic.
-/

/-! ## Generic body-preserving embedding transport -/

/-- An injective reindexing which preserves each actual convex body. -/
structure BodyPreservingEmbedding
    {iota kappa : Type*} [Fintype iota] [Fintype kappa]
    (F : ConvexFamily iota) (G : ConvexFamily kappa) where
  index : iota ↪ kappa
  body_eq : forall i, F i = G (index i)

namespace BodyPreservingEmbedding

variable {iota kappa : Type*} [Fintype iota] [Fintype kappa]
  {F : ConvexFamily iota} {G : ConvexFamily kappa}
  (E : BodyPreservingEmbedding F G)
include E

/-- Extend a source carrier family by the empty set off the embedded range. -/
def pushforwardCarrier (Y : Shading F) : kappa -> Set Space :=
  Function.extend E.index Y.carrier (fun _ => ∅)

@[simp]
theorem pushforwardCarrier_index (Y : Shading F) (i : iota) :
    E.pushforwardCarrier Y (E.index i) = Y.carrier i := by
  exact E.index.injective.extend_apply Y.carrier (fun _ => ∅) i

theorem pushforwardCarrier_of_not_range (Y : Shading F) (j : kappa)
    (hj : ¬ exists i, E.index i = j) :
    E.pushforwardCarrier Y j = ∅ := by
  exact Function.extend_apply' (f := E.index) Y.carrier (fun _ => ∅) j hj

theorem mem_pushforwardCarrier_iff (Y : Shading F) (j : kappa) (x : Space) :
    x ∈ E.pushforwardCarrier Y j <->
      exists i, E.index i = j ∧ x ∈ Y.carrier i := by
  constructor
  · intro hx
    by_cases hj : exists i, E.index i = j
    · obtain ⟨i, rfl⟩ := hj
      exact ⟨i, rfl, by simpa using hx⟩
    · rw [E.pushforwardCarrier_of_not_range Y j hj] at hx
      exact hx.elim
  · rintro ⟨i, rfl, hx⟩
    simpa using hx

/-- Empty extension is a genuine shading of the larger body family. -/
def pushforwardShading (Y : Shading F) : Shading G where
  carrier := E.pushforwardCarrier Y
  measurable_carrier := by
    intro j
    by_cases hj : exists i, E.index i = j
    · obtain ⟨i, rfl⟩ := hj
      simpa using Y.measurable_carrier i
    · rw [E.pushforwardCarrier_of_not_range Y j hj]
      exact MeasurableSet.empty
  carrier_subset := by
    intro j x hx
    obtain ⟨i, hi, hxi⟩ := (E.mem_pushforwardCarrier_iff Y j x).mp hx
    subst j
    simpa only [← E.body_eq i] using Y.carrier_subset i hxi

@[simp]
theorem pushforwardShading_carrier_index (Y : Shading F) (i : iota) :
    (E.pushforwardShading Y).carrier (E.index i) = Y.carrier i :=
  E.pushforwardCarrier_index Y i

/-- Every source body occurs literally in the target family. -/
theorem familyUnion_subset : familyUnion F ⊆ familyUnion G := by
  intro x hx
  obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hx
  apply Set.mem_iUnion.mpr
  refine ⟨E.index i, ?_⟩
  simpa only [← E.body_eq i] using hxi

/-- Injective body-preserving reindexing cannot decrease summed family
volume.  Repetitions are retained because the map is injective. -/
theorem familyVolume_le : familyVolume F <= familyVolume G := by
  classical
  unfold familyVolume
  calc
    (∑ i : iota, volume (F i : Set Space)) =
        ∑ i : iota, volume (G (E.index i) : Set Space) := by
      apply Finset.sum_congr rfl
      intro i _hi
      rw [E.body_eq i]
    _ = ∑ j ∈ (Finset.univ : Finset iota).image E.index,
        volume (G j : Set Space) := by
      rw [Finset.sum_image]
      intro i _hi i' _hi' hii'
      exact E.index.injective hii'
    _ <= ∑ j : kappa, volume (G j : Set Space) := by
      exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)

/-- Empty extension preserves the exact shaded union. -/
theorem pushforwardShading_shadedUnion (Y : Shading F) :
    (E.pushforwardShading Y).shadedUnion = Y.shadedUnion := by
  ext x
  constructor
  · intro hx
    obtain ⟨j, hxj⟩ := Set.mem_iUnion.mp hx
    obtain ⟨i, _hi, hxi⟩ :=
      (E.mem_pushforwardCarrier_iff Y j x).mp hxj
    exact Set.mem_iUnion.mpr ⟨i, hxi⟩
  · intro hx
    obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hx
    exact Set.mem_iUnion.mpr ⟨E.index i, by simpa using hxi⟩

/-- Empty extension preserves summed shading mass exactly. -/
theorem pushforwardShading_shadingMass (Y : Shading F) :
    (E.pushforwardShading Y).shadingMass = Y.shadingMass := by
  classical
  unfold Shading.shadingMass
  change (∑ j : kappa, volume (E.pushforwardCarrier Y j)) =
    ∑ i : iota, volume (Y.carrier i)
  calc
    (∑ j : kappa, volume (E.pushforwardCarrier Y j)) =
        ∑ j ∈ (Finset.univ : Finset iota).image E.index,
          volume (E.pushforwardCarrier Y j) := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro j _hj hjImage
      have hjRange : ¬ exists i, E.index i = j := by
        intro h
        obtain ⟨i, rfl⟩ := h
        exact hjImage (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)
      rw [E.pushforwardCarrier_of_not_range Y j hjRange]
      simp
    _ = ∑ i : iota, volume (E.pushforwardCarrier Y (E.index i)) := by
      rw [Finset.sum_image]
      intro i _hi i' _hi' hii'
      exact E.index.injective hii'
    _ = ∑ i : iota, volume (Y.carrier i) := by
      apply Finset.sum_congr rfl
      intro i _hi
      rw [E.pushforwardCarrier_index]

/-- Every set-valued map, in particular WZ2's twisted projection, sees the
same indexed union after empty extension. -/
theorem iUnion_image_pushforwardShading
    {omega : Type*} (p : Space -> omega) (Y : Shading F) :
    (⋃ j, p '' (E.pushforwardShading Y).carrier j) =
      ⋃ i, p '' Y.carrier i := by
  ext z
  constructor
  · intro hz
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hz
    obtain ⟨x, hx, rfl⟩ := hj
    obtain ⟨i, _hi, hxi⟩ :=
      (E.mem_pushforwardCarrier_iff Y j x).mp hx
    exact Set.mem_iUnion.mpr ⟨i, ⟨x, hxi, rfl⟩⟩
  · intro hz
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hz
    obtain ⟨x, hxi, rfl⟩ := hi
    apply Set.mem_iUnion.mpr
    exact ⟨E.index i, ⟨x, by simpa using hxi, rfl⟩⟩

/-- Surjectivity is exactly enough to upgrade coverage monotonicity to
equality. -/
theorem familyUnion_eq_of_surjective
    (hsurj : Function.Surjective E.index) :
    familyUnion F = familyUnion G := by
  apply Set.Subset.antisymm E.familyUnion_subset
  intro x hx
  obtain ⟨j, hxj⟩ := Set.mem_iUnion.mp hx
  obtain ⟨i, rfl⟩ := hsurj j
  apply Set.mem_iUnion.mpr
  refine ⟨i, ?_⟩
  simpa only [E.body_eq i] using hxj

/-- Surjectivity also removes the possible extra denominator in the target
family volume. -/
theorem familyVolume_eq_of_surjective
    (hsurj : Function.Surjective E.index) :
    familyVolume F = familyVolume G := by
  classical
  unfold familyVolume
  have hImage : (Finset.univ : Finset iota).image E.index =
      (Finset.univ : Finset kappa) := by
    ext j
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · intro _h
      trivial
    · intro _h
      exact hsurj j
  calc
    (∑ i : iota, volume (F i : Set Space)) =
        ∑ i : iota, volume (G (E.index i) : Set Space) := by
      apply Finset.sum_congr rfl
      intro i _hi
      rw [E.body_eq i]
    _ = ∑ j ∈ (Finset.univ : Finset iota).image E.index,
        volume (G j : Set Space) := by
      rw [Finset.sum_image]
      intro i _hi i' _hi' hii'
      exact E.index.injective hii'
    _ = ∑ j : kappa, volume (G j : Set Space) := by rw [hImage]

/-- With range exhaustion, empty extension preserves shading density as well
as shading mass. -/
theorem pushforwardShading_shadingDensity_of_surjective
    (Y : Shading F) (hsurj : Function.Surjective E.index) :
    (E.pushforwardShading Y).shadingDensity = Y.shadingDensity := by
  unfold Shading.shadingDensity
  rw [E.pushforwardShading_shadingMass Y,
    E.familyVolume_eq_of_surjective hsurj]

end BodyPreservingEmbedding

/-! ## Parent aggregation for an actual Sticky cover -/

namespace StickyScaleCover

variable {delta rho : NNReal} {iota : Type*}
  [Fintype iota] [DecidableEq iota]
  {fine : UniformTubeFamily delta iota}
  (S : StickyScaleCover fine rho)

/-- Restrict a source shading to the active fine occurrences of this cover. -/
def activeFineShading (Y : Shading fine.bodyFamily) :
    Shading (activeFineFamily S) where
  carrier := fun i => Y.carrier i.1
  measurable_carrier := fun i => Y.measurable_carrier i.1
  carrier_subset := fun i => Y.carrier_subset i.1

/-- The literal active-subtype factorization induced by the cover's parent
map. -/
def activeIndexFactorization :
    IndexFactorization
      {i // i ∈ S.activeFine} {k // k ∈ S.activeCoarse} where
  fine := Finset.univ
  coarse := Finset.univ
  parent := fun i => ⟨S.parent i.1, S.parent_mem i.1 i.2⟩
  parent_mem := by simp

/-- Union all active fine shading pieces assigned to one literal parent. -/
def parentAggregatedCarrier (Y : Shading fine.bodyFamily)
    (k : {k // k ∈ S.activeCoarse}) : Set Space :=
  ⋃ i ∈ ((activeIndexFactorization S).fiber k), Y.carrier i.1

/-- Parent aggregation is a genuine shading of the active coarse family;
validity follows from the cover's carrier containment. -/
def parentAggregatedShading (Y : Shading fine.bodyFamily) :
    Shading S.activeCoarseFamily where
  carrier := parentAggregatedCarrier S Y
  measurable_carrier := by
    intro k
    exact MeasurableSet.biUnion
      ((activeIndexFactorization S).fiber k).countable_toSet
      (fun i _hi => Y.measurable_carrier i.1)
  carrier_subset := by
    intro k x hx
    obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hx
    obtain ⟨hiFiber, hxiY⟩ := Set.mem_iUnion.mp hxi
    have hiParent :=
      (IndexFactorization.mem_fiber (activeIndexFactorization S) i k).mp hiFiber
    have hFine : x ∈ (fine.tubes i.1).carrier := by
      simpa [UniformTubeFamily.bodyFamily] using
        Y.carrier_subset i.1 hxiY
    have hCoarse := S.carrier_subset i.1 i.2 hFine
    have hParentEq : S.parent i.1 = k.1 := by
      exact congrArg Subtype.val hiParent.2
    simpa [FamilyStickyAtEveryScaleCoreV1.StickyScaleCover.activeCoarseFamily,
      UniformTubeFamily.bodyFamily, hParentEq] using hCoarse

/-- The active fine bodies are covered by their active parent bodies. -/
theorem familyUnion_activeFine_subset_activeCoarse :
    familyUnion (activeFineFamily S) ⊆ familyUnion S.activeCoarseFamily := by
  intro x hx
  obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hx
  let k : {k // k ∈ S.activeCoarse} :=
    ⟨S.parent i.1, S.parent_mem i.1 i.2⟩
  apply Set.mem_iUnion.mpr
  refine ⟨k, ?_⟩
  have hFine : x ∈ (fine.tubes i.1).carrier := by
    simpa [activeFineFamily, UniformTubeFamily.bodyFamily] using hxi
  have hCoarse := S.carrier_subset i.1 i.2 hFine
  simpa [k, FamilyStickyAtEveryScaleCoreV1.StickyScaleCover.activeCoarseFamily,
    UniformTubeFamily.bodyFamily] using hCoarse

/-- Parent aggregation preserves the shaded union exactly. -/
theorem parentAggregatedShading_shadedUnion
    (Y : Shading fine.bodyFamily) :
    (parentAggregatedShading S Y).shadedUnion =
      (activeFineShading S Y).shadedUnion := by
  ext x
  constructor
  · intro hx
    obtain ⟨k, hxk⟩ := Set.mem_iUnion.mp hx
    obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hxk
    obtain ⟨_hiFiber, hxiY⟩ := Set.mem_iUnion.mp hxi
    exact Set.mem_iUnion.mpr ⟨i, hxiY⟩
  · intro hx
    obtain ⟨i, hxiY⟩ := Set.mem_iUnion.mp hx
    let k : {k // k ∈ S.activeCoarse} :=
      ⟨S.parent i.1, S.parent_mem i.1 i.2⟩
    have hiFiber : i ∈ (activeIndexFactorization S).fiber k := by
      rw [IndexFactorization.mem_fiber]
      exact ⟨Finset.mem_univ i, rfl⟩
    apply Set.mem_iUnion.mpr
    refine ⟨k, Set.mem_iUnion.mpr ⟨i, ?_⟩⟩
    exact Set.mem_iUnion.mpr ⟨hiFiber, hxiY⟩

/-- Any projection sees exactly the same union before and after literal
parent aggregation. -/
theorem iUnion_image_parentAggregatedShading
    {omega : Type*} (p : Space -> omega)
    (Y : Shading fine.bodyFamily) :
    (⋃ k, p '' (parentAggregatedShading S Y).carrier k) =
      ⋃ i, p '' (activeFineShading S Y).carrier i := by
  ext z
  constructor
  · intro hz
    obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hz
    obtain ⟨x, hx, rfl⟩ := hk
    have hxFine : x ∈ (activeFineShading S Y).shadedUnion := by
      rw [← parentAggregatedShading_shadedUnion S Y]
      exact Set.mem_iUnion.mpr ⟨k, hx⟩
    obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hxFine
    exact Set.mem_iUnion.mpr ⟨i, ⟨x, hxi, rfl⟩⟩
  · intro hz
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hz
    obtain ⟨x, hxi, rfl⟩ := hi
    have hxParent : x ∈ (parentAggregatedShading S Y).shadedUnion := by
      rw [parentAggregatedShading_shadedUnion S Y]
      exact Set.mem_iUnion.mpr ⟨i, hxi⟩
    obtain ⟨k, hxk⟩ := Set.mem_iUnion.mp hxParent
    exact Set.mem_iUnion.mpr ⟨k, ⟨x, hxk, rfl⟩⟩

/-- Exact regrouping of the active fine shading mass by actual parent
fibres. -/
theorem activeFineShading_shadingMass_eq_sum_fibers
    (Y : Shading fine.bodyFamily) :
    (activeFineShading S Y).shadingMass =
      ∑ k : {k // k ∈ S.activeCoarse},
        ∑ i ∈ (activeIndexFactorization S).fiber k,
          volume (Y.carrier i.1) := by
  simpa [Shading.shadingMass, activeFineShading,
    activeIndexFactorization] using
      (activeIndexFactorization S).sum_fiberwise
        (fun i => volume (Y.carrier i.1))

/-- Merging pieces inside a parent can only decrease total shading mass. -/
theorem parentAggregatedShading_shadingMass_le
    (Y : Shading fine.bodyFamily) :
    (parentAggregatedShading S Y).shadingMass <=
      (activeFineShading S Y).shadingMass := by
  rw [activeFineShading_shadingMass_eq_sum_fibers S Y]
  unfold Shading.shadingMass
  apply Finset.sum_le_sum
  intro k _hk
  exact measure_biUnion_finset_le
    ((activeIndexFactorization S).fiber k) (fun i => Y.carrier i.1)

/-- The reverse loss is exactly controlled by the actual parent-fibre
cardinality, with no geometric estimate hidden in the statement. -/
theorem activeFineShading_shadingMass_le_sum_fiberCard_nsmul
    (Y : Shading fine.bodyFamily) :
    (activeFineShading S Y).shadingMass <=
      ∑ k : {k // k ∈ S.activeCoarse},
        ((activeIndexFactorization S).fiber k).card •
          volume ((parentAggregatedShading S Y).carrier k) := by
  rw [activeFineShading_shadingMass_eq_sum_fibers S Y]
  apply Finset.sum_le_sum
  intro k _hk
  apply Finset.sum_le_card_nsmul
  intro i hi
  apply measure_mono
  intro x hxi
  exact Set.mem_iUnion.mpr ⟨i,
    Set.mem_iUnion.mpr ⟨hi, hxi⟩⟩

/-- A uniform literal fibre-card bound converts the exact weighted loss to a
single multiplicative loss. -/
theorem activeFineShading_shadingMass_le_nsmul_parent_of_fiberCard_le
    (Y : Shading fine.bodyFamily) (M : Nat)
    (hM : forall k : {k // k ∈ S.activeCoarse},
      ((activeIndexFactorization S).fiber k).card <= M) :
    (activeFineShading S Y).shadingMass <=
      M • (parentAggregatedShading S Y).shadingMass := by
  calc
    (activeFineShading S Y).shadingMass <=
        ∑ k : {k // k ∈ S.activeCoarse},
          ((activeIndexFactorization S).fiber k).card •
            volume ((parentAggregatedShading S Y).carrier k) :=
      activeFineShading_shadingMass_le_sum_fiberCard_nsmul S Y
    _ <= ∑ k : {k // k ∈ S.activeCoarse},
        M • volume ((parentAggregatedShading S Y).carrier k) := by
      apply Finset.sum_le_sum
      intro k _hk
      exact nsmul_le_nsmul_left (by positivity) (hM k)
    _ = M • (parentAggregatedShading S Y).shadingMass := by
      unfold Shading.shadingMass
      simp_rw [nsmul_eq_mul]
      rw [Finset.mul_sum]

end StickyScaleCover

/-! ## The actual endpoint-to-supplied-prefix composite -/

variable {depth : Nat} {nominalRadius : Nat -> NNReal}
  {Index : Nat -> Type*}
  [forall l, Fintype (Index l)] [forall l, DecidableEq (Index l)]
  (H : MultiscaleTubeHierarchy depth nominalRadius Index)
  {G : FamilyStickyHierarchyRandomMotionAdapterV1.HierarchyRandomMotionGeometry H}
  {P : HierarchyPackingPlan.Plan H}
  (Q : SuppliedHierarchy.Certificate H G P)
  (C : FamilyStickyScaleChainCoherentIntervalProducerV1.CoherentStickyMultiscaleCover
    (H.effectiveFamily 0))
  (S : FamilyStickyDividingScalesFiniteStoppingV1.FiniteScaleSequence
    (H.effectiveRadius 0) depth)

namespace Identification

variable {H Q C S}
  (I : FamilyStickyHierarchyEndpointPrefixBridgeV1.Identification H Q C S)

/-- The endpoint-prefix identification as a reusable body-preserving
embedding certificate. -/
def endpointPrefixBodyEmbedding (m : Fin depth) :
    BodyPreservingEmbedding
      (endpointFamily H C S m)
      (suppliedPrefixFamily H Q (I.effectivePrefix.path m)
        (I.endpointEffective.layer m) (I.effectivePrefix.parent m)) where
  index := I.endpointPrefixEmbedding m
  body_eq := I.endpointPrefix_body_eq m

/-- Aggregate the active level-zero shading in the endpoint parents and then
extend it by empty pieces to the literal supplied prefix. -/
def suppliedPrefixShading (m : Fin depth)
    (Y : Shading (H.effectiveFamily 0).bodyFamily) :
    Shading
      (suppliedPrefixFamily H Q (I.effectivePrefix.path m)
        (I.endpointEffective.layer m) (I.effectivePrefix.parent m)) :=
  (endpointPrefixBodyEmbedding I m).pushforwardShading
    (StickyScaleCover.parentAggregatedShading (upperEndpointCover C S m) Y)

/-- Body coverage composes from active fine tubes, through the endpoint
parents, into the supplied hierarchy prefix. -/
theorem familyUnion_activeFine_subset_suppliedPrefix (m : Fin depth) :
    familyUnion (activeFineFamily (upperEndpointCover C S m)) ⊆
      familyUnion
        (suppliedPrefixFamily H Q (I.effectivePrefix.path m)
          (I.endpointEffective.layer m) (I.effectivePrefix.parent m)) := by
  exact (StickyScaleCover.familyUnion_activeFine_subset_activeCoarse (upperEndpointCover C S m)).trans
    (endpointPrefixBodyEmbedding I m).familyUnion_subset

/-- The supplied-prefix shading covers exactly the active fine shaded union,
not a merely comparable surrogate. -/
theorem suppliedPrefixShading_shadedUnion (m : Fin depth)
    (Y : Shading (H.effectiveFamily 0).bodyFamily) :
    (suppliedPrefixShading I m Y).shadedUnion =
      (StickyScaleCover.activeFineShading (upperEndpointCover C S m) Y).shadedUnion := by
  rw [suppliedPrefixShading,
    BodyPreservingEmbedding.pushforwardShading_shadedUnion,
    StickyScaleCover.parentAggregatedShading_shadedUnion]

/-- The only automatic summed-mass change in the composite is the honest
within-parent union loss. -/
theorem suppliedPrefixShading_shadingMass_le (m : Fin depth)
    (Y : Shading (H.effectiveFamily 0).bodyFamily) :
    (suppliedPrefixShading I m Y).shadingMass <=
      (StickyScaleCover.activeFineShading (upperEndpointCover C S m) Y).shadingMass := by
  rw [suppliedPrefixShading,
    BodyPreservingEmbedding.pushforwardShading_shadingMass]
  exact StickyScaleCover.parentAggregatedShading_shadingMass_le (upperEndpointCover C S m) Y

/-- WZ2's literal twisted projection sees exactly the original active fine
shading union after the full endpoint-to-prefix transport. -/
theorem twistedProjection_iUnion_suppliedPrefixShading
    (m : Fin depth) (f : Real -> Real)
    (Y : Shading (H.effectiveFamily 0).bodyFamily) :
    (⋃ j, twistedProjection f ''
        (suppliedPrefixShading I m Y).carrier j) =
      ⋃ i, twistedProjection f ''
        (StickyScaleCover.activeFineShading (upperEndpointCover C S m) Y).carrier i := by
  rw [suppliedPrefixShading,
    BodyPreservingEmbedding.iUnion_image_pushforwardShading,
    StickyScaleCover.iUnion_image_parentAggregatedShading]

/-- The endpoint family contributes no more summed body volume than the
literal supplied prefix; equality additionally requires range exhaustion. -/
theorem familyVolume_endpoint_le_suppliedPrefix (m : Fin depth) :
    familyVolume (endpointFamily H C S m) <=
      familyVolume
        (suppliedPrefixFamily H Q (I.effectivePrefix.path m)
          (I.endpointEffective.layer m) (I.effectivePrefix.parent m)) :=
  (endpointPrefixBodyEmbedding I m).familyVolume_le

end Identification

/-! ## Sharp obstruction to denominator transport from an embedding alone -/

/-- The unique embedding from the empty finite type into a singleton. -/
def emptyToSingletonEmbedding : Fin 0 ↪ Fin 1 where
  toFun := fun i => Fin.elim0 i
  inj' := fun i => Fin.elim0 i

/-- Empty indexed family, used only to expose the range obstruction. -/
def emptyFamily : ConvexFamily (Fin 0) := fun i => Fin.elim0 i

/-- A singleton indexed family with prescribed body. -/
def singletonFamily (K : ConvexBody Space) : ConvexFamily (Fin 1) := fun _ => K

/-- The empty-to-singleton map is body-preserving vacuously. -/
def emptySingletonBodyEmbedding (K : ConvexBody Space) :
    BodyPreservingEmbedding emptyFamily (singletonFamily K) where
  index := emptyToSingletonEmbedding
  body_eq := fun i => Fin.elim0 i

/-- The body-preserving embedding does not exhaust its target. -/
theorem emptyToSingletonEmbedding_not_surjective :
    ¬ Function.Surjective emptyToSingletonEmbedding := by
  intro h
  obtain ⟨i, _hi⟩ := h (0 : Fin 1)
  exact Fin.elim0 i

/-- If the extra singleton body has positive volume, summed family volume is
strictly different.  Thus an endpoint embedding alone cannot transport the
family-volume denominator or a density lower bound. -/
theorem familyVolume_empty_ne_singleton
    (K : ConvexBody Space) (hK : volume (K : Set Space) ≠ 0) :
    familyVolume emptyFamily ≠ familyVolume (singletonFamily K) := by
  simpa [familyVolume, emptyFamily, singletonFamily] using hK.symm

#print axioms BodyPreservingEmbedding.familyUnion_subset
#print axioms BodyPreservingEmbedding.familyVolume_le
#print axioms BodyPreservingEmbedding.pushforwardShading
#print axioms BodyPreservingEmbedding.pushforwardShading_shadedUnion
#print axioms BodyPreservingEmbedding.pushforwardShading_shadingMass
#print axioms BodyPreservingEmbedding.iUnion_image_pushforwardShading
#print axioms BodyPreservingEmbedding.familyVolume_eq_of_surjective
#print axioms StickyScaleCover.parentAggregatedShading
#print axioms StickyScaleCover.parentAggregatedShading_shadedUnion
#print axioms StickyScaleCover.parentAggregatedShading_shadingMass_le
#print axioms StickyScaleCover.activeFineShading_shadingMass_le_nsmul_parent_of_fiberCard_le
#print axioms Identification.familyUnion_activeFine_subset_suppliedPrefix
#print axioms Identification.suppliedPrefixShading_shadedUnion
#print axioms Identification.suppliedPrefixShading_shadingMass_le
#print axioms Identification.twistedProjection_iUnion_suppliedPrefixShading
#print axioms familyVolume_empty_ne_singleton

end
end FamilyStickyHierarchyEndpointPrefixShadingTransportV1
