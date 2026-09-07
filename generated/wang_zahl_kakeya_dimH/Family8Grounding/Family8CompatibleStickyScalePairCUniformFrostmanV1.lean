import Family8Grounding.Family8NormalizedLongIntervalCUniformEndpointV1

/-!
# Frostman inheritance for one compatible pair of Sticky covers

The long-interval argument does not intrinsically need an all-radius
coherent cover.  At one selected interval it needs two endpoint covers, one
cross-parent map, literal carrier containment, and the fine-parent commuting
square.  This file isolates that finite object and proves the same
C-uniform Frostman inheritance used by the global coherent-cover theorem.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8CompatibleStickyScalePairCUniformFrostmanV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.HeavyParentSelection
open Submission.Kakeya.ConvexFactoring.JointTubeFactoring
open Submission.Kakeya.Uniformity
open Family8CUniformPairwiseFiberDensityV1
open Family8Def212ConvexWolffAtEveryScaleV2
open Family8Def212ConvexWolffAtEveryScaleV2.ScaleCover
open Family8KatzTaoFrostmanPropertiesV1
open Family8NormalizedCFDividingWitnessBridgeV2.StickyScaleCover
open Family8NormalizedLongIntervalFrostmanInheritanceV1
open Family8PairwiseFiberDensityFrostmanInheritanceV1
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyScaleChainHierarchySiblingRigidityV1

noncomputable section

variable {delta r R : NNReal} {iota : Type}
  [Fintype iota] [DecidableEq iota]
  {fine : UniformTubeFamily delta iota}

/-- Exact finite coherence data between two endpoint covers of one common
fine family.  The cross cover is constructed below, rather than stored as a
second independent object. -/
structure CompatibleStickyScalePair
    (lower : StickyScaleCover fine r)
    (upper : StickyScaleCover fine R) where
  crossParent : Fin lower.coarseCard -> Fin upper.coarseCard
  crossParent_mem : forall q,
    q ∈ lower.activeCoarse ->
      crossParent q ∈ upper.activeCoarse
  crossParent_surjective : forall k,
    k ∈ upper.activeCoarse ->
      exists q, q ∈ lower.activeCoarse ∧ crossParent q = k
  carrier_subset : forall q,
    q ∈ lower.activeCoarse ->
      (lower.coarse.tubes q).carrier ⊆
        (upper.coarse.tubes (crossParent q)).carrier
  fine_parent_commutes : forall i,
    i ∈ lower.activeFine ->
      upper.parent i = crossParent (lower.parent i)

namespace CompatibleStickyScalePair

variable {lower : StickyScaleCover fine r}
  {upper : StickyScaleCover fine R}

/-- The literal cross cover supplied by a compatible endpoint pair. -/
def intervalCover
    (X : CompatibleStickyScalePair lower upper) :
    StickyScaleCover lower.coarse R where
  coarseCard := upper.coarseCard
  coarse := upper.coarse
  activeFine := lower.activeCoarse
  activeCoarse := upper.activeCoarse
  parent := X.crossParent
  activeFine_eq_refined := lower.activeCoarse_eq_refined
  activeCoarse_eq_refined := upper.activeCoarse_eq_refined
  parent_mem := X.crossParent_mem
  parent_surjective := X.crossParent_surjective
  carrier_subset := X.carrier_subset

@[simp] theorem intervalCover_parent
    (X : CompatibleStickyScalePair lower upper)
    (q : Fin lower.coarseCard) :
    X.intervalCover.parent q = X.crossParent q :=
  rfl

@[simp] theorem intervalCover_coarse
    (X : CompatibleStickyScalePair lower upper) :
    X.intervalCover.coarse = upper.coarse :=
  rfl

/-- The local factorization over one upper parent uses the actual lower
parent fibres. -/
def endpointFiberFactorization
    (X : CompatibleStickyScalePair lower upper)
    (k : Fin upper.coarseCard) :
    ConvexFactorization fine.bodyFamily lower.coarse.bodyFamily where
  index := selectedIndexFactorization lower.activeFine lower.parent
    (X.intervalCover.fiber k)
  contained := by
    intro i hi
    have hiLower : i ∈ lower.activeFine := (Finset.mem_filter.mp hi).1
    exact lower.carrier_subset i hiLower

/-- Fine-parent commutation identifies the selected original fine indices
with the literal upper fibre. -/
theorem endpointFiberFactorization_fine_eq_upperFiber
    (X : CompatibleStickyScalePair lower upper)
    (k : Fin upper.coarseCard) :
    (X.endpointFiberFactorization k).index.fine = upper.fiber k := by
  classical
  ext i
  change i ∈ selectedFineIndices lower.activeFine lower.parent
      (X.intervalCover.fiber k) ↔ i ∈ upper.fiber k
  unfold selectedFineIndices StickyScaleCover.fiber
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hiLower, hparentFiber⟩
    have hiUpper : i ∈ upper.activeFine := by
      rw [upper.activeFine_eq_refined, ← lower.activeFine_eq_refined]
      exact hiLower
    refine ⟨hiUpper, ?_⟩
    rw [← hparentFiber.2]
    exact X.fine_parent_commutes i hiLower
  · rintro ⟨hiUpper, hparentUpper⟩
    have hiLower : i ∈ lower.activeFine := by
      rw [lower.activeFine_eq_refined, ← upper.activeFine_eq_refined]
      exact hiUpper
    refine ⟨hiLower, ⟨lower.parent_mem i hiLower, ?_⟩⟩
    rw [← hparentUpper]
    exact (X.fine_parent_commutes i hiLower).symm

/-- Restricting to one upper fibre does not change the original mass
assigned to a retained lower parent. -/
theorem endpointFiberFactorization_fiberBodyMass_eq
    (X : CompatibleStickyScalePair lower upper)
    (k : Fin upper.coarseCard)
    (q : Fin lower.coarseCard)
    (hq : q ∈ X.intervalCover.fiber k) :
    fiberBodyMass (X.endpointFiberFactorization k) q =
      familyVolume (lower.fiberFamily q) := by
  classical
  unfold fiberBodyMass
  change (∑ i ∈
      (selectedIndexFactorization lower.activeFine lower.parent
        (X.intervalCover.fiber k)).fiber q,
      volume (fine.bodyFamily i : Set Space)) = _
  rw [selected_fiber_eq_raw_fiber lower.activeFine lower.parent _ hq]
  change (∑ i ∈ lower.fiber q,
      volume (fine.bodyFamily i : Set Space)) =
    ∑ i : {i // i ∈ lower.fiber q},
      volume (fine.bodyFamily i.1 : Set Space)
  exact Finset.sum_subtype (M := ENNReal)
    (lower.fiber q) (fun _i => Iff.rfl) _

/-- C-uniformity at the lower endpoint and Frostman control at the upper
endpoint imply the normalized Frostman bound for the literal cross cover. -/
theorem intervalCover_isFrostmanAtScale_of_upperFrostman_cUniform
    (X : CompatibleStickyScalePair lower upper)
    (hdeltaPos : 0 < delta)
    (hdeltaHalf : delta <= (2 : NNReal)⁻¹)
    (hrHalf : r <= (2 : NNReal)⁻¹)
    {baseError uniformity : ENNReal}
    (huniform : IsCUniform lower uniformity)
    (hupper : StickyScaleCover.IsFrostmanAtScale upper baseError) :
    StickyScaleCover.IsFrostmanAtScale X.intervalCover
      (baseError * ((16 * uniformity) * 16)) := by
  change forall k : Fin upper.coarseCard, k ∈ upper.activeCoarse ->
    forall K : ConvexBody Space,
      (K : Set Space) ⊆ (upper.coarse.tubes k).carrier ->
        concentration (X.intervalCover.fiberFamily k) K <=
          (baseError * ((16 * uniformity) * 16)) *
            concentration (X.intervalCover.fiberFamily k)
              (upper.coarse.tubes k).body
  intro k hk K hK
  let P := X.endpointFiberFactorization k
  have hfineSubtype :
      IsFrostmanIn baseError (upper.fiberFamily k)
        (upper.coarse.tubes k).body := by
    apply (isFrostmanIn_iff_concentration_le).2
    refine ⟨upper.fiber_carrier_subset_parent k, ?_⟩
    exact hupper k hk
  have hfineActive :
      IsFrostmanOn baseError fine.bodyFamily P.index.fine
        (upper.coarse.tubes k).body := by
    change IsFrostmanOn baseError fine.bodyFamily
      (X.endpointFiberFactorization k).index.fine
        (upper.coarse.tubes k).body
    rw [X.endpointFiberFactorization_fine_eq_upperFiber]
    exact (isFrostmanOn_iff_isFrostmanIn_activeSubtypeFamily
      fine.bodyFamily (upper.fiber k) (upper.coarse.tubes k).body).2
        hfineSubtype
  have hcoarseContained : ∀ q ∈ P.index.coarse,
      (lower.coarse.bodyFamily q : Set Space) ⊆
        ((upper.coarse.tubes k).body : Set Space) := by
    intro q hq
    have hqFiber : q ∈ X.intervalCover.fiber k := hq
    have hqData := (X.intervalCover.mem_fiber q k).1 hqFiber
    have hcarrier := X.intervalCover.carrier_subset q hqData.1
    rw [hqData.2] at hcarrier
    simpa only [UniformTubeFamily.bodyFamily, Tube.coe_body,
      CompatibleStickyScalePair.intervalCover] using hcarrier
  have hfineMassEq :
      bodyMassOn fine.bodyFamily P.index.fine =
        familyVolume (upper.fiberFamily k) := by
    rw [X.endpointFiberFactorization_fine_eq_upperFiber]
    unfold bodyMassOn
    rw [familyVolume_fiberFamily_eq_sum upper k]
  have hfineMass0 : bodyMassOn fine.bodyFamily P.index.fine ≠ 0 := by
    rw [hfineMassEq]
    exact (fiberFamilyVolume_pos upper hdeltaPos ⟨k, hk⟩).ne'
  have hfineMassTop : bodyMassOn fine.bodyFamily P.index.fine ≠ ∞ := by
    rw [hfineMassEq]
    exact familyVolume_ne_top (upper.fiberFamily k)
  have hlocal :
      IsFrostmanOn (baseError * ((16 * uniformity) * 16))
        lower.coarse.bodyFamily P.index.coarse
          (upper.coarse.tubes k).body := by
    apply
      activeCoarse_isFrostmanOn_of_pairwise_fiberDensity
        P (upper.coarse.tubes k).body hfineActive hcoarseContained
        hfineMass0 hfineMassTop
    intro q hq l hl
    have hqFiber : q ∈ X.intervalCover.fiber k := hq
    have hlFiber : l ∈ X.intervalCover.fiber k := hl
    have hqActive : q ∈ lower.activeCoarse :=
      ((X.intervalCover.mem_fiber q k).1 hqFiber).1
    have hlActive : l ∈ lower.activeCoarse :=
      ((X.intervalCover.mem_fiber l k).1 hlFiber).1
    rw [X.endpointFiberFactorization_fiberBodyMass_eq k l hlFiber,
      X.endpointFiberFactorization_fiberBodyMass_eq k q hqFiber]
    simpa only [UniformTubeFamily.bodyFamily, Tube.coe_body] using
      (pairwiseFiberDensity_of_isCUniform
        lower hdeltaHalf hrHalf huniform q hqActive l hlActive)
  have hlocalSubtype :
      IsFrostmanIn (baseError * ((16 * uniformity) * 16))
        (X.intervalCover.fiberFamily k)
          (upper.coarse.tubes k).body := by
    exact (isFrostmanOn_iff_isFrostmanIn_activeSubtypeFamily
      lower.coarse.bodyFamily (X.intervalCover.fiber k)
        (upper.coarse.tubes k).body).1 hlocal
  exact (isFrostmanIn_iff_concentration_le).1 hlocalSubtype |>.2 K hK

#print axioms CompatibleStickyScalePair.intervalCover
#print axioms CompatibleStickyScalePair.endpointFiberFactorization_fine_eq_upperFiber
#print axioms CompatibleStickyScalePair.endpointFiberFactorization_fiberBodyMass_eq
#print axioms
  CompatibleStickyScalePair.intervalCover_isFrostmanAtScale_of_upperFrostman_cUniform

end CompatibleStickyScalePair
end
end Family8CompatibleStickyScalePairCUniformFrostmanV1
