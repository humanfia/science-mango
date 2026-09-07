import Family8Grounding.Family8StickyScaleCoverFrostmanInheritanceV1
import FamilyStickyGrounding.FamilyStickyScaleChainCoherentIntervalProducerV1
import Mathlib.Tactic

/-!
# Frostman inheritance for a literal rerooted Sticky interval

The global cover at radius `rho` controls the original `delta`-tube fibre,
whereas the cover rerooted at `tau` has the chosen `tau`-tubes as its fine
family.  Coherence of the coarse carriers alone does not identify those two
partitions.  This file isolates the missing structural square and the exact
two-sided assigned-parent mass comparison, then applies the existing upward
Frostman inheritance theorem fibre by fibre.

No interval Frostman conclusion is stored in the input.  The only analytic
loss is the displayed ratio `upper * lower⁻¹`.
-/

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8NormalizedLongIntervalFrostmanInheritanceV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.HeavyParentSelection
open Submission.Kakeya.ConvexFactoring.JointTubeFactoring
open Submission.Kakeya.Uniformity
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyScaleChainCoherentIntervalProducerV1
open FamilyStickyScaleChainCoherentIntervalProducerV1.CoherentStickyMultiscaleCover

noncomputable section

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

variable {delta : NNReal} {iota : Type*}
  [Fintype iota] [DecidableEq iota]
  {fine : UniformTubeFamily delta iota}

/-! ## Active-finset versus literal subtype -/

/-- Restrict a convex family to the subtype attached to an active finset. -/
def activeSubtypeFamily {alpha : Type*} [Fintype alpha]
    (F : ConvexFamily alpha) (active : Finset alpha) :
    ConvexFamily {i // i ∈ active} :=
  fun i => F i.1

/-- The literal subtype contained mass is the active-finset contained mass. -/
theorem containedMass_activeSubtypeFamily
    {alpha : Type*} [Fintype alpha] [DecidableEq alpha]
    (F : ConvexFamily alpha) (active : Finset alpha)
    (K : ConvexBody Space) :
    containedMass (activeSubtypeFamily F active) K =
      containedMassOn F active K := by
  let e :
      {i // i ∈ containedIndices (activeSubtypeFamily F active) K} ≃
        {i // i ∈ active ∩ containedIndices F K} :=
    { toFun := fun i => ⟨i.1.1, Finset.mem_inter.mpr ⟨i.1.2, by
          exact (mem_containedIndices F K i.1.1).2
            ((mem_containedIndices (activeSubtypeFamily F active) K i.1).1 i.2)⟩⟩
      invFun := fun i =>
        let hi := Finset.mem_inter.mp i.2
        ⟨⟨i.1, hi.1⟩, by
          exact (mem_containedIndices (activeSubtypeFamily F active) K ⟨i.1, hi.1⟩).2
            ((mem_containedIndices F K i.1).1 hi.2)⟩
      left_inv := by intro i; apply Subtype.ext; apply Subtype.ext; rfl
      right_inv := by intro i; apply Subtype.ext; rfl }
  unfold containedMass containedMassOn
  calc
    (∑ i ∈ containedIndices (activeSubtypeFamily F active) K,
        volume (activeSubtypeFamily F active i : Set Space)) =
        ∑ i : {i // i ∈ containedIndices (activeSubtypeFamily F active) K},
          volume (activeSubtypeFamily F active i.1 : Set Space) := by
      exact Finset.sum_subtype _ (fun _i => Iff.rfl) _
    _ = ∑ i : {i // i ∈ active ∩ containedIndices F K},
          volume (F i.1 : Set Space) := by
      exact Fintype.sum_equiv e _ _ (fun i => rfl)
    _ = ∑ i ∈ active ∩ containedIndices F K,
          volume (F i : Set Space) := by
      simpa only using
        (Finset.sum_subtype (M := ENNReal)
          (active ∩ containedIndices F K) (fun _i => Iff.rfl)
          (fun i => volume (F i : Set Space))).symm

  all_goals
    apply Finset.sum_congr
    · ext i
      simp only [Finset.mem_inter]
    · intro i hi
      rfl
/-- Cross-multiplied Frostman control is unchanged by replacing an active
finset with its literal subtype. -/
theorem isFrostmanOn_iff_isFrostmanIn_activeSubtypeFamily
    {alpha : Type*} [Fintype alpha] [DecidableEq alpha]
    {C : ENNReal} (F : ConvexFamily alpha) (active : Finset alpha)
    (K : ConvexBody Space) :
    IsFrostmanOn C F active K ↔
      IsFrostmanIn C (activeSubtypeFamily F active) K := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · intro i
      exact h.1 i.1 i.2
    · intro K' hK'
      simpa only [containedMass_activeSubtypeFamily] using h.2 K' hK'
  · intro h
    refine ⟨?_, ?_⟩
    · intro i hi
      exact h.1 ⟨i, hi⟩
    · intro K' hK'
      simpa only [containedMass_activeSubtypeFamily] using h.2 K' hK'

/-! ## The minimal same-object inheritance data -/

/-- The structural and two-sided mass data needed to reroot at one fixed
`tau`.

`parent_compatible` is the missing commuting square between the original
fine-index parents and the cross-scale parent map.  The other two fields say
that the original `delta`-tube mass assigned to every active `tau` parent is
between common multiples `lower` and `upper` of that parent's actual volume.
These are parent-mass comparisons, not a stored Frostman conclusion. -/
structure IntervalParentMassComparison
    (C : CoherentStickyMultiscaleCover fine)
    (tau : NNReal) (hdeltaTau : delta ≤ tau) (hTauOne : tau ≤ 1)
    (lower upper : ENNReal) : Prop where
  parent_compatible : ∀ (rho : NNReal) (hTauRho : tau ≤ rho)
      (hRhoOne : rho ≤ 1) (i : iota),
    i ∈ (C.base.cover tau hdeltaTau hTauOne).activeFine →
      (C.base.cover rho (hdeltaTau.trans hTauRho) hRhoOne).parent i =
        C.parent tau rho hdeltaTau hTauRho hRhoOne
          ((C.base.cover tau hdeltaTau hTauOne).parent i)
  lower_parent_mass : ∀ q,
    q ∈ (C.base.cover tau hdeltaTau hTauOne).activeCoarse →
      lower * volume
          ((C.base.cover tau hdeltaTau hTauOne).coarse.tubes q).carrier ≤
        familyVolume
          ((C.base.cover tau hdeltaTau hTauOne).fiberFamily q)
  upper_parent_mass : ∀ q,
    q ∈ (C.base.cover tau hdeltaTau hTauOne).activeCoarse →
      familyVolume
          ((C.base.cover tau hdeltaTau hTauOne).fiberFamily q) ≤
        upper * volume
          ((C.base.cover tau hdeltaTau hTauOne).coarse.tubes q).carrier

namespace IntervalParentMassComparison

variable {C : CoherentStickyMultiscaleCover fine}
  {tau : NNReal} {hdeltaTau : delta ≤ tau} {hTauOne : tau ≤ 1}
  {lower upper : ENNReal}

/-- Restrict the actual `delta -> tau` factorization to the `tau` parents
lying over one fixed `rho` parent. -/
def intervalFiberFactorization
    (_H : IntervalParentMassComparison C tau hdeltaTau hTauOne lower upper)
    (rho : NNReal) (hTauRho : tau ≤ rho) (hRhoOne : rho ≤ 1)
    (k : Fin
      (C.intervalScaleCover tau rho hdeltaTau hTauRho hRhoOne).coarseCard) :
    ConvexFactorization fine.bodyFamily
      (C.base.cover tau hdeltaTau hTauOne).coarse.bodyFamily where
  index := selectedIndexFactorization
    (C.base.cover tau hdeltaTau hTauOne).activeFine
    (C.base.cover tau hdeltaTau hTauOne).parent
    ((C.intervalScaleCover tau rho hdeltaTau hTauRho hRhoOne).fiber k)
  contained := by
    intro i hi
    have hiTau : i ∈ (C.base.cover tau hdeltaTau hTauOne).activeFine :=
      (Finset.mem_filter.mp hi).1
    exact (C.base.cover tau hdeltaTau hTauOne).carrier_subset i hiTau

/-- Parent compatibility identifies the selected fine indices of the local
factorization with the literal original `delta`-fibre over `k`. -/
theorem intervalFiberFactorization_fine_eq_baseFiber
    (H : IntervalParentMassComparison C tau hdeltaTau hTauOne lower upper)
    (rho : NNReal) (hTauRho : tau ≤ rho) (hRhoOne : rho ≤ 1)
    (k : Fin
      (C.intervalScaleCover tau rho hdeltaTau hTauRho hRhoOne).coarseCard) :
    (H.intervalFiberFactorization rho hTauRho hRhoOne k).index.fine =
      (C.base.cover rho (hdeltaTau.trans hTauRho) hRhoOne).fiber k := by
  classical
  let T := C.base.cover tau hdeltaTau hTauOne
  let R := C.base.cover rho (hdeltaTau.trans hTauRho) hRhoOne
  let I := C.intervalScaleCover tau rho hdeltaTau hTauRho hRhoOne
  ext i
  change i ∈ selectedFineIndices T.activeFine T.parent (I.fiber k) ↔
    i ∈ R.fiber k
  unfold selectedFineIndices StickyScaleCover.fiber
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hiTau, hparentFiber⟩
    have hiRho : i ∈ R.activeFine := by
      rw [R.activeFine_eq_refined, ← T.activeFine_eq_refined]
      exact hiTau
    have hparentFiber' := hparentFiber
    refine ⟨hiRho, ?_⟩
    rw [← hparentFiber'.2]
    exact H.parent_compatible rho hTauRho hRhoOne i hiTau
  · rintro ⟨hiRho, hparentRho⟩
    have hiTau : i ∈ T.activeFine := by
      rw [T.activeFine_eq_refined, ← R.activeFine_eq_refined]
      exact hiRho
    refine ⟨hiTau, ⟨T.parent_mem i hiTau, ?_⟩⟩
    rw [← hparentRho]
    exact (H.parent_compatible rho hTauRho hRhoOne i hiTau).symm

/-- Selection does not change the assigned mass over a retained `tau`
parent. -/
theorem intervalFiberFactorization_fiberBodyMass_eq
    (H : IntervalParentMassComparison C tau hdeltaTau hTauOne lower upper)
    (rho : NNReal) (hTauRho : tau ≤ rho) (hRhoOne : rho ≤ 1)
    (k : Fin
      (C.intervalScaleCover tau rho hdeltaTau hTauRho hRhoOne).coarseCard)
    (q : Fin (C.base.cover tau hdeltaTau hTauOne).coarseCard)
    (hq : q ∈
      (C.intervalScaleCover tau rho hdeltaTau hTauRho hRhoOne).fiber k) :
    fiberBodyMass (H.intervalFiberFactorization rho hTauRho hRhoOne k) q =
      familyVolume
        ((C.base.cover tau hdeltaTau hTauOne).fiberFamily q) := by
  classical
  let T := C.base.cover tau hdeltaTau hTauOne
  unfold fiberBodyMass
  change (∑ i ∈
      (selectedIndexFactorization T.activeFine T.parent
        ((C.intervalScaleCover tau rho hdeltaTau hTauRho hRhoOne).fiber k)).fiber q,
      volume (fine.bodyFamily i : Set Space)) = _
  rw [selected_fiber_eq_raw_fiber T.activeFine T.parent _ hq]
  change (∑ i ∈ T.fiber q,
      volume (fine.bodyFamily i : Set Space)) = _
  change (∑ i ∈ T.fiber q,
      volume (fine.bodyFamily i : Set Space)) =
    ∑ i : {i // i ∈ T.fiber q},
      volume (fine.bodyFamily i.1 : Set Space)
  exact Finset.sum_subtype (M := ENNReal)
    (T.fiber q) (fun _i => Iff.rfl) _

end IntervalParentMassComparison

/-! ## Fibrewise and all-scale inheritance -/

/-- Base Frostman control at `rho`, the commuting parent square, and the
two-sided assigned-parent mass comparison produce Frostman control for the
literal interval cover at the same `rho`. -/
theorem intervalScaleCover_isFrostmanAtScale
    (C : CoherentStickyMultiscaleCover fine)
    (tau rho : NNReal) (hdeltaTau : delta ≤ tau)
    (hTauOne : tau ≤ 1) (hTauRho : tau ≤ rho) (hRhoOne : rho ≤ 1)
    {baseError lower upper : ENNReal}
    (hlower0 : lower ≠ 0) (hlowerTop : lower ≠ ∞)
    (H : IntervalParentMassComparison C tau hdeltaTau hTauOne lower upper)
    (hbase : StickyScaleCover.IsFrostmanAtScale
      (C.base.cover rho (hdeltaTau.trans hTauRho) hRhoOne) baseError) :
    StickyScaleCover.IsFrostmanAtScale
      (C.intervalScaleCover tau rho hdeltaTau hTauRho hRhoOne)
      (baseError * upper * lower⁻¹) := by
  intro k hk K hK
  let T := C.base.cover tau hdeltaTau hTauOne
  let R := C.base.cover rho (hdeltaTau.trans hTauRho) hRhoOne
  let I := C.intervalScaleCover tau rho hdeltaTau hTauRho hRhoOne
  let P := H.intervalFiberFactorization rho hTauRho hRhoOne k
  have hfineSubtype :
      IsFrostmanIn baseError (R.fiberFamily k) (R.coarse.tubes k).body := by
    apply (isFrostmanIn_iff_concentration_le).2
    refine ⟨R.fiber_carrier_subset_parent k, ?_⟩
    exact hbase k hk
  have hfineActive :
      IsFrostmanOn baseError fine.bodyFamily P.index.fine
        (R.coarse.tubes k).body := by
    rw [IntervalParentMassComparison.intervalFiberFactorization_fine_eq_baseFiber]
    exact (isFrostmanOn_iff_isFrostmanIn_activeSubtypeFamily
      fine.bodyFamily (R.fiber k) (R.coarse.tubes k).body).2 hfineSubtype
  have hcoarseContained : ∀ q ∈ P.index.coarse,
      (T.coarse.bodyFamily q : Set Space) ⊆
        ((R.coarse.tubes k).body : Set Space) := by
    intro q hq
    have hqFiber : q ∈ I.fiber k := hq
    have hqData := (I.mem_fiber q k).1 hqFiber
    have hcarrier := I.carrier_subset q hqData.1
    rw [hqData.2] at hcarrier
    simpa only [UniformTubeFamily.bodyFamily, Tube.coe_body, I, R, T,
      CoherentStickyMultiscaleCover.intervalScaleCover] using hcarrier
  have hlocal :
      IsFrostmanOn (baseError * upper * lower⁻¹)
        T.coarse.bodyFamily P.index.coarse (R.coarse.tubes k).body := by
    apply
      Family8FrostmanInheritanceToActiveCoarseV3.activeCoarse_isFrostmanOn_of_comparable_fiberDensity
        P (R.coarse.tubes k).body hlower0 hlowerTop hfineActive
        hcoarseContained
    · intro q hq
      have hqFiber : q ∈ I.fiber k := hq
      have hqActive := (I.mem_fiber q k).1 hqFiber |>.1
      rw [H.intervalFiberFactorization_fiberBodyMass_eq
        rho hTauRho hRhoOne k q hqFiber]
      exact H.lower_parent_mass q hqActive
    · intro q hq
      have hqFiber : q ∈ I.fiber k := hq
      have hqActive := (I.mem_fiber q k).1 hqFiber |>.1
      rw [H.intervalFiberFactorization_fiberBodyMass_eq
        rho hTauRho hRhoOne k q hqFiber]
      exact H.upper_parent_mass q hqActive
  have hlocalSubtype :
      IsFrostmanIn (baseError * upper * lower⁻¹)
        (I.fiberFamily k) (R.coarse.tubes k).body := by
    exact (isFrostmanOn_iff_isFrostmanIn_activeSubtypeFamily
      T.coarse.bodyFamily (I.fiber k) (R.coarse.tubes k).body).1 hlocal
  exact (isFrostmanIn_iff_concentration_le).1 hlocalSubtype |>.2 K hK

/-- The fixed-`tau` mass comparison produces a genuine all-scale Frostman
certificate on the literal multiscale cover rerooted at `tau`. -/
theorem intervalMultiscaleCover_isFrostmanAtEveryScale
    (C : CoherentStickyMultiscaleCover fine)
    (tau : NNReal) (hdeltaTau : delta ≤ tau) (hTauOne : tau ≤ 1)
    {baseError lower upper : ENNReal}
    (hlower0 : lower ≠ 0) (hlowerTop : lower ≠ ∞)
    (H : IntervalParentMassComparison C tau hdeltaTau hTauOne lower upper)
    (hbase : C.base.IsFrostmanAtEveryScale baseError) :
    StickyMultiscaleCover.IsFrostmanAtEveryScale
      (C.intervalMultiscaleCover tau hdeltaTau hTauOne)
      (baseError * upper * lower⁻¹) := by
  intro rho hTauRho hRhoOne
  simpa only [intervalMultiscaleCover_cover] using
    intervalScaleCover_isFrostmanAtScale C tau rho hdeltaTau hTauOne
      hTauRho hRhoOne hlower0 hlowerTop H
      (hbase rho (hdeltaTau.trans hTauRho) hRhoOne)

#print axioms containedMass_activeSubtypeFamily
#print axioms isFrostmanOn_iff_isFrostmanIn_activeSubtypeFamily
#print axioms IntervalParentMassComparison.intervalFiberFactorization_fine_eq_baseFiber
#print axioms IntervalParentMassComparison.intervalFiberFactorization_fiberBodyMass_eq
#print axioms intervalScaleCover_isFrostmanAtScale
#print axioms intervalMultiscaleCover_isFrostmanAtEveryScale

end

end Family8NormalizedLongIntervalFrostmanInheritanceV1
