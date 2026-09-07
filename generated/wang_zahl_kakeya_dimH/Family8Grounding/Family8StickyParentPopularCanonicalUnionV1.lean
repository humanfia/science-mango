import Family8Grounding.Family8AllFrostmanStickyUnionProducerV1
import FamilyStickyGrounding.FamilyStickyHierarchyWZ2TranslatedCollisionCellPopularFloorUnionV1

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8StickyParentPopularCanonicalUnionV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyHierarchyEndpointPrefixShadingTransportV1.StickyScaleCover
open FamilyStickyKatzTaoAtEveryScaleOverlapMultiplicityConsumerV1
open FamilyStickyHierarchyWZ2TranslatedCollisionCellCanonicalRowGeometryV1
open FamilyStickyHierarchyWZ2TranslatedCollisionCellCanonicalRowScaleFloorV1
open FamilyStickyHierarchyWZ2TranslatedCollisionCellPopularFloorUnionV1
open FamilyStickyWZ2ShadingPopularityV2
open Family8AllFrostmanStickyUnionProducerV1
open Family8KatzTaoFrostmanPropertiesV1

noncomputable section

/-!
# Popular parent rows close the canonical Sticky scale without a callback

The canonical scale of the unmodified parent shading cannot be controlled
from total mass: a single arbitrarily small nonzero carrier forces a
pointwise full-body/carrier ratio.  This module performs the paper-faithful
repair.  It retains the parent rows selected by a positive mass threshold,
uses their automatic carrier floor, applies Katz--Tao to that literal
subshading, and enlarges its union back to the original source union.
-/

/-- A positive popular-row threshold gives a callback-free canonical
Katz--Tao union estimate on an actual one-scale Sticky parent shading. -/
theorem parentAggregatedPopular_halfMass_le_activeFineUnion
    {delta rho : NNReal} {iota : Type*}
    [Fintype iota] [DecidableEq iota]
    {fine : UniformTubeFamily delta iota}
    (S : StickyScaleCover fine rho)
    (Y : Shading fine.bodyFamily)
    (active : Finset {k // k ∈ S.activeCoarse}) (X : Set Space)
    (alpha cap : Real) (halphaPos : 0 < alpha) (hcapPos : 0 < cap)
    (hmass :
      alpha * active.card * cap ≤
        ∑ k ∈ active,
          restrictedMassReal (parentAggregatedShading S Y) X k)
    {C : ENNReal} (hKT : S.IsKatzTaoAtScale C) :
    ENNReal.ofReal (alpha / 2 * active.card * cap) ≤
      (C *
        (volume
            (fullFamilyHullContainer S.activeCoarseFamily : Set Space) /
          popularCarrierFloor alpha cap)) *
        volume (activeFineShading S Y).shadedUnion := by
  let P := parentAggregatedShading S Y
  let lower := popularCarrierFloor alpha cap
  let P' := retainCarrierFloor P lower
  have hlowerPos : 0 < lower := by
    dsimp only [lower]
    rw [popularCarrierFloor, ENNReal.ofReal_pos]
    exact mul_pos (div_pos halphaPos (by norm_num)) hcapPos
  have hretained :
      ENNReal.ofReal (alpha / 2 * active.card * cap) ≤
        P'.shadingMass := by
    exact popularRestricted_halfMass_le_retainCarrierFloor_shadingMass
      P active X alpha cap halphaPos.le hcapPos.le hmass
  let R := canonicalKatzTaoOverlapRowGeometry P'
  have hWZ :
      P'.shadingMass ≤
        (C * canonicalOverlapScaleFactor P') *
          volume P'.shadedUnion := by
    simpa only [R, canonicalKatzTaoOverlapRowGeometry] using
      (FamilyStickyKatzTaoAtEveryScaleOverlapMultiplicityConsumerV1.StickyScaleCover.shadingMass_le_of_isKatzTaoAtScale
        S hKT P' R)
  have hscale :
      canonicalOverlapScaleFactor P' ≤
        volume (fullFamilyHullContainer S.activeCoarseFamily : Set Space) /
          lower := by
    exact canonicalOverlapScaleFactor_retainCarrierFloor_le
      P lower (ne_of_gt hlowerPos) ENNReal.ofReal_ne_top
  have hunion :
      volume P'.shadedUnion ≤
        volume (activeFineShading S Y).shadedUnion := by
    apply measure_mono
    intro x hx
    obtain ⟨k, hxk⟩ := Set.mem_iUnion.mp hx
    rw [← parentAggregatedShading_shadedUnion S Y]
    exact Set.mem_iUnion.mpr
      ⟨k, retainCarrierFloor_carrier_subset P lower k hxk⟩
  calc
    ENNReal.ofReal (alpha / 2 * active.card * cap) ≤
        P'.shadingMass := hretained
    _ ≤ (C * canonicalOverlapScaleFactor P') *
        volume P'.shadedUnion := hWZ
    _ ≤ (C *
          (volume
              (fullFamilyHullContainer S.activeCoarseFamily : Set Space) /
            lower)) *
        volume (activeFineShading S Y).shadedUnion := by
      exact mul_le_mul' (mul_le_mul' le_rfl hscale) hunion

/-- If the selected Sticky cover uses every source index, the same automatic
popular-row estimate lands on the literal original shaded union. -/
theorem parentAggregatedPopular_halfMass_le_originalUnion
    {delta rho : NNReal} {iota : Type*}
    [Fintype iota] [DecidableEq iota]
    {fine : UniformTubeFamily delta iota}
    (S : StickyScaleCover fine rho)
    (Y : Shading fine.bodyFamily)
    (hactive : S.activeFine = Finset.univ)
    (active : Finset {k // k ∈ S.activeCoarse}) (X : Set Space)
    (alpha cap : Real) (halphaPos : 0 < alpha) (hcapPos : 0 < cap)
    (hmass :
      alpha * active.card * cap ≤
        ∑ k ∈ active,
          restrictedMassReal (parentAggregatedShading S Y) X k)
    {C : ENNReal} (hKT : S.IsKatzTaoAtScale C) :
    ENNReal.ofReal (alpha / 2 * active.card * cap) ≤
      (C *
        (volume
            (fullFamilyHullContainer S.activeCoarseFamily : Set Space) /
          popularCarrierFloor alpha cap)) *
        volume Y.shadedUnion := by
  have h := parentAggregatedPopular_halfMass_le_activeFineUnion
    S Y active X alpha cap halphaPos hcapPos hmass hKT
  have heq :
      (activeFineShading S Y).shadedUnion = Y.shadedUnion := by
    ext x
    simp [Shading.shadedUnion, activeFineShading, hactive]
  simpa only [heq] using h


/-! ## Automatic full-index popularity -/

/-- Restricting every shading piece to the whole ambient space loses no
mass.  This is the exact finite identity used to discharge the popularity
mass premise below. -/
theorem sum_restrictedMassReal_univ_eq_shadingMass_toReal
    {kappa : Type*} [Fintype kappa]
    {F : ConvexFamily kappa} (Z : Shading F) :
    (∑ k ∈ (Finset.univ : Finset kappa),
        restrictedMassReal Z Set.univ k) = Z.shadingMass.toReal := by
  classical
  unfold restrictedMassReal restrictedMass Shading.shadingMass
  simp only [Set.inter_univ]
  exact (ENNReal.toReal_sum fun k _hk =>
    ((measure_mono (Z.carrier_subset k)).trans_lt
      (F k).isCompact.measure_lt_top).ne).symm

/-- The average real mass of an actual parent row.  It is defined without a
nonemptiness assumption; the automatic theorem below supplies nonemptiness,
so its denominator is positive there. -/
noncomputable def parentAverageCarrierMassReal
    {delta rho : NNReal} {iota : Type*}
    [Fintype iota] [DecidableEq iota]
    {fine : UniformTubeFamily delta iota}
    (S : StickyScaleCover fine rho) (Y : Shading fine.bodyFamily) : Real :=
  (parentAggregatedShading S Y).shadingMass.toReal /
    Fintype.card {k // k ∈ S.activeCoarse}

/-- On all parent rows and the full ambient set, the popularity mass premise
is automatic: choose the threshold to be the exact average parent mass and
the cap to be one.  Thus only positivity/nonemptiness and the genuine
Katz--Tao input remain. -/
theorem parentAggregatedAveragePopular_halfMass_le_originalUnion
    {delta rho : NNReal} {iota : Type*}
    [Fintype iota] [DecidableEq iota]
    {fine : UniformTubeFamily delta iota}
    (S : StickyScaleCover fine rho)
    (Y : Shading fine.bodyFamily)
    (hactive : S.activeFine = Finset.univ)
    (hcoarse : S.activeCoarse.Nonempty)
    (hparentPos : 0 < (parentAggregatedShading S Y).shadingMass)
    {C : ENNReal} (hKT : S.IsKatzTaoAtScale C) :
    ENNReal.ofReal
        (parentAverageCarrierMassReal S Y / 2 *
          Fintype.card {k // k ∈ S.activeCoarse}) ≤
      (C *
        (volume
            (fullFamilyHullContainer S.activeCoarseFamily : Set Space) /
          popularCarrierFloor (parentAverageCarrierMassReal S Y) 1)) *
        volume Y.shadedUnion := by
  have hindexNonempty : Nonempty {k // k ∈ S.activeCoarse} :=
    ⟨⟨hcoarse.choose, hcoarse.choose_spec⟩⟩
  have hcardPos :
      (0 : Real) < Fintype.card {k // k ∈ S.activeCoarse} := by
    exact_mod_cast (Fintype.card_pos_iff.mpr hindexNonempty)
  have haveragePos : 0 < parentAverageCarrierMassReal S Y := by
    unfold parentAverageCarrierMassReal
    exact div_pos
      (ENNReal.toReal_pos (ne_of_gt hparentPos)
        (parentAggregatedShading S Y).shadingMass_lt_top.ne)
      hcardPos
  have hmass :
      parentAverageCarrierMassReal S Y *
          (Finset.univ : Finset {k // k ∈ S.activeCoarse}).card * 1 ≤
        ∑ k ∈ (Finset.univ : Finset {k // k ∈ S.activeCoarse}),
          restrictedMassReal (parentAggregatedShading S Y) Set.univ k := by
    rw [sum_restrictedMassReal_univ_eq_shadingMass_toReal]
    simp only [Finset.card_univ, mul_one]
    unfold parentAverageCarrierMassReal
    exact le_of_eq (div_mul_cancel₀ _ (ne_of_gt hcardPos))
  simpa only [Finset.card_univ, mul_one] using
    (parentAggregatedPopular_halfMass_le_originalUnion
      S Y hactive
      (Finset.univ : Finset {k // k ∈ S.activeCoarse}) Set.univ
      (parentAverageCarrierMassReal S Y) 1 haveragePos (by norm_num)
      hmass hKT)


/-- Positive source shading mass forces the finite source index type to be
nonempty; an empty index type has a literally empty shading-mass sum. -/
theorem nonempty_of_shadingMass_pos
    {kappa : Type*} [Fintype kappa]
    {F : ConvexFamily kappa} (Z : Shading F)
    (hmassPos : 0 < Z.shadingMass) : Nonempty kappa := by
  by_contra hnot
  let _ : IsEmpty kappa := not_nonempty_iff.mp hnot
  have hzero : Z.shadingMass = 0 := by
    simp [Shading.shadingMass]
  exact (ne_of_gt hmassPos) hzero

/-- If every source occurrence is active, positive source mass survives
literal parent aggregation.  The proof uses the exact finite fibre-card loss;
there is no geometric or scalar callback. -/
theorem parentAggregatedShading_shadingMass_pos_of_source
    {delta rho : NNReal} {iota : Type*}
    [Fintype iota] [DecidableEq iota]
    {fine : UniformTubeFamily delta iota}
    (S : StickyScaleCover fine rho)
    (Y : Shading fine.bodyFamily)
    (hactive : S.activeFine = Finset.univ)
    (hsourcePos : 0 < Y.shadingMass) :
    0 < (parentAggregatedShading S Y).shadingMass := by
  have hbound :=
    activeFineShading_shadingMass_le_nsmul_parent_of_fiberCard_le
      S Y (Fintype.card {i // i ∈ S.activeFine})
      (fun k => Finset.card_le_univ
        ((activeIndexFactorization S).fiber k))
  have hactiveMass :
      (activeFineShading S Y).shadingMass = Y.shadingMass := by
    classical
    let e : {i // i ∈ S.activeFine} ≃ iota :=
      { toFun := Subtype.val
        invFun := fun i => ⟨i, by rw [hactive]; exact Finset.mem_univ i⟩
        left_inv := fun i => Subtype.ext rfl
        right_inv := fun _ => rfl }
    unfold Shading.shadingMass
    exact Fintype.sum_equiv e
      (fun i : {i // i ∈ S.activeFine} =>
        volume ((activeFineShading S Y).carrier i))
      (fun i : iota => volume (Y.carrier i))
      (fun _ => rfl)
  have hboundSource :
      Y.shadingMass ≤
        Fintype.card {i // i ∈ S.activeFine} •
          (parentAggregatedShading S Y).shadingMass := by
    calc
      Y.shadingMass = (activeFineShading S Y).shadingMass :=
        hactiveMass.symm
      _ ≤ Fintype.card {i // i ∈ S.activeFine} •
          (parentAggregatedShading S Y).shadingMass := hbound
  by_contra hnot
  have hzero : (parentAggregatedShading S Y).shadingMass = 0 :=
    nonpos_iff_eq_zero.mp (le_of_not_gt hnot)
  have hsourceZero : Y.shadingMass ≤ 0 := by
    simpa only [hzero, nsmul_zero] using hboundSource
  exact (not_le_of_gt hsourcePos) hsourceZero

/-- Fully automatic full-index popularity from positive literal source mass.
The source mass supplies both an active occurrence and positive parent mass,
so the only remaining analytic premise is the actual Katz--Tao property. -/
theorem parentAggregatedAveragePopular_halfMass_le_originalUnion_of_sourceMass_pos
    {delta rho : NNReal} {iota : Type*}
    [Fintype iota] [DecidableEq iota]
    {fine : UniformTubeFamily delta iota}
    (S : StickyScaleCover fine rho)
    (Y : Shading fine.bodyFamily)
    (hactive : S.activeFine = Finset.univ)
    (hsourcePos : 0 < Y.shadingMass)
    {C : ENNReal} (hKT : S.IsKatzTaoAtScale C) :
    ENNReal.ofReal
        (parentAverageCarrierMassReal S Y / 2 *
          Fintype.card {k // k ∈ S.activeCoarse}) ≤
      (C *
        (volume
            (fullFamilyHullContainer S.activeCoarseFamily : Set Space) /
          popularCarrierFloor (parentAverageCarrierMassReal S Y) 1)) *
        volume Y.shadedUnion := by
  have hiota : Nonempty iota :=
    nonempty_of_shadingMass_pos Y hsourcePos
  let i : iota := Classical.choice hiota
  have hiActive : i ∈ S.activeFine := by
    rw [hactive]
    exact Finset.mem_univ i
  have hcoarse : S.activeCoarse.Nonempty :=
    ⟨S.parent i, S.parent_mem i hiActive⟩
  exact parentAggregatedAveragePopular_halfMass_le_originalUnion
    S Y hactive hcoarse
      (parentAggregatedShading_shadingMass_pos_of_source
        S Y hactive hsourcePos) hKT


/-- The automatic retained-mass lower bound is literally one half of the
parent shading mass, not merely an opaque `ofReal` expression. -/
theorem ofReal_parentAverageCarrierMassReal_half_card_eq
    {delta rho : NNReal} {iota : Type*}
    [Fintype iota] [DecidableEq iota]
    {fine : UniformTubeFamily delta iota}
    (S : StickyScaleCover fine rho) (Y : Shading fine.bodyFamily)
    (hcoarse : S.activeCoarse.Nonempty) :
    ENNReal.ofReal
        (parentAverageCarrierMassReal S Y / 2 *
          Fintype.card {k // k ∈ S.activeCoarse}) =
      (parentAggregatedShading S Y).shadingMass / 2 := by
  have hindexNonempty : Nonempty {k // k ∈ S.activeCoarse} :=
    ⟨⟨hcoarse.choose, hcoarse.choose_spec⟩⟩
  have hcardPos :
      (0 : Real) < Fintype.card {k // k ∈ S.activeCoarse} := by
    exact_mod_cast (Fintype.card_pos_iff.mpr hindexNonempty)
  have hreal :
      ((parentAggregatedShading S Y).shadingMass.toReal /
          (Fintype.card {k // k ∈ S.activeCoarse} : Real)) / 2 *
          (Fintype.card {k // k ∈ S.activeCoarse} : Real) =
        (parentAggregatedShading S Y).shadingMass.toReal / 2 := by
    calc
      _ = ((parentAggregatedShading S Y).shadingMass.toReal / 2) /
          (Fintype.card {k // k ∈ S.activeCoarse} : Real) *
            Fintype.card {k // k ∈ S.activeCoarse} := by ring
      _ = (parentAggregatedShading S Y).shadingMass.toReal / 2 :=
        div_mul_cancel₀ _ (ne_of_gt hcardPos)
  rw [parentAverageCarrierMassReal, hreal]
  rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : Real) < 2)]
  rw [ENNReal.ofReal_toReal
    (parentAggregatedShading S Y).shadingMass_lt_top.ne]
  norm_num

/-- The automatic popularity floor is exactly average parent mass divided by
two, expressed in `ENNReal`; this exposes the remaining card/hull numerics. -/
theorem popularCarrierFloor_parentAverageCarrierMassReal_eq
    {delta rho : NNReal} {iota : Type*}
    [Fintype iota] [DecidableEq iota]
    {fine : UniformTubeFamily delta iota}
    (S : StickyScaleCover fine rho) (Y : Shading fine.bodyFamily)
    (hcoarse : S.activeCoarse.Nonempty) :
    popularCarrierFloor (parentAverageCarrierMassReal S Y) 1 =
      (parentAggregatedShading S Y).shadingMass /
        ((Fintype.card {k // k ∈ S.activeCoarse} : ENNReal) * 2) := by
  have hindexNonempty : Nonempty {k // k ∈ S.activeCoarse} :=
    ⟨⟨hcoarse.choose, hcoarse.choose_spec⟩⟩
  have hcardPos :
      (0 : Real) < Fintype.card {k // k ∈ S.activeCoarse} := by
    exact_mod_cast (Fintype.card_pos_iff.mpr hindexNonempty)
  rw [popularCarrierFloor, parentAverageCarrierMassReal, mul_one, div_div]
  rw [ENNReal.ofReal_div_of_pos
    (mul_pos hcardPos (by norm_num : (0 : Real) < 2))]
  rw [ENNReal.ofReal_toReal
    (parentAggregatedShading S Y).shadingMass_lt_top.ne]
  norm_num [ENNReal.ofReal_mul]

/-- Normalized callback-free endpoint: half of the literal parent mass is
controlled by the original shaded union, and its denominator displays only
the actual parent cardinality and hull volume. -/
theorem parentAggregatedShading_halfMass_le_originalUnion_of_sourceMass_pos
    {delta rho : NNReal} {iota : Type*}
    [Fintype iota] [DecidableEq iota]
    {fine : UniformTubeFamily delta iota}
    (S : StickyScaleCover fine rho)
    (Y : Shading fine.bodyFamily)
    (hactive : S.activeFine = Finset.univ)
    (hsourcePos : 0 < Y.shadingMass)
    {C : ENNReal} (hKT : S.IsKatzTaoAtScale C) :
    (parentAggregatedShading S Y).shadingMass / 2 ≤
      (C *
        (volume
            (fullFamilyHullContainer S.activeCoarseFamily : Set Space) /
          ((parentAggregatedShading S Y).shadingMass /
            ((Fintype.card {k // k ∈ S.activeCoarse} : ENNReal) * 2)))) *
        volume Y.shadedUnion := by
  have hiota : Nonempty iota :=
    nonempty_of_shadingMass_pos Y hsourcePos
  let i : iota := Classical.choice hiota
  have hiActive : i ∈ S.activeFine := by
    rw [hactive]
    exact Finset.mem_univ i
  have hcoarse : S.activeCoarse.Nonempty :=
    ⟨S.parent i, S.parent_mem i hiActive⟩
  have hraw :=
    parentAggregatedAveragePopular_halfMass_le_originalUnion_of_sourceMass_pos
      S Y hactive hsourcePos hKT
  rw [ofReal_parentAverageCarrierMassReal_half_card_eq S Y hcoarse,
    popularCarrierFloor_parentAverageCarrierMassReal_eq S Y hcoarse] at hraw
  exact hraw


/-- Division-free ENNReal algebra behind the popular-row endpoint.  A positive
finite mass and a positive finite row count allow both displayed denominators
to cancel exactly, with no finiteness premise on the remaining factors. -/
theorem sq_le_four_mul_of_half_le_averageFloor_ratio
    {mass rows C hull union : ENNReal}
    (hmass0 : mass ≠ 0) (hmassTop : mass ≠ ∞)
    (hrows0 : rows ≠ 0) (hrowsTop : rows ≠ ∞)
    (hhalf :
      mass / 2 ≤
        (C * (hull / (mass / (rows * 2)))) * union) :
    mass * mass ≤ (4 * rows * C * hull) * union := by
  have hden0 : rows * 2 ≠ 0 := by simp [hrows0]
  have hdenTop : rows * 2 ≠ ∞ :=
    ENNReal.mul_ne_top hrowsTop (by norm_num)
  have hfloor0 : mass / (rows * 2) ≠ 0 :=
    ENNReal.div_ne_zero.mpr ⟨hmass0, hdenTop⟩
  have hfloorTop : mass / (rows * 2) ≠ ∞ :=
    ENNReal.div_ne_top hmassTop hden0
  have hmul := mul_le_mul_right hhalf (mass / (rows * 2))
  have hcancelled :
      (mass / 2) * (mass / (rows * 2)) ≤ (C * hull) * union := by
    calc
      (mass / 2) * (mass / (rows * 2)) ≤
          ((C * (hull / (mass / (rows * 2)))) * union) *
            (mass / (rows * 2)) := by simpa only [mul_comm] using hmul
      _ = (C * union) *
          ((hull / (mass / (rows * 2))) *
            (mass / (rows * 2))) := by ac_rfl
      _ = (C * union) * hull := by
        rw [ENNReal.div_mul_cancel hfloor0 hfloorTop]
      _ = (C * hull) * union := by ac_rfl
  have hscaled := mul_le_mul_right hcancelled (2 * (rows * 2))
  calc
    mass * mass =
        ((mass / 2) * (mass / (rows * 2))) *
          (2 * (rows * 2)) := by
      calc
        mass * mass = (mass / 2 * 2) *
            (mass / (rows * 2) * (rows * 2)) := by
          rw [ENNReal.div_mul_cancel (by norm_num) (by norm_num),
            ENNReal.div_mul_cancel hden0 hdenTop]
        _ = ((mass / 2) * (mass / (rows * 2))) *
            (2 * (rows * 2)) := by ac_rfl
    _ ≤ ((C * hull) * union) * (2 * (rows * 2)) := by simpa only [mul_comm] using hscaled
    _ = (4 * rows * C * hull) * union := by ring

/-- Actual division-free popular-row estimate.  Positive literal source mass
automatically supplies every nonzero/finite denominator used in the algebra. -/
theorem parentAggregatedShading_sq_le_popularLoss_mul_originalUnion
    {delta rho : NNReal} {iota : Type*}
    [Fintype iota] [DecidableEq iota]
    {fine : UniformTubeFamily delta iota}
    (S : StickyScaleCover fine rho)
    (Y : Shading fine.bodyFamily)
    (hactive : S.activeFine = Finset.univ)
    (hsourcePos : 0 < Y.shadingMass)
    {C : ENNReal} (hKT : S.IsKatzTaoAtScale C) :
    (parentAggregatedShading S Y).shadingMass *
        (parentAggregatedShading S Y).shadingMass ≤
      (4 * (Fintype.card {k // k ∈ S.activeCoarse} : ENNReal) * C *
        volume (fullFamilyHullContainer S.activeCoarseFamily : Set Space)) *
        volume Y.shadedUnion := by
  have hiota : Nonempty iota :=
    nonempty_of_shadingMass_pos Y hsourcePos
  let i : iota := Classical.choice hiota
  have hiActive : i ∈ S.activeFine := by
    rw [hactive]
    exact Finset.mem_univ i
  have hcoarse : S.activeCoarse.Nonempty :=
    ⟨S.parent i, S.parent_mem i hiActive⟩
  have hparentPos : 0 < (parentAggregatedShading S Y).shadingMass :=
    parentAggregatedShading_shadingMass_pos_of_source
      S Y hactive hsourcePos
  have hrows0 :
      (Fintype.card {k // k ∈ S.activeCoarse} : ENNReal) ≠ 0 := by
    exact_mod_cast (Fintype.card_pos_iff.mpr
      (show Nonempty {k // k ∈ S.activeCoarse} from
        ⟨⟨hcoarse.choose, hcoarse.choose_spec⟩⟩)).ne'
  exact sq_le_four_mul_of_half_le_averageFloor_ratio
    (ne_of_gt hparentPos)
    (parentAggregatedShading S Y).shadingMass_lt_top.ne
    hrows0 (by simp)
    (parentAggregatedShading_halfMass_le_originalUnion_of_sourceMass_pos
      S Y hactive hsourcePos hKT)


/-- Complete explicit loss in the popular-row square-mass route.  Unlike the
old canonical factor, every component is a finite combinatorial count, the
actual Katz--Tao constant, or a literal convex-hull volume. -/
def stickyPopularFineSquareFactor
    {delta rho : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    {fine : UniformTubeFamily delta iota}
    (S : StickyScaleCover fine rho) (fiberCap : Nat)
    (katzTaoError : ENNReal) : ENNReal :=
  (fiberCap : ENNReal) ^ 2 *
    (4 * (Fintype.card {k // k ∈ S.activeCoarse} : ENNReal) *
      katzTaoError *
      volume (fullFamilyHullContainer S.activeCoarseFamily : Set Space))

/-- Full source version of the division-free popular-row estimate.  The
actual fibre-card loss is squared because the incidence estimate controls the
square of parent mass. -/
theorem shadingMass_sq_le_stickyPopularFineSquareFactor_mul_shadedUnion
    {delta rho : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    {fine : UniformTubeFamily delta iota}
    (S : StickyScaleCover fine rho)
    (Y : Shading fine.bodyFamily)
    (hactive : S.activeFine = Finset.univ)
    (hsourcePos : 0 < Y.shadingMass)
    (fiberCap : Nat)
    (hfiber : ∀ k : {k // k ∈ S.activeCoarse},
      ((activeIndexFactorization S).fiber k).card ≤ fiberCap)
    {katzTaoError : ENNReal}
    (hKT : S.IsKatzTaoAtScale katzTaoError) :
    Y.shadingMass * Y.shadingMass ≤
      stickyPopularFineSquareFactor S fiberCap katzTaoError *
        volume Y.shadedUnion := by
  have hsourceParent :
      Y.shadingMass ≤
        (fiberCap : ENNReal) *
          (parentAggregatedShading S Y).shadingMass := by
    calc
      Y.shadingMass = (activeFineShading S Y).shadingMass :=
        (activeFineShading_shadingMass_eq_of_activeFine_eq_univ
          S Y hactive).symm
      _ ≤ (fiberCap : ENNReal) *
          (parentAggregatedShading S Y).shadingMass := by
        simpa only [nsmul_eq_mul] using
          (activeFineShading_shadingMass_le_nsmul_parent_of_fiberCard_le
            S Y fiberCap hfiber)
  have hsourceSq :
      Y.shadingMass * Y.shadingMass ≤
        ((fiberCap : ENNReal) *
          (parentAggregatedShading S Y).shadingMass) *
        ((fiberCap : ENNReal) *
          (parentAggregatedShading S Y).shadingMass) :=
    mul_le_mul hsourceParent hsourceParent bot_le bot_le
  have hparentSq :=
    parentAggregatedShading_sq_le_popularLoss_mul_originalUnion
      S Y hactive hsourcePos hKT
  calc
    Y.shadingMass * Y.shadingMass ≤
        ((fiberCap : ENNReal) *
          (parentAggregatedShading S Y).shadingMass) *
        ((fiberCap : ENNReal) *
          (parentAggregatedShading S Y).shadingMass) := hsourceSq
    _ = (fiberCap : ENNReal) ^ 2 *
        ((parentAggregatedShading S Y).shadingMass *
          (parentAggregatedShading S Y).shadingMass) := by ring
    _ ≤ (fiberCap : ENNReal) ^ 2 *
        ((4 * (Fintype.card {k // k ∈ S.activeCoarse} : ENNReal) *
          katzTaoError *
          volume (fullFamilyHullContainer S.activeCoarseFamily : Set Space)) *
          volume Y.shadedUnion) :=
      mul_le_mul' le_rfl hparentSq
    _ = stickyPopularFineSquareFactor S fiberCap katzTaoError *
        volume Y.shadedUnion := by
      simp only [stickyPopularFineSquareFactor]
      ring


/-- All-Frostman union lower bound through the fully explicit popular-row
square factor.  The former canonical row-scale callback is absent; the only
remaining budget is the displayed product of finite counts, Katz--Tao error,
and literal hull volume.  Squaring the source mass changes the exponent
bookkeeping from `2 * eta` to `4 * eta`. -/
theorem allFrostman_unionLower_of_stickyPopularSquareFactor
    {delta : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    {eta zeta gamma : Real}
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible)
    (hF : FrostmanHypotheses D eta)
    (cover : StickyMultiscaleCover D.family)
    {frostmanError katzTaoError : ENNReal}
    (hsticky : cover.IsStickyAtEveryScale frostmanError katzTaoError)
    (rho : NNReal) (hdeltaRho : delta ≤ rho) (hrhoOne : rho ≤ 1)
    (hactive :
      (cover.cover rho hdeltaRho hrhoOne).activeFine = Finset.univ)
    (fiberCap : Nat)
    (hfiber : ∀ k :
      {k // k ∈ (cover.cover rho hdeltaRho hrhoOne).activeCoarse},
      ((activeIndexFactorization
        (cover.cover rho hdeltaRho hrhoOne)).fiber k).card ≤ fiberCap)
    (hexponent : 4 * eta + zeta ≤ gamma / 2)
    (hfactor :
      stickyPopularFineSquareFactor
          (cover.cover rho hdeltaRho hrhoOne) fiberCap katzTaoError ≤
        (delta : ENNReal) ^ (-zeta)) :
    (delta : ENNReal) ^ (gamma / 2) ≤
      volume D.shading.shadedUnion := by
  let S := cover.cover rho hdeltaRho hrhoOne
  let factor := stickyPopularFineSquareFactor S fiberCap katzTaoError
  have hmassLower :
      (delta : ENNReal) ^ (2 * eta) ≤ D.shading.shadingMass :=
    delta_rpow_two_eta_le_shadingMass_of_frostman D hD hF
  have hmassPos : 0 < D.shading.shadingMass := by
    have hpowPos : 0 < (delta : ENNReal) ^ (2 * eta) :=
      ENNReal.rpow_pos (ENNReal.coe_pos.mpr hD.delta_pos) ENNReal.coe_ne_top
    exact hpowPos.trans_le hmassLower
  have hmassSqUpper :
      D.shading.shadingMass * D.shading.shadingMass ≤
        factor * volume D.shading.shadedUnion := by
    dsimp only [factor]
    exact shadingMass_sq_le_stickyPopularFineSquareFactor_mul_shadedUnion
      S D.shading hactive hmassPos fiberCap hfiber
        (hsticky.katzTao rho hdeltaRho hrhoOne)
  have hd0 : (delta : ENNReal) ≠ 0 :=
    ne_of_gt (ENNReal.coe_pos.mpr hD.delta_pos)
  have hdTop : (delta : ENNReal) ≠ ∞ := ENNReal.coe_ne_top
  have hmassSqLower :
      (delta : ENNReal) ^ (2 * (2 * eta)) ≤
        D.shading.shadingMass * D.shading.shadingMass := by
    rw [show 2 * (2 * eta) = (2 * eta) + (2 * eta) by ring,
      ENNReal.rpow_add _ _ hd0 hdTop]
    exact mul_le_mul hmassLower hmassLower bot_le bot_le
  have hdeltaOne : delta ≤ 1 :=
    hD.delta_le_half.trans (by norm_num)
  have hexponentTwo : 2 * (2 * eta) + zeta ≤ gamma / 2 := by
    linarith
  have hpower :
      factor * (delta : ENNReal) ^ (gamma / 2) ≤
        (delta : ENNReal) ^ (2 * (2 * eta)) := by
    exact stickyFactor_mul_targetPower_le_twoDensityPower
      hD.delta_pos hdeltaOne hfactor hexponentTwo
  have hfactorTop : factor ≠ ∞ :=
    ne_top_of_le_ne_top
      (ENNReal.rpow_ne_top_of_ne_zero hd0 ENNReal.coe_ne_top) hfactor
  have hfactor0 : factor ≠ 0 := by
    intro hzero
    rw [hzero, zero_mul] at hmassSqUpper
    exact (mul_ne_zero (ne_of_gt hmassPos) (ne_of_gt hmassPos))
      (nonpos_iff_eq_zero.mp hmassSqUpper)
  apply (ENNReal.mul_le_mul_iff_right hfactor0 hfactorTop).mp
  exact hpower.trans (hmassSqLower.trans hmassSqUpper)


/-- Fully automatic combinatorial version of the popular square factor.  Both
the largest parent fibre and the number of active parents are bounded by the
literal source index cardinality, leaving a cubic source-card loss. -/
def stickyPopularCardCubeFactor
    {delta rho : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    {fine : UniformTubeFamily delta iota}
    (S : StickyScaleCover fine rho) (katzTaoError : ENNReal) : ENNReal :=
  (Fintype.card iota : ENNReal) ^ 2 *
    (4 * (Fintype.card iota : ENNReal) * katzTaoError *
      volume (fullFamilyHullContainer S.activeCoarseFamily : Set Space))

/-- The explicit fibre/parent factor is bounded by the source-card cube with
no cardinality premise. -/
theorem stickyPopularFineSquareFactor_sourceCard_le_cardCube
    {delta rho : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    {fine : UniformTubeFamily delta iota}
    (S : StickyScaleCover fine rho) (katzTaoError : ENNReal) :
    stickyPopularFineSquareFactor S (Fintype.card iota) katzTaoError ≤
      stickyPopularCardCubeFactor S katzTaoError := by
  have hparentNat : S.activeCoarse.card ≤ S.activeFine.card := by
    apply Finset.card_le_card_of_surjOn S.parent
    intro k hk
    obtain ⟨i, hi, hparent⟩ := S.parent_surjective k hk
    exact ⟨i, hi, hparent⟩
  have hparentSourceNat :
      Fintype.card {k // k ∈ S.activeCoarse} ≤ Fintype.card iota := by
    calc
      Fintype.card {k // k ∈ S.activeCoarse} = S.activeCoarse.card :=
        Fintype.card_coe S.activeCoarse
      _ ≤ S.activeFine.card := hparentNat
      _ ≤ Fintype.card iota := Finset.card_le_univ S.activeFine
  have hparentSource :
      (Fintype.card {k // k ∈ S.activeCoarse} : ENNReal) ≤
        Fintype.card iota := by
    exact_mod_cast hparentSourceNat
  unfold stickyPopularFineSquareFactor stickyPopularCardCubeFactor
  gcongr

/-- Callback-free source-card form of the square-mass estimate. -/
theorem shadingMass_sq_le_stickyPopularCardCubeFactor_mul_shadedUnion
    {delta rho : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    {fine : UniformTubeFamily delta iota}
    (S : StickyScaleCover fine rho)
    (Y : Shading fine.bodyFamily)
    (hactive : S.activeFine = Finset.univ)
    (hsourcePos : 0 < Y.shadingMass)
    {katzTaoError : ENNReal}
    (hKT : S.IsKatzTaoAtScale katzTaoError) :
    Y.shadingMass * Y.shadingMass ≤
      stickyPopularCardCubeFactor S katzTaoError *
        volume Y.shadedUnion := by
  have hfiber : ∀ k : {k // k ∈ S.activeCoarse},
      ((activeIndexFactorization S).fiber k).card ≤ Fintype.card iota := by
    intro k
    exact (Finset.card_le_univ
      ((activeIndexFactorization S).fiber k)).trans
        (Fintype.card_subtype_le fun i => i ∈ S.activeFine)
  have hraw :=
    shadingMass_sq_le_stickyPopularFineSquareFactor_mul_shadedUnion
      S Y hactive hsourcePos (Fintype.card iota) hfiber hKT
  exact hraw.trans (mul_le_mul'
    (stickyPopularFineSquareFactor_sourceCard_le_cardCube S katzTaoError)
    le_rfl)

/-- Actual all-Frostman endpoint with every finite cardinality callback
removed.  The remaining scalar power budget is the literal source-card cube,
Katz--Tao error, and parent hull volume. -/
theorem allFrostman_unionLower_of_stickyPopularCardCubeFactor
    {delta : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    {eta zeta gamma : Real}
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible)
    (hF : FrostmanHypotheses D eta)
    (cover : StickyMultiscaleCover D.family)
    {frostmanError katzTaoError : ENNReal}
    (hsticky : cover.IsStickyAtEveryScale frostmanError katzTaoError)
    (rho : NNReal) (hdeltaRho : delta ≤ rho) (hrhoOne : rho ≤ 1)
    (hactive :
      (cover.cover rho hdeltaRho hrhoOne).activeFine = Finset.univ)
    (hexponent : 4 * eta + zeta ≤ gamma / 2)
    (hfactor :
      stickyPopularCardCubeFactor
          (cover.cover rho hdeltaRho hrhoOne) katzTaoError ≤
        (delta : ENNReal) ^ (-zeta)) :
    (delta : ENNReal) ^ (gamma / 2) ≤
      volume D.shading.shadedUnion := by
  have hfiber : ∀ k :
      {k // k ∈ (cover.cover rho hdeltaRho hrhoOne).activeCoarse},
      ((activeIndexFactorization
        (cover.cover rho hdeltaRho hrhoOne)).fiber k).card ≤
        Fintype.card iota := by
    intro k
    exact (Finset.card_le_univ
      ((activeIndexFactorization
        (cover.cover rho hdeltaRho hrhoOne)).fiber k)).trans
      (Fintype.card_subtype_le fun i =>
        i ∈ (cover.cover rho hdeltaRho hrhoOne).activeFine)
  apply allFrostman_unionLower_of_stickyPopularSquareFactor
    D hD hF cover hsticky rho hdeltaRho hrhoOne hactive
      (Fintype.card iota) hfiber hexponent
  exact (stickyPopularFineSquareFactor_sourceCard_le_cardCube
    (cover.cover rho hdeltaRho hrhoOne) katzTaoError).trans hfactor

#print axioms parentAggregatedPopular_halfMass_le_activeFineUnion
#print axioms parentAggregatedPopular_halfMass_le_originalUnion
#print axioms sum_restrictedMassReal_univ_eq_shadingMass_toReal
#print axioms parentAggregatedAveragePopular_halfMass_le_originalUnion
#print axioms nonempty_of_shadingMass_pos
#print axioms parentAggregatedShading_shadingMass_pos_of_source
#print axioms parentAggregatedAveragePopular_halfMass_le_originalUnion_of_sourceMass_pos
#print axioms ofReal_parentAverageCarrierMassReal_half_card_eq
#print axioms popularCarrierFloor_parentAverageCarrierMassReal_eq
#print axioms parentAggregatedShading_halfMass_le_originalUnion_of_sourceMass_pos
#print axioms sq_le_four_mul_of_half_le_averageFloor_ratio
#print axioms parentAggregatedShading_sq_le_popularLoss_mul_originalUnion
#print axioms shadingMass_sq_le_stickyPopularFineSquareFactor_mul_shadedUnion
#print axioms allFrostman_unionLower_of_stickyPopularSquareFactor
#print axioms stickyPopularFineSquareFactor_sourceCard_le_cardCube
#print axioms shadingMass_sq_le_stickyPopularCardCubeFactor_mul_shadedUnion
#print axioms allFrostman_unionLower_of_stickyPopularCardCubeFactor

end
end Family8StickyParentPopularCanonicalUnionV1
