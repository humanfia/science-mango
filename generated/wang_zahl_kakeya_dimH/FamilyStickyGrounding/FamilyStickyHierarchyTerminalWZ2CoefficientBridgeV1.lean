import FamilyStickyGrounding.FamilyStickyHierarchyTerminalEssentialDistinctAdapterV1
import FamilyStickyGrounding.FamilyStickyWZ2SameScaleCoefficientCapV1
import FamilyStickyGrounding.FamilyStickySameRadiusTubeContainmentCompatibleV1
import FamilyStickyCinematicL32ActualTubeIndexedCoefficientSelectionV1
import FamilyStickyCinematicL32ActualHalfScaleCoefficientCoverV1
import Family6Grounding.Family6ProjectiveSineTriangleV1

set_option autoImplicit false
set_option warningAsError true

open Set
open scoped NNReal

namespace FamilyStickyHierarchyTerminalWZ2CoefficientBridgeV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family4GlobalExtremalUpstream
open FamilyStickyCinematicL32Lemma57EssentiallyDistinctTubeImageV1
open FamilyStickyCinematicL32ActualTubeCoefficientDistancesV1
open FamilyStickyCinematicL32ActualTubeCoefficientSelectionV1
open FamilyStickyCinematicL32ActualTubeCoefficientFiberV1
open FamilyStickyCinematicL32ActualTubeIndexedCoefficientSelectionV1
open FamilyStickyCinematicL32ActualHalfScaleCoefficientCoverV1
open Family6ProjectiveSineTriangleV1
open FamilyStickySameRadiusTubeContainmentCompatibleV1
open FamilyStickyWZ2SameScaleCoefficientCapV1
open FamilyStickyHierarchyRandomMotionAdapterV1
open FamilyStickyHierarchyJointRandomMotionCertificateV1
open FamilyStickyHierarchyJointRandomMotionCertificateV1.HierarchyJointRandomMotionCertificate
open FamilyStickyHierarchyTerminalCarrierDedupV1
open FamilyStickyHierarchyTerminalEssentialDistinctAdapterV1

noncomputable section
set_option linter.unusedSectionVars false

/-!
# WZ2 terminal families through coefficient deduplication

The Cinematic coefficient-image and same-scale-cover arguments used a
Family4 half-volume-overlap hypothesis only to prove two finite facts:

* the active-index-to-tube map is injective;
* a same-radius cover-parent fibre contains at most one active child.

Both facts follow directly from WZ2 two-fold noncontainment.  This module
factors the finite arguments first through the minimal `Set.InjOn` premise,
then supplies WZ2 wrappers, and finally specializes the complete chain to
the canonical terminal strong family.  No implication from WZ2 separation
to Family4's volume-overlap predicate is used or asserted.
-/

universe u

variable {delta : NNReal} {iota : Type u} [DecidableEq iota]
  {fine : UniformTubeFamily delta iota} {active : Finset iota}

/-! ## Lossless active images from the minimal injectivity input -/

/-- Imaging active indices by an injective-on-active tube map loses no
cardinality. -/
theorem activeTubeImage_card_of_injOn
    (hinj : Set.InjOn fine.tubes (active : Set iota)) :
    (activeTubeImage fine active).card = active.card := by
  classical
  rw [activeTubeImage]
  exact Finset.card_image_iff.mpr fun i hi j hj htube =>
    hinj hi hj htube

/-- Pairwise WZ2 separation makes the tube map injective on the active
indices, without a positive-radius premise. -/
theorem tubes_injectiveOn_active_of_pairwise_wz2
    (hpair : Set.Pairwise (active : Set iota) fun i j =>
      WZ2EssentiallyDistinct (fine.tubes i) (fine.tubes j)) :
    Set.InjOn fine.tubes (active : Set iota) := by
  intro i hi j hj htube
  by_contra hij
  exact (hpair hi hj hij).tube_ne htube

/-- The active image retains cardinality under pairwise WZ2 separation. -/
theorem activeTubeImage_card_of_pairwise_wz2
    (hpair : Set.Pairwise (active : Set iota) fun i j =>
      WZ2EssentiallyDistinct (fine.tubes i) (fine.tubes j)) :
    (activeTubeImage fine active).card = active.card :=
  activeTubeImage_card_of_injOn
    (tubes_injectiveOn_active_of_pairwise_wz2 hpair)

/-! ## Near-coefficient fibres from the minimal injectivity input -/

/-- Filtering the concrete tube image and filtering active indices have the
same cardinality whenever the tube map is injective on active indices. -/
theorem card_activeTubeImage_filter_near_eq_of_injOn
    (hinj : Set.InjOn fine.tubes (active : Set iota))
    (center : Tube delta) (scale : Real) :
    ((activeTubeImage fine active).filter fun T =>
      projectedTubePairCoefficientDistance T center < scale).card =
      (activeNearCoefficientIndices fine active center scale).card := by
  classical
  rw [activeTubeImage_filter_near_eq_image]
  change ((activeNearCoefficientIndices fine active center scale).image
    fine.tubes).card = _
  apply Finset.card_image_iff.mpr
  intro i hi j hj htube
  exact hinj (Finset.mem_filter.mp hi).1
    (Finset.mem_filter.mp hj).1 htube

/-- WZ2 form of the exact concrete/indexed near-fibre equicardinality. -/
theorem card_activeTubeImage_filter_near_eq_of_pairwise_wz2
    (hpair : Set.Pairwise (active : Set iota) fun i j =>
      WZ2EssentiallyDistinct (fine.tubes i) (fine.tubes j))
    (center : Tube delta) (scale : Real) :
    ((activeTubeImage fine active).filter fun T =>
      projectedTubePairCoefficientDistance T center < scale).card =
      (activeNearCoefficientIndices fine active center scale).card :=
  card_activeTubeImage_filter_near_eq_of_injOn
    (tubes_injectiveOn_active_of_pairwise_wz2 hpair) center scale

/-- An indexed near-coefficient cap transports to the concrete image using
only injectivity of the tube map on the active set. -/
theorem concrete_nearCap_of_active_cap_of_injOn
    (hinj : Set.InjOn fine.tubes (active : Set iota))
    (scale : Real) (multiplicity : Nat)
    (hactiveCap : forall center,
      center ∈ selectedTubes (activeTubeImage fine active) scale ->
      (activeNearCoefficientIndices fine active center scale).card ≤
        multiplicity) :
    forall center,
      center ∈ selectedTubes (activeTubeImage fine active) scale ->
      ((activeTubeImage fine active).filter fun T =>
        projectedTubePairCoefficientDistance T center < scale).card ≤
          multiplicity := by
  intro center hcenter
  rw [card_activeTubeImage_filter_near_eq_of_injOn
    hinj center scale]
  exact hactiveCap center hcenter

/-- WZ2 wrapper for transport of an indexed near-coefficient cap. -/
theorem concrete_nearCap_of_active_cap_of_pairwise_wz2
    (hpair : Set.Pairwise (active : Set iota) fun i j =>
      WZ2EssentiallyDistinct (fine.tubes i) (fine.tubes j))
    (scale : Real) (multiplicity : Nat)
    (hactiveCap : forall center,
      center ∈ selectedTubes (activeTubeImage fine active) scale ->
      (activeNearCoefficientIndices fine active center scale).card ≤
        multiplicity) :
    forall center,
      center ∈ selectedTubes (activeTubeImage fine active) scale ->
      ((activeTubeImage fine active).filter fun T =>
        projectedTubePairCoefficientDistance T center < scale).card ≤
          multiplicity :=
  concrete_nearCap_of_active_cap_of_injOn
    (tubes_injectiveOn_active_of_pairwise_wz2 hpair)
    scale multiplicity hactiveCap

/-! ## Coefficient selection with no volume-overlap hypothesis -/

/-- Minimal-injectivity version of indexed coefficient-card retention. -/
theorem active_card_le_multiplicity_mul_selectedTubes_card_of_injOn
    (hinj : Set.InjOn fine.tubes (active : Set iota))
    {scale : Real} (hscale : 0 < scale) (multiplicity : Nat)
    (hactiveCap : forall center,
      center ∈ selectedTubes (activeTubeImage fine active) scale ->
      (activeNearCoefficientIndices fine active center scale).card ≤
        multiplicity) :
    active.card ≤ multiplicity *
      (selectedTubes (activeTubeImage fine active) scale).card := by
  have hconcreteCap := concrete_nearCap_of_active_cap_of_injOn
    hinj scale multiplicity hactiveCap
  have hretention := family_card_le_mul_selectedTubes_card_of_near_cap
    (activeTubeImage fine active) hscale multiplicity hconcreteCap
  rw [activeTubeImage_card_of_injOn hinj] at hretention
  exact hretention

/-- WZ2 version of indexed coefficient-card retention. -/
theorem active_card_le_multiplicity_mul_selectedTubes_card_of_pairwise_wz2
    (hpair : Set.Pairwise (active : Set iota) fun i j =>
      WZ2EssentiallyDistinct (fine.tubes i) (fine.tubes j))
    {scale : Real} (hscale : 0 < scale) (multiplicity : Nat)
    (hactiveCap : forall center,
      center ∈ selectedTubes (activeTubeImage fine active) scale ->
      (activeNearCoefficientIndices fine active center scale).card ≤
        multiplicity) :
    active.card ≤ multiplicity *
      (selectedTubes (activeTubeImage fine active) scale).card :=
  active_card_le_multiplicity_mul_selectedTubes_card_of_injOn
    (tubes_injectiveOn_active_of_pairwise_wz2 hpair)
    hscale multiplicity hactiveCap

/-- A large WZ2-separated active family retains at least three selected
coefficient centres. -/
theorem three_le_selectedTubes_card_of_pairwise_wz2
    (hpair : Set.Pairwise (active : Set iota) fun i j =>
      WZ2EssentiallyDistinct (fine.tubes i) (fine.tubes j))
    {scale : Real} (hscale : 0 < scale)
    {multiplicity : Nat} (hmultiplicity : 0 < multiplicity)
    (hlarge : 3 * multiplicity ≤ active.card)
    (hactiveCap : forall center,
      center ∈ selectedTubes (activeTubeImage fine active) scale ->
      (activeNearCoefficientIndices fine active center scale).card ≤
        multiplicity) :
    3 ≤ (selectedTubes (activeTubeImage fine active) scale).card := by
  have hconcreteCap := concrete_nearCap_of_active_cap_of_pairwise_wz2
    hpair scale multiplicity hactiveCap
  apply three_le_selectedTubes_card_of_near_cap
    (activeTubeImage fine active) hscale hmultiplicity
  · rw [activeTubeImage_card_of_pairwise_wz2 hpair]
    exact hlarge
  · exact hconcreteCap

/-- Under the same WZ2 data, the selected concrete coefficient family is
nonempty. -/
theorem selectedTubes_nonempty_of_pairwise_wz2
    (hpair : Set.Pairwise (active : Set iota) fun i j =>
      WZ2EssentiallyDistinct (fine.tubes i) (fine.tubes j))
    {scale : Real} (hscale : 0 < scale)
    {multiplicity : Nat} (hmultiplicity : 0 < multiplicity)
    (hlarge : 3 * multiplicity ≤ active.card)
    (hactiveCap : forall center,
      center ∈ selectedTubes (activeTubeImage fine active) scale ->
      (activeNearCoefficientIndices fine active center scale).card ≤
        multiplicity) :
    (selectedTubes (activeTubeImage fine active) scale).Nonempty := by
  apply Finset.card_pos.mp
  exact lt_of_lt_of_le (by decide)
    (three_le_selectedTubes_card_of_pairwise_wz2
      hpair hscale hmultiplicity hlarge hactiveCap)

/-! ## Direct terminal-strong endpoints -/

variable {depth : Nat} {nominalRadius : Nat -> NNReal}
  {Index : Nat -> Type*}
  [forall l, Fintype (Index l)] [forall l, DecidableEq (Index l)]
  {H : MultiscaleTubeHierarchy depth nominalRadius Index}
  {G : HierarchyRandomMotionGeometry H}
  (C : HierarchyJointRandomMotionCertificate H G)

/-- A same-scale cover of the canonical terminal strong family. -/
abbrev TerminalStrongSameScaleCover :=
  @TubeScaleCover (H.effectiveRadius 0) (H.effectiveRadius 0)
    (TerminalStrongIndex C) _ (terminalStrongTubeFamily C) Finset.univ

/-- The terminal pairwise theorem restricted to the concrete finite active set. -/
theorem terminalStrongTubeFamily_pairwise_wz2_on_activeUniv :
    Set.Pairwise
      ((Finset.univ : Finset (TerminalStrongIndex C)) :
        Set (TerminalStrongIndex C)) fun a b =>
      WZ2EssentiallyDistinct
        ((terminalStrongTubeFamily C).tubes a)
        ((terminalStrongTubeFamily C).tubes b) := by
  intro a _ha b _hb hab
  exact terminalStrongTubeFamily_pairwise_wz2EssentiallyDistinct C
    (Set.mem_univ a) (Set.mem_univ b) hab

/-- The complete full coefficient-fibre cap for terminal strong
representatives, directly from their proved WZ2 separation.  No
WZ2-to-volume-overlap seam appears. -/
theorem terminalStrong_activeNearCoefficientIndices_card_le_fullCap
    (Q : TerminalStrongSameScaleCover C)
    (hdelta : 0 < H.effectiveRadius 0)
    (hhalfParallel : forall j : TerminalStrongIndex C,
      forall i : TerminalStrongIndex C,
      i ∈ activeNearCoefficientIndices (terminalStrongTubeFamily C)
        Finset.univ ((terminalStrongTubeFamily C).tubes j)
          (((H.effectiveRadius 0 : NNReal) : Real) / 2) ->
      EssentiallyParallelAtScale
        ((terminalStrongTubeFamily C).tubes i)
        ((terminalStrongTubeFamily C).tubes j))
    (center : Tube (H.effectiveRadius 0)) :
    (activeNearCoefficientIndices (terminalStrongTubeFamily C) Finset.univ
      center ((H.effectiveRadius 0 : NNReal) : Real)).card ≤
      actualHalfScaleCoefficientCoverLoss * Q.count := by
  apply activeNearCoefficientIndices_card_le_coverLoss_mul_count_wz2
    Q hdelta
      (terminalStrongTubeFamily_pairwise_wz2_on_activeUniv C)
  intro j _hj i hi
  exact hhalfParallel j i hi

/-- Terminal strong representatives retain their full index cardinality up
to the explicit same-scale coefficient multiplicity. -/
theorem terminalStrong_card_le_fullCap_mul_selectedTubes_card
    (Q : TerminalStrongSameScaleCover C)
    (hdelta : 0 < H.effectiveRadius 0)
    (hhalfParallel : forall j : TerminalStrongIndex C,
      forall i : TerminalStrongIndex C,
      i ∈ activeNearCoefficientIndices (terminalStrongTubeFamily C)
        Finset.univ ((terminalStrongTubeFamily C).tubes j)
          (((H.effectiveRadius 0 : NNReal) : Real) / 2) ->
      EssentiallyParallelAtScale
        ((terminalStrongTubeFamily C).tubes i)
        ((terminalStrongTubeFamily C).tubes j)) :
    Fintype.card (TerminalStrongIndex C) ≤
      (actualHalfScaleCoefficientCoverLoss * Q.count) *
        (selectedTubes
          (activeTubeImage (terminalStrongTubeFamily C) Finset.univ)
          ((H.effectiveRadius 0 : NNReal) : Real)).card := by
  have hscale : 0 < ((H.effectiveRadius 0 : NNReal) : Real) := by
    exact_mod_cast hdelta
  have hcap : forall center,
      center ∈ selectedTubes
        (activeTubeImage (terminalStrongTubeFamily C) Finset.univ)
        ((H.effectiveRadius 0 : NNReal) : Real) ->
      (activeNearCoefficientIndices (terminalStrongTubeFamily C) Finset.univ
        center ((H.effectiveRadius 0 : NNReal) : Real)).card ≤
          actualHalfScaleCoefficientCoverLoss * Q.count := by
    intro center _hcenter
    exact terminalStrong_activeNearCoefficientIndices_card_le_fullCap
      C Q hdelta hhalfParallel center
  simpa only [Finset.card_univ] using
    (active_card_le_multiplicity_mul_selectedTubes_card_of_pairwise_wz2
      (terminalStrongTubeFamily_pairwise_wz2_on_activeUniv C)
      hscale (actualHalfScaleCoefficientCoverLoss * Q.count) hcap)

/-- If the terminal strong family is large compared with the explicit full
coefficient cap, the selected concrete family is nonempty, still with no
volume-overlap premise. -/
theorem terminalStrong_selectedTubes_nonempty
    (Q : TerminalStrongSameScaleCover C)
    (hdelta : 0 < H.effectiveRadius 0)
    (hcount : 0 < Q.count)
    (hlarge :
      3 * (actualHalfScaleCoefficientCoverLoss * Q.count) ≤
        Fintype.card (TerminalStrongIndex C))
    (hhalfParallel : forall j : TerminalStrongIndex C,
      forall i : TerminalStrongIndex C,
      i ∈ activeNearCoefficientIndices (terminalStrongTubeFamily C)
        Finset.univ ((terminalStrongTubeFamily C).tubes j)
          (((H.effectiveRadius 0 : NNReal) : Real) / 2) ->
      EssentiallyParallelAtScale
        ((terminalStrongTubeFamily C).tubes i)
        ((terminalStrongTubeFamily C).tubes j)) :
    (selectedTubes
      (activeTubeImage (terminalStrongTubeFamily C) Finset.univ)
      ((H.effectiveRadius 0 : NNReal) : Real)).Nonempty := by
  have hscale : 0 < ((H.effectiveRadius 0 : NNReal) : Real) := by
    exact_mod_cast hdelta
  have hmultiplicity :
      0 < actualHalfScaleCoefficientCoverLoss * Q.count := by
    exact Nat.mul_pos (by norm_num [actualHalfScaleCoefficientCoverLoss]) hcount
  have hcap : forall center,
      center ∈ selectedTubes
        (activeTubeImage (terminalStrongTubeFamily C) Finset.univ)
        ((H.effectiveRadius 0 : NNReal) : Real) ->
      (activeNearCoefficientIndices (terminalStrongTubeFamily C) Finset.univ
        center ((H.effectiveRadius 0 : NNReal) : Real)).card ≤
          actualHalfScaleCoefficientCoverLoss * Q.count := by
    intro center _hcenter
    exact terminalStrong_activeNearCoefficientIndices_card_le_fullCap
      C Q hdelta hhalfParallel center
  apply selectedTubes_nonempty_of_pairwise_wz2
    (terminalStrongTubeFamily_pairwise_wz2_on_activeUniv C)
    hscale hmultiplicity
  · simpa only [Finset.card_univ] using hlarge
  · exact hcap

#print axioms activeTubeImage_card_of_pairwise_wz2
#print axioms card_activeTubeImage_filter_near_eq_of_pairwise_wz2
#print axioms concrete_nearCap_of_active_cap_of_pairwise_wz2
#print axioms active_card_le_multiplicity_mul_selectedTubes_card_of_pairwise_wz2
#print axioms selectedTubes_nonempty_of_pairwise_wz2
#print axioms actualCoverParentFiber_card_le_one_of_pairwise_wz2
#print axioms activeNearCoefficientIndices_card_le_coverLoss_mul_count_wz2
#print axioms terminalStrong_activeNearCoefficientIndices_card_le_fullCap
#print axioms terminalStrong_card_le_fullCap_mul_selectedTubes_card
#print axioms terminalStrong_selectedTubes_nonempty

end

end FamilyStickyHierarchyTerminalWZ2CoefficientBridgeV1
