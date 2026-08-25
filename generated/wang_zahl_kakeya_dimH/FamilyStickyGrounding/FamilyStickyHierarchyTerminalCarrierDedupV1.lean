import FamilyStickyGrounding.FamilyStickyRandomLocalExactCarrierDedupV1
import FamilyStickyGrounding.FamilyStickyHierarchyWidenedCrossParentCollisionCountingV1
import FamilyStickyGrounding.FamilyStickyRandomHundredContainerSelectionV1

set_option autoImplicit false

open Set
open scoped BigOperators NNReal

namespace FamilyStickyHierarchyTerminalCarrierDedupV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open FamilyStickyActualTubeTranslationV1
open FamilyStickyRandomFiniteCollisionRefinementV1
open FamilyStickyRandomFiniteCollisionRefinementV1.BoundedCollisionCode
open FamilyStickyRandomFiniteMaximalCellCodeV1
open FamilyStickyRandomHundredContainerSelectionV1
open FamilyStickyRandomModelTubeCollisionGridV1
open FamilyStickyHierarchyRandomMotionAdapterV1
open FamilyStickyHierarchyRandomMotionAdapterV1.HierarchyRandomMotionGeometry
open FamilyStickyHierarchyJointRandomMotionCertificateV1
open FamilyStickyHierarchyJointRandomMotionCertificateV1.HierarchyJointRandomMotionCertificate
open FamilyStickyHierarchyPathFirstDivergenceV1
open FamilyStickyHierarchyWidenedCrossParentCollisionCountingV1

noncomputable section
set_option linter.unusedSectionVars false
set_option maxHeartbeats 3000000

/-!
# Terminal exact-carrier representatives and strong finite refinement

The final hierarchy is occurrence-indexed: a path and an initial active fine
source may produce the same literal final carrier as another occurrence.
This module performs the missing finite terminal bookkeeping with every
multiplicity computed from the finite hierarchy data.

For one fixed occurrence, an equal-carrier partner is routed into exactly
one of two honest pieces.

* A partner with the same path is encoded by its initial fine source.  Its
  loss is the internally computed initial-source exact-carrier multiplicity.
* A partner with a different path is sent to its canonical first divergent
  layer, hence to the already constructed widened partner finset.

This gives a uniform terminal exact-carrier multiplicity, one representative
per occupied carrier, the resulting cardinal and weighted-load bounds, and
the inherited total-radius containment.  A second finite maximal selection
is pairwise `NoCommonHundredContainer`, a strong geometric separation.  The
paper-specific phrase `essentially distinct` still needs an explicit bridge
from that strong relation because the repository has no single canonical
predicate matching all cited papers.
-/

variable {depth : Nat} {nominalRadius : Nat -> NNReal}
  {Index : Nat -> Type*}
  [forall l, Fintype (Index l)] [forall l, DecidableEq (Index l)]
  {H : MultiscaleTubeHierarchy depth nominalRadius Index}
  {G : HierarchyRandomMotionGeometry H}
  (C : HierarchyJointRandomMotionCertificate H G)

/-- The literal final carrier used as the terminal collision code. -/
def terminalCarrier (a : C.FinalIndex) : Set Space :=
  (C.finalTube a).carrier

/-- Exact final-carrier fibre through one terminal occurrence. -/
abbrev TerminalExactCarrierFiber (a : C.FinalIndex) :=
  {b : C.FinalIndex // terminalCarrier C b = terminalCarrier C a}

/-- Initial active fine sources, retained by every final occurrence. -/
abbrev InitialActiveSource :=
  {i // i ∈ (H.family 0).refinement.refined}

/-- Equal-carrier fibre in the untranslated initial fine source. -/
abbrev InitialSourceExactCarrierFiber (i : InitialActiveSource (H := H)) :=
  {j : InitialActiveSource (H := H) //
    ((H.effectiveFamily 0).tubes j.1).carrier =
      ((H.effectiveFamily 0).tubes i.1).carrier}

/-- The actual maximum same-path source loss; it is computed from the finite
hierarchy source rather than supplied as a bound. -/
def initialSourceExactCarrierMultiplicity : Nat :=
  Finset.univ.sup fun i : InitialActiveSource (H := H) =>
    Fintype.card (InitialSourceExactCarrierFiber (H := H) i)

theorem initialSourceExactCarrierFiber_card_le_multiplicity
    (i : InitialActiveSource (H := H)) :
    Fintype.card (InitialSourceExactCarrierFiber (H := H) i) <=
      initialSourceExactCarrierMultiplicity (H := H) := by
  exact Finset.le_sup
    (s := (Finset.univ : Finset (InitialActiveSource (H := H))))
    (f := fun j =>
      Fintype.card (InitialSourceExactCarrierFiber (H := H) j))
    (Finset.mem_univ i)
/-- Transparent finite fallback for the same-path source term. -/
theorem initialSourceExactCarrierMultiplicity_le_card :
    initialSourceExactCarrierMultiplicity (H := H) <=
      (H.family 0).refinement.refined.card := by
  unfold initialSourceExactCarrierMultiplicity
  apply Finset.sup_le
  intro i _hi
  simpa only [Fintype.card_coe] using
    (Fintype.card_subtype_le
      (fun j : InitialActiveSource (H := H) =>
        ((H.effectiveFamily 0).tubes j.1).carrier =
          ((H.effectiveFamily 0).tubes i.1).carrier))


/-- A common translation can be cancelled from equality of two carrier
images. -/
theorem source_carrier_eq_of_common_final_translation
    (i j : InitialActiveSource (H := H)) (v : Space)
    (hcarrier :
      (translateTube ((H.effectiveFamily 0).tubes j.1) v).carrier =
        (translateTube ((H.effectiveFamily 0).tubes i.1) v).carrier) :
    ((H.effectiveFamily 0).tubes j.1).carrier =
      ((H.effectiveFamily 0).tubes i.1).carrier := by
  rw [translateTube_carrier, translateTube_carrier] at hcarrier
  exact (show Function.Injective (fun x : Space => v + x) by
    intro x y hxy
    exact add_left_cancel hxy).image_injective hcarrier

/-- Equal-carrier partners whose whole motion path agrees with the centre. -/
abbrev SamePathExactCarrierFiber (a : C.FinalIndex) :=
  {b : C.FinalIndex //
    b.1 = a.1 /\ terminalCarrier C b = terminalCarrier C a}

/-- A same-path terminal partner is encoded by its initial source. -/
def samePathExactCarrierFiberToInitialSource
    (a : C.FinalIndex) :
    SamePathExactCarrierFiber C a ->
      InitialSourceExactCarrierFiber (H := H) a.2 := by
  intro b
  refine ⟨b.1.2, ?_⟩
  apply source_carrier_eq_of_common_final_translation
    (H := H) a.2 b.1.2
    (C.output.toComposition.composedVector a.1)
  simpa [terminalCarrier, HierarchyJointRandomMotionCertificate.finalTube,
    b.2.1] using b.2.2

theorem samePathExactCarrierFiberToInitialSource_injective
    (a : C.FinalIndex) :
    Function.Injective (samePathExactCarrierFiberToInitialSource C a) := by
  intro b c hbc
  apply Subtype.ext
  apply Prod.ext
  · exact b.2.1.trans c.2.1.symm
  · exact congrArg Subtype.val hbc

theorem samePathExactCarrierFiber_card_le_sourceMultiplicity
    (a : C.FinalIndex) :
    Fintype.card (SamePathExactCarrierFiber C a) <=
      initialSourceExactCarrierMultiplicity (H := H) := by
  exact (Fintype.card_le_of_injective
      (samePathExactCarrierFiberToInitialSource C a)
      (samePathExactCarrierFiberToInitialSource_injective C a)).trans
    (initialSourceExactCarrierFiber_card_le_multiplicity (H := H) a.2)

/-- Target of the canonical exact-fibre routing: the same-path source piece,
or a widened partner at one first-divergence layer. -/
abbrev TerminalExactCarrierRouteTarget (a : C.FinalIndex) :=
  SamePathExactCarrierFiber C a ⊕
    Sigma fun k : Fin depth =>
      {b // b ∈ widenedCrossParentPartnersAtLayer C k a}

/-- Route every exact-carrier partner.  The output retains the partner
itself, so the route is injective. -/
def terminalExactCarrierRoute
    (a : C.FinalIndex) :
    TerminalExactCarrierFiber C a ->
      TerminalExactCarrierRouteTarget C a := by
  intro b
  by_cases hpath : b.1.1 = a.1
  · exact Sum.inl ⟨b.1, hpath, b.2⟩
  · have hcollision : DistinctPathFinalCarrierCollision C a b.1 :=
      ⟨Ne.symm hpath, b.2.symm⟩
    let k := hierarchyFirstDivergenceLayer C a.1 b.1.1 hcollision.1
    exact Sum.inr ⟨k, ⟨b.1,
      (mem_widenedCrossParentPartnersAtLayer C k a b.1).2
        (distinctPathFinalCarrierCollision_at_firstDivergence
          C a b.1 hcollision)⟩⟩

theorem terminalExactCarrierRoute_injective
    (a : C.FinalIndex) :
    Function.Injective (terminalExactCarrierRoute C a) := by
  let forget : TerminalExactCarrierRouteTarget C a -> C.FinalIndex :=
    Sum.elim (fun q => q.1) (fun q => q.2.1)
  have hforget (b : TerminalExactCarrierFiber C a) :
      forget (terminalExactCarrierRoute C a b) = b.1 := by
    by_cases hb : b.1.1 = a.1
    · simp [forget, terminalExactCarrierRoute, hb]
    · simp [forget, terminalExactCarrierRoute, hb]
  intro b c hbc
  apply Subtype.ext
  rw [← hforget b, ← hforget c, hbc]

/-- Uniform exact-carrier multiplicity at the terminal level.
The first term is precisely the same-path seam; the remaining terms are the
already routed first-divergence partner constants. -/
def terminalExactCarrierMultiplicityBound : Nat :=
  initialSourceExactCarrierMultiplicity (H := H) +
    ∑ k : Fin depth, widenedCrossParentPackingConstant C k

theorem terminalExactCarrierFiber_card_le
    (a : C.FinalIndex) :
    Fintype.card (TerminalExactCarrierFiber C a) <=
      terminalExactCarrierMultiplicityBound C := by
  calc
    Fintype.card (TerminalExactCarrierFiber C a) <=
        Fintype.card (TerminalExactCarrierRouteTarget C a) :=
      Fintype.card_le_of_injective (terminalExactCarrierRoute C a)
        (terminalExactCarrierRoute_injective C a)
    _ = Fintype.card (SamePathExactCarrierFiber C a) +
        ∑ k : Fin depth,
          (widenedCrossParentPartnersAtLayer C k a).card := by
      simp only [TerminalExactCarrierRouteTarget, Fintype.card_sum,
        Fintype.card_sigma, Fintype.card_coe]
    _ <= initialSourceExactCarrierMultiplicity (H := H) +
        ∑ k : Fin depth, widenedCrossParentPackingConstant C k := by
      apply Nat.add_le_add
      · exact samePathExactCarrierFiber_card_le_sourceMultiplicity C a
      · exact Finset.sum_le_sum fun k _hk =>
          widenedCrossParentPartnersAtLayer_card_le_packingConstant C k a
    _ = terminalExactCarrierMultiplicityBound C := rfl

/-- The finite bounded-collision code on all terminal occurrences. -/
def terminalBoundedCarrierCode :
    BoundedCollisionCode (occurrence := C.FinalIndex)
      (codeType := Set Space) where
  code := terminalCarrier C
  multiplicity := terminalExactCarrierMultiplicityBound C
  fiber_card_le := by
    intro K hK
    obtain ⟨a, _ha, rfl⟩ := Finset.mem_image.mp hK
    rw [← Fintype.card_subtype]
    exact terminalExactCarrierFiber_card_le C a

/-- Occupied literal terminal carriers. -/
abbrev TerminalCarrierCell := (terminalBoundedCarrierCode C).Cell

/-- Canonical chosen occurrence representing one occupied terminal carrier. -/
def terminalRepresentative (K : TerminalCarrierCell C) : C.FinalIndex :=
  (terminalBoundedCarrierCode C).representative K

@[simp] theorem terminalRepresentative_carrier
    (K : TerminalCarrierCell C) :
    terminalCarrier C (terminalRepresentative C K) = K.1 := by
  exact (terminalBoundedCarrierCode C).code_representative K

theorem terminalRepresentative_injective :
    Function.Injective (terminalRepresentative C) :=
  (terminalBoundedCarrierCode C).representative_injective

/-- The requested finite terminal representative family. -/
def terminalRepresentatives : Finset C.FinalIndex :=
  Finset.univ.image (terminalRepresentative C)

theorem terminalRepresentatives_card :
    (terminalRepresentatives C).card = Fintype.card (TerminalCarrierCell C) := by
  classical
  rw [terminalRepresentatives,
    Finset.card_image_of_injective _ (terminalRepresentative_injective C),
    Finset.card_univ]

/-- Every terminal occurrence has a representative with literally equal
carrier. -/
theorem exists_terminalRepresentative_carrier_eq
    (a : C.FinalIndex) :
    exists b, b ∈ terminalRepresentatives C ∧
      terminalCarrier C b = terminalCarrier C a := by
  obtain ⟨K, hK⟩ :=
    (terminalBoundedCarrierCode C).exists_cell_code_eq a
  refine ⟨terminalRepresentative C K, ?_, ?_⟩
  · exact Finset.mem_image.mpr ⟨K, Finset.mem_univ _, rfl⟩
  · exact (terminalRepresentative_carrier C K).trans hK.symm

/-- Distinct terminal representatives have distinct literal carriers. -/
theorem terminalRepresentatives_pairwise_carrier_ne :
    Set.Pairwise (terminalRepresentatives C : Set C.FinalIndex)
      fun a b => terminalCarrier C a ≠ terminalCarrier C b := by
  classical
  intro a ha b hb hab hcarrier
  obtain ⟨K, _hK, rfl⟩ := Finset.mem_image.mp ha
  obtain ⟨L, _hL, rfl⟩ := Finset.mem_image.mp hb
  apply hab
  have hKL : K = L := by
    apply Subtype.ext
    simpa only [terminalRepresentative_carrier] using hcarrier
  exact congrArg (terminalRepresentative C) hKL

/-- Total-radius containment is inherited by every chosen representative. -/
theorem terminalRepresentative_carrier_subset_totalRadius
    {a : C.FinalIndex} (_ha : a ∈ terminalRepresentatives C) :
    terminalCarrier C a ⊆
      Metric.cthickening
        ((∑ k : Fin depth, H.effectiveRadius (k.1 + 1) : NNReal) : Real)
        ((H.effectiveFamily 0).tubes a.2.1).carrier := by
  exact C.finalTube_carrier_subset_totalRadius a

/-- Exact terminal deduplication loses only the internally produced source
and widened-collision multiplicities. -/
theorem finalIndex_card_le_terminalMultiplicity_mul_representatives :
    Fintype.card C.FinalIndex <=
      terminalExactCarrierMultiplicityBound C *
        (terminalRepresentatives C).card := by
  rw [terminalRepresentatives_card C]
  exact (terminalBoundedCarrierCode C).card_le_multiplicity_mul_card_cell

/-- Weighted terminal load transfer for every carrier-dependent natural
weight.  Taking an indicator of `K ⊆ A` gives every finite containment-test
load as a direct specialization. -/
theorem terminal_weighted_load_le_mul_carrierCell_load
    (w : Set Space -> Nat) :
    (∑ a : C.FinalIndex, w (terminalCarrier C a)) <=
      terminalExactCarrierMultiplicityBound C *
        ∑ K : TerminalCarrierCell C, w K.1 := by
  classical
  let D := terminalBoundedCarrierCode C
  have hdecomp :
      (∑ a : C.FinalIndex, w (terminalCarrier C a)) =
        ∑ K ∈ Finset.univ.image D.code,
          ∑ a ∈ (Finset.univ : Finset C.FinalIndex).filter
            (fun a => D.code a = K), w (terminalCarrier C a) := by
    exact (Finset.sum_fiberwise_of_maps_to
      (s := (Finset.univ : Finset C.FinalIndex))
      (t := Finset.univ.image D.code) (g := D.code)
      (fun a _ha => Finset.mem_image.mpr ⟨a, Finset.mem_univ _, rfl⟩)
      (fun a => w (terminalCarrier C a))).symm
  rw [hdecomp]
  calc
    (∑ K ∈ Finset.univ.image D.code,
        ∑ a ∈ (Finset.univ : Finset C.FinalIndex).filter
          (fun a => D.code a = K), w (terminalCarrier C a)) <=
        ∑ K ∈ Finset.univ.image D.code,
          terminalExactCarrierMultiplicityBound C * w K := by
      apply Finset.sum_le_sum
      intro K hK
      have hweight :
          (∑ a ∈ (Finset.univ : Finset C.FinalIndex).filter
              (fun a => D.code a = K), w (terminalCarrier C a)) =
            ((Finset.univ : Finset C.FinalIndex).filter
              (fun a => D.code a = K)).card * w K := by
        calc
          (∑ a ∈ (Finset.univ : Finset C.FinalIndex).filter
              (fun a => D.code a = K), w (terminalCarrier C a)) =
              ∑ _a ∈ (Finset.univ : Finset C.FinalIndex).filter
                (fun a => D.code a = K), w K := by
            apply Finset.sum_congr rfl
            intro a ha
            have hcode := (Finset.mem_filter.mp ha).2
            simpa [D, terminalBoundedCarrierCode] using congrArg w hcode
          _ = ((Finset.univ : Finset C.FinalIndex).filter
              (fun a => D.code a = K)).card * w K := by simp
      rw [hweight]
      exact Nat.mul_le_mul_right (w K) (D.fiber_card_le K hK)
    _ = terminalExactCarrierMultiplicityBound C *
        ∑ K : TerminalCarrierCell C, w K.1 := by
      rw [← Finset.mul_sum]
      congr 1
      rw [← Finset.attach_eq_univ]
      exact (Finset.sum_attach (Finset.univ.image D.code) w).symm

/-- The representative finset realizes exactly the occupied-carrier weighted
load, not merely its cardinality. -/
theorem terminalRepresentatives_weighted_load
    (w : Set Space -> Nat) :
    (∑ a ∈ terminalRepresentatives C, w (terminalCarrier C a)) =
      ∑ K : TerminalCarrierCell C, w K.1 := by
  classical
  unfold terminalRepresentatives
  rw [Finset.sum_image]
  · simp only [terminalRepresentative_carrier]
  · intro K _hK L _hL hKL
    exact terminalRepresentative_injective C hKL

theorem terminal_weighted_load_le_mul_representative_load
    (w : Set Space -> Nat) :
    (∑ a : C.FinalIndex, w (terminalCarrier C a)) <=
      terminalExactCarrierMultiplicityBound C *
        ∑ a ∈ terminalRepresentatives C,
          w (terminalCarrier C a) := by
  rw [terminalRepresentatives_weighted_load C w]
  exact terminal_weighted_load_le_mul_carrierCell_load C w

/-! ## Strong finite terminal refinement -/

/-- Strong separation relation on exact-carrier cells, evaluated on their
chosen terminal representatives. -/
def terminalNoCommonHundredRelation
    (K L : TerminalCarrierCell C) : Prop :=
  NoCommonHundredContainer
    (C.finalTube (terminalRepresentative C K))
    (C.finalTube (terminalRepresentative C L))

theorem terminalNoCommonHundredRelation_symm :
    Std.Symm (terminalNoCommonHundredRelation C) := by
  constructor
  intro K L hKL
  exact noCommonHundredContainer_symm hKL

/-- Canonical maximal strongly separated selection of occupied terminal
carrier cells. -/
def terminalStrongSelection :
    MaximalSeparatedCells (terminalNoCommonHundredRelation C) :=
  Classical.choice
    (exists_maximalSeparatedCells (terminalNoCommonHundredRelation C)
      (terminalNoCommonHundredRelation_symm C))

/-- Final occurrence representatives after strong finite refinement. -/
def terminalStrongRepresentatives : Finset C.FinalIndex :=
  (terminalStrongSelection C).cells.image (terminalRepresentative C)

theorem terminalStrongRepresentatives_pairwise_noCommonHundredContainer :
    Set.Pairwise (terminalStrongRepresentatives C : Set C.FinalIndex)
      fun a b => NoCommonHundredContainer (C.finalTube a) (C.finalTube b) := by
  classical
  intro a ha b hb hab
  obtain ⟨K, hK, rfl⟩ := Finset.mem_image.mp ha
  obtain ⟨L, hL, rfl⟩ := Finset.mem_image.mp hb
  apply (terminalStrongSelection C).pairwise hK hL
  intro hKL
  apply hab
  exact congrArg (terminalRepresentative C) hKL

theorem commonHundredContainer_self
    {delta : NNReal} (T : Tube delta) :
    CommonHundredContainer T T :=
  ⟨T, carrier_subset_hundredTube T, carrier_subset_hundredTube T⟩

theorem commonHundredContainer_of_left_carrier_eq
    {delta : NNReal} {T U V : Tube delta}
    (hcarrier : T.carrier = U.carrier)
    (hcommon : CommonHundredContainer U V) :
    CommonHundredContainer T V := by
  obtain ⟨W, hU, hV⟩ := hcommon
  exact ⟨W, hcarrier.subset.trans hU, hV⟩

/-- Every original terminal occurrence is covered by a selected strong
representative through one literal common `100`-tube container. -/
theorem exists_strongRepresentative_commonHundredContainer
    (a : C.FinalIndex) :
    exists b, b ∈ terminalStrongRepresentatives C ∧
      CommonHundredContainer (C.finalTube a) (C.finalTube b) := by
  obtain ⟨K, hK⟩ :=
    (terminalBoundedCarrierCode C).exists_cell_code_eq a
  let L := (terminalStrongSelection C).code K
  have hLmem : terminalRepresentative C L.1 ∈
      terminalStrongRepresentatives C := by
    exact Finset.mem_image.mpr ⟨L.1, L.2, rfl⟩
  have hcommonRep : CommonHundredContainer
      (C.finalTube (terminalRepresentative C K))
      (C.finalTube (terminalRepresentative C L.1)) := by
    rcases (terminalStrongSelection C).eq_or_not_separated_code K with hEq | hnot
    · rw [hEq]
      exact commonHundredContainer_self _
    · exact Classical.not_not.mp hnot
  refine ⟨terminalRepresentative C L.1, hLmem, ?_⟩
  apply commonHundredContainer_of_left_carrier_eq
    (T := C.finalTube a)
    (U := C.finalTube (terminalRepresentative C K))
  · change terminalCarrier C a = terminalCarrier C (terminalRepresentative C K)
    exact hK.trans (terminalRepresentative_carrier C K).symm
  · exact hcommonRep

/-- The internally computed fibre multiplicity of the strong maximal code. -/
def terminalStrongMultiplicity : Nat :=
  Finset.univ.sup fun L : (terminalStrongSelection C).Cell =>
    ((Finset.univ : Finset (TerminalCarrierCell C)).filter fun K =>
      (terminalStrongSelection C).code K = L).card

theorem terminalStrong_codeFiber_card_le
    (L : (terminalStrongSelection C).Cell) :
    ((Finset.univ : Finset (TerminalCarrierCell C)).filter fun K =>
      (terminalStrongSelection C).code K = L).card <=
        terminalStrongMultiplicity C := by
  exact Finset.le_sup
    (s := (Finset.univ : Finset (terminalStrongSelection C).Cell))
    (f := fun M =>
      ((Finset.univ : Finset (TerminalCarrierCell C)).filter fun K =>
        (terminalStrongSelection C).code K = M).card)
    (Finset.mem_univ L)

theorem terminalStrongRepresentatives_card :
    (terminalStrongRepresentatives C).card =
      Fintype.card (terminalStrongSelection C).Cell := by
  classical
  rw [terminalStrongRepresentatives,
    Finset.card_image_of_injective _ (terminalRepresentative_injective C),
    Fintype.card_coe]

theorem terminalCarrierCell_card_le_strongMultiplicity_mul_representatives :
    Fintype.card (TerminalCarrierCell C) <=
      terminalStrongMultiplicity C *
        (terminalStrongRepresentatives C).card := by
  rw [terminalStrongRepresentatives_card C]
  exact (terminalStrongSelection C).card_le_of_fiber_bound
    (terminalStrongMultiplicity C) (terminalStrong_codeFiber_card_le C)

/-- Fully internal two-stage terminal card loss: exact-carrier collisions,
then the strong common-container maximal refinement. -/
theorem finalIndex_card_le_terminalStrongRepresentatives :
    Fintype.card C.FinalIndex <=
      terminalExactCarrierMultiplicityBound C *
        (terminalStrongMultiplicity C *
          (terminalStrongRepresentatives C).card) := by
  calc
    Fintype.card C.FinalIndex <=
        terminalExactCarrierMultiplicityBound C *
          Fintype.card (TerminalCarrierCell C) :=
      (terminalBoundedCarrierCode C).card_le_multiplicity_mul_card_cell
    _ <= terminalExactCarrierMultiplicityBound C *
        (terminalStrongMultiplicity C *
          (terminalStrongRepresentatives C).card) :=
      Nat.mul_le_mul_left _
        (terminalCarrierCell_card_le_strongMultiplicity_mul_representatives C)

/-- Minimal honest interface for a chosen paper-specific notion of essential
distinctness: strong common-container separation must imply that predicate. -/
def StrongSeparationImplies
    (essentiallyDistinct :
      Tube (H.effectiveRadius 0) -> Tube (H.effectiveRadius 0) -> Prop) : Prop :=
  forall T U, NoCommonHundredContainer T U -> essentiallyDistinct T U

theorem terminalStrongRepresentatives_pairwise_essentiallyDistinct
    (essentiallyDistinct :
      Tube (H.effectiveRadius 0) -> Tube (H.effectiveRadius 0) -> Prop)
    (hbridge : StrongSeparationImplies (H := H) essentiallyDistinct) :
    Set.Pairwise (terminalStrongRepresentatives C : Set C.FinalIndex)
      fun a b => essentiallyDistinct (C.finalTube a) (C.finalTube b) := by
  intro a ha b hb hab
  exact hbridge _ _
    (terminalStrongRepresentatives_pairwise_noCommonHundredContainer C
      ha hb hab)

/-!
## Sharp parent-local obstruction for the same-path term

At the finite interface, put one source in every parent and give every source
the same carrier code.  Each literal parent fibre has size one, while the
global same-path carrier fibre has all `P` sources.  Thus parent-local load
alone cannot remove the cross-parent source term without an additional
geometric relation between different parents.
-/

abbrev SingletonParentSource (P : Nat) := Fin P

def singletonSourceParent {P : Nat} :
    SingletonParentSource P -> Fin P := id

def collapsedSourceCarrier {P : Nat} :
    SingletonParentSource P -> Unit := fun _ => ()

theorem singletonSourceParent_fiber_card
    {P : Nat} (p : Fin P) :
    ((Finset.univ : Finset (SingletonParentSource P)).filter fun i =>
      singletonSourceParent i = p).card = 1 := by
  have heq :
      (Finset.univ : Finset (SingletonParentSource P)).filter
        (fun i => singletonSourceParent i = p) = {p} := by
    ext i
    constructor
    · intro hi
      apply Finset.mem_singleton.mpr
      simpa [singletonSourceParent] using (Finset.mem_filter.mp hi).2
    · intro hi
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, by
          simpa [singletonSourceParent] using Finset.mem_singleton.mp hi⟩
  rw [heq]
  simp

theorem collapsedSourceCarrier_fiber_card
    {P : Nat} (i : SingletonParentSource P) :
    ((Finset.univ : Finset (SingletonParentSource P)).filter fun j =>
      collapsedSourceCarrier j = collapsedSourceCarrier i).card = P := by
  simp [collapsedSourceCarrier]

#print axioms source_carrier_eq_of_common_final_translation
#print axioms initialSourceExactCarrierMultiplicity_le_card
#print axioms terminalExactCarrierFiber_card_le
#print axioms terminalRepresentatives_pairwise_carrier_ne
#print axioms terminalRepresentative_carrier_subset_totalRadius
#print axioms finalIndex_card_le_terminalMultiplicity_mul_representatives
#print axioms terminal_weighted_load_le_mul_representative_load
#print axioms terminalStrongRepresentatives_pairwise_noCommonHundredContainer
#print axioms exists_strongRepresentative_commonHundredContainer
#print axioms finalIndex_card_le_terminalStrongRepresentatives
#print axioms terminalStrongRepresentatives_pairwise_essentiallyDistinct
#print axioms singletonSourceParent_fiber_card
#print axioms collapsedSourceCarrier_fiber_card

end
end FamilyStickyHierarchyTerminalCarrierDedupV1
