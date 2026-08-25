import FamilyStickyGrounding.FamilyStickyHierarchyWidenedCrossParentSourceBoundV1
import FamilyStickyGrounding.FamilyStickyHierarchyTerminalSamePathWZEliminationV1

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

open Set
open scoped BigOperators NNReal

namespace FamilyStickyHierarchyWidenedCrossParentRigidityV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexFactoring
open FamilyStickyDependentMultiscaleAllParentJointRandomMotionV1
open FamilyStickyHierarchyRandomMotionAdapterV1
open FamilyStickyHierarchyRandomMotionAdapterV1.HierarchyRandomMotionGeometry
open FamilyStickyHierarchyJointRandomMotionCertificateV1
open FamilyStickyHierarchyJointRandomMotionCertificateV1.HierarchyJointRandomMotionCertificate
open FamilyStickyHierarchyWidenedCrossParentCollisionCountingV1
open FamilyStickyHierarchyWidenedCrossParentSourceBoundV1
open FamilyStickyHierarchyTerminalCarrierDedupV1
open FamilyStickyHierarchyTerminalSamePathWZEliminationV1
open FamilyStickyHierarchyLevelWZSeparationCoreV1
open FamilyStickyRandomWZCommonNeighbourPackingV1

noncomputable section
set_option linter.unusedSectionVars false

/-!
# A minimal rigidity certificate for widened cross-parent collisions

The widened first-divergence relation is not a literal same-parent `100 T`
relation, so the existing WZ packing theorem does not bound it.  The exact
extra datum needed by the finite argument is only an injective finite code
on every partner fibre.  `PartnerSeparationCode` records that datum without
accepting a cardinality inequality as a callback.

For the actual hierarchy, a single `CrossParentRigidityCertificate C K`
uses codes in `Fin K` at every layer.  It immediately bounds every computed
`widenedCrossParentPackingConstant` by the same `K`, and hence replaces the
terminal widened loss by `depth * K`.

The existing suffix/source encoding automatically constructs such a
certificate with the uniform supremum of the source bounds.  This producer
is useful but deliberately does not pretend that its bound is dimension
only: it still contains suffix repetitions and active hierarchy sources.

The final finite model proves the obstruction sharply.  One WZ-separated
source (so source separation is vacuous) may be selected `K + 2` times with
replacement.  Every other choice is a partner, producing `K + 1` partners;
there can be no injective code into `Fin K`.  Thus level WZ separation,
first-divergence prefix coherence, and the present with-replacement selector
cannot synthesize a fixed cross-parent constant without new rigidity.
-/

section FiniteCode

variable {occurrence : Type*} [Fintype occurrence] [DecidableEq occurrence]

/-- Minimal proof-carrying separation datum for a finite partner relation.
It supplies an actual injective code, not the desired cardinality bound. -/
structure PartnerSeparationCode
    (partners : occurrence -> Finset occurrence) (K : Nat) where
  encode : forall a, {b // b ∈ partners a} -> Fin K
  encode_injective : forall a, Function.Injective (encode a)

theorem partner_card_le_of_separationCode
    {partners : occurrence -> Finset occurrence} {K : Nat}
    (R : PartnerSeparationCode partners K) (a : occurrence) :
    (partners a).card <= K := by
  have hcard := Fintype.card_le_of_injective
    (R.encode a) (R.encode_injective a)
  simpa only [Fintype.card_coe, Fintype.card_fin] using hcard

end FiniteCode

variable {depth : Nat} {nominalRadius : Nat -> NNReal}
  {Index : Nat -> Type*}
  [forall l, Fintype (Index l)] [forall l, DecidableEq (Index l)]
  {H : MultiscaleTubeHierarchy depth nominalRadius Index}
  {G : HierarchyRandomMotionGeometry H}
  (C : HierarchyJointRandomMotionCertificate H G)

/-- One uniform finite code for the widened relation at every hierarchy
layer.  A dimension-only proof should construct this with fixed `K`. -/
structure CrossParentRigidityCertificate (K : Nat) where
  layerCode : forall k : Fin depth,
    PartnerSeparationCode
      (fun a => widenedCrossParentPartnersAtLayer C k a) K

theorem widenedCrossParentPartnersAtLayer_card_le_rigidity
    {K : Nat} (R : CrossParentRigidityCertificate C K)
    (k : Fin depth) (a : C.FinalIndex) :
    (widenedCrossParentPartnersAtLayer C k a).card <= K :=
  partner_card_le_of_separationCode (R.layerCode k) a

/-- The internally computed widened constant is capped by the certificate's
single layer-independent code size. -/
theorem widenedCrossParentPackingConstant_le_rigidity
    {K : Nat} (R : CrossParentRigidityCertificate C K)
    (k : Fin depth) :
    widenedCrossParentPackingConstant C k <= K := by
  unfold widenedCrossParentPackingConstant
  apply Finset.sup_le
  intro a _ha
  exact widenedCrossParentPartnersAtLayer_card_le_rigidity C R k a

theorem sum_widenedCrossParentPackingConstant_le_depth_mul
    {K : Nat} (R : CrossParentRigidityCertificate C K) :
    (∑ k : Fin depth, widenedCrossParentPackingConstant C k) <=
      depth * K := by
  calc
    (∑ k : Fin depth, widenedCrossParentPackingConstant C k) <=
        ∑ _k : Fin depth, K := by
      exact Finset.sum_le_sum fun k _hk =>
        widenedCrossParentPackingConstant_le_rigidity C R k
    _ = depth * K := by simp

/-- Terminal exact-carrier loss under a uniform cross-parent rigidity
constant, before using WZ to remove the same-path source term. -/
def terminalExactCarrierRigidityBound (K : Nat) : Nat :=
  initialSourceExactCarrierMultiplicity (H := H) + depth * K

theorem terminalExactCarrierMultiplicityBound_le_rigidityBound
    {K : Nat} (R : CrossParentRigidityCertificate C K) :
    terminalExactCarrierMultiplicityBound C <=
      terminalExactCarrierRigidityBound (H := H) K := by
  unfold terminalExactCarrierMultiplicityBound terminalExactCarrierRigidityBound
  exact Nat.add_le_add_left
    (sum_widenedCrossParentPackingConstant_le_depth_mul C R) _

/-- Fully fixed terminal loss once level-zero WZ packing removes the
same-path term as well. -/
def terminalExactCarrierWZRigidityBound (K : Nat) : Nat :=
  commonHundredNeighbourPackingConstant + depth * K

theorem terminalExactCarrierWZMultiplicityBound_le_rigidityBound
    {K : Nat} (R : CrossParentRigidityCertificate C K) :
    terminalExactCarrierWZMultiplicityBound C <=
      terminalExactCarrierWZRigidityBound (depth := depth) K := by
  unfold terminalExactCarrierWZMultiplicityBound
    terminalExactCarrierWZRigidityBound
  exact Nat.add_le_add_left
    (sum_widenedCrossParentPackingConstant_le_depth_mul C R) _

theorem terminalExactCarrierFiber_card_le_WZRigidityBound
    {K : Nat} (R : CrossParentRigidityCertificate C K)
    (hdelta : 0 < H.effectiveRadius 0)
    (W : HierarchyLevelWZSeparationData H)
    (a : C.FinalIndex) :
    Fintype.card (TerminalExactCarrierFiber C a) <=
      terminalExactCarrierWZRigidityBound (depth := depth) K := by
  exact (terminalExactCarrierFiber_card_le_WZMultiplicityBound
      C hdelta W a).trans
    (terminalExactCarrierWZMultiplicityBound_le_rigidityBound C R)

theorem finalIndex_card_le_WZRigidity_mul_representatives
    {K : Nat} (R : CrossParentRigidityCertificate C K)
    (hdelta : 0 < H.effectiveRadius 0)
    (W : HierarchyLevelWZSeparationData H) :
    Fintype.card C.FinalIndex <=
      terminalExactCarrierWZRigidityBound (depth := depth) K *
        (terminalRepresentatives C).card := by
  exact (finalIndex_card_le_WZMultiplicity_mul_representatives
      C hdelta W).trans
    (Nat.mul_le_mul_right _
      (terminalExactCarrierWZMultiplicityBound_le_rigidityBound C R))

theorem terminal_weighted_load_le_WZRigidity_mul_representative_load
    {K : Nat} (R : CrossParentRigidityCertificate C K)
    (hdelta : 0 < H.effectiveRadius 0)
    (W : HierarchyLevelWZSeparationData H)
    (w : Set Space -> Nat) :
    (∑ a : C.FinalIndex, w (terminalCarrier C a)) <=
      terminalExactCarrierWZRigidityBound (depth := depth) K *
        ∑ a ∈ terminalRepresentatives C, w (terminalCarrier C a) := by
  exact (terminal_weighted_load_le_WZMultiplicity_mul_representative_load
      C hdelta W w).trans
    (Nat.mul_le_mul_right _
      (terminalExactCarrierWZMultiplicityBound_le_rigidityBound C R))

theorem finalIndex_card_le_WZRigidity_mul_terminalStrongRepresentatives
    {K : Nat} (R : CrossParentRigidityCertificate C K)
    (hdelta : 0 < H.effectiveRadius 0)
    (W : HierarchyLevelWZSeparationData H) :
    Fintype.card C.FinalIndex <=
      terminalExactCarrierWZRigidityBound (depth := depth) K *
        (terminalStrongMultiplicity C *
          (terminalStrongRepresentatives C).card) := by
  exact (finalIndex_card_le_WZMultiplicity_mul_terminalStrongRepresentatives
      C hdelta W).trans
    (Nat.mul_le_mul_right _
      (terminalExactCarrierWZMultiplicityBound_le_rigidityBound C R))

/-! ## Automatic hierarchy-source producer -/

/-- Uniformize the already proved layerwise suffix/source bounds. -/
def widenedCrossParentUniformSourceBound : Nat :=
  Finset.univ.sup fun k : Fin depth => widenedCrossParentSourceBound C k

theorem widenedCrossParentSourceBound_le_uniformSourceBound
    (k : Fin depth) :
    widenedCrossParentSourceBound C k <=
      widenedCrossParentUniformSourceBound C := by
  exact Finset.le_sup
    (s := (Finset.univ : Finset (Fin depth)))
    (f := fun i => widenedCrossParentSourceBound C i)
    (Finset.mem_univ k)

theorem suffixSourceCode_card_le_sourceBound (k : Fin depth) :
    Fintype.card
        (SuffixChoice C k ×
          {i // i ∈ (H.family 0).refinement.refined}) <=
      widenedCrossParentSourceBound C k := by
  rw [Fintype.card_prod, suffixChoice_card C, Fintype.card_coe]
  exact Nat.mul_le_mul_left _
    (initialFine_card_le_parentCount_mul_branchingProduct (H := H) k)

/-- Promote the existing injective suffix/source code to the one uniform
finite target. -/
def sourcePartnerSeparationCode (k : Fin depth) :
    PartnerSeparationCode
      (fun a => widenedCrossParentPartnersAtLayer C k a)
      (widenedCrossParentUniformSourceBound C) where
  encode := fun a b =>
    Fin.castLE
      ((suffixSourceCode_card_le_sourceBound C k).trans
        (widenedCrossParentSourceBound_le_uniformSourceBound C k))
      ((Fintype.equivFin
        (SuffixChoice C k ×
          {i // i ∈ (H.family 0).refinement.refined}))
        (widenedPartnerSuffixSourceCode C k a b))
  encode_injective := by
    intro a b c hbc
    apply widenedPartnerSuffixSourceCode_injective C k a
    apply (Fintype.equivFin
      (SuffixChoice C k ×
        {i // i ∈ (H.family 0).refinement.refined})).injective
    exact Fin.castLE_injective
      ((suffixSourceCode_card_le_sourceBound C k).trans
        (widenedCrossParentSourceBound_le_uniformSourceBound C k)) hbc

/-- Everything currently present in the hierarchy produces a rigidity
certificate, but only at the honest hierarchy-dependent source bound. -/
def sourceCrossParentRigidityCertificate :
    CrossParentRigidityCertificate C
      (widenedCrossParentUniformSourceBound C) where
  layerCode := sourcePartnerSeparationCode C

theorem widenedCrossParentPackingConstant_le_uniformSourceBound
    (k : Fin depth) :
    widenedCrossParentPackingConstant C k <=
      widenedCrossParentUniformSourceBound C :=
  widenedCrossParentPackingConstant_le_rigidity C
    (sourceCrossParentRigidityCertificate C) k

/-! ## Global rigidity and a truly fixed terminal loss

A layerwise `Fin K` code controls every `Kwide`, but summing the separate
maxima still pays `depth * K`.  The terminal routing actually uses one sigma
fibre at a fixed centre.  The following stronger, still minimal certificate
codes that whole sigma fibre at once.  It is exactly what makes the terminal
cross-parent loss a single fixed `K` rather than a depth sum. -/

/-- All widened first-divergence partners of one centre, retaining the
canonical divergent layer. -/
abbrev AllWidenedCrossParentPartners (a : C.FinalIndex) :=
  Sigma fun k : Fin depth =>
    {b // b ∈ widenedCrossParentPartnersAtLayer C k a}

/-- Minimal global rigidity datum: one injective `Fin K` code on the entire
first-divergence sigma fibre of each terminal occurrence. -/
structure GlobalCrossParentRigidityCertificate (K : Nat) where
  encode : forall a : C.FinalIndex,
    AllWidenedCrossParentPartners C a -> Fin K
  encode_injective : forall a, Function.Injective (encode a)

theorem allWidenedCrossParentPartners_card_le_globalRigidity
    {K : Nat} (R : GlobalCrossParentRigidityCertificate C K)
    (a : C.FinalIndex) :
    Fintype.card (AllWidenedCrossParentPartners C a) <= K := by
  have hcard := Fintype.card_le_of_injective
    (R.encode a) (R.encode_injective a)
  simpa only [Fintype.card_fin] using hcard

/-- A global code automatically caps each individual layer's computed
`Kwide` by the same fixed constant. -/
theorem widenedCrossParentPackingConstant_le_globalRigidity
    {K : Nat} (R : GlobalCrossParentRigidityCertificate C K)
    (k : Fin depth) :
    widenedCrossParentPackingConstant C k <= K := by
  unfold widenedCrossParentPackingConstant
  apply Finset.sup_le
  intro a _ha
  have hinj : Function.Injective
      (fun b : {b // b ∈ widenedCrossParentPartnersAtLayer C k a} =>
        R.encode a ⟨k, b⟩) := by
    intro b c hbc
    have hsigma : (⟨k, b⟩ : AllWidenedCrossParentPartners C a) =
        ⟨k, c⟩ := R.encode_injective a hbc
    cases hsigma
    rfl
  have hcard := Fintype.card_le_of_injective
    (fun b : {b // b ∈ widenedCrossParentPartnersAtLayer C k a} =>
      R.encode a ⟨k, b⟩) hinj
  simpa only [Fintype.card_coe, Fintype.card_fin] using hcard

/-- Fixed terminal exact-carrier loss: one WZ same-path constant and one
global cross-parent rigidity constant, with no source, repetition, parent,
or depth factor. -/
def terminalExactCarrierWZGlobalRigidityBound (K : Nat) : Nat :=
  commonHundredNeighbourPackingConstant + K

theorem terminalExactCarrierFiber_card_le_WZGlobalRigidityBound
    {K : Nat} (R : GlobalCrossParentRigidityCertificate C K)
    (hdelta : 0 < H.effectiveRadius 0)
    (W : HierarchyLevelWZSeparationData H)
    (a : C.FinalIndex) :
    Fintype.card (TerminalExactCarrierFiber C a) <=
      terminalExactCarrierWZGlobalRigidityBound K := by
  calc
    Fintype.card (TerminalExactCarrierFiber C a) <=
        Fintype.card (TerminalExactCarrierRouteTarget C a) :=
      Fintype.card_le_of_injective (terminalExactCarrierRoute C a)
        (terminalExactCarrierRoute_injective C a)
    _ = Fintype.card (SamePathExactCarrierFiber C a) +
        Fintype.card (AllWidenedCrossParentPartners C a) := by
      simp only [TerminalExactCarrierRouteTarget,
        AllWidenedCrossParentPartners, Fintype.card_sum]
    _ <= commonHundredNeighbourPackingConstant + K := by
      apply Nat.add_le_add
      · exact (samePathExactCarrierFiber_card_le_sourceMultiplicity C a).trans
          (initialSourceExactCarrierMultiplicity_le_WZConstant
            (H := H) hdelta W)
      · exact allWidenedCrossParentPartners_card_le_globalRigidity C R a
    _ = terminalExactCarrierWZGlobalRigidityBound K := rfl

/-- Bounded terminal carrier code with the genuinely fixed global-rigidity
multiplicity. -/
def terminalWZGlobalRigidityBoundedCarrierCode
    {K : Nat} (R : GlobalCrossParentRigidityCertificate C K)
    (hdelta : 0 < H.effectiveRadius 0)
    (W : HierarchyLevelWZSeparationData H) :
    FamilyStickyRandomFiniteCollisionRefinementV1.BoundedCollisionCode
      (occurrence := C.FinalIndex) (codeType := Set Space) where
  code := terminalCarrier C
  multiplicity := terminalExactCarrierWZGlobalRigidityBound K
  fiber_card_le := by
    intro L hL
    obtain ⟨a, _ha, rfl⟩ := Finset.mem_image.mp hL
    rw [← Fintype.card_subtype]
    exact terminalExactCarrierFiber_card_le_WZGlobalRigidityBound
      C R hdelta W a


/-! ### Automatic global source producer -/

/-- Dependent sum of the existing suffix/source codes over all layers. -/
abbrev GlobalSuffixSourceCode :=
  Sigma fun k : Fin depth =>
    SuffixChoice C k × {i // i ∈ (H.family 0).refinement.refined}

/-- Honest total source bound for the whole first-divergence sigma fibre. -/
def widenedCrossParentTotalSourceBound : Nat :=
  ∑ k : Fin depth, widenedCrossParentSourceBound C k

theorem globalSuffixSourceCode_card_le_totalSourceBound :
    Fintype.card (GlobalSuffixSourceCode C) <=
      widenedCrossParentTotalSourceBound C := by
  rw [Fintype.card_sigma]
  exact Finset.sum_le_sum fun k _hk =>
    suffixSourceCode_card_le_sourceBound C k

/-- Encode a global widened partner by its divergent layer and the existing
suffix/source code at that layer. -/
def allWidenedPartnerSuffixSourceCode (a : C.FinalIndex) :
    AllWidenedCrossParentPartners C a -> GlobalSuffixSourceCode C :=
  fun q => ⟨q.1, widenedPartnerSuffixSourceCode C q.1 a q.2⟩

theorem allWidenedPartnerSuffixSourceCode_injective
    (a : C.FinalIndex) :
    Function.Injective (allWidenedPartnerSuffixSourceCode C a) := by
  intro q r hqr
  rcases q with ⟨k, b⟩
  rcases r with ⟨l, c⟩
  have hkl : k = l := congrArg Sigma.fst hqr
  subst l
  apply Sigma.mk.inj_iff.mpr
  refine ⟨rfl, ?_⟩
  apply heq_of_eq
  apply widenedPartnerSuffixSourceCode_injective C k a
  exact eq_of_heq (Sigma.mk.inj_iff.mp hqr).2

/-- Current hierarchy data automatically supply a global certificate only
with the hierarchy-dependent sum of suffix/source bounds. -/
def sourceGlobalCrossParentRigidityCertificate :
    GlobalCrossParentRigidityCertificate C
      (widenedCrossParentTotalSourceBound C) where
  encode := fun a q =>
    Fin.castLE (globalSuffixSourceCode_card_le_totalSourceBound C)
      ((Fintype.equivFin (GlobalSuffixSourceCode C))
        (allWidenedPartnerSuffixSourceCode C a q))
  encode_injective := by
    intro a q r hqr
    apply allWidenedPartnerSuffixSourceCode_injective C a
    apply (Fintype.equivFin (GlobalSuffixSourceCode C)).injective
    exact Fin.castLE_injective
      (globalSuffixSourceCode_card_le_totalSourceBound C) hqr

theorem terminalExactCarrierFiber_card_le_automaticTotalSourceBound
    (hdelta : 0 < H.effectiveRadius 0)
    (W : HierarchyLevelWZSeparationData H)
    (a : C.FinalIndex) :
    Fintype.card (TerminalExactCarrierFiber C a) <=
      commonHundredNeighbourPackingConstant +
        widenedCrossParentTotalSourceBound C := by
  exact terminalExactCarrierFiber_card_le_WZGlobalRigidityBound C
    (sourceGlobalCrossParentRigidityCertificate C) hdelta W a

#print axioms allWidenedCrossParentPartners_card_le_globalRigidity
#print axioms widenedCrossParentPackingConstant_le_globalRigidity
#print axioms terminalExactCarrierFiber_card_le_WZGlobalRigidityBound
#print axioms allWidenedPartnerSuffixSourceCode_injective
#print axioms sourceGlobalCrossParentRigidityCertificate
#print axioms terminalExactCarrierFiber_card_le_automaticTotalSourceBound


/-! ## Sharp finite obstruction to an automatic fixed constant -/

/-- Repeated choices of one source; source-level WZ separation only sees the
singleton `Unit` source. -/
abbrev RepeatedSingletonOccurrence (J : Nat) := Fin J

def repeatedSingletonSource {J : Nat} :
    RepeatedSingletonOccurrence J -> Unit := fun _ => ()

/-- Every occurrence with a different repetition coordinate is a partner. -/
def repeatedSingletonPartners {J : Nat}
    (a : RepeatedSingletonOccurrence J) :
    Finset (RepeatedSingletonOccurrence J) :=
  Finset.univ.erase a

theorem repeatedSingletonPartners_card {J : Nat}
    (a : RepeatedSingletonOccurrence J) :
    (repeatedSingletonPartners a).card = J - 1 := by
  simp [repeatedSingletonPartners]

/-- All `J` repetitions collapse to the one source code. -/
theorem repeatedSingletonSource_fiber_card {J : Nat} :
    ((Finset.univ : Finset (RepeatedSingletonOccurrence J)).filter fun a =>
      repeatedSingletonSource a = ()).card = J := by
  simp [repeatedSingletonSource]

/-- Any pairwise source separation predicate is vacuous on the singleton
source, including the actual WZ endpoint separation predicate. -/
theorem repeatedSingleton_sourcePairwise_vacuous
    (R : Unit -> Unit -> Prop) :
    Set.Pairwise ({()} : Set Unit) R := by
  simp [Set.Pairwise]

/-- `K + 2` repetitions have exactly `K + 1` partners through every
occurrence, so no injective `Fin K` partner code can exist. -/
theorem no_fixedCode_for_repeatedSingleton (K : Nat) :
    ¬ Nonempty
      (PartnerSeparationCode
        (fun a : RepeatedSingletonOccurrence (K + 2) =>
          repeatedSingletonPartners a) K) := by
  intro hcode
  obtain ⟨R⟩ := hcode
  let a : RepeatedSingletonOccurrence (K + 2) := ⟨0, by omega⟩
  have hle := partner_card_le_of_separationCode R a
  rw [repeatedSingletonPartners_card] at hle
  omega

#print axioms partner_card_le_of_separationCode
#print axioms widenedCrossParentPackingConstant_le_rigidity
#print axioms sum_widenedCrossParentPackingConstant_le_depth_mul
#print axioms terminalExactCarrierMultiplicityBound_le_rigidityBound
#print axioms terminalExactCarrierWZMultiplicityBound_le_rigidityBound
#print axioms terminalExactCarrierFiber_card_le_WZRigidityBound
#print axioms finalIndex_card_le_WZRigidity_mul_representatives
#print axioms terminal_weighted_load_le_WZRigidity_mul_representative_load
#print axioms finalIndex_card_le_WZRigidity_mul_terminalStrongRepresentatives
#print axioms sourceCrossParentRigidityCertificate
#print axioms widenedCrossParentPackingConstant_le_uniformSourceBound
#print axioms repeatedSingletonPartners_card
#print axioms repeatedSingletonSource_fiber_card
#print axioms repeatedSingleton_sourcePairwise_vacuous
#print axioms no_fixedCode_for_repeatedSingleton

end
end FamilyStickyHierarchyWidenedCrossParentRigidityV1
