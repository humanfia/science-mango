import FamilyStickyGrounding.FamilyStickyScaleChainHierarchySiblingRigidityV1
import FamilyStickyGrounding.FamilyStickyHierarchyEndpointPrefixBridgeV1
import Submission.Kakeya.ConvexFactoring.TubeVolumeBounds

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 3000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace FamilyStickyScaleChainHierarchySiblingRigidityProducerV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyAtEveryScaleCoreV1.StickyScaleCover
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainCoherentIntervalProducerV1
open FamilyStickyScaleChainArbitraryRadiusInterpolationV1
open FamilyStickyScaleChainArbitraryRadiusBoundsV1
open FamilyStickyScaleChainParentNormalizerReverseProducerV1
open FamilyStickyScaleChainHierarchySiblingRigidityV1

noncomputable section

/-!
# Producing hierarchy sibling rigidity from structural identifications

The endpoint-to-effective bridge preserves bodies but does not mention parent
maps.  This file adds the strictly stronger square needed by the reverse
normalizer: active lower and upper cover parents embed into the two sides of
one honest hierarchy step, and the cross-scale parent map commutes with the
hierarchy parent map.  That square automatically produces the sibling code
consumed by `HierarchySiblingRigidityCertificate`.

The remaining weighted issue is separated from geometry.  A proof-carrying
occurrence code embeds every lower sibling fiber into `Fin cardLoss` copies of
the distinguished lower fiber.  It yields the cardinal comparison, while the
actual tube-volume sandwich upgrades it to mass comparison with loss
`16 * cardLoss`.  Thus neither the sibling-cardinality inequality nor the
mass inequality is accepted as a callback.

The final models record both genuine obstructions.  Body-preserving endpoint
embeddings do not force parent-map commutation, and a parent with exactly two
children may have descendant fibers of sizes `1` and `N`; hence one-step
branching alone cannot produce a uniform occurrence code.
-/

variable {depth : Nat} {nominalRadius : Nat -> NNReal}
  {Index : Nat -> Type*}
  [forall l, Fintype (Index l)] [forall l, DecidableEq (Index l)]
  (H : MultiscaleTubeHierarchy depth nominalRadius Index)
  (C : CoherentStickyMultiscaleCover (H.effectiveFamily 0))
  (S : FiniteScaleSequence (H.effectiveRadius 0) depth)

/-! ## Active parent indices and the cross-scale parent -/

abbrev LowerActiveParent
    (m : Fin depth) (rho : NNReal)
    (hTauRho : S.tau m <= rho) (hRhoTheta : rho <= S.theta m) :=
  {q // q ∈
    (lowerScaleCover C S m rho hTauRho hRhoTheta).activeCoarse}

abbrev UpperActiveParent (m : Fin depth) :=
  {p // p ∈ (upperEndpointCover C S m).activeCoarse}

/-- The actual cross-scale parent of an active lower parent, retaining its
proof of upper activity. -/
def crossParentOfLower
    (m : Fin depth) (rho : NNReal)
    (hTauRho : S.tau m <= rho) (hRhoTheta : rho <= S.theta m)
    (q : LowerActiveParent H C S m rho hTauRho hRhoTheta) :
    UpperActiveParent H C S m := by
  let I := rhoToUpperCover C S m rho hTauRho hRhoTheta
  refine ⟨I.parent q.1, ?_⟩
  change I.parent q.1 ∈ I.activeCoarse
  apply I.parent_mem q.1
  exact q.2

@[simp]
theorem crossParentOfLower_val
    (m : Fin depth) (rho : NNReal)
    (hTauRho : S.tau m <= rho) (hRhoTheta : rho <= S.theta m)
    (q : LowerActiveParent H C S m rho hTauRho hRhoTheta) :
    (crossParentOfLower H C S m rho hTauRho hRhoTheta q).1 =
      (rhoToUpperCover C S m rho hTauRho hRhoTheta).parent q.1 :=
  rfl

/-- Regard a literal sibling as an active lower parent. -/
def lowerActiveOfSibling
    (m : Fin depth) (rho : NNReal)
    (hTauRho : S.tau m <= rho) (hRhoTheta : rho <= S.theta m)
    (k : Fin (lowerScaleCover C S m rho hTauRho hRhoTheta).coarseCard)
    (q : LowerSibling H C S m rho hTauRho hRhoTheta k) :
    LowerActiveParent H C S m rho hTauRho hRhoTheta := by
  refine ⟨q.1, ?_⟩
  exact ((rhoToUpperCover C S m rho hTauRho hRhoTheta).mem_fiber
    q.1 ((rhoToUpperCover C S m rho hTauRho hRhoTheta).parent k)).1 q.2 |>.1

theorem lowerActiveOfSibling_injective
    (m : Fin depth) (rho : NNReal)
    (hTauRho : S.tau m <= rho) (hRhoTheta : rho <= S.theta m)
    (k : Fin (lowerScaleCover C S m rho hTauRho hRhoTheta).coarseCard) :
    Function.Injective
      (lowerActiveOfSibling H C S m rho hTauRho hRhoTheta k) := by
  intro q q' hqq'
  apply Subtype.ext
  exact congrArg
    (fun x : LowerActiveParent H C S m rho hTauRho hRhoTheta => x.1) hqq'

/-! ## The parent-preserving hierarchy square -/

/-- Structural identification of every actual cross-scale cover with one
honest hierarchy step.  Unlike the endpoint body bridge, this explicitly
retains both active parent maps and their commutative square. -/
structure ParentSquareIdentification where
  lowerEmbedding : forall (m : Fin depth) (rho : NNReal)
      (hTauRho : S.tau m <= rho) (hRhoTheta : rho <= S.theta m),
    LowerActiveParent H C S m rho hTauRho hRhoTheta ↪
      {i // i ∈ (H.step m.1 m.2).combinatorics.index.fine}
  upperEmbedding : forall (m : Fin depth) (rho : NNReal)
      (_hTauRho : S.tau m <= rho) (_hRhoTheta : rho <= S.theta m),
    UpperActiveParent H C S m ↪
      {p // p ∈ (H.step m.1 m.2).combinatorics.index.coarse}
  parent_commutes : forall (m : Fin depth) (rho : NNReal)
      (hTauRho : S.tau m <= rho) (hRhoTheta : rho <= S.theta m)
      (q : LowerActiveParent H C S m rho hTauRho hRhoTheta),
    (H.step m.1 m.2).parentIndex
        ((lowerEmbedding m rho hTauRho hRhoTheta q).1) =
      (upperEmbedding m rho hTauRho hRhoTheta
        (crossParentOfLower H C S m rho hTauRho hRhoTheta q)).1

namespace ParentSquareIdentification

variable {H C S}
  (P : ParentSquareIdentification H C S)

/-- A sibling's lower active parent has the same cross parent as the
distinguished lower parent. -/
theorem crossParent_lowerActiveOfSibling_eq
    (m : Fin depth) (rho : NNReal)
    (hTauRho : S.tau m <= rho) (hRhoTheta : rho <= S.theta m)
    (k : Fin (lowerScaleCover C S m rho hTauRho hRhoTheta).coarseCard)
    (hk : k ∈
      (lowerScaleCover C S m rho hTauRho hRhoTheta).activeCoarse)
    (q : LowerSibling H C S m rho hTauRho hRhoTheta k) :
    crossParentOfLower H C S m rho hTauRho hRhoTheta
        (lowerActiveOfSibling H C S m rho hTauRho hRhoTheta k q) =
      crossParentOfLower H C S m rho hTauRho hRhoTheta ⟨k, hk⟩ := by
  apply Subtype.ext
  exact ((rhoToUpperCover C S m rho hTauRho hRhoTheta).mem_fiber
    q.1 ((rhoToUpperCover C S m rho hTauRho hRhoTheta).parent k)).1 q.2 |>.2

/-- The commuting parent square automatically supplies the genuine hierarchy
fiber code for every literal sibling set. -/
def toHierarchySiblingCode
    (m : Fin depth) (rho : NNReal)
    (hTauRho : S.tau m <= rho) (hRhoTheta : rho <= S.theta m)
    (k : Fin (lowerScaleCover C S m rho hTauRho hRhoTheta).coarseCard)
    (hk : k ∈
      (lowerScaleCover C S m rho hTauRho hRhoTheta).activeCoarse) :
    HierarchySiblingCode H C S m rho hTauRho hRhoTheta k hk where
  hierarchyParent :=
    (P.upperEmbedding m rho hTauRho hRhoTheta
      (crossParentOfLower H C S m rho hTauRho hRhoTheta ⟨k, hk⟩)).1
  hierarchyParent_mem :=
    (P.upperEmbedding m rho hTauRho hRhoTheta
      (crossParentOfLower H C S m rho hTauRho hRhoTheta ⟨k, hk⟩)).2
  siblingEmbedding :=
    { toFun := fun q => ⟨
        (P.lowerEmbedding m rho hTauRho hRhoTheta
          (lowerActiveOfSibling H C S m rho hTauRho hRhoTheta k q)).1,
        by
          refine ((H.step m.1 m.2).combinatorics.index.mem_fiber _ _).2
            ⟨(P.lowerEmbedding m rho hTauRho hRhoTheta
                (lowerActiveOfSibling H C S m rho hTauRho hRhoTheta k q)).2,
              ?_⟩
          change (H.step m.1 m.2).parentIndex
              ((P.lowerEmbedding m rho hTauRho hRhoTheta
                (lowerActiveOfSibling H C S m rho
                  hTauRho hRhoTheta k q)).1) = _
          rw [P.parent_commutes m rho hTauRho hRhoTheta]
          exact congrArg Subtype.val
            (congrArg (P.upperEmbedding m rho hTauRho hRhoTheta)
              (ParentSquareIdentification.crossParent_lowerActiveOfSibling_eq
                (H := H) (C := C) (S := S)
                m rho hTauRho hRhoTheta k hk q))⟩
      inj' := by
        intro q q' hqq'
        apply lowerActiveOfSibling_injective H C S
          m rho hTauRho hRhoTheta k
        apply (P.lowerEmbedding m rho hTauRho hRhoTheta).injective
        apply Subtype.ext
        have hval := congrArg (fun x => x.1) hqq'
        exact hval }

end ParentSquareIdentification

/-! ## The computed uniform hierarchy branching bound -/

/-- Maximum of the literal certified branching factors over the finite
hierarchy. -/
def hierarchyBranchingBound : Nat :=
  Finset.univ.sup fun m : Fin depth =>
    (H.step m.1 m.2).combinatorics.branchingFactor

theorem branchingFactor_le_hierarchyBranchingBound (m : Fin depth) :
    (H.step m.1 m.2).combinatorics.branchingFactor <=
      hierarchyBranchingBound H := by
  exact Finset.le_sup
    (s := (Finset.univ : Finset (Fin depth)))
    (f := fun k => (H.step k.1 k.2).combinatorics.branchingFactor)
    (Finset.mem_univ m)

/-! ## Occurrence-level sibling uniformity and mass production -/

/-- A structural, finite occurrence code for sibling lower fibers.  The
target retains the actual distinguished fiber and a separate finite loss
coordinate. -/
structure SiblingOccurrenceCode (cardLoss : Nat) where
  fiberEmbedding : forall (m : Fin depth) (rho : NNReal)
      (hTauRho : S.tau m <= rho) (hRhoTheta : rho <= S.theta m)
      (k : Fin (lowerScaleCover C S m rho hTauRho hRhoTheta).coarseCard)
      (_hk : k ∈
        (lowerScaleCover C S m rho hTauRho hRhoTheta).activeCoarse)
      (q : LowerSibling H C S m rho hTauRho hRhoTheta k),
    {i // i ∈
      (lowerScaleCover C S m rho hTauRho hRhoTheta).fiber q.1} ↪
      Fin cardLoss ×
        {i // i ∈
          (lowerScaleCover C S m rho hTauRho hRhoTheta).fiber k}

namespace SiblingOccurrenceCode

variable {H C S} {cardLoss : Nat}

theorem siblingFiber_card_le
    (O : SiblingOccurrenceCode H C S cardLoss)
    (m : Fin depth) (rho : NNReal)
    (hTauRho : S.tau m <= rho) (hRhoTheta : rho <= S.theta m)
    (k : Fin (lowerScaleCover C S m rho hTauRho hRhoTheta).coarseCard)
    (hk : k ∈
      (lowerScaleCover C S m rho hTauRho hRhoTheta).activeCoarse)
    (q : LowerSibling H C S m rho hTauRho hRhoTheta k) :
    ((lowerScaleCover C S m rho hTauRho hRhoTheta).fiber q.1).card <=
      cardLoss *
        ((lowerScaleCover C S m rho hTauRho hRhoTheta).fiber k).card := by
  have hcard := Fintype.card_le_of_injective
    (O.fiberEmbedding m rho hTauRho hRhoTheta k hk q)
    (O.fiberEmbedding m rho hTauRho hRhoTheta k hk q).injective
  simpa only [Fintype.card_coe, Fintype.card_prod, Fintype.card_fin] using hcard

end SiblingOccurrenceCode

variable {delta rho : NNReal} {iota : Type*}
  [Fintype iota] [DecidableEq iota]
  {fine : UniformTubeFamily delta iota}

/-- Uniform upper tube-volume bound summed over one literal cover fiber. -/
theorem fiberFamilyVolume_le_card_mul_eight_sq
    (hhalf : delta <= (2 : NNReal)⁻¹)
    {r : NNReal} (T : StickyScaleCover fine r)
    (k : Fin T.coarseCard) :
    familyVolume (T.fiberFamily k) <=
      ((T.fiber k).card : ENNReal) * (8 * (delta : ENNReal) ^ 2) := by
  rw [familyVolume_fiberFamily_eq_sum T k]
  calc
    (∑ i ∈ T.fiber k, volume (fine.bodyFamily i : Set Space)) <=
        ∑ _i ∈ T.fiber k, 8 * (delta : ENNReal) ^ 2 := by
      exact Finset.sum_le_sum fun i _hi =>
        (fine.tubes i).volume_le_eight_mul_sq_of_le_half hhalf
    _ = ((T.fiber k).card : ENNReal) *
          (8 * (delta : ENNReal) ^ 2) := by simp

/-- Uniform lower tube-volume bound summed over one literal cover fiber. -/
theorem card_mul_half_sq_le_fiberFamilyVolume
    (hhalf : delta <= (2 : NNReal)⁻¹)
    {r : NNReal} (T : StickyScaleCover fine r)
    (k : Fin T.coarseCard) :
    ((T.fiber k).card : ENNReal) * ((delta : ENNReal) ^ 2 / 2) <=
      familyVolume (T.fiberFamily k) := by
  rw [familyVolume_fiberFamily_eq_sum T k]
  calc
    ((T.fiber k).card : ENNReal) * ((delta : ENNReal) ^ 2 / 2) =
        ∑ _i ∈ T.fiber k, (delta : ENNReal) ^ 2 / 2 := by simp
    _ <= ∑ i ∈ T.fiber k, volume (fine.bodyFamily i : Set Space) := by
      exact Finset.sum_le_sum fun i _hi =>
        (fine.tubes i).half_sq_le_volume_of_le_half hhalf

variable {H C S} {cardLoss : Nat}

/-- The occurrence code plus the actual tube-volume sandwich produces the
uniform sibling-mass comparison, with no mass inequality stored as data. -/
theorem siblingMass_le_sixteen_mul_cardLoss
    (hhalf : H.effectiveRadius 0 <= (2 : NNReal)⁻¹)
    (O : SiblingOccurrenceCode H C S cardLoss)
    (m : Fin depth) (rho : NNReal)
    (hTauRho : S.tau m <= rho) (hRhoTheta : rho <= S.theta m)
    (k : Fin (lowerScaleCover C S m rho hTauRho hRhoTheta).coarseCard)
    (hk : k ∈
      (lowerScaleCover C S m rho hTauRho hRhoTheta).activeCoarse)
    (q : LowerSibling H C S m rho hTauRho hRhoTheta k) :
    familyVolume
        ((lowerScaleCover C S m rho hTauRho hRhoTheta).fiberFamily q.1) <=
      (16 * (cardLoss : ENNReal)) * familyVolume
        ((lowerScaleCover C S m rho hTauRho hRhoTheta).fiberFamily k) := by
  let L := lowerScaleCover C S m rho hTauRho hRhoTheta
  have hcardNat := SiblingOccurrenceCode.siblingFiber_card_le O
    m rho hTauRho hRhoTheta k hk q
  have hcard : ((L.fiber q.1).card : ENNReal) <=
      (cardLoss : ENNReal) * ((L.fiber k).card : ENNReal) := by
    exact_mod_cast hcardNat
  calc
    familyVolume (L.fiberFamily q.1) <=
        ((L.fiber q.1).card : ENNReal) *
          (8 * (H.effectiveRadius 0 : ENNReal) ^ 2) :=
      fiberFamilyVolume_le_card_mul_eight_sq hhalf L q.1
    _ <= ((cardLoss : ENNReal) * ((L.fiber k).card : ENNReal)) *
          (8 * (H.effectiveRadius 0 : ENNReal) ^ 2) := by gcongr
    _ = (16 * (cardLoss : ENNReal)) *
          (((L.fiber k).card : ENNReal) *
            ((H.effectiveRadius 0 : ENNReal) ^ 2 / 2)) := by
      have h16 : (16 : ENNReal) * (2 : ENNReal)⁻¹ = 8 := by
        rw [show (16 : ENNReal) = 8 * 2 by norm_num,
          mul_assoc, ENNReal.mul_inv_cancel] <;> norm_num
      rw [ENNReal.div_eq_inv_mul]
      rw [← h16]
      ac_rfl
    _ <= (16 * (cardLoss : ENNReal)) *
          familyVolume (L.fiberFamily k) := by
      gcongr
      exact card_mul_half_sq_le_fiberFamilyVolume hhalf L k

/-! ## Full producer and arbitrary-radius endpoint -/

/-- The two structural identifications produce the complete reverse sibling
rigidity certificate with computed hierarchy branching bound. -/
def hierarchySiblingRigidityCertificate
    (hhalf : H.effectiveRadius 0 <= (2 : NNReal)⁻¹)
    (P : ParentSquareIdentification H C S)
    (O : SiblingOccurrenceCode H C S cardLoss) :
    HierarchySiblingRigidityCertificate H C S
      (hierarchyBranchingBound H) (16 * (cardLoss : ENNReal)) where
  branchingFactor_le := branchingFactor_le_hierarchyBranchingBound H
  code := P.toHierarchySiblingCode
  siblingMass_le := by
    intro m rho hTauRho hRhoTheta k hk q
    exact siblingMass_le_sixteen_mul_cardLoss hhalf O
      m rho hTauRho hRhoTheta k hk q

/-- The actual reverse-parent loss is now bounded entirely by the computed
hierarchy branching maximum and the occurrence-code loss. -/
theorem actualReverseParentNormalizerLoss_le_of_parentSquare_occurrenceCode
    (hdelta : 0 < H.effectiveRadius 0)
    (hhalf : H.effectiveRadius 0 <= (2 : NNReal)⁻¹)
    (P : ParentSquareIdentification H C S)
    (O : SiblingOccurrenceCode H C S cardLoss)
    (hcompat : forall (m : Fin depth) (rho : NNReal)
      (hTauRho : S.tau m <= rho) (hRhoTheta : rho <= S.theta m)
      (i : Index 0),
      i ∈ (lowerScaleCover C S m rho hTauRho hRhoTheta).activeFine ->
      (upperEndpointCover C S m).parent i =
        (rhoToUpperCover C S m rho hTauRho hRhoTheta).parent
          ((lowerScaleCover C S m rho hTauRho hRhoTheta).parent i)) :
    actualReverseParentNormalizerLoss C S <=
      hierarchyReverseNormalizerBound (hierarchyBranchingBound H)
        (16 * (cardLoss : ENNReal)) := by
  exact actualReverseParentNormalizerLoss_le_hierarchyBound hdelta
    (hierarchySiblingRigidityCertificate hhalf P O) hcompat

/-- Fixed-loss arbitrary-radius Sticky endpoint produced from the two
structural identifications. -/
theorem isStickyAtEveryScale_of_parentSquare_occurrenceCode
    {epsilon : Real}
    (hdepth : 0 < depth) (hdelta : 0 < H.effectiveRadius 0)
    (hhalf : H.effectiveRadius 0 <= (2 : NNReal)⁻¹)
    {massLoss bodyLoss katzTaoLoss frostmanError katzTaoError : ENNReal}
    (D : LargeIntervalLocalGeometry C S epsilon
      massLoss bodyLoss katzTaoLoss)
    (B : DiscreteAllLargeStickyBounds C S epsilon
      frostmanError katzTaoError)
    (P : ParentSquareIdentification H C S)
    (O : SiblingOccurrenceCode H C S cardLoss) :
    C.base.IsStickyAtEveryScale
      (hierarchyReverseNormalizerBound (hierarchyBranchingBound H)
          (16 * (cardLoss : ENNReal)) * frostmanError)
      (katzTaoLoss * katzTaoError) := by
  exact isStickyAtEveryScale_of_hierarchySiblingRigidity
    hdepth hdelta D B (hierarchySiblingRigidityCertificate hhalf P O)

/-! ## Sharp finite obstructions to automatic production -/

/-- Two indexed families can agree body-for-body while their parent maps do
not commute.  This is the finite logical gap in the existing endpoint body
embedding. -/
theorem body_preservation_does_not_force_parent_commutation :
    let body : Fin 2 -> Unit := fun _ => ()
    let coverParent : Fin 2 -> Fin 2 := fun i => i
    let hierarchyParent : Fin 2 -> Fin 2 := fun i => 1 - i
    (forall i, body i = body i) ∧
      ¬ (forall i, coverParent i = hierarchyParent i) := by
  dsimp
  constructor
  · intro i
    rfl
  · intro h
    have hzero := h (0 : Fin 2)
    norm_num at hzero

/-- A fixed loss `K` cannot encode a heavy sibling with `K + 1` occurrences
into `K` copies of a singleton light sibling.  Both may still be the two
children of one hierarchy parent. -/
theorem no_fixed_occurrence_code_for_two_siblings (K : Nat) :
    ¬ Nonempty (Fin (K + 1) ↪ Fin K × Fin 1) := by
  intro h
  obtain ⟨E⟩ := h
  have hcard := Fintype.card_le_of_injective E E.injective
  simp only [Fintype.card_fin, Fintype.card_prod] at hcard
  omega

#print axioms crossParentOfLower
#print axioms lowerActiveOfSibling_injective
#print axioms ParentSquareIdentification.crossParent_lowerActiveOfSibling_eq
#print axioms ParentSquareIdentification.toHierarchySiblingCode
#print axioms branchingFactor_le_hierarchyBranchingBound
#print axioms SiblingOccurrenceCode.siblingFiber_card_le
#print axioms fiberFamilyVolume_le_card_mul_eight_sq
#print axioms card_mul_half_sq_le_fiberFamilyVolume
#print axioms siblingMass_le_sixteen_mul_cardLoss
#print axioms hierarchySiblingRigidityCertificate
#print axioms actualReverseParentNormalizerLoss_le_of_parentSquare_occurrenceCode
#print axioms isStickyAtEveryScale_of_parentSquare_occurrenceCode
#print axioms body_preservation_does_not_force_parent_commutation
#print axioms no_fixed_occurrence_code_for_two_siblings

end
end FamilyStickyScaleChainHierarchySiblingRigidityProducerV1
