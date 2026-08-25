import FamilyStickyGrounding.FamilyStickyScaleChainParentNormalizerReverseProducerV1
import Submission.Kakeya.ConvexFactoring.MultiscaleTubeHierarchy

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 3000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace FamilyStickyScaleChainHierarchySiblingRigidityV1

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

noncomputable section

/-!
# Capping the reverse normalizer by hierarchy sibling rigidity

For an intermediate parent `k`, the upper endpoint fiber is the disjoint
union of the lower fibers whose cross-scale parent equals the parent of `k`.
Consequently two, and only two, quantitative inputs are needed:

* the actual lower siblings embed into one genuine hierarchy-step fiber, so
  their number is bounded by that step's certified branching factor; and
* every sibling lower fiber has mass at most `siblingMassLoss` times the mass
  of the distinguished lower fiber.

The first input is combinatorial hierarchy branching.  The second is the
weighted sibling rigidity which branching alone cannot see.  Their product
caps the literal `actualReverseParentNormalizerLoss`, and hence produces the
arbitrary-radius Sticky endpoint with a fixed reverse-normalizer constant.

The closing two-sibling model is sharp: even with exactly two siblings, their
weights can be `1` and `N`, so no weighted reverse bound follows from the
branching cardinality without the relative-mass field.
-/

variable {depth : Nat} {nominalRadius : Nat -> NNReal}
  {Index : Nat -> Type*}
  [forall l, Fintype (Index l)] [forall l, DecidableEq (Index l)]
  (H : MultiscaleTubeHierarchy depth nominalRadius Index)
  (C : CoherentStickyMultiscaleCover (H.effectiveFamily 0))
  (S : FiniteScaleSequence (H.effectiveRadius 0) depth)

/-! ## The literal lower-sibling fiber -/

/-- Active intermediate parents which merge into the same upper endpoint
parent as `k`. -/
abbrev LowerSibling
    (m : Fin depth) (rho : NNReal)
    (hTauRho : S.tau m <= rho) (hRhoTheta : rho <= S.theta m)
    (k : Fin (lowerScaleCover C S m rho hTauRho hRhoTheta).coarseCard) :=
  {q // q ∈
    (rhoToUpperCover C S m rho hTauRho hRhoTheta).fiber
      ((rhoToUpperCover C S m rho hTauRho hRhoTheta).parent k)}

/-- A proof-carrying identification of one actual sibling set with part of a
genuine hierarchy-step fiber.  This is the parent-preserving seam which is
not present in a bare coherent multiscale cover. -/
structure HierarchySiblingCode
    (m : Fin depth) (rho : NNReal)
    (hTauRho : S.tau m <= rho) (hRhoTheta : rho <= S.theta m)
    (k : Fin (lowerScaleCover C S m rho hTauRho hRhoTheta).coarseCard)
    (hk : k ∈
      (lowerScaleCover C S m rho hTauRho hRhoTheta).activeCoarse) where
  hierarchyParent : Index (m.1 + 1)
  hierarchyParent_mem : hierarchyParent ∈
    ((H.step m.1 m.2).combinatorics.index.coarse)
  siblingEmbedding :
    LowerSibling H C S m rho hTauRho hRhoTheta k ↪
      {i // i ∈ (H.step m.1 m.2).combinatorics.index.fiber hierarchyParent}

/-- The minimal structural input which turns hierarchy branching into a
weighted reverse-normalizer bound.  `siblingMass_le` compares actual finite
fiber masses; it is not a concentration or final-endpoint callback. -/
structure HierarchySiblingRigidityCertificate
    (branchingBound : Nat) (siblingMassLoss : ENNReal) where
  branchingFactor_le : forall m : Fin depth,
    (H.step m.1 m.2).combinatorics.branchingFactor <= branchingBound
  code : forall (m : Fin depth) (rho : NNReal)
      (hTauRho : S.tau m <= rho) (hRhoTheta : rho <= S.theta m)
      (k : Fin (lowerScaleCover C S m rho hTauRho hRhoTheta).coarseCard)
      (hk : k ∈
        (lowerScaleCover C S m rho hTauRho hRhoTheta).activeCoarse),
    HierarchySiblingCode H C S m rho hTauRho hRhoTheta k hk
  siblingMass_le : forall (m : Fin depth) (rho : NNReal)
      (hTauRho : S.tau m <= rho) (hRhoTheta : rho <= S.theta m)
      (k : Fin (lowerScaleCover C S m rho hTauRho hRhoTheta).coarseCard)
      (_hk : k ∈
        (lowerScaleCover C S m rho hTauRho hRhoTheta).activeCoarse)
      (q : LowerSibling H C S m rho hTauRho hRhoTheta k),
    familyVolume
        ((lowerScaleCover C S m rho hTauRho hRhoTheta).fiberFamily q.1) <=
      siblingMassLoss * familyVolume
        ((lowerScaleCover C S m rho hTauRho hRhoTheta).fiberFamily k)

/-- The fixed reverse-normalizer constant supplied by branching and relative
sibling mass rigidity. -/
def hierarchyReverseNormalizerBound
    (branchingBound : Nat) (siblingMassLoss : ENNReal) : ENNReal :=
  (branchingBound : ENNReal) * siblingMassLoss

namespace HierarchySiblingRigidityCertificate

variable {H C S}
  {branchingBound : Nat} {siblingMassLoss : ENNReal}

/-- The actual sibling set is bounded first by the literal hierarchy fiber. -/
theorem lowerSibling_card_le_hierarchyBranchingFactor
    (R : HierarchySiblingRigidityCertificate H C S
      branchingBound siblingMassLoss)
    (m : Fin depth) (rho : NNReal)
    (hTauRho : S.tau m <= rho) (hRhoTheta : rho <= S.theta m)
    (k : Fin (lowerScaleCover C S m rho hTauRho hRhoTheta).coarseCard)
    (hk : k ∈
      (lowerScaleCover C S m rho hTauRho hRhoTheta).activeCoarse) :
    ((rhoToUpperCover C S m rho hTauRho hRhoTheta).fiber
      ((rhoToUpperCover C S m rho hTauRho hRhoTheta).parent k)).card <=
        (H.step m.1 m.2).combinatorics.branchingFactor := by
  let E := HierarchySiblingRigidityCertificate.code R m rho hTauRho hRhoTheta k hk
  have hinj : Fintype.card
      (LowerSibling H C S m rho hTauRho hRhoTheta k) <=
      Fintype.card
        {i // i ∈ (H.step m.1 m.2).combinatorics.index.fiber
          E.hierarchyParent} :=
    Fintype.card_le_of_injective E.siblingEmbedding
      E.siblingEmbedding.injective
  have hfiber :=
    (H.step m.1 m.2).combinatorics.fiber_card_le_loss_mul_branching
      E.hierarchyParent E.hierarchyParent_mem
  have hfiber' : Fintype.card
      {i // i ∈ (H.step m.1 m.2).combinatorics.index.fiber
        E.hierarchyParent} <=
      (H.step m.1 m.2).combinatorics.branchingFactor := by
    simpa only [Fintype.card_coe,
      TubePartitionCombinatorics.branchingFactor] using hfiber
  simpa only [Fintype.card_coe] using hinj.trans hfiber'

/-- Uniformizing the certified hierarchy branching factors gives the desired
fixed sibling-cardinality bound. -/
theorem lowerSibling_card_le_branchingBound
    (R : HierarchySiblingRigidityCertificate H C S
      branchingBound siblingMassLoss)
    (m : Fin depth) (rho : NNReal)
    (hTauRho : S.tau m <= rho) (hRhoTheta : rho <= S.theta m)
    (k : Fin (lowerScaleCover C S m rho hTauRho hRhoTheta).coarseCard)
    (hk : k ∈
      (lowerScaleCover C S m rho hTauRho hRhoTheta).activeCoarse) :
    ((rhoToUpperCover C S m rho hTauRho hRhoTheta).fiber
      ((rhoToUpperCover C S m rho hTauRho hRhoTheta).parent k)).card <=
        branchingBound :=
  (lowerSibling_card_le_hierarchyBranchingFactor R
    m rho hTauRho hRhoTheta k hk).trans (HierarchySiblingRigidityCertificate.branchingFactor_le R m)

end HierarchySiblingRigidityCertificate

/-! ## Automatic fiber partition and weighted bound -/

variable {delta rho : NNReal} {iota : Type*}
  [Fintype iota] [DecidableEq iota]
  {fine : UniformTubeFamily delta iota}

/-- `familyVolume` of a literal cover fiber is its sum over the underlying
finite fiber. -/
theorem familyVolume_fiberFamily_eq_sum
    {r : NNReal} (T : StickyScaleCover fine r)
    (k : Fin T.coarseCard) :
    familyVolume (T.fiberFamily k) =
      ∑ i ∈ T.fiber k, volume (fine.bodyFamily i : Set Space) := by
  unfold familyVolume StickyScaleCover.fiberFamily
  rw [← Finset.attach_eq_univ]
  exact Finset.sum_attach (T.fiber k)
    (fun i => volume (fine.bodyFamily i : Set Space))

variable {H C S}

/-- Parent compatibility partitions the full upper fiber exactly into the
actual lower sibling fibers. -/
theorem upperFiberFamilyVolume_eq_sum_lowerSiblings
    (m : Fin depth) (rho : NNReal)
    (hTauRho : S.tau m <= rho) (hRhoTheta : rho <= S.theta m)
    (k : Fin (lowerScaleCover C S m rho hTauRho hRhoTheta).coarseCard)
    (hcompat : forall i,
      i ∈ (lowerScaleCover C S m rho hTauRho hRhoTheta).activeFine ->
      (upperEndpointCover C S m).parent i =
        (rhoToUpperCover C S m rho hTauRho hRhoTheta).parent
          ((lowerScaleCover C S m rho hTauRho hRhoTheta).parent i)) :
    familyVolume
        ((upperEndpointCover C S m).fiberFamily
          ((rhoToUpperCover C S m rho hTauRho hRhoTheta).parent k)) =
      ∑ q ∈
          (rhoToUpperCover C S m rho hTauRho hRhoTheta).fiber
            ((rhoToUpperCover C S m rho hTauRho hRhoTheta).parent k),
        familyVolume
          ((lowerScaleCover C S m rho hTauRho hRhoTheta).fiberFamily q) := by
  classical
  let L := lowerScaleCover C S m rho hTauRho hRhoTheta
  let U := upperEndpointCover C S m
  let I := rhoToUpperCover C S m rho hTauRho hRhoTheta
  let p : Fin U.coarseCard := I.parent k
  let P : IndexFactorization (Index 0) (Fin L.coarseCard) := {
    fine := U.fiber p
    coarse := I.fiber p
    parent := L.parent
    parent_mem := by
      intro i hi
      have hiU : i ∈ U.activeFine ∧ U.parent i = p :=
        (U.mem_fiber i p).1 hi
      have hiL : i ∈ L.activeFine := by
        rw [L.activeFine_eq_refined, ← U.activeFine_eq_refined]
        exact hiU.1
      exact (I.mem_fiber (L.parent i) p).2 ⟨
        L.parent_mem i hiL, by
          rw [← hcompat i hiL]
          exact hiU.2⟩
  }
  have hPfiber (q : Fin L.coarseCard) (hq : q ∈ I.fiber p) :
      P.fiber q = L.fiber q := by
    ext i
    constructor
    · intro hi
      have hiP := (P.mem_fiber i q).1 hi
      have hiU := (U.mem_fiber i p).1 hiP.1
      have hiL : i ∈ L.activeFine := by
        rw [L.activeFine_eq_refined, ← U.activeFine_eq_refined]
        exact hiU.1
      exact (L.mem_fiber i q).2 ⟨hiL, hiP.2⟩
    · intro hi
      have hiL := (L.mem_fiber i q).1 hi
      have hqI := (I.mem_fiber q p).1 hq
      have hiUactive : i ∈ U.activeFine := by
        rw [U.activeFine_eq_refined, ← L.activeFine_eq_refined]
        exact hiL.1
      have hiUparent : U.parent i = p := by
        rw [hcompat i hiL.1, hiL.2]
        exact hqI.2
      exact (P.mem_fiber i q).2
        ⟨(U.mem_fiber i p).2 ⟨hiUactive, hiUparent⟩, hiL.2⟩
  rw [familyVolume_fiberFamily_eq_sum U p]
  calc
    (∑ i ∈ U.fiber p, volume ((H.effectiveFamily 0).bodyFamily i : Set Space)) =
        ∑ q ∈ I.fiber p,
          ∑ i ∈ P.fiber q, volume ((H.effectiveFamily 0).bodyFamily i : Set Space) :=
      P.sum_fiberwise (fun i => volume ((H.effectiveFamily 0).bodyFamily i : Set Space))
    _ = ∑ q ∈ I.fiber p,
          ∑ i ∈ L.fiber q, volume ((H.effectiveFamily 0).bodyFamily i : Set Space) := by
      apply Finset.sum_congr rfl
      intro q hq
      rw [hPfiber q hq]
    _ = ∑ q ∈ I.fiber p, familyVolume (L.fiberFamily q) := by
      apply Finset.sum_congr rfl
      intro q _hq
      rw [familyVolume_fiberFamily_eq_sum L q]

variable {branchingBound : Nat} {siblingMassLoss : ENNReal}

/-- Hierarchy branching times relative sibling mass controls every literal
upper fiber. -/
theorem upperFiberMass_le_hierarchyReverseNormalizerBound
    (R : HierarchySiblingRigidityCertificate H C S
      branchingBound siblingMassLoss)
    (m : Fin depth) (rho : NNReal)
    (hTauRho : S.tau m <= rho) (hRhoTheta : rho <= S.theta m)
    (k : Fin (lowerScaleCover C S m rho hTauRho hRhoTheta).coarseCard)
    (hk : k ∈
      (lowerScaleCover C S m rho hTauRho hRhoTheta).activeCoarse)
    (hcompat : forall i,
      i ∈ (lowerScaleCover C S m rho hTauRho hRhoTheta).activeFine ->
      (upperEndpointCover C S m).parent i =
        (rhoToUpperCover C S m rho hTauRho hRhoTheta).parent
          ((lowerScaleCover C S m rho hTauRho hRhoTheta).parent i)) :
    familyVolume
        ((upperEndpointCover C S m).fiberFamily
          ((rhoToUpperCover C S m rho hTauRho hRhoTheta).parent k)) <=
      hierarchyReverseNormalizerBound branchingBound siblingMassLoss *
        familyVolume
          ((lowerScaleCover C S m rho hTauRho hRhoTheta).fiberFamily k) := by
  let I := rhoToUpperCover C S m rho hTauRho hRhoTheta
  let M := familyVolume
    ((lowerScaleCover C S m rho hTauRho hRhoTheta).fiberFamily k)
  rw [upperFiberFamilyVolume_eq_sum_lowerSiblings
    (H := H) (C := C) (S := S) m rho hTauRho hRhoTheta k hcompat]
  calc
    (∑ q ∈ I.fiber (I.parent k),
        familyVolume
          ((lowerScaleCover C S m rho hTauRho hRhoTheta).fiberFamily q)) <=
        ∑ _q ∈ I.fiber (I.parent k), siblingMassLoss * M := by
      exact Finset.sum_le_sum fun q hq =>
        HierarchySiblingRigidityCertificate.siblingMass_le R m rho hTauRho hRhoTheta k hk ⟨q, hq⟩
    _ = ((I.fiber (I.parent k)).card : ENNReal) *
          (siblingMassLoss * M) := by simp
    _ <= (branchingBound : ENNReal) * (siblingMassLoss * M) := by
      gcongr
      exact_mod_cast HierarchySiblingRigidityCertificate.lowerSibling_card_le_branchingBound R
        m rho hTauRho hRhoTheta k hk
    _ = hierarchyReverseNormalizerBound branchingBound siblingMassLoss * M := by
      unfold hierarchyReverseNormalizerBound
      ac_rfl

/-- The structural hierarchy certificate produces the weighted-growth input
used by arbitrary-radius interpolation. -/
theorem toLargeIntervalReverseFiberMassGrowth
    {epsilon : Real}
    (R : HierarchySiblingRigidityCertificate H C S
      branchingBound siblingMassLoss)
    (hcompat : forall (m : Fin depth) (rho : NNReal)
      (hTauRho : S.tau m <= rho) (hRhoTheta : rho <= S.theta m)
      (i : Index 0),
      i ∈ (lowerScaleCover C S m rho hTauRho hRhoTheta).activeFine ->
      (upperEndpointCover C S m).parent i =
        (rhoToUpperCover C S m rho hTauRho hRhoTheta).parent
          ((lowerScaleCover C S m rho hTauRho hRhoTheta).parent i)) :
    LargeIntervalReverseFiberMassGrowth C S epsilon
      (hierarchyReverseNormalizerBound branchingBound siblingMassLoss) where
  mass_le := by
    intro m rho hTauRho hRhoTheta _hlarge k hk
    exact upperFiberMass_le_hierarchyReverseNormalizerBound
      R m rho hTauRho hRhoTheta k hk
        (hcompat m rho hTauRho hRhoTheta)

/-- The actual iSup loss is capped by the hierarchy branching/rigidity
product.  Positivity is used only to divide by the distinguished lower-fiber
mass. -/
theorem actualReverseParentNormalizerLoss_le_hierarchyBound
    (hdelta : 0 < H.effectiveRadius 0)
    (R : HierarchySiblingRigidityCertificate H C S
      branchingBound siblingMassLoss)
    (hcompat : forall (m : Fin depth) (rho : NNReal)
      (hTauRho : S.tau m <= rho) (hRhoTheta : rho <= S.theta m)
      (i : Index 0),
      i ∈ (lowerScaleCover C S m rho hTauRho hRhoTheta).activeFine ->
      (upperEndpointCover C S m).parent i =
        (rhoToUpperCover C S m rho hTauRho hRhoTheta).parent
          ((lowerScaleCover C S m rho hTauRho hRhoTheta).parent i)) :
    actualReverseParentNormalizerLoss C S <=
      hierarchyReverseNormalizerBound branchingBound siblingMassLoss := by
  unfold actualReverseParentNormalizerLoss
  apply iSup_le
  intro m
  apply iSup_le
  intro rho
  apply iSup_le
  intro hTauRho
  apply iSup_le
  intro hRhoTheta
  apply iSup_le
  intro k
  by_cases hk : k ∈
      (lowerScaleCover C S m rho hTauRho hRhoTheta).activeCoarse
  · rw [actualReverseFiberMassRatio, dif_pos hk]
    apply (ENNReal.div_le_iff
      (lowerFiberFamilyVolume_pos C S hdelta m rho
        hTauRho hRhoTheta k hk).ne'
      (familyVolume_ne_top
        ((lowerScaleCover C S m rho hTauRho hRhoTheta).fiberFamily k))).2
    exact upperFiberMass_le_hierarchyReverseNormalizerBound
      R m rho hTauRho hRhoTheta k hk
        (hcompat m rho hTauRho hRhoTheta)
  · simp [actualReverseFiberMassRatio, hk]

/-- End-to-end arbitrary-radius Sticky with the actual reverse loss replaced
by the fixed hierarchy branching/rigidity product. -/
theorem isStickyAtEveryScale_of_hierarchySiblingRigidity
    {epsilon : Real}
    (hdepth : 0 < depth) (hdelta : 0 < H.effectiveRadius 0)
    {massLoss bodyLoss katzTaoLoss frostmanError katzTaoError : ENNReal}
    (D : LargeIntervalLocalGeometry C S epsilon
      massLoss bodyLoss katzTaoLoss)
    (B : DiscreteAllLargeStickyBounds C S epsilon
      frostmanError katzTaoError)
    (R : HierarchySiblingRigidityCertificate H C S
      branchingBound siblingMassLoss) :
    C.base.IsStickyAtEveryScale
      (hierarchyReverseNormalizerBound branchingBound siblingMassLoss *
        frostmanError)
      (katzTaoLoss * katzTaoError) := by
  have hactual := isStickyAtEveryScale_of_actualReverseParentNormalizerLoss
    C S hdepth hdelta D B
  apply hactual.mono
  · gcongr
    exact actualReverseParentNormalizerLoss_le_hierarchyBound
      hdelta R D.parent_compatible
  · exact le_rfl

/-! ## Sharp obstruction: branching does not compare sibling masses -/

/-- Two fixed siblings with weights `1` and `N`. -/
def twoSiblingWeight (N : Nat) (q : Fin 2) : Nat :=
  if q = 0 then 1 else N

@[simp]
theorem twoSiblingWeight_zero (N : Nat) :
    twoSiblingWeight N 0 = 1 := by
  simp [twoSiblingWeight]

theorem twoSiblingWeight_sum (N : Nat) :
    (∑ q : Fin 2, twoSiblingWeight N q) = N + 1 := by
  rw [Fin.sum_univ_two]
  simp [twoSiblingWeight, Nat.add_comm]

/-- Even the fixed branching cardinality two permits arbitrarily large
weighted reverse growth when one compares against the light sibling. -/
theorem fixed_two_siblings_allow_arbitrary_reverse_growth (loss : Nat) :
    Fintype.card (Fin 2) = 2 ∧
      loss * twoSiblingWeight (loss + 1) 0 <
        ∑ q : Fin 2, twoSiblingWeight (loss + 1) q := by
  constructor
  · simp
  · rw [twoSiblingWeight_sum, twoSiblingWeight_zero]
    omega

#print axioms HierarchySiblingRigidityCertificate.lowerSibling_card_le_hierarchyBranchingFactor
#print axioms HierarchySiblingRigidityCertificate.lowerSibling_card_le_branchingBound
#print axioms familyVolume_fiberFamily_eq_sum
#print axioms upperFiberFamilyVolume_eq_sum_lowerSiblings
#print axioms upperFiberMass_le_hierarchyReverseNormalizerBound
#print axioms toLargeIntervalReverseFiberMassGrowth
#print axioms actualReverseParentNormalizerLoss_le_hierarchyBound
#print axioms isStickyAtEveryScale_of_hierarchySiblingRigidity
#print axioms twoSiblingWeight_sum
#print axioms fixed_two_siblings_allow_arbitrary_reverse_growth

end
end FamilyStickyScaleChainHierarchySiblingRigidityV1
