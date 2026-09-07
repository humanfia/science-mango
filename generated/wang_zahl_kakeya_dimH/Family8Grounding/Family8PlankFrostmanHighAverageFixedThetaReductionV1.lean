import Family8Grounding.Family8PlankFixedThetaAllSlabAssemblyV1
import Mathlib.Tactic

/-!
# The derivable fixed-theta core of the plank Frostman reduction

The high-average branch of the paper first selects a typical angle and then
constructs all occupied slab rows at that one angle.  The present repository
does not yet contain that typical-angle/all-slab selection theorem.

This file records, without assuming that missing conclusion, everything that
is already derivable once a scale `theta` is supplied:

* maximal mutual-thickening clustering;
* one mass-retaining logarithmic owner-fibre bucket;
* the half-average heavy-owner restriction;
* the common fibre window `N <= card < 2 N` and `card <= M * theta`;
* automatic positivity of every row family volume in any genuine all-slab
  catalogue; and
* the exact affine-Jacobian sum, followed by bounded overlap, bounded by the
  original source shaded union.

Thus the declarations below are a fixed-scale combinatorial/geometric core,
not a proof that high multiplicity chooses `theta`, not a construction of the
all-slab catalogue, and not an invocation of a Family 7 hypothesis.
-/

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal InnerProductSpace

namespace Family8PlankFrostmanHighAverageFixedThetaReductionV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Family6AffineConvexVolumeCoreV1
open Family6AffinePlankAnalyticHypothesesStableV1
open Family8PlankThickControlMutualContainmentClusteringV2
open Family8PlankThickControlOwnerFiberLogBucketV2
open Family8PlankThickControlRetainedOwnerFamilyV3
open Family8PlankRetainedOwnerHeavyMassSelectionV3
open Family8PlankHeavyRetainedOwnerActualDatumV2
open Family8PlankFixedThetaAllSlabRowsV1
open Family8PlankFixedThetaAllSlabAssemblyV1

noncomputable section

/- The generalized Frostman property currently quantifies index types in
`Type`, so this reduction boundary intentionally uses the same universe. -/
variable {iota : Type} [Fintype iota] [DecidableEq iota]
variable {a b : NNReal}

/-- The complete fixed-scale owner reduction already supplied by the
clustering and finite-selection modules.

The loss is exactly twice the number of logarithmic fibre-cardinality labels:
one factor for selecting a label and one factor for the half-average heavy
selection. -/
structure FixedThetaHeavyOwnerReduction
    (D : ShadedConvexPlankFamily iota a b) (M theta : NNReal) where
  clustering : MutualThickeningClustering D theta
  q : Fin (Nat.log 2 (Fintype.card iota) + 1)
  source_mass_le :
    D.shading.shadingMass <=
      (2 * ((Nat.log 2 (Fintype.card iota) + 1 : Nat) : ENNReal)) *
        (heavyRetainedOwnerPlankFamily D clustering q).shading.shadingMass
  branching_pos : 0 < ownerBucketBranching q
  fibre_card_bounds : forall s,
    s ∈ heavyRetainedOwners clustering q ->
      ownerBucketBranching q <= (ownerFiber clustering s).card /\
        (ownerFiber clustering s).card < 2 * ownerBucketBranching q /\
        ((ownerFiber clustering s).card : ENNReal) <=
          (M : ENNReal) * (theta : ENNReal)

/-- At every supplied admissible scale the fixed-theta owner reduction exists.

No multiplicity premise occurs: high multiplicity is needed earlier in the
paper to select a useful common `theta`, not for this finite clustering tail. -/
theorem exists_fixedThetaHeavyOwnerReduction
    [Nonempty iota]
    (D : ShadedConvexPlankFamily iota a b) (M theta : NNReal)
    (hthick : FrostmanThickenedPlankControl D M)
    (hatheta : a / b <= theta) (htheta : theta <= 1) :
    Nonempty (FixedThetaHeavyOwnerReduction D M theta) := by
  obtain ⟨C⟩ := exists_mutualThickeningClustering D theta
  obtain ⟨q, hmass, hNpos, hbounds⟩ :=
    exists_retainedOwnerPlankFamily_mass_card_thickControl
      D M theta C hthick hatheta htheta
  refine ⟨{
    clustering := C
    q := q
    source_mass_le := ?_
    branching_pos := hNpos
    fibre_card_bounds := ?_ }⟩
  · have hheavy := sourceMass_le_two_mul_loss_mul_heavyActualMass
      D C q
      ((Nat.log 2 (Fintype.card iota) + 1 : Nat) : ENNReal) hmass
    simpa only using hheavy
  · intro s hs
    have hsBucket : s ∈ selectedOwnerLogBucket C q :=
      (mem_heavyRetainedOwners C q s).1 hs |>.1
    exact hbounds s hsBucket

/-- Nonzero source shading mass survives the fixed-theta heavy restriction. -/
theorem FixedThetaHeavyOwnerReduction.heavySourceMass_ne_zero
    {D : ShadedConvexPlankFamily iota a b} {M theta : NNReal}
    (H : FixedThetaHeavyOwnerReduction D M theta)
    (hsource : D.shading.shadingMass ≠ 0) :
    (heavyRetainedOwnerPlankFamily D H.clustering H.q).shading.shadingMass ≠ 0 := by
  intro hzero
  apply hsource
  apply le_antisymm
  · simpa only [hzero, mul_zero] using H.source_mass_le
  · exact bot_le

/-- A genuine high-average premise already forces nonzero source shading
mass.  This closes the nondegeneracy input above in the intended branch. -/
theorem shadingMass_ne_zero_of_rpow_le_averageMultiplicity
    (D : ShadedConvexPlankFamily iota a b) (eta : Real)
    (ha : 0 < a)
    (hhigh :
      (a : ENNReal) ^ (-eta) <= D.shading.averageMultiplicity) :
    D.shading.shadingMass ≠ 0 := by
  intro hmass
  have havg : D.shading.averageMultiplicity = 0 := by
    simp [Shading.averageMultiplicity, hmass]
  have hpow : 0 < (a : ENNReal) ^ (-eta) := by
    positivity
  rw [havg] at hhigh
  exact (not_lt_of_ge hhigh) hpow

/-- The same nonzero source mass gives at least one genuinely heavy owner. -/
theorem FixedThetaHeavyOwnerReduction.heavyOwners_nonempty
    {D : ShadedConvexPlankFamily iota a b} {M theta : NNReal}
    (H : FixedThetaHeavyOwnerReduction D M theta)
    (hsource : D.shading.shadingMass ≠ 0) :
    (heavyRetainedOwners H.clustering H.q).Nonempty := by
  by_contra hempty
  have howners : heavyRetainedOwners H.clustering H.q = ∅ :=
    Finset.not_nonempty_iff_eq_empty.mp hempty
  apply H.heavySourceMass_ne_zero hsource
  rw [heavyRetainedOwnerPlankFamily_shadingMass]
  simp [heavyRetainedOwnerMass, howners]

/-- The common owner-fibre bounds apply to every literal member of every row
in any all-slab catalogue built from this reduction. -/
theorem FixedThetaHeavyOwnerReduction.rowMember_fibre_card_bounds
    {D : ShadedConvexPlankFamily iota a b} {M theta : NNReal}
    (H : FixedThetaHeavyOwnerReduction D M theta)
    {rowIndex : Type} [Fintype rowIndex] [DecidableEq rowIndex]
    {slabComparisonConstant : NNReal}
    (R : FixedThetaAllSlabRows D H.clustering H.q rowIndex
      slabComparisonConstant)
    (r : rowIndex) (s : {s // s ∈ R.rowOwners r}) :
    ownerBucketBranching H.q <= (ownerFiber H.clustering s.1.1).card /\
      (ownerFiber H.clustering s.1.1).card <
        2 * ownerBucketBranching H.q /\
      ((ownerFiber H.clustering s.1.1).card : ENNReal) <=
        (M : ENNReal) * (theta : ENNReal) :=
  H.fibre_card_bounds s.1.1 s.1.2

/-- Every row member also retains the common half-average fine-fibre mass
floor.  This is a fine mass statement; it does not assert the still-missing
density lower bound for the induced thickened-owner row shading. -/
theorem fixedThetaAllSlab_rowMember_fibre_mass_floor
    {D : ShadedConvexPlankFamily iota a b} {theta : NNReal}
    {C : MutualThickeningClustering D theta}
    {q : Fin (Nat.log 2 (Fintype.card iota) + 1)}
    {rowIndex : Type} [Fintype rowIndex] [DecidableEq rowIndex]
    {slabComparisonConstant : NNReal}
    (R : FixedThetaAllSlabRows D C q rowIndex slabComparisonConstant)
    (r : rowIndex) (s : {s // s ∈ R.rowOwners r}) :
    retainedOwnerHalfAverageFloor C q <= ownerFiberMass C s.1.1 :=
  heavyRetainedOwner_row_mass_floor C q s.1

/-- Summed fine-fibre mass floor on one literal catalogue row. -/
theorem fixedThetaAllSlab_rowOwners_card_mul_fibreFloor_le
    {D : ShadedConvexPlankFamily iota a b} {theta : NNReal}
    {C : MutualThickeningClustering D theta}
    {q : Fin (Nat.log 2 (Fintype.card iota) + 1)}
    {rowIndex : Type} [Fintype rowIndex] [DecidableEq rowIndex]
    {slabComparisonConstant : NNReal}
    (R : FixedThetaAllSlabRows D C q rowIndex slabComparisonConstant)
    (r : rowIndex) :
    ((R.rowOwners r).card : ENNReal) * retainedOwnerHalfAverageFloor C q <=
      ∑ s ∈ R.rowOwners r, ownerFiberMass C s.1 := by
  calc
    ((R.rowOwners r).card : ENNReal) *
          retainedOwnerHalfAverageFloor C q =
        ∑ _s ∈ R.rowOwners r, retainedOwnerHalfAverageFloor C q := by
      simp
    _ <= ∑ s ∈ R.rowOwners r, ownerFiberMass C s.1 := by
      apply Finset.sum_le_sum
      intro s hs
      let ss : {t // t ∈ R.rowOwners r} := ⟨s, hs⟩
      exact fixedThetaAllSlab_rowMember_fibre_mass_floor R r ss

/-- Every occupied literal row has positive family volume.  This premise of
the mass-weighted Eq. (43) producer is automatic from `IsPlank` positivity
and the fact that an owner thickening contains its source owner. -/
theorem fixedThetaAllSlab_rowFamilyVolume_pos
    {D : ShadedConvexPlankFamily iota a b} {theta : NNReal}
    {C : MutualThickeningClustering D theta}
    {q : Fin (Nat.log 2 (Fintype.card iota) + 1)}
    {rowIndex : Type} [Fintype rowIndex] [DecidableEq rowIndex]
    {slabComparisonConstant : NNReal}
    (R : FixedThetaAllSlabRows D C q rowIndex slabComparisonConstant)
    (r : rowIndex) :
    0 < familyVolume (R.rowFamily r) := by
  obtain ⟨s, hs⟩ := R.rowOwners_nonempty r
  let ss : {t // t ∈ R.rowOwners r} := ⟨s, hs⟩
  have hsourceBody :
      0 < volume (D.family s.1 : Set Space) :=
    (D.all_isPlank s.1).volume_pos
  have hcontained :
      (D.family s.1 : Set Space) ⊆ (R.rowFamily r ss : Set Space) := by
    rw [R.rowFamily_apply]
    change (D.family s.1 : Set Space) ⊆
      Metric.cthickening ((theta * b : NNReal) : Real)
        (D.family s.1 : Set Space)
    exact Metric.self_subset_cthickening _
  have hmember :
      0 < volume (R.rowFamily r ss : Set Space) :=
    hsourceBody.trans_le (measure_mono hcontained)
  have hsingle :
      volume (R.rowFamily r ss : Set Space) <=
        familyVolume (R.rowFamily r) := by
    unfold familyVolume
    exact Finset.single_le_sum
      (fun t _ht => show (0 : ENNReal) <=
        volume (R.rowFamily r t : Set Space) from bot_le)
      (Finset.mem_univ ss)
  exact hmember.trans_le hsingle

/-- Convenient nonzero form consumed by the Eq. (43) Frostman producer. -/
theorem fixedThetaAllSlab_rowFamilyVolume_ne_zero
    {D : ShadedConvexPlankFamily iota a b} {theta : NNReal}
    {C : MutualThickeningClustering D theta}
    {q : Fin (Nat.log 2 (Fintype.card iota) + 1)}
    {rowIndex : Type} [Fintype rowIndex] [DecidableEq rowIndex]
    {slabComparisonConstant : NNReal}
    (R : FixedThetaAllSlabRows D C q rowIndex slabComparisonConstant)
    (r : rowIndex) :
    familyVolume (R.rowFamily r) ≠ 0 :=
  (fixedThetaAllSlab_rowFamilyVolume_pos R r).ne'

/-- Once the source mass is nonzero, any all-slab catalogue built on the
fixed-theta reduction has nonzero global thick-owner family volume. -/
theorem FixedThetaHeavyOwnerReduction.globalFamilyVolume_ne_zero
    {D : ShadedConvexPlankFamily iota a b} {M theta : NNReal}
    (H : FixedThetaHeavyOwnerReduction D M theta)
    (hsource : D.shading.shadingMass ≠ 0)
    {rowIndex : Type} [Fintype rowIndex] [DecidableEq rowIndex]
    {slabComparisonConstant : NNReal}
    (R : FixedThetaAllSlabRows D H.clustering H.q rowIndex
      slabComparisonConstant) :
    familyVolume
      (heavyRetainedOwnerThickenedFamily D H.clustering H.q) ≠ 0 := by
  obtain ⟨s, hs⟩ := H.heavyOwners_nonempty hsource
  let ss : {s // s ∈ heavyRetainedOwners H.clustering H.q} := ⟨s, hs⟩
  let r : rowIndex := R.ownerToRow ss
  have hrow : 0 < familyVolume (R.rowFamily r) :=
    fixedThetaAllSlab_rowFamilyVolume_pos R r
  have hrowLe : familyVolume (R.rowFamily r) <=
      ∑ t : rowIndex, familyVolume (R.rowFamily t) := by
    exact Finset.single_le_sum
      (fun t _ht => show (0 : ENNReal) <=
        familyVolume (R.rowFamily t) from bot_le)
      (Finset.mem_univ r)
  rw [← R.familyVolume_eq_sum_rowFamily_familyVolume] at hrowLe
  exact (hrow.trans_le hrowLe).ne'

/-- The selected heavy source is a literal subtype of the original source,
so its shaded union is contained in the original shaded union. -/
theorem heavySource_shadedUnion_subset_source
    (D : ShadedConvexPlankFamily iota a b) {theta : NNReal}
    (C : MutualThickeningClustering D theta)
    (q : Fin (Nat.log 2 (Fintype.card iota) + 1)) :
    (heavyRetainedOwnerPlankFamily D C q).shading.shadedUnion ⊆
      D.shading.shadedUnion := by
  intro x hx
  obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hx
  exact Set.mem_iUnion.mpr ⟨i.1, hxi⟩

/-- All physical catalogue rows together lie in the original source shaded
union.  The equality with the heavy source union is supplied by `RowsV1`. -/
theorem allRows_shadedUnion_subset_source
    {D : ShadedConvexPlankFamily iota a b} {theta : NNReal}
    {C : MutualThickeningClustering D theta}
    {q : Fin (Nat.log 2 (Fintype.card iota) + 1)}
    {rowIndex : Type} [Fintype rowIndex] [DecidableEq rowIndex]
    {slabComparisonConstant : NNReal}
    (R : FixedThetaAllSlabRows D C q rowIndex slabComparisonConstant) :
    (⋃ r : rowIndex, (R.rowShading r).shadedUnion) ⊆
      D.shading.shadedUnion := by
  rw [R.iUnion_rowShadedUnion_eq_heavySource]
  exact heavySource_shadedUnion_subset_source D C q

/-- Exact affine reconstruction plus a pointwise row-overlap cap bounds the
weighted normalized row sum by the *original* source shaded union. -/
theorem inverseJacobian_weightedRows_le_source
    {D : ShadedConvexPlankFamily iota a b} {theta : NNReal}
    {C : MutualThickeningClustering D theta}
    {q : Fin (Nat.log 2 (Fintype.card iota) + 1)}
    {rowIndex : Type} [Fintype rowIndex] [DecidableEq rowIndex]
    {slabComparisonConstant : NNReal}
    (R : FixedThetaAllSlabRows D C q rowIndex slabComparisonConstant)
    (normalize : rowIndex -> Space ≃ᵃ[Real] Space)
    (overlapCap : Nat)
    (hOverlap : forall x,
      (rowUnionShading R).pointMultiplicity x <= overlapCap) :
    (∑ r : rowIndex,
        inverseAffineJacobianRowWeight normalize r *
          affineNormalizedRowUnion R normalize r) <=
      (overlapCap : ENNReal) * volume D.shading.shadedUnion := by
  let J := affineNormalizationJacobianOverlapCertificate
    R normalize overlapCap hOverlap
  have hglobal := J.weighted_rows_le_global
  calc
    (∑ r : rowIndex,
        inverseAffineJacobianRowWeight normalize r *
          affineNormalizedRowUnion R normalize r) <=
        (overlapCap : ENNReal) *
          volume ((heavyRetainedOwnerThickenedShading D C q).shadedUnion) := by
      simpa only [J, one_mul] using hglobal
    _ = (overlapCap : ENNReal) *
        volume ((heavyRetainedOwnerPlankFamily D C q).shading.shadedUnion) := by
      rw [heavyRetainedOwnerThickenedShading_shadedUnion_eq]
    _ <= (overlapCap : ENNReal) * volume D.shading.shadedUnion := by
      exact mul_le_mul' le_rfl
        (measure_mono (heavySource_shadedUnion_subset_source D C q))

#print axioms exists_fixedThetaHeavyOwnerReduction
#print axioms FixedThetaHeavyOwnerReduction.heavySourceMass_ne_zero
#print axioms shadingMass_ne_zero_of_rpow_le_averageMultiplicity
#print axioms FixedThetaHeavyOwnerReduction.heavyOwners_nonempty
#print axioms FixedThetaHeavyOwnerReduction.rowMember_fibre_card_bounds
#print axioms fixedThetaAllSlab_rowMember_fibre_mass_floor
#print axioms fixedThetaAllSlab_rowOwners_card_mul_fibreFloor_le
#print axioms fixedThetaAllSlab_rowFamilyVolume_pos
#print axioms fixedThetaAllSlab_rowFamilyVolume_ne_zero
#print axioms FixedThetaHeavyOwnerReduction.globalFamilyVolume_ne_zero
#print axioms heavySource_shadedUnion_subset_source
#print axioms allRows_shadedUnion_subset_source
#print axioms inverseJacobian_weightedRows_le_source

end
end Family8PlankFrostmanHighAverageFixedThetaReductionV1
