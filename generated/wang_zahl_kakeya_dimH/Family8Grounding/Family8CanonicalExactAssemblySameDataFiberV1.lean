import Family8Grounding.Family8ExactAssemblySameDataFiberBridgeV1
import Mathlib.Tactic

/-!
# Canonical exact assembly with saturated same-data fibres

The generic `ExactAssembly` interface remembers only the source fine statistic,
so an arbitrary inhabitant gives an upper bound for the final fibre average.
For the canonical constructor, however, the last restriction is by one common
spatial statistic slice.  Hence every fine occurrence through a surviving
point in a selected parent survives together.  This file proves that fact from
the definitions and exposes it as a theorem conclusion, without adding it as a
field or accepting it as a hypothesis.
-/

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8CanonicalExactAssemblySameDataFiberV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FiberwiseMultiplicityAssembly
open Submission.Kakeya.ConvexFactoring.StatisticLevelRestriction
open Submission.Kakeya.ConvexFactoring.FactoringMultiplicityAssembly
open Family8ExactAssemblyActualAverageBridgeV1
open Family8ExactAssemblyActualAverageBridgeV1.ExactAssembly
open Family8ExactAssemblySameDataFiberBridgeV1
open Family8ExactAssemblySameDataFiberBridgeV1.ExactAssembly

noncomputable section

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

local instance (p : Prop) : Decidable p := Classical.propDecidable p

variable {iota kappa : Type*} [Fintype iota] [Fintype kappa]
  [DecidableEq iota] [DecidableEq kappa]
  {F : ConvexFamily iota} {W : ConvexFamily kappa}

omit [Fintype kappa] in
/-- Restricting every carrier by one common statistic slice preserves the
factorization fibre multiplicity at every point of that slice. -/
theorem fiberMultiplicity_restrictStatisticLevel_eq_of_mem
    (P : ConvexFactorization F W) (Z : Shading F)
    (stat : Space → Nat) (hstat : ∀ n, MeasurableSet {x | stat x = n})
    (n : Nat) (k : kappa) (x : Space)
    (hx : x ∈ statisticSlice Z stat n) :
    P.fiberMultiplicity (restrictStatisticLevel Z stat hstat n) k x =
      P.fiberMultiplicity Z k x := by
  classical
  unfold ConvexFactorization.fiberMultiplicity
  apply congrArg Finset.card
  ext i
  simp only [Finset.mem_filter, restrictStatisticLevel_carrier,
    Set.mem_inter_iff]
  constructor
  · rintro ⟨hi, hxi, _hxSlice⟩
    exact ⟨hi, hxi⟩
  · rintro ⟨hi, hxi⟩
    exact ⟨hi, hxi, hx⟩

/-- A common coarse-level bucket contains all and only the source occurrences
through a point in a selected fibre.  Thus its actual fibre multiplicity is
the common selected level. -/
theorem coarseLevelBucket_fiberMultiplicity_eq_of_source_level
    (P : ConvexFactorization F W) (Y : Shading F) (M : Nat)
    (hM : ∀ k ∈ P.index.coarse, (P.index.fiber k).card ≤ M)
    (b : Fin (M + 1)) (k : kappa) (x : Space)
    (hselected : selectedFiberLevel P Y k = b.1)
    (hsource : P.fiberMultiplicity Y k x = b.1) :
    P.fiberMultiplicity (coarseLevelBucket P Y M hM b).shading k x =
      b.1 := by
  classical
  rw [← hsource]
  unfold ConvexFactorization.fiberMultiplicity
  apply congrArg Finset.card
  ext i
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hiFiber, hxi⟩
    exact ⟨hiFiber,
      assembledShading_carrier_subset P Y i
        ((coarseLevelBucket P Y M hM b).carrier_subset i hxi)⟩
  · rintro ⟨hiFiber, hxi⟩
    have hif : i ∈ P.index.fine := P.index.fiber_subset_fine k hiFiber
    have hp : P.index.parent i = k :=
      (P.index.mem_fiber i k).1 hiFiber |>.2
    have hiBucket : i ∈ (coarseLevelBucket P Y M hM b).indices :=
      (mem_coarseLevelBucket_indices P Y M hM b i).2
        ⟨hif, by simpa only [hp] using hselected⟩
    have hxAssembly : x ∈ (assembledShading P Y).carrier i := by
      rw [assembledShading_carrier, if_pos hif]
      exact ⟨hxi, by
        simpa only [Set.mem_ofPred_eq, hp] using
          hsource.trans hselected.symm⟩
    refine ⟨hiFiber, ?_⟩
    change x ∈ if i ∈ (coarseLevelBucket P Y M hM b).indices then
      (assembledShading P Y).carrier i else ∅
    rw [if_pos hiBucket]
    exact hxAssembly

/-- The canonical exact-assembly producer, strengthened by the derived fact
that every final same-parent fibre is saturated at the selected fine level on
its actual shaded union. -/
theorem exists_exactAssembly_with_sameDataFiber_saturation_of_fiber_card_le
    (P : ConvexFactorization F W) (Y : Shading F) (M : Nat)
    (hM : ∀ k ∈ P.index.coarse, (P.index.fiber k).card ≤ M) :
    ∃ A : FactoringMultiplicityAssembly.ExactAssembly P Y
        (((M + 1) * (M + 1)) * (Fintype.card kappa + 1)),
      A.fineLevel ≤ M ∧
      A.outerLevel ≤ Fintype.card kappa ∧
      ∀ (k : kappa) (x : Space),
        x ∈ (finalFiberShading A k).shadedUnion →
          (finalFiberShading A k).pointMultiplicity x = A.fineLevel := by
  obtain ⟨b, hFiberMass, hFiberConst⟩ :=
    exists_common_coarseLevelBucket_from_active P Y M hM
  let B := coarseLevelBucket P Y M hM b
  let R₀ : IndexedShadingRefinement Y :=
    refinementTrans (assembledRefinement P Y) B
  let stat : Space → Nat := fun x =>
    (P.inducedShading R₀.shading).pointMultiplicity x
  have hstat : ∀ n, MeasurableSet {x | stat x = n} := by
    intro n
    exact measurableSet_pointMultiplicity_eq (P.inducedShading R₀.shading) n
  have hbound : ∀ x ∈ R₀.shading.shadedUnion,
      stat x ≤ Fintype.card kappa := by
    intro x hx
    exact (P.inducedShading R₀.shading).pointMultiplicity_le_card x
  obtain ⟨m, hm, hOuterMass, hOuterConst⟩ :=
    exists_restrictStatisticLevel_with_large_mass
      R₀.shading stat (Fintype.card kappa) hstat hbound
  let R : IndexedShadingRefinement Y :=
    refinementRestrictStatisticLevel R₀ stat hstat m
  have hFiberMass' : WithinFactor ((M + 1) * (M + 1))
      (IndexedShadingRefinement.restrictTo Y P.index.fine).shading.shadingMass
      R₀.shading.shadingMass := by
    unfold WithinFactor
    simpa [R₀, B, refinementTrans] using hFiberMass
  have hOuterMass' : WithinFactor (Fintype.card kappa + 1)
      R₀.shading.shadingMass R.shading.shadingMass := by
    unfold WithinFactor
    simpa [R, refinementRestrictStatisticLevel] using hOuterMass
  let A : FactoringMultiplicityAssembly.ExactAssembly P Y
      (((M + 1) * (M + 1)) * (Fintype.card kappa + 1)) :=
    { refinement := R
      fineLevel := b.1
      outerLevel := m
      indices_subset_fine := by
        intro i hi
        have hiB : i ∈ B.indices := by
          simpa [R, R₀, refinementRestrictStatisticLevel,
            refinementTrans] using hi
        exact (mem_coarseLevelBucket_indices P Y M hM b i).1 hiB |>.1
      retained := WithinFactor.trans hFiberMass' hOuterMass'
      fineStatistic_constant := by
        intro i x hx
        have hxR₀ : x ∈ R₀.shading.carrier i :=
          refinementRestrictStatisticLevel_carrier_subset_source
            R₀ stat hstat m i hx
        have hxB : x ∈ B.shading.carrier i := by
          simpa [R₀, B, refinementTrans] using hxR₀
        exact hFiberConst i x hxB
      outerStatistic_constant := by
        intro x hx
        have hxLevel :
            x ∈ (restrictStatisticLevel R₀.shading stat hstat m).shadedUnion := by
          simpa [R, refinementRestrictStatisticLevel] using hx
        have hconst : stat x = m := hOuterConst x hxLevel
        calc
          P.outerMultiplicity R.shading x =
              (P.inducedShading R.shading).pointMultiplicity x :=
            (P.pointMultiplicity_inducedShading_eq_outer R.shading x).symm
          _ = (P.inducedShading R₀.shading).pointMultiplicity x :=
            recomputedInducedPointMultiplicity_eq_on_refinementRestriction
              P R₀ stat hstat m hx
          _ = stat x := rfl
          _ = m := hconst }
  have hsaturation : ∀ (k : kappa) (x : Space),
      x ∈ (finalFiberShading A k).shadedUnion →
        (finalFiberShading A k).pointMultiplicity x = A.fineLevel := by
    intro k x hx
    obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hx
    rw [finalFiberShading_carrier] at hxi
    have hiFiber : i ∈ P.index.fiber k := by
      by_contra hni
      rw [if_neg hni] at hxi
      exact hxi
    rw [if_pos hiFiber] at hxi
    have hp : P.index.parent i = k :=
      (P.index.mem_fiber i k).1 hiFiber |>.2
    have hxR₀ : x ∈ R₀.shading.carrier i := by
      exact refinementRestrictStatisticLevel_carrier_subset_source
        R₀ stat hstat m i (by simpa only [A] using hxi)
    have hxB : x ∈ B.shading.carrier i := by
      simpa [R₀, B, refinementTrans] using hxR₀
    have hsource : P.fiberMultiplicity Y k x = b.1 := by
      simpa only [hp] using hFiberConst i x hxB
    have hiB : i ∈ B.indices := by
      by_contra hni
      rw [B.carrier_eq_empty_of_not_mem i hni] at hxB
      exact hxB
    have hselected : selectedFiberLevel P Y k = b.1 := by
      have hlevel := (mem_coarseLevelBucket_indices P Y M hM b i).1 hiB |>.2
      simpa only [hp] using hlevel
    have hxSlice : x ∈ statisticSlice R₀.shading stat m := by
      have hxi' :
          x ∈ (restrictStatisticLevel R₀.shading stat hstat m).carrier i := by
        simpa [A, R, refinementRestrictStatisticLevel] using hxi
      rw [restrictStatisticLevel_carrier] at hxi'
      exact hxi'.2
    rw [finalFiberShading,
      fiberShading_pointMultiplicity]
    change P.fiberMultiplicity R.shading k x = b.1
    calc
      P.fiberMultiplicity R.shading k x =
          P.fiberMultiplicity R₀.shading k x := by
        simpa [R, refinementRestrictStatisticLevel] using
          fiberMultiplicity_restrictStatisticLevel_eq_of_mem
            P R₀.shading stat hstat m k x hxSlice
      _ = P.fiberMultiplicity B.shading k x := by
        rfl
      _ = b.1 :=
        coarseLevelBucket_fiberMultiplicity_eq_of_source_level
          P Y M hM b k x hselected hsource
  exact ⟨A, Nat.le_of_lt_succ b.isLt,
    Nat.le_of_lt_succ (Finset.mem_range.mp hm), hsaturation⟩

/-- With nonzero source active mass, the strengthened canonical producer gives
one actual surviving final fibre whose average is exactly the selected fine
level.  The original refinement average is therefore bounded by the product
of the actual induced-coarse average and the actual final-fibre average, on
the same constructed data. -/
theorem exists_exactAssembly_with_sameDataFiber_actualAverage_product_of_fiber_card_le
    (P : ConvexFactorization F W) (Y : Shading F) (M : Nat)
    (hM : ∀ k ∈ P.index.coarse, (P.index.fiber k).card ≤ M)
    (hsource :
      (IndexedShadingRefinement.restrictTo Y P.index.fine).shading.shadingMass ≠
        0) :
    ∃ A : FactoringMultiplicityAssembly.ExactAssembly P Y
        (((M + 1) * (M + 1)) * (Fintype.card kappa + 1)),
      A.fineLevel ≤ M ∧
      A.outerLevel ≤ Fintype.card kappa ∧
      ∃ k ∈ P.index.coarse,
        0 < volume (finalFiberShading A k).shadedUnion ∧
        (finalFiberShading A k).averageMultiplicity =
          (A.fineLevel : ENNReal) ∧
        (P.inducedShading A.refinement.shading).averageMultiplicity =
          (A.outerLevel : ENNReal) ∧
        A.refinement.shading.averageMultiplicity ≤
          (P.inducedShading A.refinement.shading).averageMultiplicity *
            (finalFiberShading A k).averageMultiplicity := by
  obtain ⟨A, hfine, houter, hsaturation⟩ :=
    exists_exactAssembly_with_sameDataFiber_saturation_of_fiber_card_le
      P Y M hM
  obtain ⟨k, hk, hvolume, _hcomparison, _hsourceAverage⟩ :=
    ExactAssembly.exists_surviving_finalFiberShading_sameData_comparison
      A hsource
  have hfineAverage : (finalFiberShading A k).averageMultiplicity =
      (A.fineLevel : ENNReal) :=
    averageMultiplicity_eq_nat_of_constant_on_shadedUnion
      (finalFiberShading A k) A.fineLevel (ne_of_gt hvolume)
        (fun x hx => hsaturation k x hx)
  have houterAverage :
      (P.inducedShading A.refinement.shading).averageMultiplicity =
        (A.outerLevel : ENNReal) :=
    ExactAssembly.inducedShading_averageMultiplicity_eq_outerLevel A hsource
  have hproduct :
      A.refinement.shading.averageMultiplicity ≤
        (P.inducedShading A.refinement.shading).averageMultiplicity *
          (finalFiberShading A k).averageMultiplicity := by
    calc
      A.refinement.shading.averageMultiplicity ≤
          (P.inducedShading A.refinement.shading).averageMultiplicity *
            (A.fineLevel : ENNReal) :=
        ExactAssembly.refinement_averageMultiplicity_le_inducedAverage_mul_fineLevel
          A hsource
      _ = (P.inducedShading A.refinement.shading).averageMultiplicity *
            (finalFiberShading A k).averageMultiplicity := by
        rw [hfineAverage]
  exact ⟨A, hfine, houter, k, hk, hvolume, hfineAverage,
    houterAverage, hproduct⟩

#print axioms fiberMultiplicity_restrictStatisticLevel_eq_of_mem
#print axioms coarseLevelBucket_fiberMultiplicity_eq_of_source_level
#print axioms
  exists_exactAssembly_with_sameDataFiber_saturation_of_fiber_card_le
#print axioms
  exists_exactAssembly_with_sameDataFiber_actualAverage_product_of_fiber_card_le

end

end Family8CanonicalExactAssemblySameDataFiberV1
