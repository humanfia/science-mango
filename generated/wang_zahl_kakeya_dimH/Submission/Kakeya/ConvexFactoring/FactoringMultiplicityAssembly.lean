import Submission.Kakeya.ConvexFactoring.FiberwiseMultiplicityAssembly
import Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization

/-!
# Exact factoring and multiplicity assembly

This module combines actual fiberwise multiplicity-level refinements with an
actual exact-induced outer multiplicity restriction. The resulting
`ExactAssembly` stores the refinement, selected levels, and division-free
retention loss; pointwise, mass, and average multiplicity product bounds are
derived theorems rather than structure fields.

The precise scope is:
* retention starts from the active mass obtained by restricting `Y` to
  `P.index.fine`, not from inactive indices;
* the selected fine statistic is the source shading's parent-fiber
  multiplicity on retained carriers, so subsequent refinement yields an upper
  bound for the final fiber multiplicity rather than a claimed equality;
* the outer constant concerns the recomputed exact induced shading;
  neighborhood-induced recomputation would require additional stability;
* no induced-density lower bound or ballwise uniformity is asserted.
-/

open scoped ENNReal NNReal
open MeasureTheory Set

namespace Submission.Kakeya.ConvexFactoring

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open StatisticLevelRestriction
open FiberwiseMultiplicityAssembly
open GreedyOccurrenceFactorization

noncomputable section

local instance (p : Prop) : Decidable p := Classical.propDecidable p

namespace FactoringMultiplicityAssembly

/-- Composition of two actual indexed shading refinements. -/
def refinementTrans
    {α : Type*} [DecidableEq α] {G : ConvexFamily α}
    {Y : Shading G} (R : IndexedShadingRefinement Y)
    (S : IndexedShadingRefinement R.shading) : IndexedShadingRefinement Y where
  indices := S.indices
  shading := S.shading
  carrier_subset i := (S.carrier_subset i).trans (R.carrier_subset i)
  carrier_eq_empty_of_not_mem := S.carrier_eq_empty_of_not_mem

/-- Restrict an actual refinement by one common statistic level while retaining
its genuine active index set. -/
def refinementRestrictStatisticLevel
    {α : Type*} [Fintype α] [DecidableEq α] {G : ConvexFamily α}
    {Y : Shading G} (R : IndexedShadingRefinement Y)
    (stat : Space → ℕ) (hstat : ∀ n, MeasurableSet {x | stat x = n})
    (n : ℕ) : IndexedShadingRefinement Y where
  indices := R.indices
  shading := restrictStatisticLevel R.shading stat hstat n
  carrier_subset i := by
    rw [restrictStatisticLevel_carrier]
    exact inter_subset_left.trans (R.carrier_subset i)
  carrier_eq_empty_of_not_mem i hi := by
    rw [restrictStatisticLevel_carrier,
      R.carrier_eq_empty_of_not_mem i hi]
    simp

theorem refinementRestrictStatisticLevel_carrier_subset_source
    {α : Type*} [Fintype α] [DecidableEq α] {G : ConvexFamily α}
    {Y : Shading G} (R : IndexedShadingRefinement Y)
    (stat : Space → ℕ) (hstat : ∀ n, MeasurableSet {x | stat x = n})
    (n : ℕ) (i : α) :
    (refinementRestrictStatisticLevel R stat hstat n).shading.carrier i ⊆
      R.shading.carrier i := by
  rw [refinementRestrictStatisticLevel, restrictStatisticLevel_carrier]
  exact inter_subset_left

/-- Exact induced outer multiplicity is unchanged on the retained union after
a common statistic restriction. -/
theorem recomputedInducedPointMultiplicity_eq_on_refinementRestriction
    {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β]
    {G : ConvexFamily α} {H : ConvexFamily β}
    (P : ConvexFactorization G H) {Y : Shading G}
    (R : IndexedShadingRefinement Y)
    (stat : Space → ℕ) (hstat : ∀ n, MeasurableSet {x | stat x = n})
    (n : ℕ) {x : Space}
    (hx : x ∈ (refinementRestrictStatisticLevel R stat hstat n).shading.shadedUnion) :
    (P.inducedShading
      (refinementRestrictStatisticLevel R stat hstat n).shading).pointMultiplicity x =
      (P.inducedShading R.shading).pointMultiplicity x := by
  have hxLevel :
      x ∈ (restrictStatisticLevel R.shading stat hstat n).shadedUnion := by
    simpa [refinementRestrictStatisticLevel] using hx
  have hxSlice : x ∈ statisticSlice R.shading stat n := by
    rw [restrictStatisticLevel_shadedUnion] at hxLevel
    exact hxLevel
  simpa [refinementRestrictStatisticLevel, restrictStatisticLevel, hxSlice] using
    (pointMultiplicity_inducedShading_restrictSet P R.shading
      (statisticSlice R.shading stat n)
      (measurableSet_statisticSlice R.shading stat hstat n) x)

/-- Data retained by the exact factoring/multiplicity assembly.  The product
bound is deliberately not a field. -/
structure ExactAssembly
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    {F : ConvexFamily ι} {W : ConvexFamily κ}
    (P : ConvexFactorization F W) (Y : Shading F) (loss : ℕ) where
  refinement : IndexedShadingRefinement Y
  fineLevel : ℕ
  outerLevel : ℕ
  indices_subset_fine : refinement.indices ⊆ P.index.fine
  retained : WithinFactor loss
    (IndexedShadingRefinement.restrictTo Y P.index.fine).shading.shadingMass
    refinement.shading.shadingMass
  fineStatistic_constant : ∀ (i : ι) (x : Space),
    x ∈ refinement.shading.carrier i →
      P.fiberMultiplicity Y (P.index.parent i) x = fineLevel
  outerStatistic_constant : ∀ (x : Space),
    x ∈ refinement.shading.shadedUnion →
      P.outerMultiplicity refinement.shading x = outerLevel

namespace ExactAssembly

variable {ι κ : Type*} [Fintype ι] [Fintype κ]
  [DecidableEq ι] [DecidableEq κ]
  {F : ConvexFamily ι} {W : ConvexFamily κ}
  {P : ConvexFactorization F W} {Y : Shading F} {loss : ℕ}

/-- Fiber multiplicity is monotone under an indexed shading refinement. -/
theorem fiberMultiplicity_refinement_le
    (A : ExactAssembly P Y loss) (k : κ) (x : Space) :
    P.fiberMultiplicity A.refinement.shading k x ≤
      P.fiberMultiplicity Y k x := by
  classical
  unfold ConvexFactorization.fiberMultiplicity
  apply Finset.card_le_card
  intro i hi
  rw [Finset.mem_filter] at hi ⊢
  exact ⟨hi.1, A.refinement.carrier_subset i hi.2⟩

/-- Every fiber of the actual refinement is bounded by the selected fine
level. -/
theorem fiberMultiplicity_refinement_le_fineLevel
    (A : ExactAssembly P Y loss) (k : κ) (_hk : k ∈ P.index.coarse)
    (x : Space) :
    P.fiberMultiplicity A.refinement.shading k x ≤ A.fineLevel := by
  by_cases hzero : P.fiberMultiplicity A.refinement.shading k x = 0
  · simp [hzero]
  · have hpos : 0 < P.fiberMultiplicity A.refinement.shading k x :=
      Nat.pos_of_ne_zero hzero
    have hxInduced :
        x ∈ (P.inducedShading A.refinement.shading).carrier k :=
      (P.mem_inducedShading_iff_fiberMultiplicity_pos
        A.refinement.shading k x).2 hpos
    obtain ⟨_hk, i, hiFiber, hxi⟩ :=
      (P.mem_inducedShading_carrier_iff A.refinement.shading k x).1 hxInduced
    have hp : P.index.parent i = k :=
      (P.index.mem_fiber i k).1 hiFiber |>.2
    calc
      P.fiberMultiplicity A.refinement.shading k x ≤
          P.fiberMultiplicity Y k x :=
        A.fiberMultiplicity_refinement_le k x
      _ = A.fineLevel := by
        simpa [hp] using A.fineStatistic_constant i x hxi

/-- Empty carriers outside the active fine set make ordinary refined point
multiplicity equal factorization fine multiplicity. -/
theorem pointMultiplicity_refinement_eq_fineMultiplicity
    (A : ExactAssembly P Y loss) (x : Space) :
    A.refinement.shading.pointMultiplicity x =
      P.fineMultiplicity A.refinement.shading x := by
  classical
  unfold Shading.pointMultiplicity ConvexFactorization.fineMultiplicity
  apply congrArg Finset.card
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro hxi
    refine ⟨?_, hxi⟩
    by_contra hif
    have hni : i ∉ A.refinement.indices := fun hi =>
      hif (A.indices_subset_fine hi)
    rw [A.refinement.carrier_eq_empty_of_not_mem i hni] at hxi
    exact hxi
  · exact fun hi => hi.2

/-- The existing exact factoring inequality gives the pointwise product bound
on the refined shaded union. -/
theorem pointMultiplicity_le_product_on
    (A : ExactAssembly P Y loss) {x : Space}
    (hx : x ∈ A.refinement.shading.shadedUnion) :
    A.refinement.shading.pointMultiplicity x ≤
      A.outerLevel * A.fineLevel := by
  rw [A.pointMultiplicity_refinement_eq_fineMultiplicity]
  calc
    P.fineMultiplicity A.refinement.shading x ≤
        P.outerMultiplicity A.refinement.shading x * A.fineLevel :=
      P.fineMultiplicity_le_outer_mul A.refinement.shading x A.fineLevel
        (fun k hk => A.fiberMultiplicity_refinement_le_fineLevel k hk x)
    _ = A.outerLevel * A.fineLevel := by
      rw [A.outerStatistic_constant x hx]

/-- The pointwise product bound holds globally, with multiplicity zero off the
refined shaded union. -/
theorem pointMultiplicity_le_product
    (A : ExactAssembly P Y loss) (x : Space) :
    A.refinement.shading.pointMultiplicity x ≤
      A.outerLevel * A.fineLevel := by
  by_cases hx : x ∈ A.refinement.shading.shadedUnion
  · exact A.pointMultiplicity_le_product_on hx
  · have hzero : A.refinement.shading.pointMultiplicity x = 0 := by
      apply Nat.eq_zero_of_not_pos
      intro hpos
      exact hx ((A.refinement.shading.pointMultiplicity_pos_iff_mem_shadedUnion x).1 hpos)
    simp [hzero]

/-- A natural pointwise multiplicity bound integrates to a division-free mass
bound, including the zero-union-volume case. -/
theorem shadingMass_le_nsmul_volume_shadedUnion_of_pointMultiplicity_le
    {α : Type*} [Fintype α] {G : ConvexFamily α}
    (Z : Shading G) (C : ℕ)
    (hpoint : ∀ x, Z.pointMultiplicity x ≤ C) :
    Z.shadingMass ≤ C • volume Z.shadedUnion := by
  rw [← Z.lintegral_pointMultiplicity]
  calc
    (∫⁻ x, (Z.pointMultiplicity x : ℝ≥0∞) ∂volume) ≤
        ∫⁻ x, Z.shadedUnion.indicator (fun _ => (C : ℝ≥0∞)) x ∂volume := by
      apply lintegral_mono
      intro x
      by_cases hx : x ∈ Z.shadedUnion
      · simp only [Set.indicator_of_mem hx]
        exact_mod_cast hpoint x
      · have hzero : Z.pointMultiplicity x = 0 := by
          apply Nat.eq_zero_of_not_pos
          intro hpos
          exact hx ((Z.pointMultiplicity_pos_iff_mem_shadedUnion x).1 hpos)
        simp [hx, hzero]
    _ = C • volume Z.shadedUnion := by
      rw [lintegral_indicator Z.shadedUnion_measurableSet]
      simp [nsmul_eq_mul]

/-- Division-free average-multiplicity numerator bound. -/
theorem shadingMass_le_product_nsmul_volume
    (A : ExactAssembly P Y loss) :
    A.refinement.shading.shadingMass ≤
      (A.outerLevel * A.fineLevel) •
        volume A.refinement.shading.shadedUnion :=
  shadingMass_le_nsmul_volume_shadedUnion_of_pointMultiplicity_le
    A.refinement.shading (A.outerLevel * A.fineLevel)
      A.pointMultiplicity_le_product

/-- The resulting average multiplicity is bounded by the same explicit
product; `ENNReal.div_le_of_le_mul` keeps zero volume safe. -/
theorem averageMultiplicity_le_product
    (A : ExactAssembly P Y loss) :
    A.refinement.shading.averageMultiplicity ≤
      (A.outerLevel * A.fineLevel : ℕ) := by
  unfold Shading.averageMultiplicity
  apply ENNReal.div_le_of_le_mul
  simpa [nsmul_eq_mul] using A.shadingMass_le_product_nsmul_volume

end ExactAssembly

/-- Actual fiberwise selection followed by an actual recomputed exact-induced
outer multiplicity restriction produces the complete data-bearing assembly. -/
theorem exists_exactAssembly_of_fiber_card_le
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    {F : ConvexFamily ι} {W : ConvexFamily κ}
    (P : ConvexFactorization F W) (Y : Shading F) (M : ℕ)
    (hM : ∀ k ∈ P.index.coarse, (P.index.fiber k).card ≤ M) :
    ∃ A : ExactAssembly P Y
        (((M + 1) * (M + 1)) * (Fintype.card κ + 1)),
      A.fineLevel ≤ M ∧ A.outerLevel ≤ Fintype.card κ := by
  obtain ⟨b, hFiberMass, hFiberConst⟩ :=
    exists_common_coarseLevelBucket_from_active P Y M hM
  let B := coarseLevelBucket P Y M hM b
  let R₀ : IndexedShadingRefinement Y :=
    refinementTrans (assembledRefinement P Y) B
  let stat : Space → ℕ := fun x =>
    (P.inducedShading R₀.shading).pointMultiplicity x
  have hstat : ∀ n, MeasurableSet {x | stat x = n} := by
    intro n
    exact measurableSet_pointMultiplicity_eq (P.inducedShading R₀.shading) n
  have hbound : ∀ x ∈ R₀.shading.shadedUnion,
      stat x ≤ Fintype.card κ := by
    intro x hx
    exact (P.inducedShading R₀.shading).pointMultiplicity_le_card x
  obtain ⟨m, hm, hOuterMass, hOuterConst⟩ :=
    exists_restrictStatisticLevel_with_large_mass
      R₀.shading stat (Fintype.card κ) hstat hbound
  let R : IndexedShadingRefinement Y :=
    refinementRestrictStatisticLevel R₀ stat hstat m
  have hFiberMass' : WithinFactor ((M + 1) * (M + 1))
      (IndexedShadingRefinement.restrictTo Y P.index.fine).shading.shadingMass
      R₀.shading.shadingMass := by
    unfold WithinFactor
    simpa [R₀, B, refinementTrans] using hFiberMass
  have hOuterMass' : WithinFactor (Fintype.card κ + 1)
      R₀.shading.shadingMass R.shading.shadingMass := by
    unfold WithinFactor
    simpa [R, refinementRestrictStatisticLevel] using hOuterMass
  let A : ExactAssembly P Y
      (((M + 1) * (M + 1)) * (Fintype.card κ + 1)) :=
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
  refine ⟨A, ?_, ?_⟩
  · exact Nat.le_of_lt_succ b.isLt
  · exact Nat.le_of_lt_succ (Finset.mem_range.mp hm)

/-- Unconditional finite-family assembly, using the ambient fine-cardinality
bound on every factorization fiber. -/
theorem exists_exactAssembly
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    {F : ConvexFamily ι} {W : ConvexFamily κ}
    (P : ConvexFactorization F W) (Y : Shading F) :
    ∃ A : ExactAssembly P Y
        (((Fintype.card ι + 1) * (Fintype.card ι + 1)) *
          (Fintype.card κ + 1)),
      A.fineLevel ≤ Fintype.card ι ∧
        A.outerLevel ≤ Fintype.card κ := by
  apply exists_exactAssembly_of_fiber_card_le P Y (Fintype.card ι)
  intro k hk
  simpa using
    (Finset.card_le_card
      (Finset.subset_univ (P.index.fiber k)))

/-- The same exact assembly applied directly to the occurrence-indexed
factorization of an actual greedy density partition. -/
theorem exists_greedyExactAssembly
    {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    {F : ConvexFamily ι} {candidates : Finset κ}
    {container : κ → ConvexBody Space} {active : Finset ι}
    (G : GreedyDensityPartition F candidates container active)
    (Y : Shading F) :
    ∃ A : ExactAssembly (convexFactorization F G) Y
        (((Fintype.card ι + 1) * (Fintype.card ι + 1)) *
          (Fintype.card (Option (Fin (blocks F G).length)) + 1)),
      A.fineLevel ≤ Fintype.card ι ∧
        A.outerLevel ≤
          Fintype.card (Option (Fin (blocks F G).length)) :=
  exists_exactAssembly (convexFactorization F G) Y

end FactoringMultiplicityAssembly

end

end Submission.Kakeya.ConvexFactoring
