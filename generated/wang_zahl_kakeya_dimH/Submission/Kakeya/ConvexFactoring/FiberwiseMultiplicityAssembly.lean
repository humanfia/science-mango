import Submission.Kakeya.ConvexFactoring.StatisticLevelRestriction
import Submission.Kakeya.ConvexFactoring.QuantitativeRefinement

open scoped ENNReal NNReal
open MeasureTheory Set

namespace Submission.Kakeya.ConvexFactoring

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open StatisticLevelRestriction

noncomputable section

local instance (p : Prop) : Decidable p := Classical.propDecidable p

set_option linter.unusedSectionVars false

/-!
# Fiberwise multiplicity-level assembly

Each coarse fiber independently chooses an actual level of its fine point
multiplicity.  The chosen pieces are then assembled on the original fine
index type.  All choices below are extracted from the finite level
pigeonhole theorem rather than supplied as hypotheses.
-/

namespace FiberwiseMultiplicityAssembly

variable {ι κ : Type*} [Fintype ι] [Fintype κ]
  [DecidableEq ι] [DecidableEq κ]
  {F : ConvexFamily ι} {W : ConvexFamily κ}

/-- The original shading restricted to one fine fiber. -/
def fiberShading (P : ConvexFactorization F W) (Y : Shading F)
    (k : κ) : Shading F :=
  (IndexedShadingRefinement.restrictTo Y (P.index.fiber k)).shading

@[simp] theorem fiberShading_carrier
    (P : ConvexFactorization F W) (Y : Shading F) (k : κ) (i : ι) :
    (fiberShading P Y k).carrier i =
      if i ∈ P.index.fiber k then Y.carrier i else ∅ :=
  rfl

/-- Point multiplicity of a fiber shading is exactly factorization fiber
multiplicity. -/
theorem fiberShading_pointMultiplicity
    (P : ConvexFactorization F W) (Y : Shading F) (k : κ) (x : Space) :
    (fiberShading P Y k).pointMultiplicity x =
      P.fiberMultiplicity Y k x := by
  rw [fiberShading, IndexedShadingRefinement.pointMultiplicity_restrictTo]
  rfl

theorem fiberMultiplicity_le_fiber_card
    (P : ConvexFactorization F W) (Y : Shading F) (k : κ) (x : Space) :
    P.fiberMultiplicity Y k x ≤ (P.index.fiber k).card := by
  classical
  unfold ConvexFactorization.fiberMultiplicity
  exact Finset.card_le_card (Finset.filter_subset _ _)

/-- The restriction of one fiber to one actual multiplicity level. -/
def fiberLevelShading (P : ConvexFactorization F W) (Y : Shading F)
    (k : κ) (n : ℕ) : Shading F :=
  restrictStatisticLevel (fiberShading P Y k)
    (P.fiberMultiplicity Y k)
    (measurableSet_fiberMultiplicity_eq P Y k) n

@[simp] theorem fiberLevelShading_carrier
    (P : ConvexFactorization F W) (Y : Shading F)
    (k : κ) (n : ℕ) (i : ι) :
    (fiberLevelShading P Y k n).carrier i =
      if i ∈ P.index.fiber k then
        Y.carrier i ∩ {x | P.fiberMultiplicity Y k x = n}
      else ∅ := by
  rw [fiberLevelShading, restrictStatisticLevel_carrier]
  simp only [statisticSlice]
  ext x
  by_cases hi : i ∈ P.index.fiber k
  · simp only [fiberShading_carrier, hi, if_pos, Set.mem_inter_iff,
      Set.mem_ofPred_eq]
    constructor
    · rintro ⟨hxi, _hunion, hstat⟩
      exact ⟨hxi, hstat⟩
    · rintro ⟨hxi, hstat⟩
      refine ⟨hxi, ?_, hstat⟩
      exact Set.mem_iUnion.mpr
        ⟨i, by simpa [fiberShading_carrier, hi] using hxi⟩
  · simp [fiberShading_carrier, hi]

/-- A fiber-level shading has no carriers outside its fiber. -/
theorem fiberLevelShading_carrier_eq_empty_of_not_mem
    (P : ConvexFactorization F W) (Y : Shading F)
    (k : κ) (n : ℕ) (i : ι) (hi : i ∉ P.index.fiber k) :
    (fiberLevelShading P Y k n).carrier i = ∅ := by
  simp [hi]

/-- Its mass is exactly the sum of the selected pieces in that fiber. -/
theorem fiberLevelShading_mass_eq_sum_fiber
    (P : ConvexFactorization F W) (Y : Shading F)
    (k : κ) (n : ℕ) :
    (fiberLevelShading P Y k n).shadingMass =
      ∑ i ∈ P.index.fiber k,
        volume ((fiberLevelShading P Y k n).carrier i) := by
  classical
  unfold Shading.shadingMass
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro i hiUniv hiFiber
  rw [fiberLevelShading_carrier_eq_empty_of_not_mem P Y k n i hiFiber]
  simp

/-- The original mass of one fiber is its finite carrier sum. -/
theorem fiberShading_mass_eq_sum_fiber
    (P : ConvexFactorization F W) (Y : Shading F) (k : κ) :
    (fiberShading P Y k).shadingMass =
      ∑ i ∈ P.index.fiber k, volume (Y.carrier i) := by
  exact shadingMass_restrictTo_eq_sum Y (P.index.fiber k)

/-- An actual level is selected separately inside every fiber, with the sharp
finite loss `fiber.card + 1`.  This also applies to empty and inactive fibers. -/
theorem exists_fiberLevel
    (P : ConvexFactorization F W) (Y : Shading F) (k : κ) :
    ∃ n ∈ Finset.range ((P.index.fiber k).card + 1),
      (fiberShading P Y k).shadingMass ≤
        ((P.index.fiber k).card + 1) •
          (fiberLevelShading P Y k n).shadingMass ∧
      ∀ x ∈ (fiberLevelShading P Y k n).shadedUnion,
        P.fiberMultiplicity Y k x = n := by
  simpa only [fiberLevelShading] using
    (exists_restrictStatisticLevel_with_large_mass
      (Y := fiberShading P Y k)
      (stat := P.fiberMultiplicity Y k)
      (M := (P.index.fiber k).card)
      (measurableSet_fiberMultiplicity_eq P Y k)
      (fun x hx => fiberMultiplicity_le_fiber_card P Y k x))

/-- The level canonically extracted from the actual fiberwise pigeonhole
theorem. -/
def selectedFiberLevel (P : ConvexFactorization F W)
    (Y : Shading F) (k : κ) : ℕ :=
  Classical.choose (exists_fiberLevel P Y k)

theorem selectedFiberLevel_mem_range
    (P : ConvexFactorization F W) (Y : Shading F) (k : κ) :
    selectedFiberLevel P Y k ∈
      Finset.range ((P.index.fiber k).card + 1) :=
  (Classical.choose_spec (exists_fiberLevel P Y k)).1

theorem selectedFiberLevel_le_card
    (P : ConvexFactorization F W) (Y : Shading F) (k : κ) :
    selectedFiberLevel P Y k ≤ (P.index.fiber k).card :=
  Nat.le_of_lt_succ
    (Finset.mem_range.mp (selectedFiberLevel_mem_range P Y k))

/-- The independently selected refinement of one fiber. -/
def selectedFiberShading (P : ConvexFactorization F W)
    (Y : Shading F) (k : κ) : Shading F :=
  fiberLevelShading P Y k (selectedFiberLevel P Y k)

theorem selectedFiberShading_mass_bound
    (P : ConvexFactorization F W) (Y : Shading F) (k : κ) :
    (fiberShading P Y k).shadingMass ≤
      ((P.index.fiber k).card + 1) •
        (selectedFiberShading P Y k).shadingMass :=
  (Classical.choose_spec (exists_fiberLevel P Y k)).2.1

theorem selectedFiberShading_constant
    (P : ConvexFactorization F W) (Y : Shading F) (k : κ)
    {x : Space} (hx : x ∈ (selectedFiberShading P Y k).shadedUnion) :
    P.fiberMultiplicity Y k x = selectedFiberLevel P Y k :=
  (Classical.choose_spec (exists_fiberLevel P Y k)).2.2 x hx

/-- A coarse index outside the active coarse set has an empty fine fiber. -/
theorem fiber_eq_empty_of_not_mem_coarse
    (P : ConvexFactorization F W) (k : κ) (hk : k ∉ P.index.coarse) :
    P.index.fiber k = ∅ := by
  apply Finset.eq_empty_of_forall_notMem
  intro i hi
  have hif := (P.index.mem_fiber i k).mp hi
  exact hk (hif.2 ▸ P.index.parent_mem i hif.1)

/-- Empty/inactive fibers select the only possible level, namely zero. -/
theorem selectedFiberLevel_eq_zero_of_not_mem_coarse
    (P : ConvexFactorization F W) (Y : Shading F)
    (k : κ) (hk : k ∉ P.index.coarse) :
    selectedFiberLevel P Y k = 0 := by
  have hle := selectedFiberLevel_le_card P Y k
  rw [fiber_eq_empty_of_not_mem_coarse P k hk] at hle
  simpa using hle

/-- Assemble all independently selected fiber pieces on the original fine
index type.  Inactive fine indices are automatically empty. -/
def assembledShading (P : ConvexFactorization F W) (Y : Shading F) :
    Shading F where
  carrier i := (selectedFiberShading P Y (P.index.parent i)).carrier i
  measurable_carrier i :=
    (selectedFiberShading P Y (P.index.parent i)).measurable_carrier i
  carrier_subset i :=
    (selectedFiberShading P Y (P.index.parent i)).carrier_subset i

@[simp] theorem assembledShading_carrier
    (P : ConvexFactorization F W) (Y : Shading F) (i : ι) :
    (assembledShading P Y).carrier i =
      if i ∈ P.index.fine then
        Y.carrier i ∩
          {x | P.fiberMultiplicity Y (P.index.parent i) x =
            selectedFiberLevel P Y (P.index.parent i)}
      else ∅ := by
  change
    (fiberLevelShading P Y (P.index.parent i)
      (selectedFiberLevel P Y (P.index.parent i))).carrier i = _
  rw [fiberLevelShading_carrier]
  simp [IndexFactorization.mem_fiber]

theorem assembledShading_carrier_subset
    (P : ConvexFactorization F W) (Y : Shading F) (i : ι) :
    (assembledShading P Y).carrier i ⊆ Y.carrier i := by
  rw [assembledShading_carrier]
  split_ifs
  · exact inter_subset_left
  · exact Set.empty_subset _

theorem assembledShading_carrier_eq_empty_of_not_mem
    (P : ConvexFactorization F W) (Y : Shading F)
    (i : ι) (hi : i ∉ P.index.fine) :
    (assembledShading P Y).carrier i = ∅ := by
  simp [hi]

/-- The assembly is an actual indexed shading refinement, not an assumed
package of witnesses. -/
def assembledRefinement (P : ConvexFactorization F W) (Y : Shading F) :
    IndexedShadingRefinement Y where
  indices := P.index.fine
  shading := assembledShading P Y
  carrier_subset := assembledShading_carrier_subset P Y
  carrier_eq_empty_of_not_mem :=
    assembledShading_carrier_eq_empty_of_not_mem P Y

/-- On each retained fine carrier the original multiplicity in its coarse
fiber is the independently chosen level of that fiber. -/
theorem assembledShading_constant_on_fiber
    (P : ConvexFactorization F W) (Y : Shading F)
    (k : κ) (i : ι) (hi : i ∈ P.index.fiber k)
    {x : Space} (hx : x ∈ (assembledShading P Y).carrier i) :
    P.fiberMultiplicity Y k x = selectedFiberLevel P Y k := by
  have hif : i ∈ P.index.fine := P.index.fiber_subset_fine k hi
  have hp : P.index.parent i = k := (P.index.mem_fiber i k).mp hi |>.2
  rw [assembledShading_carrier, if_pos hif] at hx
  simpa [hp] using hx.2

theorem assembledShading_carrier_eq_selectedFiberShading
    (P : ConvexFactorization F W) (Y : Shading F)
    (k : κ) (i : ι) (hi : i ∈ P.index.fiber k) :
    (assembledShading P Y).carrier i =
      (selectedFiberShading P Y k).carrier i := by
  have hif : i ∈ P.index.fine := P.index.fiber_subset_fine k hi
  have hp : P.index.parent i = k := (P.index.mem_fiber i k).mp hi |>.2
  rw [assembledShading_carrier, if_pos hif,
    selectedFiberShading, fiberLevelShading_carrier, if_pos hi]
  simp [hp]

/-- Exact assembly: disjoint index fibers make total assembled mass the sum
of independently selected fiber masses. -/
theorem assembledShading_mass_eq_sum_selectedFiberShading
    (P : ConvexFactorization F W) (Y : Shading F) :
    (assembledShading P Y).shadingMass =
      ∑ k ∈ P.index.coarse,
        (selectedFiberShading P Y k).shadingMass := by
  classical
  unfold Shading.shadingMass
  calc
    (∑ i : ι, volume ((assembledShading P Y).carrier i)) =
        ∑ i ∈ P.index.fine,
          volume ((assembledShading P Y).carrier i) := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro i hiUniv hif
      rw [assembledShading_carrier_eq_empty_of_not_mem P Y i hif]
      simp
    _ = ∑ k ∈ P.index.coarse, ∑ i ∈ P.index.fiber k,
          volume ((assembledShading P Y).carrier i) :=
      P.index.sum_fiberwise
        (fun i => volume ((assembledShading P Y).carrier i))
    _ = ∑ k ∈ P.index.coarse,
          (selectedFiberShading P Y k).shadingMass := by
      apply Finset.sum_congr rfl
      intro k hk
      change
        (∑ i ∈ P.index.fiber k,
          volume ((assembledShading P Y).carrier i)) =
          (fiberLevelShading P Y k
            (selectedFiberLevel P Y k)).shadingMass
      rw [fiberLevelShading_mass_eq_sum_fiber]
      apply Finset.sum_congr rfl
      intro i hi
      rw [assembledShading_carrier_eq_selectedFiberShading P Y k i hi]
      rfl

/-- Exact decomposition of the original active mass into its coarse fibers. -/
theorem activeShading_mass_eq_sum_fiberShading
    (P : ConvexFactorization F W) (Y : Shading F) :
    (IndexedShadingRefinement.restrictTo Y P.index.fine).shading.shadingMass =
      ∑ k ∈ P.index.coarse, (fiberShading P Y k).shadingMass := by
  rw [shadingMass_restrictTo_eq_sum]
  calc
    (∑ i ∈ P.index.fine, volume (Y.carrier i)) =
        ∑ k ∈ P.index.coarse,
          ∑ i ∈ P.index.fiber k, volume (Y.carrier i) :=
      P.index.sum_fiberwise (fun i => volume (Y.carrier i))
    _ = ∑ k ∈ P.index.coarse, (fiberShading P Y k).shadingMass := by
      apply Finset.sum_congr rfl
      intro k hk
      exact (fiberShading_mass_eq_sum_fiber P Y k).symm

/-- If every active fiber has `fiber.card + 1 ≤ B`, independent selections
retain at least a `1/B` fraction of the original active shaded mass. -/
theorem activeShading_mass_le_bound_smul_assembled
    (P : ConvexFactorization F W) (Y : Shading F) (B : ℕ)
    (hB : ∀ k ∈ P.index.coarse, (P.index.fiber k).card + 1 ≤ B) :
    (IndexedShadingRefinement.restrictTo Y P.index.fine).shading.shadingMass ≤
      B • (assembledShading P Y).shadingMass := by
  rw [activeShading_mass_eq_sum_fiberShading P Y,
    assembledShading_mass_eq_sum_selectedFiberShading P Y]
  calc
    (∑ k ∈ P.index.coarse, (fiberShading P Y k).shadingMass) ≤
        ∑ k ∈ P.index.coarse,
          B • (selectedFiberShading P Y k).shadingMass := by
      apply Finset.sum_le_sum
      intro k hk
      exact (selectedFiberShading_mass_bound P Y k).trans
        (nsmul_le_nsmul_left zero_le (hB k hk))
    _ = B • ∑ k ∈ P.index.coarse,
          (selectedFiberShading P Y k).shadingMass := by
      simp only [nsmul_eq_mul]
      exact (Finset.mul_sum P.index.coarse
        (fun k => (selectedFiberShading P Y k).shadingMass)
        (B : ℝ≥0∞)).symm

/-- A uniform active-fiber cardinality bound extends to every coarse index,
since inactive fibers are empty. -/
theorem fiber_card_le_all
    (P : ConvexFactorization F W) (M : ℕ)
    (hM : ∀ k ∈ P.index.coarse, (P.index.fiber k).card ≤ M) (k : κ) :
    (P.index.fiber k).card ≤ M := by
  by_cases hk : k ∈ P.index.coarse
  · exact hM k hk
  · rw [fiber_eq_empty_of_not_mem_coarse P k hk]
    exact Nat.zero_le M

/-- The selected level, packaged in the finite type of all levels allowed by
a uniform active-fiber bound. -/
def selectedFiberLevelFin
    (P : ConvexFactorization F W) (Y : Shading F) (M : ℕ)
    (hM : ∀ k ∈ P.index.coarse, (P.index.fiber k).card ≤ M)
    (k : κ) : Fin (M + 1) :=
  ⟨selectedFiberLevel P Y k,
    Nat.lt_succ_of_le ((selectedFiberLevel_le_card P Y k).trans
      (fiber_card_le_all P M hM k))⟩

/-- Keep precisely the active fine indices whose parent occurrence selected
one common multiplicity level. -/
def coarseLevelBucket
    (P : ConvexFactorization F W) (Y : Shading F) (M : ℕ)
    (hM : ∀ k ∈ P.index.coarse, (P.index.fiber k).card ≤ M)
    (b : Fin (M + 1)) : IndexedShadingRefinement (assembledShading P Y) :=
  IndexedShadingRefinement.restrictTo (assembledShading P Y)
    (dyadicFiber P.index.fine
      (fun i => selectedFiberLevelFin P Y M hM (P.index.parent i)) b)

@[simp] theorem mem_coarseLevelBucket_indices
    (P : ConvexFactorization F W) (Y : Shading F) (M : ℕ)
    (hM : ∀ k ∈ P.index.coarse, (P.index.fiber k).card ≤ M)
    (b : Fin (M + 1)) (i : ι) :
    i ∈ (coarseLevelBucket P Y M hM b).indices ↔
      i ∈ P.index.fine ∧ selectedFiberLevel P Y (P.index.parent i) = b.1 := by
  change
    i ∈ dyadicFiber P.index.fine
      (fun i => selectedFiberLevelFin P Y M hM (P.index.parent i)) b ↔ _
  rw [mem_dyadicFiber]
  constructor
  · rintro ⟨hi, hb⟩
    exact ⟨hi, congrArg Fin.val hb⟩
  · rintro ⟨hi, hb⟩
    exact ⟨hi, Fin.ext hb⟩

/-- The coarse occurrences whose independently selected level is the common
bucket level. -/
def coarseOccurrenceBucket
    (P : ConvexFactorization F W) (Y : Shading F) (M : ℕ)
    (_hM : ∀ k ∈ P.index.coarse, (P.index.fiber k).card ≤ M)
    (b : Fin (M + 1)) : Finset κ :=
  P.index.coarse.filter fun k => selectedFiberLevel P Y k = b.1

@[simp] theorem mem_coarseOccurrenceBucket
    (P : ConvexFactorization F W) (Y : Shading F) (M : ℕ)
    (hM : ∀ k ∈ P.index.coarse, (P.index.fiber k).card ≤ M)
    (b : Fin (M + 1)) (k : κ) :
    k ∈ coarseOccurrenceBucket P Y M hM b ↔
      k ∈ P.index.coarse ∧ selectedFiberLevel P Y k = b.1 := by
  simp [coarseOccurrenceBucket]

/-- The fine-index bucket is exactly the union of the selected coarse
occurrence fibers. -/
theorem coarseLevelBucket_indices_eq_biUnion_occurrences
    (P : ConvexFactorization F W) (Y : Shading F) (M : ℕ)
    (hM : ∀ k ∈ P.index.coarse, (P.index.fiber k).card ≤ M)
    (b : Fin (M + 1)) :
    (coarseLevelBucket P Y M hM b).indices =
      (coarseOccurrenceBucket P Y M hM b).biUnion P.index.fiber := by
  ext i
  constructor
  · intro hi
    have hi' := (mem_coarseLevelBucket_indices P Y M hM b i).mp hi
    exact Finset.mem_biUnion.mpr
      ⟨P.index.parent i,
        (mem_coarseOccurrenceBucket P Y M hM b
          (P.index.parent i)).mpr
          ⟨P.index.parent_mem i hi'.1, hi'.2⟩,
        (P.index.mem_fiber i (P.index.parent i)).mpr ⟨hi'.1, rfl⟩⟩
  · intro hi
    obtain ⟨k, hk, hik⟩ := Finset.mem_biUnion.mp hi
    have hk' := (mem_coarseOccurrenceBucket P Y M hM b k).mp hk
    have hik' := (P.index.mem_fiber i k).mp hik
    exact (mem_coarseLevelBucket_indices P Y M hM b i).mpr
      ⟨hik'.1, by simpa [hik'.2] using hk'.2⟩

/-- Exact weighted interpretation of clustering coarse occurrences: the mass
of a common-level bucket is the sum of the independently selected masses of
the coarse occurrences in that bucket. -/
theorem coarseLevelBucket_mass_eq_sum_occurrences
    (P : ConvexFactorization F W) (Y : Shading F) (M : ℕ)
    (hM : ∀ k ∈ P.index.coarse, (P.index.fiber k).card ≤ M)
    (b : Fin (M + 1)) :
    (coarseLevelBucket P Y M hM b).shading.shadingMass =
      ∑ k ∈ coarseOccurrenceBucket P Y M hM b,
        (selectedFiberShading P Y k).shadingMass := by
  classical
  rw [coarseLevelBucket, shadingMass_restrictTo_eq_sum]
  have hindices :
      dyadicFiber P.index.fine
          (fun i => selectedFiberLevelFin P Y M hM (P.index.parent i)) b =
        (coarseOccurrenceBucket P Y M hM b).biUnion P.index.fiber := by
    have h :=
      coarseLevelBucket_indices_eq_biUnion_occurrences P Y M hM b
    change
      dyadicFiber P.index.fine
          (fun i => selectedFiberLevelFin P Y M hM (P.index.parent i)) b =
        _ at h
    exact h
  rw [hindices]
  have hdisjoint :
      Set.PairwiseDisjoint
        (↑(coarseOccurrenceBucket P Y M hM b) : Set κ) P.index.fiber := by
    intro k hk l hl hkl
    change Disjoint (P.index.fiber k) (P.index.fiber l)
    rw [Finset.disjoint_left]
    intro i hik hil
    have hpik := (P.index.mem_fiber i k).mp hik |>.2
    have hpil := (P.index.mem_fiber i l).mp hil |>.2
    exact hkl (hpik.symm.trans hpil)
  rw [Finset.sum_biUnion hdisjoint]
  apply Finset.sum_congr rfl
  intro k hk
  change
    (∑ i ∈ P.index.fiber k,
      volume ((assembledShading P Y).carrier i)) =
      (fiberLevelShading P Y k
        (selectedFiberLevel P Y k)).shadingMass
  rw [fiberLevelShading_mass_eq_sum_fiber]
  apply Finset.sum_congr rfl
  intro i hi
  rw [assembledShading_carrier_eq_selectedFiberShading P Y k i hi]
  rfl

/-- Restricting the already assembled shading to all active indices changes
no mass, because every inactive carrier is empty. -/
theorem assembledShading_mass_eq_restrictTo_fine
    (P : ConvexFactorization F W) (Y : Shading F) :
    (assembledShading P Y).shadingMass =
      (IndexedShadingRefinement.restrictTo
        (assembledShading P Y) P.index.fine).shading.shadingMass := by
  classical
  unfold Shading.shadingMass
  apply Finset.sum_congr rfl
  intro i hi
  rw [IndexedShadingRefinement.restrictTo_carrier]
  by_cases hif : i ∈ P.index.fine
  · rw [if_pos hif]
  · rw [if_neg hif,
      assembledShading_carrier_eq_empty_of_not_mem P Y i hif]

/-- Weighted coarse-occurrence pigeonholing chooses one common selected level
and incurs exactly one further factor `M+1`. -/
theorem exists_common_coarseLevelBucket
    (P : ConvexFactorization F W) (Y : Shading F) (M : ℕ)
    (hM : ∀ k ∈ P.index.coarse, (P.index.fiber k).card ≤ M) :
    ∃ b : Fin (M + 1),
      (assembledShading P Y).shadingMass ≤
        (M + 1) • (coarseLevelBucket P Y M hM b).shading.shadingMass ∧
      (∀ i ∈ (coarseLevelBucket P Y M hM b).indices,
        selectedFiberLevel P Y (P.index.parent i) = b.1) ∧
      (∀ (i : ι) (x : Space),
        x ∈ (coarseLevelBucket P Y M hM b).shading.carrier i →
        P.fiberMultiplicity Y (P.index.parent i) x = b.1) := by
  obtain ⟨b, hb⟩ := exists_weighted_bucket_retaining
    P.index.fine
    (fun i => selectedFiberLevelFin P Y M hM (P.index.parent i))
    (shadingWeight (assembledShading P Y))
  refine ⟨b, ?_, ?_, ?_⟩
  · rw [assembledShading_mass_eq_restrictTo_fine P Y,
      shadingMass_restrictTo_eq_coe_sum_shadingWeight,
      coarseLevelBucket, shadingMass_restrictTo_eq_coe_sum_shadingWeight]
    unfold RetainsBy at hb
    have hb' :
        (∑ i ∈ P.index.fine,
          shadingWeight (assembledShading P Y) i) ≤
          (M + 1) •
            ∑ i ∈ dyadicFiber P.index.fine
              (fun i => selectedFiberLevelFin P Y M hM
                (P.index.parent i)) b,
              shadingWeight (assembledShading P Y) i := by
      simpa using hb
    exact_mod_cast hb'
  · intro i hi
    exact (mem_coarseLevelBucket_indices P Y M hM b i).mp hi |>.2
  · intro i x hx
    have hi : i ∈ (coarseLevelBucket P Y M hM b).indices := by
      by_contra hni
      rw [IndexedShadingRefinement.carrier_eq_empty_of_not_mem
        (coarseLevelBucket P Y M hM b) i hni] at hx
      exact hx
    have hlevel :=
      (mem_coarseLevelBucket_indices P Y M hM b i).mp hi |>.2
    have hxAssembly : x ∈ (assembledShading P Y).carrier i :=
      (coarseLevelBucket P Y M hM b).carrier_subset i hx
    have hif :=
      (mem_coarseLevelBucket_indices P Y M hM b i).mp hi |>.1
    have hiFiber : i ∈ P.index.fiber (P.index.parent i) :=
      (P.index.mem_fiber i (P.index.parent i)).mpr ⟨hif, rfl⟩
    exact (assembledShading_constant_on_fiber P Y
      (P.index.parent i) i hiFiber hxAssembly).trans hlevel

/-- Combining independent fiber selection with the common-level bucket gives
the explicit product loss `(M+1)^2`. -/
theorem exists_common_coarseLevelBucket_from_active
    (P : ConvexFactorization F W) (Y : Shading F) (M : ℕ)
    (hM : ∀ k ∈ P.index.coarse, (P.index.fiber k).card ≤ M) :
    ∃ b : Fin (M + 1),
      (IndexedShadingRefinement.restrictTo Y P.index.fine).shading.shadingMass ≤
        ((M + 1) * (M + 1)) •
          (coarseLevelBucket P Y M hM b).shading.shadingMass ∧
      ∀ (i : ι) (x : Space),
        x ∈ (coarseLevelBucket P Y M hM b).shading.carrier i →
        P.fiberMultiplicity Y (P.index.parent i) x = b.1 := by
  obtain ⟨b, hbMass, hbIndices, hbConst⟩ :=
    exists_common_coarseLevelBucket P Y M hM
  refine ⟨b, ?_, hbConst⟩
  have hFirst := activeShading_mass_le_bound_smul_assembled
    P Y (M + 1) (fun k hk => Nat.succ_le_succ (hM k hk))
  exact WithinFactor.trans hFirst hbMass

end FiberwiseMultiplicityAssembly

end

end Submission.Kakeya.ConvexFactoring
