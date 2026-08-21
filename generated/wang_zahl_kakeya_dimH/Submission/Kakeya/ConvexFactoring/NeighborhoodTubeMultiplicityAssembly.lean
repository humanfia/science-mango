import Submission.Kakeya.ConvexFactoring.FactoringMultiplicityAssembly
import Submission.Kakeya.ConvexFactoring.HeavyParentSelection

/-!
# Selected-parent neighborhood multiplicity assembly

This module pairs an actual fiberwise common-level refinement with a
second restriction by a frozen neighborhood outer statistic.  The frozen
statistic is computed from the first refinement and only counts the same
selected parent set used to define the source fine shading.

The final restriction is not claimed to preserve the neighborhood statistic
when the neighborhood shading is recomputed.  Only the monotone upper bound
needed for the pointwise product estimate is derived.

The mass budget begins with the source shading on the selected parent fibers.  A dense-fiber
witness proved for the source shading is not asserted to survive the final spatial restriction,
and no lower bound for the final neighborhood mass or density is claimed.  The parameterized
constructor uses one cardinality bound on all active fibers; its unconditional specialization
uses the ambient fine-family cardinality.
-/

open scoped ENNReal NNReal
open MeasureTheory Set

namespace Submission.Kakeya.ConvexFactoring

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open StatisticLevelRestriction
open FiberwiseMultiplicityAssembly
open FactoringMultiplicityAssembly
open HeavyParentSelection

noncomputable section

local instance (p : Prop) : Decidable p := Classical.propDecidable p

set_option linter.unusedSectionVars false
set_option linter.unnecessarySimpa false

namespace NeighborhoodTubeMultiplicityAssembly

variable {ι κ : Type*} [Fintype ι] [Fintype κ]
  [DecidableEq ι] [DecidableEq κ]
  {F : ConvexFamily ι} {W : ConvexFamily κ}

/-- Fine indices lying over one fixed set of selected coarse parents. -/
def selectedFineIndices (P : ConvexFactorization F W)
    (parents : Finset κ) : Finset ι :=
  parents.biUnion P.index.fiber

theorem selectedFineIndices_subset_fine
    (P : ConvexFactorization F W) (parents : Finset κ) :
    selectedFineIndices P parents ⊆ P.index.fine := by
  intro i hi
  obtain ⟨k, _hk, hik⟩ := Finset.mem_biUnion.mp hi
  exact P.index.fiber_subset_fine k hik

/-- The source shading supported on exactly the fibers of the selected parents. -/
def selectedParentRefinement (P : ConvexFactorization F W)
    (Y : Shading F) (parents : Finset κ) : IndexedShadingRefinement Y :=
  IndexedShadingRefinement.restrictTo Y (selectedFineIndices P parents)

def selectedParentShading (P : ConvexFactorization F W)
    (Y : Shading F) (parents : Finset κ) : Shading F :=
  (selectedParentRefinement P Y parents).shading

@[simp] theorem selectedParentShading_carrier
    (P : ConvexFactorization F W) (Y : Shading F)
    (parents : Finset κ) (i : ι) :
    (selectedParentShading P Y parents).carrier i =
      if i ∈ selectedFineIndices P parents then Y.carrier i else ∅ :=
  rfl

/-- The selected-parent source mass is exactly the heavy-parent API's sum of
the original fiber masses on the same parent set. -/
theorem selectedParentShading_mass_eq_sum_fiberShadingMass
    (P : ConvexFactorization F W) (Y : Shading F)
    (parents : Finset κ) :
    (selectedParentShading P Y parents).shadingMass =
      ∑ k ∈ parents, HeavyParentSelection.fiberShadingMass P Y k := by
  classical
  rw [selectedParentShading, selectedParentRefinement,
    shadingMass_restrictTo_eq_sum]
  change
    (∑ i ∈ parents.biUnion P.index.fiber, volume (Y.carrier i)) =
      ∑ k ∈ parents, ∑ i ∈ P.index.fiber k, volume (Y.carrier i)
  have hdisjoint :
      Set.PairwiseDisjoint (↑parents : Set κ) P.index.fiber := by
    intro k hk l hl hkl
    change Disjoint (P.index.fiber k) (P.index.fiber l)
    rw [Finset.disjoint_left]
    intro i hik hil
    have hpik := (P.index.mem_fiber i k).mp hik |>.2
    have hpil := (P.index.mem_fiber i l).mp hil |>.2
    exact hkl (hpik.symm.trans hpil)
  rw [Finset.sum_biUnion hdisjoint]

/-- Restriction to all active fine indices changes no selected-parent mass. -/
theorem selectedParentShading_mass_eq_restrictTo_fine
    (P : ConvexFactorization F W) (Y : Shading F)
    (parents : Finset κ) :
    (selectedParentShading P Y parents).shadingMass =
      (IndexedShadingRefinement.restrictTo
        (selectedParentShading P Y parents) P.index.fine).shading.shadingMass := by
  classical
  unfold Shading.shadingMass
  apply Finset.sum_congr rfl
  intro i hi
  rw [IndexedShadingRefinement.restrictTo_carrier]
  by_cases hif : i ∈ P.index.fine
  · rw [if_pos hif]
  · have hnotSelected : i ∉ selectedFineIndices P parents :=
      fun hisel => hif (selectedFineIndices_subset_fine P parents hisel)
    rw [if_neg hif, selectedParentShading_carrier, if_neg hnotSelected]

/-- The coarse neighborhood shading with all unselected parent carriers
replaced by the empty set, while retaining the original coarse index type. -/
def parentRestrictedNeighborhoodShading
    (P : ConvexFactorization F W) (parents : Finset κ)
    (Z : Shading F) (r : ℝ) : Shading W :=
  (IndexedShadingRefinement.restrictTo
    (P.neighborhoodInducedShading Z r) parents).shading

/-- The neighborhood outer statistic frozen before the second restriction. -/
def frozenNeighborhoodOuterStatistic
    (P : ConvexFactorization F W) (parents : Finset κ)
    (Z : Shading F) (r : ℝ) (x : Space) : ℕ :=
  (parentRestrictedNeighborhoodShading P parents Z r).pointMultiplicity x

theorem measurableSet_frozenNeighborhoodOuterStatistic_eq
    (P : ConvexFactorization F W) (parents : Finset κ)
    (Z : Shading F) (r : ℝ) (n : ℕ) :
    MeasurableSet {x | frozenNeighborhoodOuterStatistic P parents Z r x = n} :=
  measurableSet_pointMultiplicity_eq
    (parentRestrictedNeighborhoodShading P parents Z r) n

theorem frozenNeighborhoodOuterStatistic_le_card
    (P : ConvexFactorization F W) (parents : Finset κ)
    (Z : Shading F) (r : ℝ) (x : Space) :
    frozenNeighborhoodOuterStatistic P parents Z r x ≤ parents.card := by
  rw [frozenNeighborhoodOuterStatistic,
    parentRestrictedNeighborhoodShading,
    IndexedShadingRefinement.pointMultiplicity_restrictTo]
  unfold IndexedShadingRefinement.restrictedPointMultiplicity
  exact Finset.card_le_card (Finset.filter_subset _ _)

/-- Freeze the selected-parent neighborhood statistic of the first shading,
then restrict it to one level.  The return type deliberately records no
equality for the recomputed neighborhood shading. -/
def freezeThenRestrictNeighborhoodLevel
    (P : ConvexFactorization F W) (parents : Finset κ) (r : ℝ)
    {Y : Shading F} (R : IndexedShadingRefinement Y) (n : ℕ) :
    IndexedShadingRefinement Y :=
  refinementRestrictStatisticLevel R
    (frozenNeighborhoodOuterStatistic P parents R.shading r)
    (measurableSet_frozenNeighborhoodOuterStatistic_eq
      P parents R.shading r) n

/-- Repackage the existing common fiber-level bucket with the exact selected
fine support, without changing its shading. -/
def selectedFiberLevelRefinement
    (P : ConvexFactorization F W) (Y : Shading F)
    (parents : Finset κ) (M : ℕ)
    (hM : ∀ k ∈ P.index.coarse, (P.index.fiber k).card ≤ M)
    (b : Fin (M + 1)) :
    IndexedShadingRefinement (selectedParentShading P Y parents) where
  indices := selectedFineIndices P parents
  shading :=
    (coarseLevelBucket P (selectedParentShading P Y parents) M hM b).shading
  carrier_subset i :=
    ((coarseLevelBucket P (selectedParentShading P Y parents)
      M hM b).carrier_subset i).trans
      (assembledShading_carrier_subset
        P (selectedParentShading P Y parents) i)
  carrier_eq_empty_of_not_mem i hi := by
    apply Set.Subset.antisymm
    · intro x hx
      have hxSource :
          x ∈ (selectedParentShading P Y parents).carrier i :=
        ((coarseLevelBucket P (selectedParentShading P Y parents)
          M hM b).carrier_subset i hx) |>
          assembledShading_carrier_subset
            P (selectedParentShading P Y parents) i
      simpa [selectedParentShading_carrier, hi] using hxSource
    · exact Set.empty_subset _

/-- Data retained by the paired selected-parent assembly.  Neither the
pointwise product estimate nor any recomputed-neighborhood equality is a
field. -/
structure Assembly
    (P : ConvexFactorization F W) (Y : Shading F)
    (parents : Finset κ) (r : ℝ) (M : ℕ) where
  parents_subset_coarse : parents ⊆ P.index.coarse
  fiberLevel : ℕ
  outerLevel : ℕ
  fiberLevel_le : fiberLevel ≤ M
  outerLevel_le : outerLevel ≤ parents.card
  fiberRefinement :
    IndexedShadingRefinement (selectedParentShading P Y parents)
  fiber_indices_eq :
    fiberRefinement.indices = selectedFineIndices P parents
  fiber_retained :
    WithinFactor ((M + 1) * (M + 1))
      (selectedParentShading P Y parents).shadingMass
      fiberRefinement.shading.shadingMass
  fiberStatistic_constant :
    ∀ (i : ι) (x : Space),
      x ∈ fiberRefinement.shading.carrier i →
        P.fiberMultiplicity (selectedParentShading P Y parents)
          (P.index.parent i) x = fiberLevel
  outer_retained :
    WithinFactor (parents.card + 1)
      fiberRefinement.shading.shadingMass
      (freezeThenRestrictNeighborhoodLevel
        P parents r fiberRefinement outerLevel).shading.shadingMass

namespace Assembly

variable {P : ConvexFactorization F W} {Y : Shading F}
  {parents : Finset κ} {r : ℝ} {M : ℕ}

/-- The one final refinement paired with the frozen pre-outer refinement. -/
def finalRefinement (A : Assembly P Y parents r M) :
    IndexedShadingRefinement (selectedParentShading P Y parents) :=
  freezeThenRestrictNeighborhoodLevel
    P parents r A.fiberRefinement A.outerLevel

/-- The final refinement lifted back to the original shading. -/
def fullRefinement (A : Assembly P Y parents r M) :
    IndexedShadingRefinement Y :=
  refinementTrans (selectedParentRefinement P Y parents) A.finalRefinement

@[simp] theorem finalRefinement_indices
    (A : Assembly P Y parents r M) :
    A.finalRefinement.indices = selectedFineIndices P parents := by
  rw [finalRefinement, freezeThenRestrictNeighborhoodLevel,
    refinementRestrictStatisticLevel, A.fiber_indices_eq]

/-- The two genuine retention steps combine into one explicit budget. -/
theorem retained (A : Assembly P Y parents r M) :
    WithinFactor
      (((M + 1) * (M + 1)) * (parents.card + 1))
      (selectedParentShading P Y parents).shadingMass
      A.finalRefinement.shading.shadingMass :=
  WithinFactor.trans A.fiber_retained A.outer_retained

/-- A selected-fiber mass budget, such as the one returned by heavy-parent
pigeonholing, composes with both assembly stages on the identical parent set. -/
theorem retained_from_selectedFiberMass
    (A : Assembly P Y parents r M) (parentLoss : ℕ)
    (originalMass : ℝ≥0∞)
    (hselected : WithinFactor parentLoss originalMass
      (∑ k ∈ parents, HeavyParentSelection.fiberShadingMass P Y k)) :
    WithinFactor
      (parentLoss * (((M + 1) * (M + 1)) * (parents.card + 1)))
      originalMass A.finalRefinement.shading.shadingMass := by
  have hsource : WithinFactor parentLoss originalMass
      (selectedParentShading P Y parents).shadingMass := by
    simpa only [selectedParentShading_mass_eq_sum_fiberShadingMass] using
      hselected
  exact WithinFactor.trans hsource A.retained

/-- The frozen selected-parent neighborhood statistic is exactly constant on
the final shaded union. -/
theorem frozenOuterStatistic_constant
    (A : Assembly P Y parents r M) {x : Space}
    (hx : x ∈ A.finalRefinement.shading.shadedUnion) :
    frozenNeighborhoodOuterStatistic
      P parents A.fiberRefinement.shading r x = A.outerLevel := by
  exact statistic_eq_on_restrictStatisticLevel
    A.fiberRefinement.shading
    (frozenNeighborhoodOuterStatistic
      P parents A.fiberRefinement.shading r)
    (measurableSet_frozenNeighborhoodOuterStatistic_eq
      P parents A.fiberRefinement.shading r)
    A.outerLevel hx

/-- Final fiber multiplicity is monotone below the selected-parent source
fiber multiplicity. -/
theorem fiberMultiplicity_final_le_source
    (A : Assembly P Y parents r M) (k : κ) (x : Space) :
    P.fiberMultiplicity A.finalRefinement.shading k x ≤
      P.fiberMultiplicity (selectedParentShading P Y parents) k x := by
  classical
  unfold ConvexFactorization.fiberMultiplicity
  apply Finset.card_le_card
  intro i hi
  rw [Finset.mem_filter] at hi ⊢
  exact ⟨hi.1, A.finalRefinement.carrier_subset i hi.2⟩

/-- Every final active fiber is bounded by the selected common fiber level. -/
theorem fiberMultiplicity_final_le_fiberLevel
    (A : Assembly P Y parents r M)
    (k : κ) (_hk : k ∈ P.index.coarse) (x : Space) :
    P.fiberMultiplicity A.finalRefinement.shading k x ≤ A.fiberLevel := by
  by_cases hzero :
      P.fiberMultiplicity A.finalRefinement.shading k x = 0
  · simp [hzero]
  · have hpos :
        0 < P.fiberMultiplicity A.finalRefinement.shading k x :=
      Nat.pos_of_ne_zero hzero
    have hxInduced :
        x ∈ (P.inducedShading A.finalRefinement.shading).carrier k :=
      (P.mem_inducedShading_iff_fiberMultiplicity_pos
        A.finalRefinement.shading k x).2 hpos
    obtain ⟨_hk', i, hiFiber, hxi⟩ :=
      (P.mem_inducedShading_carrier_iff
        A.finalRefinement.shading k x).1 hxInduced
    have hp : P.index.parent i = k :=
      (P.index.mem_fiber i k).1 hiFiber |>.2
    have hxPre :
        x ∈ A.fiberRefinement.shading.carrier i := by
      exact refinementRestrictStatisticLevel_carrier_subset_source
        A.fiberRefinement
        (frozenNeighborhoodOuterStatistic
          P parents A.fiberRefinement.shading r)
        (measurableSet_frozenNeighborhoodOuterStatistic_eq
          P parents A.fiberRefinement.shading r)
        A.outerLevel i hxi
    calc
      P.fiberMultiplicity A.finalRefinement.shading k x ≤
          P.fiberMultiplicity (selectedParentShading P Y parents) k x :=
        A.fiberMultiplicity_final_le_source k x
      _ = A.fiberLevel := by
        simpa [hp] using A.fiberStatistic_constant i x hxPre

/-- Final ordinary point multiplicity equals factorization fine multiplicity,
because all final carriers are supported over the selected parent fibers. -/
theorem pointMultiplicity_final_eq_fineMultiplicity
    (A : Assembly P Y parents r M) (x : Space) :
    A.finalRefinement.shading.pointMultiplicity x =
      P.fineMultiplicity A.finalRefinement.shading x := by
  classical
  unfold Shading.pointMultiplicity ConvexFactorization.fineMultiplicity
  apply congrArg Finset.card
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro hxi
    have hsource :
        x ∈ (selectedParentShading P Y parents).carrier i :=
      A.finalRefinement.carrier_subset i hxi
    have hisel : i ∈ selectedFineIndices P parents := by
      by_cases hi : i ∈ selectedFineIndices P parents
      · exact hi
      · simp [selectedParentShading_carrier, hi] at hsource
    exact ⟨selectedFineIndices_subset_fine P parents hisel, hxi⟩
  · exact fun hi => hi.2

/-- A neighborhood carrier of the pre-outer refinement is empty outside the
same selected parent set. -/
theorem fiberNeighborhood_carrier_eq_empty_of_not_mem
    (A : Assembly P Y parents r M) {k : κ} (hk : k ∉ parents) :
    (P.neighborhoodInducedShading A.fiberRefinement.shading r).carrier k = ∅ := by
  apply Set.Subset.antisymm
  · intro x hx
    obtain ⟨_hxW, y, hyFiber, _hxy⟩ :=
      (P.mem_neighborhoodInducedShading_carrier_iff
        A.fiberRefinement.shading r k x).1 hx
    obtain ⟨i, hyi⟩ := Set.mem_iUnion.mp hyFiber
    have hySource :
        y ∈ (selectedParentShading P Y parents).carrier i.1 :=
      A.fiberRefinement.carrier_subset i.1 hyi
    have hiSelected : i.1 ∈ selectedFineIndices P parents := by
      by_cases hi : i.1 ∈ selectedFineIndices P parents
      · exact hi
      · simp [selectedParentShading_carrier, hi] at hySource
    obtain ⟨l, hl, hil⟩ := Finset.mem_biUnion.mp hiSelected
    have hpik : P.index.parent i.1 = k :=
      (P.index.mem_fiber i.1 k).1 i.2 |>.2
    have hpil : P.index.parent i.1 = l :=
      (P.index.mem_fiber i.1 l).1 hil |>.2
    have hlk : l = k := hpil.symm.trans hpik
    exact (hk (hlk ▸ hl)).elim
  · exact Set.empty_subset _

/-- On the pre-outer refinement, counting all coarse indices equals counting
only the selected parents. -/
theorem neighborhoodPointMultiplicity_eq_frozen
    (A : Assembly P Y parents r M) (x : Space) :
    (P.neighborhoodInducedShading
      A.fiberRefinement.shading r).pointMultiplicity x =
        frozenNeighborhoodOuterStatistic
          P parents A.fiberRefinement.shading r x := by
  classical
  unfold frozenNeighborhoodOuterStatistic
  unfold Shading.pointMultiplicity
  apply congrArg Finset.card
  ext k
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [parentRestrictedNeighborhoodShading,
    IndexedShadingRefinement.restrictTo_carrier]
  by_cases hk : k ∈ parents
  · simp [hk]
  · rw [if_neg hk, A.fiberNeighborhood_carrier_eq_empty_of_not_mem hk]

/-- Recomputed final neighborhood multiplicity is only bounded above by the
frozen selected-parent statistic; no equality is asserted. -/
theorem recomputedNeighborhoodOuterMultiplicity_le_frozen
    (A : Assembly P Y parents r M) (x : Space) :
    P.neighborhoodOuterMultiplicity A.finalRefinement.shading r x ≤
      frozenNeighborhoodOuterStatistic
        P parents A.fiberRefinement.shading r x := by
  rw [← pointMultiplicity_neighborhoodInducedShading_eq_outer]
  calc
    (P.neighborhoodInducedShading
        A.finalRefinement.shading r).pointMultiplicity x ≤
        (P.neighborhoodInducedShading
          A.fiberRefinement.shading r).pointMultiplicity x := by
      simpa [finalRefinement, freezeThenRestrictNeighborhoodLevel,
        refinementRestrictStatisticLevel, restrictStatisticLevel] using
        (pointMultiplicity_neighborhoodInducedShading_restrictSet_le
          P A.fiberRefinement.shading
          (statisticSlice A.fiberRefinement.shading
            (frozenNeighborhoodOuterStatistic
              P parents A.fiberRefinement.shading r) A.outerLevel)
          (measurableSet_statisticSlice
            A.fiberRefinement.shading
            (frozenNeighborhoodOuterStatistic
              P parents A.fiberRefinement.shading r)
            (measurableSet_frozenNeighborhoodOuterStatistic_eq
              P parents A.fiberRefinement.shading r)
            A.outerLevel)
          r x)
    _ = frozenNeighborhoodOuterStatistic
          P parents A.fiberRefinement.shading r x :=
      A.neighborhoodPointMultiplicity_eq_frozen x

/-- The final fine point multiplicity is bounded by the product of the frozen
selected-parent outer level and the common parent-fiber level. -/
theorem pointMultiplicity_le_product
    (A : Assembly P Y parents r M) (hr : 0 < r) (x : Space) :
    A.finalRefinement.shading.pointMultiplicity x ≤
      A.outerLevel * A.fiberLevel := by
  by_cases hx : x ∈ A.finalRefinement.shading.shadedUnion
  · rw [A.pointMultiplicity_final_eq_fineMultiplicity x]
    calc
      P.fineMultiplicity A.finalRefinement.shading x ≤
          P.neighborhoodOuterMultiplicity
              A.finalRefinement.shading r x * A.fiberLevel :=
        P.fineMultiplicity_le_neighborhoodOuter_mul
          A.finalRefinement.shading hr x A.fiberLevel
          (fun k hk => A.fiberMultiplicity_final_le_fiberLevel k hk x)
      _ ≤ frozenNeighborhoodOuterStatistic
            P parents A.fiberRefinement.shading r x * A.fiberLevel :=
        Nat.mul_le_mul_right A.fiberLevel
          (A.recomputedNeighborhoodOuterMultiplicity_le_frozen x)
      _ = A.outerLevel * A.fiberLevel := by
        rw [A.frozenOuterStatistic_constant hx]
  · have hzero : A.finalRefinement.shading.pointMultiplicity x = 0 := by
      apply Nat.eq_zero_of_not_pos
      intro hpos
      exact hx
        ((A.finalRefinement.shading.pointMultiplicity_pos_iff_mem_shadedUnion x).1
          hpos)
    simp [hzero]

/-- Integrated division-free consequence of the pointwise product bound. -/
theorem shadingMass_le_product_nsmul_volume
    (A : Assembly P Y parents r M) (hr : 0 < r) :
    A.finalRefinement.shading.shadingMass ≤
      (A.outerLevel * A.fiberLevel) •
        volume A.finalRefinement.shading.shadedUnion :=
  FactoringMultiplicityAssembly.ExactAssembly.shadingMass_le_nsmul_volume_shadedUnion_of_pointMultiplicity_le
      A.finalRefinement.shading (A.outerLevel * A.fiberLevel)
      (A.pointMultiplicity_le_product hr)

end Assembly

/-- Actual fiberwise selection followed by actual frozen neighborhood-level
selection constructs the paired assembly on any selected active parent set. -/
theorem exists_assembly_of_fiber_card_le
    (P : ConvexFactorization F W) (Y : Shading F)
    (parents : Finset κ) (hparents : parents ⊆ P.index.coarse)
    (r : ℝ) (M : ℕ)
    (hM : ∀ k ∈ P.index.coarse, (P.index.fiber k).card ≤ M) :
    Nonempty (Assembly P Y parents r M) := by
  let Ysel := selectedParentShading P Y parents
  obtain ⟨b, hFiberMass, hFiberConst⟩ :=
    exists_common_coarseLevelBucket_from_active P Ysel M hM
  let R₀ : IndexedShadingRefinement Ysel :=
    selectedFiberLevelRefinement P Y parents M hM b
  let stat : Space → ℕ :=
    frozenNeighborhoodOuterStatistic P parents R₀.shading r
  have hstat : ∀ n, MeasurableSet {x | stat x = n} := by
    intro n
    exact measurableSet_frozenNeighborhoodOuterStatistic_eq
      P parents R₀.shading r n
  have hbound : ∀ x ∈ R₀.shading.shadedUnion, stat x ≤ parents.card := by
    intro x hx
    exact frozenNeighborhoodOuterStatistic_le_card
      P parents R₀.shading r x
  obtain ⟨m, hm, hOuterMass, _hOuterConst⟩ :=
    exists_restrictStatisticLevel_with_large_mass
      R₀.shading stat parents.card hstat hbound
  refine ⟨{
    parents_subset_coarse := hparents
    fiberLevel := b.1
    outerLevel := m
    fiberLevel_le := Nat.le_of_lt_succ b.isLt
    outerLevel_le := Nat.le_of_lt_succ (Finset.mem_range.mp hm)
    fiberRefinement := R₀
    fiber_indices_eq := rfl
    fiber_retained := ?_
    fiberStatistic_constant := ?_
    outer_retained := ?_ }⟩
  · unfold WithinFactor
    rw [selectedParentShading_mass_eq_restrictTo_fine P Y parents]
    simpa [Ysel, R₀, selectedFiberLevelRefinement] using hFiberMass
  · intro i x hx
    simpa [Ysel, R₀, selectedFiberLevelRefinement] using
      hFiberConst i x hx
  · unfold WithinFactor
    simpa [stat, R₀, freezeThenRestrictNeighborhoodLevel,
      refinementRestrictStatisticLevel] using hOuterMass

/-- Unconditional finite-family form, using the ambient fine-cardinality
bound for every selected parent fiber. -/
theorem exists_assembly
    (P : ConvexFactorization F W) (Y : Shading F)
    (parents : Finset κ) (hparents : parents ⊆ P.index.coarse)
    (r : ℝ) :
    Nonempty (Assembly P Y parents r (Fintype.card ι)) := by
  apply exists_assembly_of_fiber_card_le
    P Y parents hparents r (Fintype.card ι)
  intro k hk
  exact Finset.card_le_card (Finset.subset_univ _)

/-- Heavy selection and its finite label bucket compose with the paired
assembly into one explicit total retention budget on the same parent set. -/
theorem exists_heavyParentLabel_bucket_assembly
    {β : Type*} [DecidableEq β] [Fintype β] [Nonempty β]
    (P : ConvexFactorization F W) (Y : Shading F)
    (lambda L : ℝ≥0∞) (label : κ → β)
    (hL0 : L ≠ 0) (hLtop : L ≠ ∞)
    (hglobal :
      lambda * activeBodyMass P ≤ L * activeShadingMass P Y)
    (r : ℝ) :
    ∃ b : β,
      let parents := dyadicFiber (heavyParents P Y lambda L) label b
      ∃ A : Assembly P Y parents r (Fintype.card ι),
        WithinFactor
          ((2 * Fintype.card β) *
            (((Fintype.card ι + 1) * (Fintype.card ι + 1)) *
              (parents.card + 1)))
          (activeShadingMass P Y)
          A.finalRefinement.shading.shadingMass := by
  obtain ⟨b, hb⟩ :=
    exists_heavyParentLabel_bucket_withinFactor
      P Y lambda L label hL0 hLtop hglobal
  let parents := dyadicFiber (heavyParents P Y lambda L) label b
  have hparents : parents ⊆ P.index.coarse := by
    intro k hk
    have hkHeavy : k ∈ heavyParents P Y lambda L :=
      ((mem_dyadicFiber (heavyParents P Y lambda L) label b k).1 hk).1
    exact (Finset.mem_filter.mp hkHeavy).1
  obtain ⟨A⟩ := exists_assembly P Y parents hparents r
  refine ⟨b, A, ?_⟩
  change WithinFactor (2 * Fintype.card β)
    (activeShadingMass P Y)
    (∑ k ∈ parents, HeavyParentSelection.fiberShadingMass P Y k) at hb
  exact A.retained_from_selectedFiberMass (2 * Fintype.card β)
    (activeShadingMass P Y) hb

/-- Any finite label bucket of the heavy-parent set is a valid selected parent
set for the same assembly constructor. -/
theorem exists_assembly_on_heavyParentLabel_bucket
    {β : Type*} [DecidableEq β]
    (P : ConvexFactorization F W) (Y : Shading F)
    (lambda L : ℝ≥0∞) (label : κ → β) (b : β) (r : ℝ) :
    Nonempty
      (Assembly P Y
        (dyadicFiber (heavyParents P Y lambda L) label b)
        r (Fintype.card ι)) := by
  apply exists_assembly P Y
  intro k hk
  have hkHeavy : k ∈ heavyParents P Y lambda L :=
    ((mem_dyadicFiber (heavyParents P Y lambda L) label b k).1 hk).1
  exact (Finset.mem_filter.mp hkHeavy).1

end NeighborhoodTubeMultiplicityAssembly

end

end Submission.Kakeya.ConvexFactoring
