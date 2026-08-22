import Submission.Kakeya.ConvexFactoring.NeighborhoodTubeMultiplicityAssembly

/-!
# Heavy-parent selection after neighborhood multiplicity assembly

The neighborhood assembly is first run on every active coarse parent.  Heavy
parent selection is then rerun on that actual final shading, with the density
loss amplified by the assembly retention factor.  The selected heavy bucket
is implemented as one further index restriction.

Consequently, mass retention, the dense-fiber witness, the frozen two-level
statistics, and the recomputed multiplicity product bound all concern the
same final shading.  Exact frozen statistics survive by subset containment;
recomputed fiber and neighborhood statistics are only asserted to decrease.
No induced-density conclusion is claimed here.
-/

open scoped ENNReal NNReal
open MeasureTheory Set

namespace Submission.Kakeya.ConvexFactoring

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open HeavyParentSelection
open NeighborhoodTubeMultiplicityAssembly
open StatisticLevelRestriction
open FactoringMultiplicityAssembly

noncomputable section

local instance (p : Prop) : Decidable p := Classical.propDecidable p

set_option linter.unusedSectionVars false
set_option linter.unnecessarySimpa false

namespace PostAssemblyHeavySelection

variable {ι κ : Type*} [Fintype ι] [Fintype κ]
  [DecidableEq ι] [DecidableEq κ]
  {F : ConvexFamily ι} {W : ConvexFamily κ}

/-- The loss of the two multiplicity-level restrictions when the first
assembly uses every active coarse parent. -/
def assemblyLoss (P : ConvexFactorization F W) (M : ℕ) : ℕ :=
  ((M + 1) * (M + 1)) * (P.index.coarse.card + 1)

/-- The density loss used when heavy selection is rerun after assembly. -/
def amplifiedLoss (P : ConvexFactorization F W) (M : ℕ)
    (L : ℝ≥0∞) : ℝ≥0∞ :=
  (assemblyLoss P M : ℝ≥0∞) * L

@[simp] theorem selectedFineIndices_active
    (P : ConvexFactorization F W) :
    selectedFineIndices P P.index.coarse = P.index.fine := by
  exact P.index.biUnion_fiber_eq_fine

theorem selectedParentShading_active_mass
    (P : ConvexFactorization F W) (Y : Shading F) :
    (selectedParentShading P Y P.index.coarse).shadingMass =
      activeShadingMass P Y := by
  rw [selectedParentShading_mass_eq_sum_fiberShadingMass,
    activeShadingMass_eq_sum_fiberShadingMass]

/-- On an active fiber, restricting the source shading to all active parents
does not change fiber multiplicity. -/
theorem fiberMultiplicity_selectedParentShading_active_eq
    (P : ConvexFactorization F W) (Y : Shading F) (k : κ) (x : Space) :
    P.fiberMultiplicity
        (selectedParentShading P Y P.index.coarse) k x =
      P.fiberMultiplicity Y k x := by
  classical
  unfold ConvexFactorization.fiberMultiplicity
  apply congrArg Finset.card
  ext i
  simp only [Finset.mem_filter]
  have hselected_of_fiber : i ∈ P.index.fiber k →
      i ∈ selectedFineIndices P P.index.coarse := by
    intro hiFiber
    rw [selectedFineIndices_active]
    exact P.index.fiber_subset_fine k hiFiber
  constructor
  · rintro ⟨hiFiber, hxi⟩
    refine ⟨hiFiber, ?_⟩
    rw [selectedParentShading_carrier,
      if_pos (hselected_of_fiber hiFiber)] at hxi
    exact hxi
  · rintro ⟨hiFiber, hxi⟩
    refine ⟨hiFiber, ?_⟩
    rw [selectedParentShading_carrier,
      if_pos (hselected_of_fiber hiFiber)]
    exact hxi

/-- A shading supported on the active fine set has active mass equal to its
ordinary shading mass. -/
theorem activeShadingMass_eq_shadingMass_of_supported
    (P : ConvexFactorization F W) (Z : Shading F)
    (hsupport : ∀ i, i ∉ P.index.fine → Z.carrier i = ∅) :
    activeShadingMass P Z = Z.shadingMass := by
  classical
  unfold activeShadingMass Shading.shadingMass
  apply Finset.sum_subset (Finset.subset_univ _)
  intro i _hiUniv hiFine
  rw [hsupport i hiFine]
  simp

namespace PostAssemblyLemmas

variable {P : ConvexFactorization F W} {Y : Shading F}
  {r : ℝ} {M : ℕ}

theorem final_carrier_eq_empty_of_not_fine
    (A : Assembly P Y P.index.coarse r M) (i : ι)
    (hi : i ∉ P.index.fine) :
    A.finalRefinement.shading.carrier i = ∅ := by
  apply A.finalRefinement.carrier_eq_empty_of_not_mem i
  rw [A.finalRefinement_indices, selectedFineIndices_active]
  exact hi

theorem activeShadingMass_final_eq
    (A : Assembly P Y P.index.coarse r M) :
    activeShadingMass P A.finalRefinement.shading =
      A.finalRefinement.shading.shadingMass :=
  activeShadingMass_eq_shadingMass_of_supported P A.finalRefinement.shading
    (final_carrier_eq_empty_of_not_fine A)

theorem active_retained
    (A : Assembly P Y P.index.coarse r M) :
    WithinFactor (assemblyLoss P M)
      (activeShadingMass P Y)
      A.finalRefinement.shading.shadingMass := by
  simpa only [assemblyLoss, selectedParentShading_active_mass] using A.retained

end PostAssemblyLemmas

theorem assemblyLoss_pos (P : ConvexFactorization F W) (M : ℕ) :
    0 < assemblyLoss P M := by
  unfold assemblyLoss
  positivity

theorem amplifiedLoss_ne_zero
    (P : ConvexFactorization F W) (M : ℕ) {L : ℝ≥0∞}
    (hL0 : L ≠ 0) :
    amplifiedLoss P M L ≠ 0 := by
  unfold amplifiedLoss
  apply mul_ne_zero
  · exact_mod_cast (assemblyLoss_pos P M).ne'
  · exact hL0

theorem amplifiedLoss_ne_top
    (P : ConvexFactorization F W) (M : ℕ) {L : ℝ≥0∞}
    (hLtop : L ≠ ∞) :
    amplifiedLoss P M L ≠ ∞ := by
  unfold amplifiedLoss
  exact ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) hLtop

/-- The original density cross inequality survives assembly after multiplying
the loss by the actual assembly retention factor. -/
theorem global_density_after_assembly
    (P : ConvexFactorization F W) (Y : Shading F)
    (lambda L : ℝ≥0∞) {r : ℝ} {M : ℕ}
    (A : Assembly P Y P.index.coarse r M)
    (hglobal :
      lambda * activeBodyMass P ≤ L * activeShadingMass P Y) :
    lambda * activeBodyMass P ≤
      amplifiedLoss P M L *
        activeShadingMass P A.finalRefinement.shading := by
  have hret := PostAssemblyLemmas.active_retained A
  unfold WithinFactor at hret
  calc
    lambda * activeBodyMass P ≤ L * activeShadingMass P Y := hglobal
    _ ≤ L * (assemblyLoss P M •
        A.finalRefinement.shading.shadingMass) :=
      mul_le_mul' le_rfl hret
    _ = amplifiedLoss P M L *
        activeShadingMass P A.finalRefinement.shading := by
      rw [PostAssemblyLemmas.activeShadingMass_final_eq A]
      simp only [amplifiedLoss, nsmul_eq_mul]
      ac_rfl

/-- Restrict a shading to the fine fibers of a post-assembly heavy bucket. -/
def postHeavyParents
    {β : Type*} [DecidableEq β]
    (P : ConvexFactorization F W)
    {Y : Shading F} {r : ℝ} {M : ℕ}
    (A : Assembly P Y P.index.coarse r M)
    (lambda L : ℝ≥0∞) (label : κ → β) (b : β) : Finset κ :=
  dyadicFiber
    (heavyParents P A.finalRefinement.shading
      lambda (amplifiedLoss P M L)) label b

def postHeavyRefinement
    {β : Type*} [DecidableEq β]
    (P : ConvexFactorization F W)
    {Y : Shading F} {r : ℝ} {M : ℕ}
    (A : Assembly P Y P.index.coarse r M)
    (lambda L : ℝ≥0∞) (label : κ → β) (b : β) :
    IndexedShadingRefinement A.finalRefinement.shading :=
  selectedParentRefinement P A.finalRefinement.shading
    (postHeavyParents P A lambda L label b)

theorem postHeavyParents_subset_coarse
    {β : Type*} [DecidableEq β]
    (P : ConvexFactorization F W)
    {Y : Shading F} {r : ℝ} {M : ℕ}
    (A : Assembly P Y P.index.coarse r M)
    (lambda L : ℝ≥0∞) (label : κ → β) (b : β) :
    postHeavyParents P A lambda L label b ⊆ P.index.coarse := by
  intro k hk
  have hkHeavy :
      k ∈ heavyParents P A.finalRefinement.shading
        lambda (amplifiedLoss P M L) :=
    (mem_dyadicFiber
      (heavyParents P A.finalRefinement.shading
        lambda (amplifiedLoss P M L)) label b k).1 hk |>.1
  exact (Finset.mem_filter.mp hkHeavy).1

/-- Dense witnesses are unchanged by selecting exactly the parent fibers on
which the witnesses live. -/
theorem hasDenseFiberWitness_selectedParentShading
    (P : ConvexFactorization F W) (Z : Shading F)
    (parents : Finset κ) (lambda loss : ℝ≥0∞)
    (h : HasDenseFiberWitness P Z parents lambda loss) :
    HasDenseFiberWitness P
      (selectedParentShading P Z parents) parents lambda loss := by
  intro k hk
  obtain ⟨i, hiFiber, hi⟩ := h k hk
  refine ⟨i, hiFiber, ?_⟩
  have hiSelected : i ∈ selectedFineIndices P parents :=
    Finset.mem_biUnion.mpr ⟨k, hk, hiFiber⟩
  simpa [selectedParentShading_carrier, hiSelected] using hi

/-- Positive retained mass forces a selected parent set to be nonempty. -/
theorem selectedParents_nonempty_of_retained
    (P : ConvexFactorization F W) (Z : Shading F)
    (parents : Finset κ) (loss : ℕ) (original : ℝ≥0∞)
    (horiginal : original ≠ 0)
    (hretained : WithinFactor loss original
      (selectedParentShading P Z parents).shadingMass) :
    parents.Nonempty := by
  by_contra hnot
  have hempty : parents = ∅ :=
    Finset.not_nonempty_iff_eq_empty.mp hnot
  have hmass :
      (selectedParentShading P Z parents).shadingMass = 0 := by
    rw [selectedParentShading_mass_eq_sum_fiberShadingMass, hempty]
    simp
  have hle : original ≤ 0 := by
    simpa [WithinFactor, hmass] using hretained
  exact horiginal (nonpos_iff_eq_zero.mp hle)

/-- Fiber unions are monotone under any pointwise carrier refinement. -/
theorem fiberShadedUnion_mono
    (P : ConvexFactorization F W) {Z Z' : Shading F}
    (hsub : ∀ i, Z'.carrier i ⊆ Z.carrier i) (k : κ) :
    P.fiberShadedUnion Z' k ⊆ P.fiberShadedUnion Z k := by
  intro x hx
  obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hx
  exact Set.mem_iUnion.mpr ⟨i, hsub i.1 hxi⟩

/-- Neighborhood-induced carriers are monotone under pointwise carrier
refinement. -/
theorem neighborhoodInducedShading_carrier_mono
    (P : ConvexFactorization F W) {Z Z' : Shading F}
    (hsub : ∀ i, Z'.carrier i ⊆ Z.carrier i)
    (r : ℝ) (k : κ) :
    (P.neighborhoodInducedShading Z' r).carrier k ⊆
      (P.neighborhoodInducedShading Z r).carrier k := by
  intro x hx
  exact ⟨hx.1, Metric.thickening_subset_of_subset r
    (fiberShadedUnion_mono P hsub k) hx.2⟩

theorem neighborhoodOuterMultiplicity_mono
    (P : ConvexFactorization F W) {Z Z' : Shading F}
    (hsub : ∀ i, Z'.carrier i ⊆ Z.carrier i)
    (r : ℝ) (x : Space) :
    P.neighborhoodOuterMultiplicity Z' r x ≤
      P.neighborhoodOuterMultiplicity Z r x := by
  classical
  unfold ConvexFactorization.neighborhoodOuterMultiplicity
  apply Finset.card_le_card
  intro k hk
  rw [Finset.mem_filter] at hk ⊢
  exact ⟨hk.1,
    neighborhoodInducedShading_carrier_mono P hsub r k hk.2⟩

theorem fiberMultiplicity_mono
    (P : ConvexFactorization F W) {Z Z' : Shading F}
    (hsub : ∀ i, Z'.carrier i ⊆ Z.carrier i)
    (k : κ) (x : Space) :
    P.fiberMultiplicity Z' k x ≤ P.fiberMultiplicity Z k x := by
  classical
  unfold ConvexFactorization.fiberMultiplicity
  apply Finset.card_le_card
  intro i hi
  rw [Finset.mem_filter] at hi ⊢
  exact ⟨hi.1, hsub i hi.2⟩

namespace PostAssemblyLemmas

variable {P : ConvexFactorization F W} {Y : Shading F}
  {r : ℝ} {M : ℕ}
  {β : Type*} [DecidableEq β]

theorem postHeavy_frozenOuterStatistic_constant
    (A : Assembly P Y P.index.coarse r M)
    (lambda L : ℝ≥0∞) (label : κ → β) (b : β)
    {x : Space}
    (hx : x ∈
      (postHeavyRefinement P A lambda L label b).shading.shadedUnion) :
    frozenNeighborhoodOuterStatistic P P.index.coarse
      A.fiberRefinement.shading r x = A.outerLevel := by
  apply A.frozenOuterStatistic_constant
  exact (postHeavyRefinement P A lambda L label b).shadedUnion_subset hx

theorem postHeavy_recomputedNeighborhoodOuterMultiplicity_le_frozen
    (A : Assembly P Y P.index.coarse r M)
    (lambda L : ℝ≥0∞) (label : κ → β) (b : β)
    (x : Space) :
    P.neighborhoodOuterMultiplicity
        (postHeavyRefinement P A lambda L label b).shading r x ≤
      frozenNeighborhoodOuterStatistic P P.index.coarse
        A.fiberRefinement.shading r x := by
  calc
    P.neighborhoodOuterMultiplicity
        (postHeavyRefinement P A lambda L label b).shading r x ≤
        P.neighborhoodOuterMultiplicity
          A.finalRefinement.shading r x :=
      neighborhoodOuterMultiplicity_mono P
        (postHeavyRefinement P A lambda L label b).carrier_subset r x
    _ ≤ frozenNeighborhoodOuterStatistic P P.index.coarse
        A.fiberRefinement.shading r x :=
      A.recomputedNeighborhoodOuterMultiplicity_le_frozen x

theorem postHeavy_pointMultiplicity_le_product
    (A : Assembly P Y P.index.coarse r M)
    (lambda L : ℝ≥0∞) (label : κ → β) (b : β)
    (hr : 0 < r) (x : Space) :
    (postHeavyRefinement P A lambda L label b).shading.pointMultiplicity x ≤
      A.outerLevel * A.fiberLevel :=
  ((postHeavyRefinement P A lambda L label b).pointMultiplicity_le x).trans
    (A.pointMultiplicity_le_product hr x)

theorem postHeavy_fiberMultiplicity_le_fiberLevel
    (A : Assembly P Y P.index.coarse r M)
    (lambda L : ℝ≥0∞) (label : κ → β) (b : β)
    (k : κ) (hk : k ∈ P.index.coarse) (x : Space) :
    P.fiberMultiplicity
        (postHeavyRefinement P A lambda L label b).shading k x ≤
      A.fiberLevel :=
  (fiberMultiplicity_mono P
      (postHeavyRefinement P A lambda L label b).carrier_subset k x).trans
    (A.fiberMultiplicity_final_le_fiberLevel k hk x)

/-- The exact pre-outer fiber statistic also survives on every post-heavy
carrier, because that carrier is contained in both restriction stages. -/
theorem postHeavy_fiberStatistic_constant
    (A : Assembly P Y P.index.coarse r M)
    (lambda L : ℝ≥0∞) (label : κ → β) (b : β)
    (i : ι) (x : Space)
    (hx : x ∈ (postHeavyRefinement P A lambda L label b).shading.carrier i) :
    P.fiberMultiplicity Y (P.index.parent i) x = A.fiberLevel := by
  have hxFinal : x ∈ A.finalRefinement.shading.carrier i :=
    (postHeavyRefinement P A lambda L label b).carrier_subset i hx
  have hxFiber : x ∈ A.fiberRefinement.shading.carrier i := by
    exact refinementRestrictStatisticLevel_carrier_subset_source
      A.fiberRefinement
      (frozenNeighborhoodOuterStatistic
        P P.index.coarse A.fiberRefinement.shading r)
      (measurableSet_frozenNeighborhoodOuterStatistic_eq
        P P.index.coarse A.fiberRefinement.shading r)
      A.outerLevel i hxFinal
  rw [← fiberMultiplicity_selectedParentShading_active_eq
    P Y (P.index.parent i) x]
  exact A.fiberStatistic_constant i x hxFiber

end PostAssemblyLemmas

/-- Run the paired multiplicity assembly on all active parents and then rerun
heavy selection on its actual final shading.  Every conclusion below concerns
the single post-heavy refinement. -/
theorem exists_postAssembly_heavyParentLabel_bucket
    {β : Type*} [DecidableEq β] [Fintype β] [Nonempty β]
    (P : ConvexFactorization F W) (Y : Shading F)
    (lambda L : ℝ≥0∞) (label : κ → β)
    (hL0 : L ≠ 0) (hLtop : L ≠ ∞)
    (hglobal :
      lambda * activeBodyMass P ≤ L * activeShadingMass P Y)
    (hfiber : ∀ k ∈ P.index.coarse, (P.index.fiber k).Nonempty)
    (r : ℝ) (hr : 0 < r) (M : ℕ)
    (hM : ∀ k ∈ P.index.coarse, (P.index.fiber k).card ≤ M) :
    ∃ A : Assembly P Y P.index.coarse r M, ∃ b : β,
      let parents := postHeavyParents P A lambda L label b
      let R := postHeavyRefinement P A lambda L label b
      parents ⊆ P.index.coarse ∧
        WithinFactor (assemblyLoss P M * (2 * Fintype.card β))
          (activeShadingMass P Y) R.shading.shadingMass ∧
        HasDenseFiberWitness P R.shading parents lambda
          (2 * amplifiedLoss P M L) ∧
        (activeShadingMass P Y ≠ 0 → parents.Nonempty) ∧
        (∀ x, R.shading.pointMultiplicity x ≤
          A.outerLevel * A.fiberLevel) ∧
        (∀ x, P.neighborhoodOuterMultiplicity R.shading r x ≤
          frozenNeighborhoodOuterStatistic P P.index.coarse
            A.fiberRefinement.shading r x) ∧
        (∀ x ∈ R.shading.shadedUnion,
          frozenNeighborhoodOuterStatistic P P.index.coarse
            A.fiberRefinement.shading r x = A.outerLevel) ∧
        (∀ k ∈ P.index.coarse, ∀ x,
          P.fiberMultiplicity R.shading k x ≤ A.fiberLevel) ∧
        (∀ i x, x ∈ R.shading.carrier i →
          P.fiberMultiplicity Y (P.index.parent i) x =
            A.fiberLevel) := by
  obtain ⟨A⟩ :=
    exists_assembly_of_fiber_card_le
      P Y P.index.coarse (fun _ hk => hk) r M hM
  have hpostGlobal :=
    global_density_after_assembly P Y lambda L A hglobal
  obtain ⟨b, hb⟩ :=
    exists_heavyParentLabel_bucket_withinFactor
      P A.finalRefinement.shading lambda (amplifiedLoss P M L) label
      (amplifiedLoss_ne_zero P M hL0)
      (amplifiedLoss_ne_top P M hLtop)
      hpostGlobal
  let parents := postHeavyParents P A lambda L label b
  let R := postHeavyRefinement P A lambda L label b
  have hRmass :
      R.shading.shadingMass =
        ∑ k ∈ parents,
          fiberShadingMass P A.finalRefinement.shading k := by
    change
      (selectedParentShading
        P A.finalRefinement.shading parents).shadingMass =
        ∑ k ∈ parents,
          fiberShadingMass P A.finalRefinement.shading k
    exact selectedParentShading_mass_eq_sum_fiberShadingMass
      P A.finalRefinement.shading parents
  have hheavy :
      WithinFactor (2 * Fintype.card β)
        A.finalRefinement.shading.shadingMass R.shading.shadingMass := by
    rw [← PostAssemblyLemmas.activeShadingMass_final_eq A, hRmass]
    exact hb
  have hretained :
      WithinFactor (assemblyLoss P M * (2 * Fintype.card β))
        (activeShadingMass P Y) R.shading.shadingMass :=
    WithinFactor.trans (PostAssemblyLemmas.active_retained A) hheavy
  have hwHeavy :=
    heavyParents_hasDenseFiberWitness
      P A.finalRefinement.shading lambda (amplifiedLoss P M L) hfiber
  have hwParents :
      HasDenseFiberWitness P A.finalRefinement.shading
        parents lambda (2 * amplifiedLoss P M L) := by
    intro k hk
    apply hwHeavy k
    exact (mem_dyadicFiber
      (heavyParents P A.finalRefinement.shading
        lambda (amplifiedLoss P M L)) label b k).1 hk |>.1
  have hwFinal :
      HasDenseFiberWitness P R.shading
        parents lambda (2 * amplifiedLoss P M L) := by
    change HasDenseFiberWitness P
      (selectedParentShading P A.finalRefinement.shading parents)
      parents lambda (2 * amplifiedLoss P M L)
    exact hasDenseFiberWitness_selectedParentShading
      P A.finalRefinement.shading parents lambda
        (2 * amplifiedLoss P M L) hwParents
  refine ⟨A, b, ?_⟩
  dsimp only
  refine ⟨postHeavyParents_subset_coarse P A lambda L label b,
    hretained, hwFinal, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro hmass0
    apply selectedParents_nonempty_of_retained
      P A.finalRefinement.shading parents
      (assemblyLoss P M * (2 * Fintype.card β))
      (activeShadingMass P Y) hmass0
    exact hretained
  · exact PostAssemblyLemmas.postHeavy_pointMultiplicity_le_product
      A lambda L label b hr
  · exact
      PostAssemblyLemmas.postHeavy_recomputedNeighborhoodOuterMultiplicity_le_frozen
        A lambda L label b
  · exact fun x hx =>
      PostAssemblyLemmas.postHeavy_frozenOuterStatistic_constant
        A lambda L label b hx
  · exact fun k hk x =>
      PostAssemblyLemmas.postHeavy_fiberMultiplicity_le_fiberLevel
        A lambda L label b k hk x
  · exact fun i x hx =>
      PostAssemblyLemmas.postHeavy_fiberStatistic_constant
        A lambda L label b i x hx

end PostAssemblyHeavySelection

end

end Submission.Kakeya.ConvexFactoring
