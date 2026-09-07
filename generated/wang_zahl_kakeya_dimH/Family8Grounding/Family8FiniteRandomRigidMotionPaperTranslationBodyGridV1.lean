import Family8Grounding.Family8FiniteRandomRigidMotionPaperTranslationAutomaticConflictCapV1
import FamilyStickyGrounding.FamilyStickyRandomTestDependentChernoffV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8FiniteRandomRigidMotionPaperTranslationBodyGridV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Family8KatzTaoFrostmanPropertiesV1
open Family8GeneralizedFrostmanMultiplicityV1
open Family8FiniteRandomRigidMotionIncidenceV1
open Family8FiniteRandomRigidMotionB2NormalizationCoreV1
open Family8FiniteRandomRigidMotionB2FreshGreedyV1
open Family8FiniteRandomRigidMotionPaperNormalizedTranslationV1
open Family8FiniteRandomRigidMotionPaperTranslationPointBudgetV1
open FamilyStickyActualTubeTranslationGridV1
open FamilyStickyLatticeMultiBoxPointCountV1
open FamilyStickyRandomTranslationGridAdapterV1
open FamilyStickyRandomTestDependentChernoffV1
open FamilyStickyActualPaperSingleLoadProducerV1.ActualTubeTranslationGrid

noncomputable section

/-!
# Paper conflict tests as honest convex bodies

The paper's enlarged test tube is longitudinally enlarged as well as
transversely thickened.  The repository's `hundredTube` changes only the
radius of a unit-axis tube, so a bounded longitudinal cover by those objects
is not available.  This module keeps the already proved finite probability
argument but lets each test be an arbitrary actual convex body.  In
particular, a length-three aligned frame box with two `O(delta)` short sides
has the correct `O(delta^2)` volume and can absorb longitudinal displacement.

All probability, lattice, maximal-concentration, and multi-cover bookkeeping
is closed below.  The only geometry input is literal containment of each
overlap conflict in a bounded family of the supplied convex test bodies.
-/

/-- The normalized finite translation grid with arbitrary convex tests. -/
def normalizedTranslationBodyGrid
    {translation iota : Type}
    [Fintype translation] [DecidableEq translation]
    [Fintype iota] [DecidableEq iota]
    {delta : NNReal} {testCard : Nat}
    (gridVector : translation -> Space)
    (D : ActualTubeDatum delta iota)
    (testBody : Fin testCard -> ConvexBody Space)
    (activeTests : Finset (Fin testCard)) :
    ActualTubeTranslationGrid (delta / 8) translation iota where
  gridVector g := eighthTranslationVector (gridVector g)
  tubes := Finset.univ
  tube i := eighthNormalizedTube (D.family.tubes i)
  testCard := testCard
  testBody := testBody
  activeTests := activeTests

/-- Literal one-motion containment load for an arbitrary convex test. -/
def normalizedTranslationBodyLoadNat
    {translation iota : Type}
    [Fintype translation] [DecidableEq translation]
    [Fintype iota] [DecidableEq iota]
    {delta : NNReal} {testCard : Nat}
    (gridVector : translation -> Space)
    (D : ActualTubeDatum delta iota)
    (testBody : Fin testCard -> ConvexBody Space)
    (K : Fin testCard) (g : translation) : Nat := by
  classical
  exact ((Finset.univ : Finset iota).filter fun i =>
    (eighthNormalizedTube
      (rigidTube (translationRigidMotion (gridVector g))
        (D.family.tubes i))).carrier ⊆
      (testBody K : Set Space)).card

/-- Product occurrences contained in one arbitrary convex test. -/
def normalizedTranslationBodyIndices
    {translation iota : Type}
    [Fintype translation] [DecidableEq translation]
    [Fintype iota] [DecidableEq iota]
    {delta : NNReal} {testCard repetitions : Nat}
    (gridVector : translation -> Space)
    (D : ActualTubeDatum delta iota)
    (testBody : Fin testCard -> ConvexBody Space)
    (omega : Fin repetitions -> translation)
    (K : Fin testCard) : Finset (Fin repetitions × iota) := by
  classical
  exact Finset.univ.filter fun b =>
    (eighthNormalizedTube
      (rigidTube (translationRigidMotion (gridVector (omega b.1)))
        (D.family.tubes b.2))).carrier ⊆
      (testBody K : Set Space)

/-- The normalized rigid load is exactly the existing actual-grid single
load, now for an arbitrary convex test body. -/
theorem normalizedTranslationBodyGrid_singleLoad
    {translation iota : Type}
    [Fintype translation] [DecidableEq translation]
    [Fintype iota] [DecidableEq iota]
    {delta : NNReal} {testCard : Nat}
    (gridVector : translation -> Space)
    (D : ActualTubeDatum delta iota)
    (testBody : Fin testCard -> ConvexBody Space)
    (activeTests : Finset (Fin testCard))
    (K : Fin testCard) (g : translation) :
    (normalizedTranslationBodyGrid
        gridVector D testBody activeTests).singleLoad K g =
      normalizedTranslationBodyLoadNat gridVector D testBody K g := by
  classical
  unfold FamilyStickyActualTubeTranslationGridV1.ActualTubeTranslationGrid.singleLoad
    normalizedTranslationBodyLoadNat normalizedTranslationBodyGrid
  apply congrArg Finset.card
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [eighthNormalizedTube_rigidTranslation]

/-- Exact splitting of the product containment count by repetition. -/
theorem normalizedTranslationBodyIndices_card_eq_sum_load
    {translation iota : Type}
    [Fintype translation] [DecidableEq translation]
    [Fintype iota] [DecidableEq iota]
    {delta : NNReal} {testCard repetitions : Nat}
    (gridVector : translation -> Space)
    (D : ActualTubeDatum delta iota)
    (testBody : Fin testCard -> ConvexBody Space)
    (omega : Fin repetitions -> translation)
    (K : Fin testCard) :
    (normalizedTranslationBodyIndices
        gridVector D testBody omega K).card =
      ∑ j, normalizedTranslationBodyLoadNat
        gridVector D testBody K (omega j) := by
  classical
  unfold normalizedTranslationBodyIndices normalizedTranslationBodyLoadNat
  rw [Finset.card_eq_sum_ones]
  rw [<- Finset.univ_product_univ, Finset.sum_filter, Finset.sum_product]
  apply Finset.sum_congr rfl
  intro j _hj
  rw [Finset.card_eq_sum_ones, Finset.sum_filter]

/-- A bounded multi-cover by arbitrary convex tests gives the exact conflict
cardinality loss. -/
theorem normalizedConflictIndices_card_le_of_bodyMultiCover
    {translation iota : Type}
    [Fintype translation] [DecidableEq translation]
    [Fintype iota] [DecidableEq iota]
    {delta : NNReal} {testCard repetitions : Nat}
    {coverMultiplicity loadThreshold : Nat}
    (gridVector : translation -> Space)
    (D : ActualTubeDatum delta iota)
    (testBody : Fin testCard -> ConvexBody Space)
    (activeTests : Finset (Fin testCard))
    (omega : Fin repetitions -> translation)
    (cover : Fin repetitions × iota -> Finset (Fin testCard))
    (hcoverActive : forall a, cover a ⊆ activeTests)
    (hcoverCard : forall a, (cover a).card <= coverMultiplicity)
    (hcover : forall a b,
      normalizedConflict
          (indexedRigidCopyDatum
            (fun j => translationRigidMotion (gridVector (omega j))) D)
          b a ->
        exists K, K ∈ cover a ∧
          (eighthNormalizedTube
            (rigidTube
              (translationRigidMotion (gridVector (omega b.1)))
              (D.family.tubes b.2))).carrier ⊆
            (testBody K : Set Space))
    (hload : forall K, K ∈ activeTests ->
      (∑ j, normalizedTranslationBodyLoadNat
        gridVector D testBody K (omega j)) <= loadThreshold) :
    forall a,
      (normalizedConflictIndices
        (indexedRigidCopyDatum
          (fun j => translationRigidMotion (gridVector (omega j))) D)
        a).card <= coverMultiplicity * loadThreshold := by
  classical
  intro a
  have hsubset :
      normalizedConflictIndices
          (indexedRigidCopyDatum
            (fun j => translationRigidMotion (gridVector (omega j))) D)
          a ⊆
        (cover a).biUnion fun K =>
          normalizedTranslationBodyIndices gridVector D testBody omega K := by
    intro b hb
    rw [normalizedConflictIndices, Finset.mem_filter] at hb
    obtain ⟨K, hK, hcontain⟩ := hcover a b hb.2
    apply Finset.mem_biUnion.mpr
    refine ⟨K, hK, ?_⟩
    rw [normalizedTranslationBodyIndices, Finset.mem_filter]
    exact ⟨Finset.mem_univ b, hcontain⟩
  calc
    (normalizedConflictIndices
        (indexedRigidCopyDatum
          (fun j => translationRigidMotion (gridVector (omega j))) D)
        a).card <=
        ((cover a).biUnion fun K =>
          normalizedTranslationBodyIndices
            gridVector D testBody omega K).card :=
      Finset.card_le_card hsubset
    _ <= ∑ K ∈ cover a,
        (normalizedTranslationBodyIndices
          gridVector D testBody omega K).card := Finset.card_biUnion_le
    _ = ∑ K ∈ cover a,
        ∑ j, normalizedTranslationBodyLoadNat
          gridVector D testBody K (omega j) := by
      apply Finset.sum_congr rfl
      intro K _hK
      exact normalizedTranslationBodyIndices_card_eq_sum_load
        gridVector D testBody omega K
    _ <= ∑ _K ∈ cover a, loadThreshold := by
      apply Finset.sum_le_sum
      intro K hK
      exact hload K (hcoverActive a hK)
    _ = (cover a).card * loadThreshold := by simp
    _ <= coverMultiplicity * loadThreshold :=
      Nat.mul_le_mul_right loadThreshold (hcoverCard a)

/-- Canonical maximal-concentration cap for one arbitrary convex test. -/
def normalizedTranslationBodyPaperCap
    {translation iota : Type}
    [Fintype translation] [DecidableEq translation]
    [Fintype iota] [DecidableEq iota]
    {delta : NNReal} {testCard : Nat}
    (gridVector : translation -> Space)
    (D : ActualTubeDatum delta iota)
    (testBody : Fin testCard -> ConvexBody Space)
    (activeTests : Finset (Fin testCard))
    (K : Fin testCard) : Real :=
  paperSingleLoadCap
    (normalizedTranslationBodyGrid gridVector D testBody activeTests) K

/-- Full paper finite-law producer for honest convex test bodies.  The local
load, choice-count and mean bounds are all generated by the actual grid and
its explicit multi-box lattice. -/
theorem exists_translationTuple_normalizedConflictIndices_card_le_of_bodyLatticeMultiCover
    {translation iota : Type}
    [Fintype translation] [Nonempty translation]
    [DecidableEq translation]
    [Fintype iota] [DecidableEq iota]
    {delta : NNReal} {testCard : Nat}
    (gridVector : translation -> Space)
    (D : ActualTubeDatum delta iota)
    (hD : D.IsAdmissible)
    (testBody : Fin testCard -> ConvexBody Space)
    (activeTests : Finset (Fin testCard))
    (L : MultiBoxLattice (Fin testCard))
    (R :
      FamilyStickyActualLatticePointBalanceV1.ActualTubeTranslationGrid.IsMultiBoxLatticeRealization
        (normalizedTranslationBodyGrid gridVector D testBody activeTests) L)
    (repetitions coverMultiplicity loadThreshold : Nat)
    (mean : Fin testCard -> Real) (A : Real)
    (hmean : forall K, K ∈ activeTests -> 0 <= mean K)
    (hlocal : forall K, K ∈ activeTests ->
      (Fintype.card iota : Real) <=
        (Fintype.card (L.Block K) : Real) * mean K)
    (hscale : forall K, K ∈ activeTests ->
      (repetitions : Real) * mean K <=
        normalizedTranslationBodyPaperCap
          gridVector D testBody activeTests K)
    (htailRoom :
      (activeTests.card : Real) * Real.exp (Real.exp 1 - 1) <
        Real.exp A)
    (hthreshold : forall K, K ∈ activeTests ->
      A * normalizedTranslationBodyPaperCap
          gridVector D testBody activeTests K <=
        (loadThreshold : Real))
    (hgridMultiCover :
      forall omega : Fin repetitions -> translation,
      exists cover : Fin repetitions × iota -> Finset (Fin testCard),
        (forall a, cover a ⊆ activeTests) ∧
        (forall a, (cover a).card <= coverMultiplicity) ∧
        (forall a b,
          normalizedConflict
              (indexedRigidCopyDatum
                (fun j => translationRigidMotion (gridVector (omega j))) D)
              b a ->
            exists K, K ∈ cover a ∧
              (eighthNormalizedTube
                (rigidTube
                  (translationRigidMotion (gridVector (omega b.1)))
                  (D.family.tubes b.2))).carrier ⊆
                (testBody K : Set Space))) :
    exists omega : Fin repetitions -> translation,
      (forall K, K ∈ activeTests ->
        (∑ j, (normalizedTranslationBodyLoadNat
          gridVector D testBody K (omega j) : Real)) <=
          A * normalizedTranslationBodyPaperCap
            gridVector D testBody activeTests K) ∧
      (forall a,
        (normalizedConflictIndices
          (indexedRigidCopyDatum
            (fun j => translationRigidMotion (gridVector (omega j))) D)
          a).card <= coverMultiplicity * loadThreshold) := by
  classical
  let G := normalizedTranslationBodyGrid gridVector D testBody activeTests
  let cap : Fin testCard -> Real := fun K =>
    normalizedTranslationBodyPaperCap gridVector D testBody activeTests K
  have hloadCap : forall K, K ∈ activeTests -> forall g,
      (normalizedTranslationBodyLoadNat gridVector D testBody K g : Real) <=
        cap K := by
    intro K _hK g
    rw [<- normalizedTranslationBodyGrid_singleLoad]
    apply
      FamilyStickyActualPaperSingleLoadAutomaticV1.ActualTubeTranslationGrid.singleLoad_real_le_paperSingleLoadCap
    · exact (div_le_self (show 0 <= delta from bot_le)
          (by norm_num : (1 : NNReal) <= 8)).trans hD.delta_le_half
    · exact div_pos hD.delta_pos (by norm_num)
  have hsum : forall K, K ∈ activeTests ->
      (∑ g : translation,
        (normalizedTranslationBodyLoadNat gridVector D testBody K g : Real)) <=
        (Fintype.card translation : Real) * mean K := by
    intro K hK
    let G' := normalizedTranslationBodyGrid gridVector D testBody activeTests
    have hgridTube : forall i, i ∈ G'.tubes ->
        G'.tubeHitCount K i <= R.translationBudget K := by
      intro i hi
      exact R.tubeHitCount_le_translationBudget K hK i hi
    have hbalanceTube :
        (G'.tubes.card : Real) * (R.translationBudget K : Real) <=
          (Fintype.card translation : Real) * mean K := by
      exact R.balance_of_tubeCard_le_blockCard_mul_mean K (hlocal K hK)
    have h :=
      FamilyStickyRandomTranslationGridAdapterV1.TranslationIncidenceModel.sum_load_le_of_gridHitsTube_le
        G'.toIncidenceModel K (R.translationBudget K) (mean K)
        (fun i hi => by
          have hi' : i ∈ G'.tubes := by
            simpa only [G'.toIncidenceModel_tubes] using hi
          convert hgridTube i hi' using 1
          unfold FamilyStickyRandomTranslationIncidenceV1.TranslationIncidenceModel.gridHitsTube
            FamilyStickyActualTubeTranslationGridV1.ActualTubeTranslationGrid.toIncidenceModel
            FamilyStickyActualTubeTranslationGridV1.ActualTubeTranslationGrid.tubeHitCount
          apply congrArg Finset.card
          ext g
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          rw [decide_eq_true_eq])
        (by simpa only [G'.toIncidenceModel_tubes] using hbalanceTube)
    have hloadEq : forall g : translation,
        G'.toIncidenceModel.load K g =
          (normalizedTranslationBodyLoadNat
            gridVector D testBody K g : Real) := by
      intro g
      calc
        G'.toIncidenceModel.load K g = (G'.singleLoad K g : Real) :=
          G'.toIncidenceModel_load K g
        _ = (normalizedTranslationBodyLoadNat
            gridVector D testBody K g : Real) := by
          norm_cast
          dsimp only [G']
          exact normalizedTranslationBodyGrid_singleLoad
            gridVector D testBody activeTests K g
    simpa only [hloadEq] using h
  obtain ⟨omega, htail⟩ :=
    exists_product_choice_load_le_A_mul_cap
      activeTests repetitions
      (fun K g =>
        (normalizedTranslationBodyLoadNat gridVector D testBody K g : Real))
      cap mean A
      (fun K _hK => ENNReal.toReal_nonneg) hmean
      (fun K _hK g => Nat.cast_nonneg _)
      hloadCap hsum hscale htailRoom
  obtain ⟨cover, hcoverActive, hcoverCard, hcover⟩ :=
    hgridMultiCover omega
  refine ⟨omega, htail, ?_⟩
  apply normalizedConflictIndices_card_le_of_bodyMultiCover
    gridVector D testBody activeTests omega cover
      hcoverActive hcoverCard hcover
  intro K hK
  have hreal :
      (∑ j, (normalizedTranslationBodyLoadNat
        gridVector D testBody K (omega j) : Real)) <=
        (loadThreshold : Real) :=
    (htail K hK).trans (hthreshold K hK)
  have hcast :
      ((∑ j, normalizedTranslationBodyLoadNat
        gridVector D testBody K (omega j) : Nat) : Real) <=
        (loadThreshold : Real) := by
    simpa only [Nat.cast_sum] using hreal
  exact_mod_cast hcast

#print axioms normalizedTranslationBodyGrid_singleLoad
#print axioms normalizedTranslationBodyIndices_card_eq_sum_load
#print axioms normalizedConflictIndices_card_le_of_bodyMultiCover
#print axioms exists_translationTuple_normalizedConflictIndices_card_le_of_bodyLatticeMultiCover

end
end Family8FiniteRandomRigidMotionPaperTranslationBodyGridV1
