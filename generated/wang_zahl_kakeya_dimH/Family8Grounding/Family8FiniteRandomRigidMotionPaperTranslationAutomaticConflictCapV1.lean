import Family8Grounding.Family8FiniteRandomRigidMotionPaperTranslationLatticeChoiceBudgetV1
import FamilyStickyGrounding.FamilyStickyActualPaperSingleLoadAutomaticV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8FiniteRandomRigidMotionPaperTranslationAutomaticConflictCapV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Family8KatzTaoFrostmanPropertiesV1
open Family8GeneralizedFrostmanMultiplicityV1
open Family8FiniteRandomRigidMotionIncidenceV1
open Family8FiniteRandomRigidMotionB2NormalizationCoreV1
open Family8FiniteRandomRigidMotionB2FreshGreedyV1
open Family8FiniteRandomRigidMotionPaperConflictTailV1
open Family8FiniteRandomRigidMotionPaperConflictMultiGridBridgeV1
open Family8FiniteRandomRigidMotionPaperNormalizedTranslationV1
open Family8FiniteRandomRigidMotionPaperTranslationPointBudgetV1
open Family8FiniteRandomRigidMotionPaperTranslationLatticeChoiceBudgetV1
open FamilyStickyActualTubeTranslationGridV1
open FamilyStickyLatticeMultiBoxPointCountV1
open FamilyStickyRandomModelTubeCollisionGridV1
open FamilyStickyActualPaperSingleLoadProducerV1.ActualTubeTranslationGrid

noncomputable section

/-!
# Fully automatic finite-law bounds for normalized translations

The normalized translation grid is not merely a point-counting adapter.  Its
single-load count is definitionally the paper's normalized rigid containment
load.  The repository's maximal-concentration theorem therefore supplies the
one-motion cap, while the explicit product lattice supplies both the
one-source choice count and its cross-multiplied mean balance.

After this file, the probability and finite bookkeeping chain has no
user-supplied `hloadCap`, `hchoice`, or `hbalance`.  Apart from explicit
numerical inequalities and the concrete lattice realization, the sole
remaining geometry premise is the bounded shifted-test multi-cover.
-/

/-- Canonical maximal-concentration cap for one normalized test. -/
def normalizedTranslationPaperSingleLoadCap
    {translation iota : Type}
    [Fintype translation] [DecidableEq translation]
    [Fintype iota] [DecidableEq iota]
    {delta : NNReal} {testCard : Nat}
    (gridVector : translation -> Space)
    (D : ActualTubeDatum delta iota)
    (testTube : Fin testCard -> Tube (delta / 8))
    (activeTests : Finset (Fin testCard))
    (K : Fin testCard) : Real :=
  paperSingleLoadCap
    (normalizedTranslationGrid gridVector D testTube activeTests) K

theorem normalizedTranslationPaperSingleLoadCap_nonneg
    {translation iota : Type}
    [Fintype translation] [DecidableEq translation]
    [Fintype iota] [DecidableEq iota]
    {delta : NNReal} {testCard : Nat}
    (gridVector : translation -> Space)
    (D : ActualTubeDatum delta iota)
    (testTube : Fin testCard -> Tube (delta / 8))
    (activeTests : Finset (Fin testCard))
    (K : Fin testCard) :
    0 <= normalizedTranslationPaperSingleLoadCap
      gridVector D testTube activeTests K := by
  exact ENNReal.toReal_nonneg

/-- The one-motion normalized rigid load is exactly the actual single load
of the normalized translation grid. -/
theorem normalizedTranslationGrid_singleLoad
    {translation iota : Type}
    [Fintype translation] [DecidableEq translation]
    [Fintype iota] [DecidableEq iota]
    {delta : NNReal} {testCard : Nat}
    (gridVector : translation -> Space)
    (D : ActualTubeDatum delta iota)
    (testTube : Fin testCard -> Tube (delta / 8))
    (activeTests : Finset (Fin testCard))
    (K : Fin testCard) (g : translation) :
    (normalizedTranslationGrid gridVector D testTube activeTests).singleLoad
        K g =
      normalizedRigidHundredLoadNat
        (fun omega => translationRigidMotion (gridVector omega))
        D testTube K g := by
  classical
  unfold FamilyStickyActualTubeTranslationGridV1.ActualTubeTranslationGrid.singleLoad
    normalizedRigidHundredLoadNat normalizedTranslationGrid
  apply congrArg Finset.card
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [eighthNormalizedTube_rigidTranslation, Tube.coe_body]

/-- Source admissibility supplies the normalized-radius hypotheses, hence
the canonical maximal-concentration cap uniformly in the translation. -/
theorem normalizedRigidHundredLoadNat_le_paperSingleLoadCap
    {translation iota : Type}
    [Fintype translation] [DecidableEq translation]
    [Fintype iota] [DecidableEq iota]
    {delta : NNReal} {testCard : Nat}
    (gridVector : translation -> Space)
    (D : ActualTubeDatum delta iota)
    (hD : D.IsAdmissible)
    (testTube : Fin testCard -> Tube (delta / 8))
    (activeTests : Finset (Fin testCard)) :
    forall K, K ∈ activeTests -> forall g,
      (normalizedRigidHundredLoadNat
          (fun omega => translationRigidMotion (gridVector omega))
          D testTube K g : Real) <=
        normalizedTranslationPaperSingleLoadCap
          gridVector D testTube activeTests K := by
  intro K _hK g
  rw [<- normalizedTranslationGrid_singleLoad]
  apply
    FamilyStickyActualPaperSingleLoadAutomaticV1.ActualTubeTranslationGrid.singleLoad_real_le_paperSingleLoadCap
  · exact (div_le_self (show 0 <= delta from bot_le) (by norm_num : (1 : NNReal) <= 8)).trans hD.delta_le_half
  · exact div_pos hD.delta_pos (by norm_num)

/-- Paper-strength finite probability and multi-cover bookkeeping with all
three local finite-law estimates (`hloadCap`, `hchoice`, `hbalance`) produced
from the actual normalized translation grid and its explicit product
lattice. -/
theorem exists_translationTuple_normalizedConflictIndices_card_le_of_lattice_multiCover
    {translation iota : Type}
    [Fintype translation] [Nonempty translation]
    [DecidableEq translation]
    [Fintype iota] [DecidableEq iota]
    {delta : NNReal} {testCard : Nat}
    (gridVector : translation -> Space)
    (D : ActualTubeDatum delta iota)
    (hD : D.IsAdmissible)
    (testTube : Fin testCard -> Tube (delta / 8))
    (activeTests : Finset (Fin testCard))
    (L : MultiBoxLattice (Fin testCard))
    (R :
      FamilyStickyActualLatticePointBalanceV1.ActualTubeTranslationGrid.IsMultiBoxLatticeRealization
        (normalizedTranslationGrid gridVector D testTube activeTests) L)
    (repetitions coverMultiplicity loadThreshold : Nat)
    (mean : Fin testCard -> Real) (A : Real)
    (hmean : forall K, K ∈ activeTests -> 0 <= mean K)
    (hlocal : forall K, K ∈ activeTests ->
      (Fintype.card iota : Real) <=
        (Fintype.card (L.Block K) : Real) * mean K)
    (hscale : forall K, K ∈ activeTests ->
      (repetitions : Real) * mean K <=
        normalizedTranslationPaperSingleLoadCap
          gridVector D testTube activeTests K)
    (htailRoom :
      (activeTests.card : Real) * Real.exp (Real.exp 1 - 1) <
        Real.exp A)
    (hthreshold : forall K, K ∈ activeTests ->
      A * normalizedTranslationPaperSingleLoadCap
          gridVector D testTube activeTests K <=
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
                (hundredTube (testTube K)).carrier)) :
    exists omega : Fin repetitions -> translation,
      (forall K, K ∈ activeTests ->
        (∑ j,
          (normalizedRigidHundredLoadNat
            (fun g => translationRigidMotion (gridVector g))
            D testTube K (omega j) : Real)) <=
          A * normalizedTranslationPaperSingleLoadCap
            gridVector D testTube activeTests K) ∧
      (forall a,
        (normalizedConflictIndices
          (indexedRigidCopyDatum
            (fun j => translationRigidMotion (gridVector (omega j))) D)
          a).card <= coverMultiplicity * loadThreshold) := by
  apply
    exists_rigidMotionTuple_normalizedConflictIndices_card_le_of_multiCover
      (motion := fun g => translationRigidMotion (gridVector g))
      (D := D) (testTube := testTube) (activeTests := activeTests)
      (choiceBudget := fun K => R.translationBudget K)
      (repetitions := repetitions) (coverMultiplicity := coverMultiplicity)
      (loadThreshold := loadThreshold)
      (cap := fun K => normalizedTranslationPaperSingleLoadCap
        gridVector D testTube activeTests K)
      (mean := mean) (A := A)
  · intro K _hK
    exact normalizedTranslationPaperSingleLoadCap_nonneg
      gridVector D testTube activeTests K
  · exact hmean
  · exact normalizedRigidHundredLoadNat_le_paperSingleLoadCap
      gridVector D hD testTube activeTests
  · exact normalizedRigidHundredChoiceCount_le_translationBudget
      gridVector D testTube activeTests L R
  · intro K hK
    exact normalizedTranslation_balance_of_tubeCard_le_blockCard_mul_mean
      gridVector D testTube activeTests L R mean K (hlocal K hK)
  · exact hscale
  · exact htailRoom
  · exact hthreshold
  · exact hgridMultiCover

#print axioms normalizedTranslationGrid_singleLoad
#print axioms normalizedRigidHundredLoadNat_le_paperSingleLoadCap
#print axioms exists_translationTuple_normalizedConflictIndices_card_le_of_lattice_multiCover

end
end Family8FiniteRandomRigidMotionPaperTranslationAutomaticConflictCapV1
