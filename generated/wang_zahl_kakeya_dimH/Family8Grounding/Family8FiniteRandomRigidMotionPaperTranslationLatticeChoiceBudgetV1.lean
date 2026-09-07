import Family8Grounding.Family8FiniteRandomRigidMotionPaperTranslationPointBudgetV1
import FamilyStickyGrounding.FamilyStickyActualLatticePointBalanceV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8FiniteRandomRigidMotionPaperTranslationLatticeChoiceBudgetV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Family8KatzTaoFrostmanPropertiesV1
open Family8GeneralizedFrostmanMultiplicityV1
open Family8FiniteRandomRigidMotionIncidenceV1
open Family8FiniteRandomRigidMotionPaperConflictTailV1
open Family8FiniteRandomRigidMotionPaperNormalizedTranslationV1
open Family8FiniteRandomRigidMotionPaperTranslationPointBudgetV1
open FamilyStickyLatticeMultiBoxPointCountV1

noncomputable section

/-!
# Automatic normalized choice budgets from the explicit product lattice

The preceding connector reduces one normalized containment event to an
actual point hit.  The repository's simultaneous oriented-box lattice has a
proved finite fibre bound for those point hits.  Combining the two removes
the abstract `hchoice` premise completely: the budget is the cardinality of
all lattice blocks except the test's distinguished block.
-/

/-- An explicit multi-box lattice realization automatically bounds every
normalized one-source-tube choice count. -/
theorem normalizedRigidHundredChoiceCount_le_translationBudget
    {translation iota : Type}
    [Fintype translation] [DecidableEq translation]
    [Fintype iota] [DecidableEq iota]
    {delta : NNReal} {testCard : Nat}
    (gridVector : translation -> Space)
    (D : ActualTubeDatum delta iota)
    (testTube : Fin testCard -> Tube (delta / 8))
    (activeTests : Finset (Fin testCard))
    (L : MultiBoxLattice (Fin testCard))
    (R :
      FamilyStickyActualLatticePointBalanceV1.ActualTubeTranslationGrid.IsMultiBoxLatticeRealization
        (normalizedTranslationGrid gridVector D testTube activeTests) L) :
    forall K, K ∈ activeTests -> forall i : iota,
      normalizedRigidHundredChoiceCount
          (fun g => translationRigidMotion (gridVector g)) D testTube K i <=
        R.translationBudget K := by
  intro K hK i
  rw [<- normalizedTranslationGrid_tubeHitCount]
  exact R.tubeHitCount_le_translationBudget K hK i (Finset.mem_univ i)

/-- The same concrete lattice data also gives the cross-multiplied mean
budget once a single distinguished block is large enough. -/
theorem normalizedTranslation_balance_of_tubeCard_le_blockCard_mul_mean
    {translation iota : Type}
    [Fintype translation] [DecidableEq translation]
    [Fintype iota] [DecidableEq iota]
    {delta : NNReal} {testCard : Nat}
    (gridVector : translation -> Space)
    (D : ActualTubeDatum delta iota)
    (testTube : Fin testCard -> Tube (delta / 8))
    (activeTests : Finset (Fin testCard))
    (L : MultiBoxLattice (Fin testCard))
    (R :
      FamilyStickyActualLatticePointBalanceV1.ActualTubeTranslationGrid.IsMultiBoxLatticeRealization
        (normalizedTranslationGrid gridVector D testTube activeTests) L)
    (mean : Fin testCard -> Real)
    (K : Fin testCard)
    (hlocal : (Fintype.card iota : Real) <=
      (Fintype.card (L.Block K) : Real) * mean K) :
    (Fintype.card iota : Real) * (R.translationBudget K : Real) <=
      (Fintype.card translation : Real) * mean K := by
  have h := R.balance_of_tubeCard_le_blockCard_mul_mean K hlocal
  simpa only [normalizedTranslationGrid_tubes, Finset.card_univ] using h

#print axioms normalizedRigidHundredChoiceCount_le_translationBudget
#print axioms normalizedTranslation_balance_of_tubeCard_le_blockCard_mul_mean

end
end Family8FiniteRandomRigidMotionPaperTranslationLatticeChoiceBudgetV1
