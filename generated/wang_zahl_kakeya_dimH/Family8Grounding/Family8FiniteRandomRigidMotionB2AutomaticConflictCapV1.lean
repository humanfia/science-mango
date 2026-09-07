import Family8Grounding.Family8FiniteRandomRigidMotionB2FreshGreedyV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8FiniteRandomRigidMotionB2AutomaticConflictCapV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family4GlobalExtremalUpstream
open Family8KatzTaoFrostmanPropertiesV1
open Family8GeneralizedKatzTaoMultiplicityV1
open Family8FiniteRandomRigidMotionB2NormalizedDatumV1
open Family8FiniteRandomRigidMotionB2FreshGreedyV1

noncomputable section

/-!
# Automatic finite fallback for the normalized conflict cap

This is the unconditional finite-power seam: every normalized conflict
neighbourhood is a filtered subset of the actual finite index set.  It is
deliberately separated from the sharper random-grid incidence estimate, so
the formal development has a callback-free baseline while retaining a clear
place for the paper-strength cap.
-/

theorem normalizedConflictIndices_card_le_indexCard
    {iota : Type} [Fintype iota] [DecidableEq iota]
    {delta : NNReal} (D : ActualTubeDatum delta iota) (a : iota) :
    (normalizedConflictIndices D a).card <= Fintype.card iota := by
  classical
  calc
    (normalizedConflictIndices D a).card <=
        (Finset.univ : Finset iota).card :=
      Finset.card_le_card (Finset.filter_subset _ _)
    _ = Fintype.card iota := Finset.card_univ

theorem normalizedConflictIndices_card_le_of_indexCard_le
    {iota : Type} [Fintype iota] [DecidableEq iota]
    {delta : NNReal} (D : ActualTubeDatum delta iota)
    {conflictThreshold : Nat}
    (hcard : Fintype.card iota <= conflictThreshold) :
    forall a, (normalizedConflictIndices D a).card <= conflictThreshold := by
  intro a
  exact (normalizedConflictIndices_card_le_indexCard D a).trans hcard

/-- Fully automatic coarse normalized refinement.  The loss is displayed as
`card + 1`; no hidden conflict or selected-subtype premise remains. -/
theorem exists_automatic_normalized_refinement_admissible_isKatzTao
    {iota : Type} [Fintype iota] [Nonempty iota] [DecidableEq iota]
    {delta : NNReal}
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible)
    (hB2 : forall i,
      (D.family.tubes i).carrier ⊆ Metric.closedBall (0 : Space) 2)
    {C : ENNReal} (hKT : IsKatzTao C D.family.bodyFamily) :
    exists selected : Finset iota,
      selected.Nonempty ∧
      (restrictActualTubeDatum
        (eighthNormalizedDatum D) selected).IsAdmissible ∧
      (Fintype.card iota : ENNReal) <=
        (Fintype.card iota + 1 : Nat) * (selected.card : ENNReal) ∧
      (eighthNormalizedDatum D).shading.shadingMass <=
        (Fintype.card iota + 1 : Nat) *
          (restrictActualTubeDatum (eighthNormalizedDatum D)
            selected).shading.shadingMass ∧
      IsKatzTao (128 * C)
        (restrictActualTubeDatum (eighthNormalizedDatum D)
          selected).family.bodyFamily ∧
      D.shading.averageMultiplicity <=
        (Fintype.card iota + 1 : Nat) *
          (restrictActualTubeDatum (eighthNormalizedDatum D)
            selected).shading.averageMultiplicity := by
  exact exists_normalized_refinement_admissible_isKatzTao
    D hD hB2 (normalizedConflictIndices_card_le_indexCard D) hKT

#print axioms normalizedConflictIndices_card_le_indexCard
#print axioms normalizedConflictIndices_card_le_of_indexCard_le
#print axioms exists_automatic_normalized_refinement_admissible_isKatzTao

end
end Family8FiniteRandomRigidMotionB2AutomaticConflictCapV1
