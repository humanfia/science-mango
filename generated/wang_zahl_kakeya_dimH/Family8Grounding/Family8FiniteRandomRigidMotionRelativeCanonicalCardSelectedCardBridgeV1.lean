import Family8Grounding.Family8FiniteRandomRigidMotionB2NormalizedDatumV1
import Family8Grounding.Family8GeneralizedFrostmanCanonicalCardInterpolationV1

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

open scoped ENNReal NNReal

namespace Family8FiniteRandomRigidMotionRelativeCanonicalCardSelectedCardBridgeV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8KatzTaoFrostmanPropertiesV1
open Family8FiniteRandomRigidMotionB2NormalizedDatumV1
open Family8GeneralizedFrostmanCanonicalCardInterpolationV1

noncomputable section

/-!
# Selected-card bridge for relative canonical-card refinements

A selected normalized rigid-copy refinement is indexed by a finite subset of
`copyIndex × sourceIndex`.  Thus a bound for the number of copies by the
canonical Frostman constant immediately gives the copied-cardinality field
needed by relative canonical-card interpolation.  No admissibility or
multiplicity hypothesis is involved.
-/

/-- A copy-count bound gives the selected-cardinality bound required by
`RelativeCanonicalCardRefinedFrostmanData`. -/
theorem
    selected_card_le_copyCardLoss_mul_eighth_sourceCanonical_mul_sourceCard
    {copyIndex sourceIndex : Type}
    [Fintype copyIndex] [DecidableEq copyIndex]
    [Fintype sourceIndex] [DecidableEq sourceIndex]
    {delta : NNReal} (source : ActualTubeDatum delta sourceIndex)
    (selected : Finset (copyIndex × sourceIndex))
    (copyCardLoss : ENNReal)
    (hcopy :
      (Fintype.card copyIndex : ENNReal) ≤
        copyCardLoss *
          sourceCanonicalFrostmanConstant (eighthNormalizedDatum source)) :
    (selected.card : ENNReal) ≤
      copyCardLoss *
          sourceCanonicalFrostmanConstant (eighthNormalizedDatum source) *
        (Fintype.card sourceIndex : ENNReal) := by
  have hselected :
      (selected.card : ENNReal) ≤
        (Fintype.card (copyIndex × sourceIndex) : ENNReal) := by
    exact_mod_cast (Finset.card_le_univ selected)
  calc
    (selected.card : ENNReal) ≤
        (Fintype.card (copyIndex × sourceIndex) : ENNReal) := hselected
    _ = (Fintype.card copyIndex : ENNReal) *
        (Fintype.card sourceIndex : ENNReal) := by
      simp only [Fintype.card_prod, Nat.cast_mul]
    _ ≤
        (copyCardLoss *
            sourceCanonicalFrostmanConstant (eighthNormalizedDatum source)) *
          (Fintype.card sourceIndex : ENNReal) :=
      mul_le_mul' hcopy le_rfl

#print axioms
  selected_card_le_copyCardLoss_mul_eighth_sourceCanonical_mul_sourceCard

end
end Family8FiniteRandomRigidMotionRelativeCanonicalCardSelectedCardBridgeV1
