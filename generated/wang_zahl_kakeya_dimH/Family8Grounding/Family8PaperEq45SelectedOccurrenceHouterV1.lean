import Family8Grounding.Family8PaperEq45SelectedOccurrenceBundleV2
import Family8Grounding.Family8SelectedOccurrenceAverageRetentionV1

/-!
# Selected Eq. (45) consumer for the full induced outer average

This file composes the paper-facing selected `W'` bundle with the exact
full-to-selected average-retention bridge.  The conclusion is the same full
induced average used by the current Family 8 endpoint.  There is no `houter`
premise: the remaining inputs are the stable Family 6 hypothesis, a genuine
selected-mass retention estimate, and a scalar absorption inequality.
-/

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8PaperEq45SelectedOccurrenceHouterV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
open Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
open Family6AffinePlankAnalyticHypothesesStableV1
open Family8PaperEq45SelectedOccurrenceBundleV2
open Family8PaperEq45SelectedOccurrenceBundleV2.PaperEq45SelectedOccurrenceInput
open Family8SelectedOccurrenceAverageRetentionV1
open Family8SelectedOccurrenceDensityFrostmanV1

noncomputable section

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000

local instance (p : Prop) : Decidable p := Classical.propDecidable p

variable {iota kappa : Type*} [Fintype iota] [DecidableEq iota]
  {F : ConvexFamily iota} {candidates : Finset kappa}
  {container : kappa -> ConvexBody Space} {active : Finset iota}
  {P : GreedyDensityPartition F candidates container active}
  {Y : Shading F} {S : Finset (Fin (blocks F P).length)}
  {a b : NNReal} {beta : Real}

/-- Scalar absorption after paying the actual selected-family retention loss.
This contains no average-multiplicity proposition. -/
def FullScaleAbsorption
    (I : PaperEq45SelectedOccurrenceInput P Y S a b)
    (selectionLoss : ENNReal) (delta : NNReal)
    (lemmaEpsilon epsilon beta : Real) : Prop :=
  selectionLoss * I.family6Factor lemmaEpsilon beta ≤
    I.rhs delta epsilon beta

/-- Callback-free Eq. (45) producer for the full induced outer average.  The
selected mass retention is exactly the Proposition 5.1-type bridge needed to
transport the Family 6 estimate on `W'` back to the endpoint's full induced
shading. -/
theorem exists_family6Parameters_fullInducedAverage_le_eq45
    (I : PaperEq45SelectedOccurrenceInput P Y S a b)
    (H : ConvexPlankFrostmanMultiplicityHypothesis
      {q // q ∈ selectedOccurrenceIndices P S} beta)
    (selectionLoss : ENNReal)
    (hretained :
      (fullOccurrenceInducedShading P Y).shadingMass ≤
        selectionLoss *
          (selectedOccurrenceOuterShading P Y S).shadingMass)
    (delta : NNReal) (lemmaEpsilon epsilon : Real)
    (hlemmaEpsilon : 0 < lemmaEpsilon)
    (habsorb : FullScaleAbsorption I selectionLoss delta
      lemmaEpsilon epsilon beta) :
    ∃ eta : Real, ∃ b0 : NNReal,
      0 < eta ∧ 0 < b0 ∧
      ∀ (_ha : 0 < a), a ≤ b → b ≤ b0 →
        (a : ENNReal) ^ eta ≤ I.datum.shading.shadingDensity →
        ((convexFactorization F P).inducedShading Y).averageMultiplicity ≤
          I.rhs delta epsilon beta := by
  obtain ⟨eta, b0, heta, hb0, hselected⟩ :=
    I.exists_family6Parameters_selectedAverage_le H lemmaEpsilon
      hlemmaEpsilon
  refine ⟨eta, b0, heta, hb0, ?_⟩
  intro ha hab hbb0 hdensity
  have hfullSelected :
      ((convexFactorization F P).inducedShading Y).averageMultiplicity ≤
        selectionLoss *
          (selectedOccurrenceOuterShading P Y S).averageMultiplicity :=
    fullAverage_le_loss_mul_selectedAverage_of_mass_retention
      P Y S selectionLoss hretained
  calc
    ((convexFactorization F P).inducedShading Y).averageMultiplicity ≤
        selectionLoss *
          (selectedOccurrenceOuterShading P Y S).averageMultiplicity :=
      hfullSelected
    _ ≤ selectionLoss * I.family6Factor lemmaEpsilon beta := by
      exact mul_le_mul' le_rfl (hselected ha hab hbb0 hdensity)
    _ ≤ I.rhs delta epsilon beta := habsorb

#print axioms exists_family6Parameters_fullInducedAverage_le_eq45

end

end Family8PaperEq45SelectedOccurrenceHouterV1
