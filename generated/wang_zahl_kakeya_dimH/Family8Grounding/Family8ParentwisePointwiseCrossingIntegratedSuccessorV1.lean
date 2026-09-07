import Family8Grounding.Family8ParentwiseCrossingIntegratedSuccessorV1
import Mathlib.Tactic

/-!
# Raw-cover bridge for the pointwise crossing successor

The integrated successor stores its transported interval bound on the
canonical `crossingIntervalCover` and `crossingBaseQ`, while the raw first
crossing is stated on `paperBufferedIntervalCover` and `W.q`.  These are the
same interval cover and the same parent by construction.  The theorems below
expose that equality at the proposition boundary used by the next stopping
layer.

No selector is invoked here.  The q-fibre state remains the unique base-cover
state already stored by the integrated successor, and the raw interval
strict crossing remains a separate interval-cover fact.
-/

set_option autoImplicit false
set_option warningAsError true

open scoped ENNReal NNReal

namespace Family8ParentwisePointwiseCrossingIntegratedSuccessorV1

open Family8FirstParentwiseNormalizedCrossingWitnessV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8NormalizedCFDividingWitnessBridgeV2.StickyScaleCover
open Family8NormalizedCFDividingWitnessParentwiseFiniteSelectionV1.CoherentStickyMultiscaleCover
open Family8ParentwiseCrossingIntegratedSuccessorV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainCoherentIntervalProducerV1

noncomputable section

variable {delta : NNReal} {iota : Type}
  [Fintype iota] [DecidableEq iota]
  {depth : Nat}
  {D : ActualTubeDatum delta iota} {hD : D.IsAdmissible}
  {C : CoherentStickyMultiscaleCover D.family}
  {S : FiniteScaleSequence delta depth}
  {epsilon : Real} {hepsilon : 0 ≤ epsilon}
  {eta : Nat → Real} {N : Nat}
  {W : FirstParentwiseNormalizedCrossingWitness
    D hD C S epsilon hepsilon eta N}

/-- Rewrite the transported interval upper bound onto the literal raw cover
and literal raw parent carried by the first-crossing witness. -/
theorem rawIntervalUpper
    (X : ParentwiseCrossingIntegratedSuccessor W) :
    parentNormalizedFiberCFAt
        (paperBufferedIntervalCover
          D hD C S epsilon hepsilon W.m W.rho W.buffered) W.q ≤
      X.readiness.baseError * X.readiness.massUpper *
        X.readiness.massLower⁻¹ := by
  simpa only [crossingIntervalCover, crossingBaseQ,
    paperBufferedIntervalCover] using X.interval_upper

/-- The raw strict crossing and the inherited pointwise upper bound concern
exactly the same interval-cover parent, not two independently selected
parents. -/
theorem rawIntervalStrict_and_pointwiseUpper
    (X : ParentwiseCrossingIntegratedSuccessor W) :
    parentNormalizedFiberCFAt
        (paperBufferedIntervalCover
          D hD C S epsilon hepsilon W.m W.rho W.buffered) W.q <
        crossingStopLower W /\
      parentNormalizedFiberCFAt
          (paperBufferedIntervalCover
            D hD C S epsilon hepsilon W.m W.rho W.buffered) W.q ≤
        X.readiness.baseError * X.readiness.massUpper *
          X.readiness.massLower⁻¹ := by
  exact ⟨X.raw_interval_strict, rawIntervalUpper X⟩

/-- One inspectable statement of the complete correlation: the integrated
and dual-child views share the single base-cover q-state, while both raw
interval inequalities are stated on the literal raw `W.q`. -/
theorem sameQ_baseState_and_rawIntervalBounds
    (X : ParentwiseCrossingIntegratedSuccessor W) :
    X.integrated.factorState = X.dualChild.qFibreState.base /\
      parentNormalizedFiberCFAt
          (crossingBaseCover W) (crossingBaseQ W) <
        crossingStopLower W /\
      parentNormalizedFiberCFAt
          (paperBufferedIntervalCover
            D hD C S epsilon hepsilon W.m W.rho W.buffered) W.q <
        crossingStopLower W /\
      parentNormalizedFiberCFAt
          (paperBufferedIntervalCover
            D hD C S epsilon hepsilon W.m W.rho W.buffered) W.q ≤
        X.readiness.baseError * X.readiness.massUpper *
          X.readiness.massLower⁻¹ := by
  exact ⟨X.same_qFibre_base, X.base_bad, X.raw_interval_strict,
    rawIntervalUpper X⟩

#print axioms rawIntervalUpper
#print axioms rawIntervalStrict_and_pointwiseUpper
#print axioms sameQ_baseState_and_rawIntervalBounds

end
end Family8ParentwisePointwiseCrossingIntegratedSuccessorV1
