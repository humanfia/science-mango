import FamilyStickyGrounding.FamilyStickyScaleChainCanonicalInsertionEnvelopeTransportV2
import FamilyStickyGrounding.FamilyStickyScaleChainCanonicalTerminalUnitBodyProducerV2
import FamilyStickyGrounding.FamilyStickyScaleChainCanonicalOneStepEnvelopeCancellationV2
import FamilyStickyGrounding.FamilyStickyScaleChainCanonicalCountedStoppingDriverV2

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 3000000

open Set MeasureTheory
open scoped ENNReal NNReal

namespace FamilyStickyScaleChainCanonicalNormalizedSuccessorAdapterV2

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainActualDividingRunV1
open FamilyStickyScaleChainCoherentIntervalProducerV1
open FamilyStickyScaleChainCoherentExactHierarchyProducerV2
open FamilyStickyScaleChainCoherentExactHierarchyProducerV2.CoherentExactHierarchyFamily
open FamilyStickyScaleChainBufferedHierarchyProducerV1.MultiscaleTubeHierarchy
open FamilyStickyScaleChainCanonicalBufferedTestBodyChainV2.MultiscaleTubeHierarchy
open FamilyStickyScaleChainCanonicalCoherentBufferedFamilyV2
open FamilyStickyScaleChainSelectedNumericalAllocationProducerV1
open FamilyStickyScaleChainHierarchyRecursiveStoppingDriverV2
open FamilyStickyScaleChainLocalSuccessorAssemblerV2
open FamilyStickyScaleChainCanonicalInsertionEnvelopeTransportV2
open FamilyStickyScaleChainCanonicalTerminalUnitBodyProducerV2
open FamilyStickyScaleChainCanonicalTerminalUnitBodyProducerV2.MultiscaleTubeHierarchy
open FamilyStickyScaleChainCanonicalOneStepEnvelopeCancellationV2
open FamilyStickyScaleChainCanonicalCountedStoppingDriverV2
open FamilyStickyScaleSequenceInsertionTransportV2.FiniteScaleSequence

noncomputable section

/-!
# Canonical normalized-terminal successor adapter

For a selected bad split, the two new child bodies are chosen canonically:
each is the explicit volume-dominating terminal unit body of its inserted
depth-one hierarchy.  Positivity and terminal concentration at most one are
therefore automatic.  All untouched bodies are transported literally.

The only fresh analytic data are two normalized-terminal exponent bounds,
one for each child.  Exact one-step cancellation turns these into the child
envelope estimates; endpoint/body transport closes every untouched interval.
-/

universe u

variable {delta : NNReal} {gapEpsilon : Real}
  {N : Nat} {eta : Nat -> Real}
  {iota : Type u} [Fintype iota] [DecidableEq iota]
  {fine : UniformTubeFamily delta iota}

variable
    (C : CoherentStickyMultiscaleCover fine)
    (gap_nonneg : 0 <= gapEpsilon) (delta_pos : 0 < delta)
    (Q : CanonicalOneStepStoppingData C N gapEpsilon eta)
    (bad : SelectedActualBadSplit C (Q.toState C delta_pos))

/-! ## Automatic inserted bodies -/

/-- The upper child's explicit volume-dominating terminal unit body. -/
def canonicalInsertedUpperBody : ConvexBody Space :=
  canonicalTerminalUnitBody
    ((insertedExactFamily C gap_nonneg delta_pos Q bad).hierarchy
      (upperChildIndex bad.selectedStep))

/-- The lower child's explicit volume-dominating terminal unit body. -/
def canonicalInsertedLowerBody : ConvexBody Space :=
  canonicalTerminalUnitBody
    ((insertedExactFamily C gap_nonneg delta_pos Q bad).hierarchy
      (lowerChildIndex bad.selectedStep))

/-- The full inserted body family: canonical unit bodies on the two children
and the old bodies, transported literally, on every untouched interval. -/
def canonicalInsertedBody : Fin (Q.depth + 1) -> ConvexBody Space :=
  insertedBody C delta_pos Q bad
    (canonicalInsertedUpperBody C gap_nonneg delta_pos Q bad)
    (canonicalInsertedLowerBody C gap_nonneg delta_pos Q bad)

theorem canonicalInsertedUpperBody_volume_pos :
    0 < volume
      (canonicalInsertedUpperBody C gap_nonneg delta_pos Q bad : Set Space) := by
  exact canonicalTerminalUnitBody_volume_pos _

theorem canonicalInsertedLowerBody_volume_pos :
    0 < volume
      (canonicalInsertedLowerBody C gap_nonneg delta_pos Q bad : Set Space) := by
  exact canonicalTerminalUnitBody_volume_pos _

theorem canonicalInsertedBody_volume_pos :
    forall k, 0 < volume
      (canonicalInsertedBody C gap_nonneg delta_pos Q bad k : Set Space) := by
  exact insertedBody_volume_pos C delta_pos Q bad
    (canonicalInsertedUpperBody C gap_nonneg delta_pos Q bad)
    (canonicalInsertedLowerBody C gap_nonneg delta_pos Q bad)
    (canonicalInsertedUpperBody_volume_pos C gap_nonneg delta_pos Q bad)
    (canonicalInsertedLowerBody_volume_pos C gap_nonneg delta_pos Q bad)

theorem canonicalInsertedUpperBody_top_le_one :
    concentration
        (effectiveActiveFamily
          ((insertedExactFamily C gap_nonneg delta_pos Q bad).hierarchy
            (upperChildIndex bad.selectedStep)) 1)
        (canonicalTestBody
          ((insertedExactFamily C gap_nonneg delta_pos Q bad).hierarchy
            (upperChildIndex bad.selectedStep))
          (canonicalInsertedUpperBody C gap_nonneg delta_pos Q bad) 1) <= 1 := by
  exact canonicalTerminalUnitBody_top_le_one _

theorem canonicalInsertedLowerBody_top_le_one :
    concentration
        (effectiveActiveFamily
          ((insertedExactFamily C gap_nonneg delta_pos Q bad).hierarchy
            (lowerChildIndex bad.selectedStep)) 1)
        (canonicalTestBody
          ((insertedExactFamily C gap_nonneg delta_pos Q bad).hierarchy
            (lowerChildIndex bad.selectedStep))
          (canonicalInsertedLowerBody C gap_nonneg delta_pos Q bad) 1) <= 1 := by
  exact canonicalTerminalUnitBody_top_le_one _

/-- Terminal normalization for the complete inserted family.  The child
bounds come from the explicit unit bodies, and insertion transport reuses the
old terminal theorem everywhere else. -/
theorem canonicalInsertedBody_terminal_top_le_one :
    forall k,
      concentration
          (effectiveActiveFamily
            ((insertedExactFamily C gap_nonneg delta_pos Q bad).hierarchy k) 1)
          (canonicalTestBody
            ((insertedExactFamily C gap_nonneg delta_pos Q bad).hierarchy k)
            (canonicalInsertedBody C gap_nonneg delta_pos Q bad k) 1) <= 1 := by
  exact insertedTerminal_top_le_one C gap_nonneg delta_pos Q bad
    (canonicalInsertedUpperBody C gap_nonneg delta_pos Q bad)
    (canonicalInsertedLowerBody C gap_nonneg delta_pos Q bad)
    (canonicalInsertedUpperBody_top_le_one C gap_nonneg delta_pos Q bad)
    (canonicalInsertedLowerBody_top_le_one C gap_nonneg delta_pos Q bad)

/-! ## The two remaining analytic atoms -/

/-- Exactly the two normalized-terminal estimates attached to the new
children, both stated for the complete automatically inserted body family. -/
structure CanonicalInsertedNormalizedTerminalBounds where
  upper : OneStepNormalizedTerminalExponentBound C
    (insertedExactFamily C gap_nonneg delta_pos Q bad)
    (canonicalInsertedBody C gap_nonneg delta_pos Q bad)
    (bad.refinedScales C (Q.toState C delta_pos) gap_nonneg delta_pos)
    eta (Q.stage + 1) (upperChildIndex bad.selectedStep)
  lower : OneStepNormalizedTerminalExponentBound C
    (insertedExactFamily C gap_nonneg delta_pos Q bad)
    (canonicalInsertedBody C gap_nonneg delta_pos Q bad)
    (bad.refinedScales C (Q.toState C delta_pos) gap_nonneg delta_pos)
    eta (Q.stage + 1) (lowerChildIndex bad.selectedStep)

/-- Exact cancellation turns one normalized-terminal atom into the
corresponding canonical hierarchy-envelope estimate. -/
theorem canonicalInsertedEnvelope_le_requiredGlobalPowerAt
    (k : Fin (Q.depth + 1))
    (bound : OneStepNormalizedTerminalExponentBound C
      (insertedExactFamily C gap_nonneg delta_pos Q bad)
      (canonicalInsertedBody C gap_nonneg delta_pos Q bad)
      (bad.refinedScales C (Q.toState C delta_pos) gap_nonneg delta_pos)
      eta (Q.stage + 1) k) :
    canonicalHierarchyEnvelopeAt
        (insertedExactFamily C gap_nonneg delta_pos Q bad) (by omega)
        (canonicalInsertedBody C gap_nonneg delta_pos Q bad) k <=
      requiredGlobalPowerAt
        (bad.refinedScales C (Q.toState C delta_pos) gap_nonneg delta_pos)
        eta (Q.stage + 1) k := by
  have theta_le_one :
      ((bad.refinedScales C (Q.toState C delta_pos) gap_nonneg delta_pos).theta k :
        ENNReal) <= 1 := by
    exact_mod_cast
      (bad.refinedScales C (Q.toState C delta_pos) gap_nonneg delta_pos).theta_le_one k
  calc
    canonicalHierarchyEnvelopeAt
          (insertedExactFamily C gap_nonneg delta_pos Q bad) (by omega)
          (canonicalInsertedBody C gap_nonneg delta_pos Q bad) k =
        canonicalOneStepNormalizedTerminalAt C
          (insertedExactFamily C gap_nonneg delta_pos Q bad)
          (canonicalInsertedBody C gap_nonneg delta_pos Q bad) k :=
      canonicalHierarchyEnvelopeAt_one_eq_normalizedTerminal C
        (insertedExactFamily C gap_nonneg delta_pos Q bad) delta_pos
        (canonicalInsertedBody C gap_nonneg delta_pos Q bad)
        (canonicalInsertedBody_volume_pos C gap_nonneg delta_pos Q bad) k
    _ <=
        ((bad.refinedScales C (Q.toState C delta_pos) gap_nonneg delta_pos).theta k :
          ENNReal) ^ bound.exponent := bound.normalizedTerminal_upper
    _ <=
        ((bad.refinedScales C (Q.toState C delta_pos) gap_nonneg delta_pos).theta k :
          ENNReal) ^ (-eta ((Q.stage + 1) - 1)) :=
      ENNReal.rpow_le_rpow_of_exponent_ge theta_le_one bound.exponent_balance
    _ = requiredGlobalPowerAt
          (bad.refinedScales C (Q.toState C delta_pos) gap_nonneg delta_pos)
          eta (Q.stage + 1) k := rfl

/-! ## Direct counted-successor construction -/

/-- Construct the complete next canonical counted datum from precisely the
two child normalized-terminal bounds.  No whole-family envelope or terminal
normalization premise is accepted. -/
def canonicalInsertedSuccessorData_of_normalizedTerminalBounds
    (eta_monotone : Monotone eta)
    (stage_lt : Q.stage < N)
    (bounds : CanonicalInsertedNormalizedTerminalBounds C gap_nonneg delta_pos
      Q bad) :
    CanonicalInsertedSuccessorData C gap_nonneg delta_pos Q bad stage_lt where
  initialBody := canonicalInsertedBody C gap_nonneg delta_pos Q bad
  initialVolume_pos :=
    canonicalInsertedBody_volume_pos C gap_nonneg delta_pos Q bad
  terminal_top_le_one :=
    canonicalInsertedBody_terminal_top_le_one C gap_nonneg delta_pos Q bad
  canonicalEnvelope_upper := by
    let href := bad.refinedScales_refinesAt C (Q.toState C delta_pos)
      gap_nonneg delta_pos
    intro k
    refine Fin.succAboveCases
      (α := fun k : Fin (Q.depth + 1) =>
        canonicalHierarchyEnvelopeAt
            (insertedExactFamily C gap_nonneg delta_pos Q bad) (by omega)
            (canonicalInsertedBody C gap_nonneg delta_pos Q bad) k <=
          requiredGlobalPowerAt
            (bad.refinedScales C (Q.toState C delta_pos) gap_nonneg delta_pos)
            eta (Q.stage + 1) k)
      (lowerChildIndex (show Fin Q.depth from bad.selectedStep))
      (canonicalInsertedEnvelope_le_requiredGlobalPowerAt C gap_nonneg
        delta_pos Q bad (lowerChildIndex (show Fin Q.depth from bad.selectedStep)) bounds.lower)
      ?_ k
    intro j
    rcases lt_trichotomy j (show Fin Q.depth from bad.selectedStep) with hjm | hjm | hmj
    . rw [lowerChild_succAbove_eq_before (show Fin Q.depth from bad.selectedStep) j hjm]
      calc
        canonicalHierarchyEnvelopeAt
            (insertedExactFamily C gap_nonneg delta_pos Q bad) (by omega)
            (canonicalInsertedBody C gap_nonneg delta_pos Q bad)
            (beforeIntervalEmbedding Q.depth j) =
          canonicalHierarchyEnvelopeAt
            (CoherentExactHierarchyFamily.ofFiniteScaleSequence C Q.scales
              Q.fine_refined_nonempty)
            (by omega) Q.initialBody j := by
              exact canonicalHierarchyEnvelopeAt_before_eq C Q.scales
                (show Fin Q.depth from bad.selectedStep) j bad.rho
                (bad.refinedScales C (Q.toState C delta_pos)
                  gap_nonneg delta_pos)
                href hjm Q.fine_refined_nonempty Q.initialBody
                (canonicalInsertedUpperBody C gap_nonneg delta_pos Q bad)
                (canonicalInsertedLowerBody C gap_nonneg delta_pos Q bad)
        _ <= requiredGlobalPowerAt Q.scales eta Q.stage j :=
          Q.canonicalEnvelope_upper j
        _ <= requiredGlobalPowerAt Q.scales eta (Q.stage + 1) j :=
          requiredGlobalPowerAt_le_succ Q.scales eta_monotone j
        _ = requiredGlobalPowerAt
            (bad.refinedScales C (Q.toState C delta_pos)
              gap_nonneg delta_pos)
            eta (Q.stage + 1) (beforeIntervalEmbedding Q.depth j) :=
          (requiredGlobalPowerAt_before_eq eta (Q.stage + 1) href hjm).symm
    . subst j
      rw [lowerChild_succAbove_eq_upper
        (show Fin Q.depth from bad.selectedStep)]
      exact canonicalInsertedEnvelope_le_requiredGlobalPowerAt C gap_nonneg
        delta_pos Q bad
        (upperChildIndex (show Fin Q.depth from bad.selectedStep)) bounds.upper
    . rw [lowerChild_succAbove_eq_after (show Fin Q.depth from bad.selectedStep) j hmj]
      calc
        canonicalHierarchyEnvelopeAt
            (insertedExactFamily C gap_nonneg delta_pos Q bad) (by omega)
            (canonicalInsertedBody C gap_nonneg delta_pos Q bad)
            (afterIntervalEmbedding Q.depth j) =
          canonicalHierarchyEnvelopeAt
            (CoherentExactHierarchyFamily.ofFiniteScaleSequence C Q.scales
              Q.fine_refined_nonempty)
            (by omega) Q.initialBody j := by
              exact canonicalHierarchyEnvelopeAt_after_eq C Q.scales
                (show Fin Q.depth from bad.selectedStep) j bad.rho
                (bad.refinedScales C (Q.toState C delta_pos)
                  gap_nonneg delta_pos)
                href hmj Q.fine_refined_nonempty Q.initialBody
                (canonicalInsertedUpperBody C gap_nonneg delta_pos Q bad)
                (canonicalInsertedLowerBody C gap_nonneg delta_pos Q bad)
        _ <= requiredGlobalPowerAt Q.scales eta Q.stage j :=
          Q.canonicalEnvelope_upper j
        _ <= requiredGlobalPowerAt Q.scales eta (Q.stage + 1) j :=
          requiredGlobalPowerAt_le_succ Q.scales eta_monotone j
        _ = requiredGlobalPowerAt
            (bad.refinedScales C (Q.toState C delta_pos)
              gap_nonneg delta_pos)
            eta (Q.stage + 1) (afterIntervalEmbedding Q.depth j) :=
          (requiredGlobalPowerAt_after_eq eta (Q.stage + 1) href hmj).symm

/-- A canonical analytic successor whose only state-dependent analytic
output is the pair of new-child normalized-terminal bounds. -/
def CanonicalNormalizedTerminalAnalyticSuccessor
    (C : CoherentStickyMultiscaleCover fine)
    (gap_nonneg : 0 <= gapEpsilon) (delta_pos : 0 < delta) : Type _ :=
  forall (X : CanonicalCountedState C delta_pos N gapEpsilon eta),
    forall _stage_lt : X.data.stage < N,
    forall bad : SelectedActualBadSplit C (X.toState C delta_pos),
      CanonicalInsertedNormalizedTerminalBounds C gap_nonneg delta_pos
        X.data bad

/-- Forget the automatic construction to the canonical counted driver's
successor interface. -/
def CanonicalNormalizedTerminalAnalyticSuccessor.toCanonicalCountedAnalyticSuccessor
    (C : CoherentStickyMultiscaleCover fine)
    (gap_nonneg : 0 <= gapEpsilon) (delta_pos : 0 < delta)
    (eta_monotone : Monotone eta)
    (successor : CanonicalNormalizedTerminalAnalyticSuccessor
      (N := N) (eta := eta) C gap_nonneg delta_pos) :
    CanonicalCountedAnalyticSuccessor (N := N) (eta := eta)
      C gap_nonneg delta_pos := by
  intro X stage_lt bad
  exact canonicalInsertedSuccessorData_of_normalizedTerminalBounds C
    gap_nonneg delta_pos X.data bad eta_monotone stage_lt
    (successor X stage_lt bad)

#print axioms canonicalInsertedBody_volume_pos
#print axioms canonicalInsertedBody_terminal_top_le_one
#print axioms canonicalInsertedEnvelope_le_requiredGlobalPowerAt
#print axioms canonicalInsertedSuccessorData_of_normalizedTerminalBounds
#print axioms CanonicalNormalizedTerminalAnalyticSuccessor.toCanonicalCountedAnalyticSuccessor

end
end FamilyStickyScaleChainCanonicalNormalizedSuccessorAdapterV2
