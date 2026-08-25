import FamilyStickyGrounding.FamilyStickyScaleChainLocalSuccessorAssemblerV2
import FamilyStickyGrounding.FamilyStickyScaleChainCanonicalCoherentBufferedFamilyV2
import FamilyStickyGrounding.FamilyStickyScaleChainCoherentMassLocalizationProducerV1
import FamilyStickyGrounding.FamilyStickyScaleChainExponentProductBudgetV1

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace FamilyStickyScaleChainBadSplitChildEnvelopeReductionV2

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDeltaMaxFiniteChainV2.StickyScaleCover
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainActualDividingRunV1
open FamilyStickyScaleChainActualDividingRunV1.BufferedChainFamily
open FamilyStickyScaleChainBufferedHierarchyProducerV1.MultiscaleTubeHierarchy
open FamilyStickyScaleChainCoherentIntervalProducerV1
open FamilyStickyScaleChainCoherentExactHierarchyProducerV2
open FamilyStickyScaleChainCoherentExactHierarchyProducerV2.BoundedMonotoneRadiusChain
open FamilyStickyScaleChainCoherentExactHierarchyProducerV2.CoherentExactHierarchyFamily
open FamilyStickyScaleChainCanonicalBufferedTestBodyChainV2.MultiscaleTubeHierarchy
open FamilyStickyScaleChainCanonicalCoherentBufferedFamilyV2
open FamilyStickyScaleChainCoherentMassLocalizationProducerV1
open FamilyStickyScaleChainExponentProductBudgetV1
open FamilyStickyScaleChainHierarchyGlobalEnvelopeV2
open FamilyStickyScaleChainHierarchyRecursiveStoppingDriverV2
open FamilyStickyScaleChainLocalSuccessorAssemblerV2
open FamilyStickyScaleChainActualStoppingUpstreamClosureV1
open FamilyStickyScaleChainTerminalFiniteSearchV1
open FamilyStickyScaleSequenceInsertionTransportV2.FiniteScaleSequence
open FamilyStickyScaleChainSelectedNumericalAllocationProducerV1

noncomputable section

/-!
# Bad-split child-envelope reduction

A literal bad split controls the terminal coarse concentration at its
inserted radius.  It does not control the exact test-body loss, the active
fine cardinality used as the coherent bridge's branching factor, or the two
endpoint volume ratios.  This module makes that boundary explicit.

The inserted scale sequence first produces the genuine one-step coherent
hierarchy on every new interval.  For the lower child, the selected strict
deficit is transported through the zero-buffer normalized round trip.  When
the selected threshold is at most one, this automatically discharges the
lower child's terminal normalization.  The final reduction asks separately
for power bounds on the exact dimensional loss, literal branching factor,
and endpoint ratio; these atomic inequalities imply the two child envelope
fields required by `LocalEnvelopeRefinementCertificate`.
-/

universe u

variable {delta : NNReal} {gapEpsilon : Real}
  {N : Nat} {eta : Nat -> Real}
  {iota : Type u} [Fintype iota] [DecidableEq iota]
  {fine : UniformTubeFamily delta iota}

variable
    (C : CoherentStickyMultiscaleCover fine)
    (gap_nonneg : 0 <= gapEpsilon) (delta_pos : 0 < delta)
    (X : HierarchyStoppingState delta N gapEpsilon eta)
    (bad : SelectedActualBadSplit C X)

/-! ## The canonical exact hierarchy after insertion -/

/-- The literal one-step coherent hierarchy family on the refined scale
sequence.  Neither child cover nor any intermediate family is supplied as
independent data. -/
def refinedExactFamily
    (hfine : fine.refinement.refined.Nonempty) :
    CoherentExactHierarchyFamily C (X.depth + 1) 1 :=
  CoherentExactHierarchyFamily.ofFiniteScaleSequence C
    (bad.refinedScales C X gap_nonneg delta_pos) hfine

@[simp] theorem upperChild_effectiveRadius_zero
    (hfine : fine.refinement.refined.Nonempty) :
    ((refinedExactFamily C gap_nonneg delta_pos X bad hfine).hierarchy
        (upperChildIndex bad.selectedStep)).effectiveRadius 0 = bad.rho := by
  change
    ((CoherentExactHierarchyFamily.ofFiniteScaleSequence C
          (bad.refinedScales C X gap_nonneg delta_pos) hfine).hierarchy
        (upperChildIndex bad.selectedStep)).effectiveRadius 0 = bad.rho
  rw [CoherentExactHierarchyFamily.ofFiniteScaleSequence_effectiveRadius_zero]
  exact tau_upperChild_eq
    (bad.refinedScales_refinesAt C X gap_nonneg delta_pos)

@[simp] theorem upperChild_effectiveRadius_one
    (hfine : fine.refinement.refined.Nonempty) :
    ((refinedExactFamily C gap_nonneg delta_pos X bad hfine).hierarchy
        (upperChildIndex bad.selectedStep)).effectiveRadius 1 =
      X.scales.theta bad.selectedStep := by
  change
    ((CoherentExactHierarchyFamily.ofFiniteScaleSequence C
          (bad.refinedScales C X gap_nonneg delta_pos) hfine).hierarchy
        (upperChildIndex bad.selectedStep)).effectiveRadius 1 =
      X.scales.theta bad.selectedStep
  rw [CoherentExactHierarchyFamily.ofFiniteScaleSequence_effectiveRadius_one]
  exact theta_upperChild_eq
    (bad.refinedScales_refinesAt C X gap_nonneg delta_pos)

@[simp] theorem lowerChild_effectiveRadius_zero
    (hfine : fine.refinement.refined.Nonempty) :
    ((refinedExactFamily C gap_nonneg delta_pos X bad hfine).hierarchy
        (lowerChildIndex bad.selectedStep)).effectiveRadius 0 =
      X.scales.tau bad.selectedStep := by
  change
    ((CoherentExactHierarchyFamily.ofFiniteScaleSequence C
          (bad.refinedScales C X gap_nonneg delta_pos) hfine).hierarchy
        (lowerChildIndex bad.selectedStep)).effectiveRadius 0 =
      X.scales.tau bad.selectedStep
  rw [CoherentExactHierarchyFamily.ofFiniteScaleSequence_effectiveRadius_zero]
  exact tau_lowerChild_eq
    (bad.refinedScales_refinesAt C X gap_nonneg delta_pos)

@[simp] theorem lowerChild_effectiveRadius_one
    (hfine : fine.refinement.refined.Nonempty) :
    ((refinedExactFamily C gap_nonneg delta_pos X bad hfine).hierarchy
        (lowerChildIndex bad.selectedStep)).effectiveRadius 1 = bad.rho := by
  change
    ((CoherentExactHierarchyFamily.ofFiniteScaleSequence C
          (bad.refinedScales C X gap_nonneg delta_pos) hfine).hierarchy
        (lowerChildIndex bad.selectedStep)).effectiveRadius 1 = bad.rho
  rw [CoherentExactHierarchyFamily.ofFiniteScaleSequence_effectiveRadius_one]
  exact theta_lowerChild_eq
    (bad.refinedScales_refinesAt C X gap_nonneg delta_pos)

/-- The source cover of either new one-step hierarchy survives the exact
partition normalizer as a full structure. -/
@[simp] theorem refined_normalizedSourceCover_eq_intervalCover
    (hfine : fine.refinement.refined.Nonempty)
    (k : Fin (X.depth + 1)) :
    let F := refinedExactFamily C gap_nonneg delta_pos X bad hfine
    (F.chain k).normalizedSourceCover C hfine 0 (by omega) =
      C.intervalScaleCover
        ((bad.refinedScales C X gap_nonneg delta_pos).tau k)
        ((bad.refinedScales C X gap_nonneg delta_pos).theta k)
        ((bad.refinedScales C X gap_nonneg delta_pos).delta_le_tau k)
        ((bad.refinedScales C X gap_nonneg delta_pos).tau_le_theta k)
        ((bad.refinedScales C X gap_nonneg delta_pos).theta_le_one k) := by
  dsimp [refinedExactFamily]
  rw [BoundedMonotoneRadiusChain.normalizedSourceCover_eq_intervalCover]
  exact BoundedMonotoneRadiusChain.ofAdjacentInterval_intervalCover_zero
    (bad.refinedScales C X gap_nonneg delta_pos) C k

/-! ## The strict bad value is the lower child's terminal coarse value -/

/-- The lower coherent child ends at exactly the coarse value appearing in
`SelectedActualBadSplit.strict`.  This is an equality, not an analytic
comparison. -/
theorem lowerChild_normalized_coarseDeltaMax_eq_badValue
    (hfine : fine.refinement.refined.Nonempty) :
    let F := refinedExactFamily C gap_nonneg delta_pos X bad hfine
    coarseDeltaMax
        ((F.chain (lowerChildIndex bad.selectedStep)).normalizedSourceCover
          C hfine 0 (by omega)) =
      (C.toActualIntervalCovers X.scales).coarseValueAt
        bad.selectedStep bad.rho := by
  dsimp only
  let Sref := bad.refinedScales C X gap_nonneg delta_pos
  let k := lowerChildIndex bad.selectedStep
  let href := bad.refinedScales_refinesAt C X gap_nonneg delta_pos
  have hTauRho : X.scales.tau bad.selectedStep <= bad.rho := by
    rw [<- tau_lowerChild_eq href, <- theta_lowerChild_eq href]
    exact Sref.tau_le_theta k
  have hRhoOne : bad.rho <= 1 := by
    rw [<- theta_lowerChild_eq href]
    exact Sref.theta_le_one k
  have hround := refined_normalizedSourceCover_eq_intervalCover C
    gap_nonneg delta_pos X bad hfine k
  calc
    coarseDeltaMax
        (((refinedExactFamily C gap_nonneg delta_pos X bad hfine).chain k).normalizedSourceCover
          C hfine 0 (by omega)) =
        coarseDeltaMax
          (C.intervalScaleCover (Sref.tau k) (Sref.theta k)
            (Sref.delta_le_tau k) (Sref.tau_le_theta k)
            (Sref.theta_le_one k)) :=
      congrArg (fun Q => coarseDeltaMax Q) hround
    _ = FamilyStickyScaleChainActualValuesV1.StickyMultiscaleCover.actualCoarseDeltaMaxAt C.base
          (Sref.theta k) :=
      CoherentStickyMultiscaleCover.intervalScaleCover_coarseDeltaMax_eq_actualCoarseDeltaMaxAt
        C (Sref.tau k) (Sref.theta k) (Sref.delta_le_tau k)
          (Sref.tau_le_theta k) (Sref.theta_le_one k)
    _ = FamilyStickyScaleChainActualValuesV1.StickyMultiscaleCover.actualCoarseDeltaMaxAt C.base bad.rho := by
      rw [theta_lowerChild_eq href]
    _ = (C.toActualIntervalCovers X.scales).coarseValueAt
          bad.selectedStep bad.rho :=
      (CoherentStickyMultiscaleCover.toActualIntervalCovers_coarseValueAt_eq_base
        C X.scales bad.selectedStep bad.rho hTauRho hRhoOne).symm

/-- The selected strict deficit, now stated on the literal normalized lower
child cover. -/
theorem lowerChild_normalized_coarseDeltaMax_lt_splitThreshold
    (hfine : fine.refinement.refined.Nonempty) :
    let F := refinedExactFamily C gap_nonneg delta_pos X bad hfine
    coarseDeltaMax
        ((F.chain (lowerChildIndex bad.selectedStep)).normalizedSourceCover
          C hfine 0 (by omega)) <
      splitThreshold X.scales eta X.stage bad.selectedStep bad.rho := by
  exact (lowerChild_normalized_coarseDeltaMax_eq_badValue C gap_nonneg
    delta_pos X bad hfine).trans_lt bad.strict
/-- Buffering a tube by zero changes neither its convex body nor its
certified radius after simplification. -/
@[simp] theorem tube_buffer_zero_body {rho : NNReal} (T : Tube rho) :
    (T.buffer 0).body = T.body := by
  apply ConvexBody.ext
  simp [Tube.buffer, Tube.changeRadius, Tube.body, Tube.carrier]
theorem refined_effective_activeCoarseFamily_eq_normalized
    (hfine : fine.refinement.refined.Nonempty)
    (k : Fin (X.depth + 1)) :
    let F := refinedExactFamily C gap_nonneg delta_pos X bad hfine
    (effectiveStickyScaleCover (F.hierarchy k) 0 (by omega)).activeCoarseFamily =
      ((F.chain k).normalizedSourceCover C hfine 0 (by omega)).activeCoarseFamily := by
  dsimp only
  let F := refinedExactFamily C gap_nonneg delta_pos X bad hfine
  funext q
  change
    (((((F.chain k).family C 1).tubes q.1).buffer
        ((F.hierarchy k).accumulatedBuffer 1)).body) =
      (((F.chain k).family C 1).tubes q.1).body
  have hbuffer : (F.hierarchy k).accumulatedBuffer 1 = 0 :=
    (F.chain k).toHierarchy_accumulatedBuffer C hfine 1
  rw [hbuffer]
  exact tube_buffer_zero_body _

/-- The effective terminal coarse Delta-max equals the normalized coherent
source-cover value. -/
theorem refined_effective_coarseDeltaMax_eq_normalized
    (hfine : fine.refinement.refined.Nonempty)
    (k : Fin (X.depth + 1)) :
    let F := refinedExactFamily C gap_nonneg delta_pos X bad hfine
    coarseDeltaMax (effectiveStickyScaleCover (F.hierarchy k) 0 (by omega)) =
      coarseDeltaMax
        ((F.chain k).normalizedSourceCover C hfine 0 (by omega)) := by
  dsimp only
  exact congrArg maximalConcentration
    (refined_effective_activeCoarseFamily_eq_normalized C gap_nonneg
      delta_pos X bad hfine k)

/-- The literal bad deficit bounds every terminal lower-child test body,
because the terminal effective family is the normalized source-cover active
coarse family. -/
theorem lowerChild_terminal_concentration_lt_splitThreshold
    (hfine : fine.refinement.refined.Nonempty) (K : ConvexBody Space) :
    let F := refinedExactFamily C gap_nonneg delta_pos X bad hfine
    concentration
        (effectiveActiveFamily
          (F.hierarchy (lowerChildIndex bad.selectedStep)) 1) K <
      splitThreshold X.scales eta X.stage bad.selectedStep bad.rho := by
  dsimp only
  let F := refinedExactFamily C gap_nonneg delta_pos X bad hfine
  let k := lowerChildIndex bad.selectedStep
  have hconcentration :
      concentration (effectiveActiveFamily (F.hierarchy k) 1) K <=
        coarseDeltaMax
          (effectiveStickyScaleCover (F.hierarchy k) 0 (by omega)) := by
    change concentration (effectiveActiveFamily (F.hierarchy k) 1) K <=
      maximalConcentration (effectiveActiveFamily (F.hierarchy k) 1)
    exact concentration_le_maximalConcentration _ _
  calc
    concentration (effectiveActiveFamily (F.hierarchy k) 1) K <=
        coarseDeltaMax
          (effectiveStickyScaleCover (F.hierarchy k) 0 (by omega)) :=
      hconcentration
    _ = coarseDeltaMax
        ((F.chain k).normalizedSourceCover C hfine 0 (by omega)) :=
      refined_effective_coarseDeltaMax_eq_normalized C gap_nonneg
        delta_pos X bad hfine k
    _ < splitThreshold X.scales eta X.stage bad.selectedStep bad.rho :=
      lowerChild_normalized_coarseDeltaMax_lt_splitThreshold C gap_nonneg
        delta_pos X bad hfine

/-- If the selected threshold is at most one, the lower child terminal
normalization required by the canonical test-body producer is automatic. -/
theorem lowerChild_terminal_concentration_le_one
    (hfine : fine.refinement.refined.Nonempty) (K : ConvexBody Space)
    (threshold_le_one :
      splitThreshold X.scales eta X.stage bad.selectedStep bad.rho <= 1) :
    let F := refinedExactFamily C gap_nonneg delta_pos X bad hfine
    concentration
        (effectiveActiveFamily
          (F.hierarchy (lowerChildIndex bad.selectedStep)) 1) K <= 1 := by
  exact (lowerChild_terminal_concentration_lt_splitThreshold C gap_nonneg
    delta_pos X bad hfine K).le.trans threshold_le_one

/-- Fill the all-interval terminal normalization while asking the caller only
for intervals other than the lower child. -/
theorem refined_terminalTop_of_bad
    (hfine : fine.refinement.refined.Nonempty)
    (initialBody : Fin (X.depth + 1) -> ConvexBody Space)
    (threshold_le_one :
      splitThreshold X.scales eta X.stage bad.selectedStep bad.rho <= 1)
    (top_other : forall k, k ≠ lowerChildIndex bad.selectedStep ->
      let F := refinedExactFamily C gap_nonneg delta_pos X bad hfine
      concentration (effectiveActiveFamily (F.hierarchy k) 1)
          (canonicalTestBody (F.hierarchy k) (initialBody k) 1) <= 1) :
    forall k,
      let F := refinedExactFamily C gap_nonneg delta_pos X bad hfine
      concentration (effectiveActiveFamily (F.hierarchy k) 1)
          (canonicalTestBody (F.hierarchy k) (initialBody k) 1) <= 1 := by
  intro k
  by_cases hk : k = lowerChildIndex bad.selectedStep
  · subst k
    exact lowerChild_terminal_concentration_le_one C gap_nonneg delta_pos
      X bad hfine _ threshold_le_one
  · exact top_other k hk


/-! ## Atomic one-step hierarchy-envelope budget -/

/-- The three genuinely quantitative estimates left by a one-step coherent
hierarchy.  None of the fields is a global-product or child-envelope bound. -/
structure OneStepHierarchyEnvelopeAtoms
    {outerDepth : Nat}
    (B : BufferedChainFamily outerDepth 1)
    (S : FiniteScaleSequence delta outerDepth)
    (profile : Nat -> Real) (stage : Nat) (k : Fin outerDepth) where
  dimensionalExponent : Real
  branchingExponent : Real
  endpointExponent : Real
  dimensionalLoss_upper :
    (B.datum k).dimensionalLoss 0 <=
      (S.theta k : ENNReal) ^ dimensionalExponent
  branchingFactor_upper :
    (((B.hierarchy k).step 0 (by omega)).combinatorics.branchingFactor :
        ENNReal) <=
      (S.theta k : ENNReal) ^ branchingExponent
  endpointRatio_upper :
    actualGlobalEndpointRatioAt B k <=
      (S.theta k : ENNReal) ^ endpointExponent
  exponent_balance :
    -profile (stage - 1) <=
      (dimensionalExponent + branchingExponent) + endpointExponent

/-- The three atomic bounds imply the exact hierarchy-envelope comparison
at one interval. -/
theorem hierarchyGlobalEnvelopeAt_le_requiredGlobalPowerAt_of_atoms
    {outerDepth stage : Nat}
    (B : BufferedChainFamily outerDepth 1)
    (S : FiniteScaleSequence delta outerDepth)
    (profile : Nat -> Real) (k : Fin outerDepth)
    (delta_pos : 0 < delta)
    (A : OneStepHierarchyEnvelopeAtoms B S profile stage k) :
    hierarchyGlobalEnvelopeAt B k <=
      requiredGlobalPowerAt S profile stage k := by
  have theta_pos : 0 < S.theta k :=
    ScaleSequence.theta_pos_of_delta_pos S delta_pos k
  have theta_ne_zero : (S.theta k : ENNReal) ≠ 0 :=
    ENNReal.coe_ne_zero.mpr theta_pos.ne'
  have theta_ne_top : (S.theta k : ENNReal) ≠ ∞ :=
    ENNReal.coe_ne_top
  have theta_le_one : (S.theta k : ENNReal) <= 1 := by
    exact_mod_cast S.theta_le_one k
  have local_upper :
      (B.datum k).dimensionalLoss 0 *
          (((B.hierarchy k).step 0 (by omega)).combinatorics.branchingFactor :
            ENNReal) <=
        (S.theta k : ENNReal) ^
          (A.dimensionalExponent + A.branchingExponent) := by
    calc
      (B.datum k).dimensionalLoss 0 *
          (((B.hierarchy k).step 0 (by omega)).combinatorics.branchingFactor :
            ENNReal) <=
          (S.theta k : ENNReal) ^ A.dimensionalExponent *
            (S.theta k : ENNReal) ^ A.branchingExponent :=
        mul_le_mul' A.dimensionalLoss_upper A.branchingFactor_upper
      _ = (S.theta k : ENNReal) ^
          (A.dimensionalExponent + A.branchingExponent) := by
        exact (ENNReal.rpow_add _ _ theta_ne_zero theta_ne_top).symm
  have envelope_upper :
      hierarchyGlobalEnvelopeAt B k <=
        (S.theta k : ENNReal) ^
          ((A.dimensionalExponent + A.branchingExponent) +
            A.endpointExponent) := by
    unfold hierarchyGlobalEnvelopeAt
    simp only [Finset.prod_range_succ, Finset.prod_range_zero,
      one_mul, zero_lt_one, dite_true]
    calc
      (B.datum k).dimensionalLoss 0 *
            (((B.hierarchy k).step 0 (by omega)).combinatorics.branchingFactor :
              ENNReal) *
          actualGlobalEndpointRatioAt B k <=
          (S.theta k : ENNReal) ^
              (A.dimensionalExponent + A.branchingExponent) *
            (S.theta k : ENNReal) ^ A.endpointExponent :=
        mul_le_mul' local_upper A.endpointRatio_upper
      _ = (S.theta k : ENNReal) ^
          ((A.dimensionalExponent + A.branchingExponent) +
            A.endpointExponent) := by
        exact (ENNReal.rpow_add _ _ theta_ne_zero theta_ne_top).symm
  calc
    hierarchyGlobalEnvelopeAt B k <=
        (S.theta k : ENNReal) ^
          ((A.dimensionalExponent + A.branchingExponent) +
            A.endpointExponent) := envelope_upper
    _ <= (S.theta k : ENNReal) ^ (-profile (stage - 1)) :=
      ENNReal.rpow_le_rpow_of_exponent_ge theta_le_one A.exponent_balance
    _ = requiredGlobalPowerAt S profile stage k := by
      rfl

/-! ## Canonical factor identity and local-certificate reduction -/

/-- Package the canonical coherent hierarchy with canonical test bodies on
the inserted scale sequence. -/
def refinedCanonicalBufferedFamily
    (hfine : fine.refinement.refined.Nonempty)
    (initialBody : Fin (X.depth + 1) -> ConvexBody Space)
    (initialVolume_pos : forall k,
      0 < volume (initialBody k : Set Space))
    (terminal_top_le_one : forall k,
      let F := refinedExactFamily C gap_nonneg delta_pos X bad hfine
      concentration (effectiveActiveFamily (F.hierarchy k) 1)
          (canonicalTestBody (F.hierarchy k) (initialBody k) 1) <= 1) :
    BufferedChainFamily (X.depth + 1) 1 :=
  canonicalBufferedChainFamily
    (refinedExactFamily C gap_nonneg delta_pos X bad hfine)
    (by omega) delta_pos initialBody initialVolume_pos terminal_top_le_one
/-- Bad-aware canonical family: only non-lower-child terminal bounds remain
as inputs; the lower-child bound is generated from the strict deficit. -/
def refinedCanonicalBufferedFamily_of_bad
    (hfine : fine.refinement.refined.Nonempty)
    (initialBody : Fin (X.depth + 1) -> ConvexBody Space)
    (initialVolume_pos : forall k,
      0 < volume (initialBody k : Set Space))
    (threshold_le_one :
      splitThreshold X.scales eta X.stage bad.selectedStep bad.rho <= 1)
    (top_other : forall k, k ≠ lowerChildIndex bad.selectedStep ->
      let F := refinedExactFamily C gap_nonneg delta_pos X bad hfine
      concentration (effectiveActiveFamily (F.hierarchy k) 1)
          (canonicalTestBody (F.hierarchy k) (initialBody k) 1) <= 1) :
    BufferedChainFamily (X.depth + 1) 1 :=
  refinedCanonicalBufferedFamily C gap_nonneg delta_pos X bad hfine
    initialBody initialVolume_pos
    (refined_terminalTop_of_bad C gap_nonneg delta_pos X bad hfine
      initialBody threshold_le_one top_other)


/-- The sole local hierarchy factor of the canonical producer is exactly the
body/tube quotient times the active-fine cardinality of the coherent interval
cover. -/
theorem refinedCanonical_localHierarchyFactor_eq
    (hfine : fine.refinement.refined.Nonempty)
    (initialBody : Fin (X.depth + 1) -> ConvexBody Space)
    (initialVolume_pos : forall k,
      0 < volume (initialBody k : Set Space))
    (terminal_top_le_one : forall k,
      let F := refinedExactFamily C gap_nonneg delta_pos X bad hfine
      concentration (effectiveActiveFamily (F.hierarchy k) 1)
          (canonicalTestBody (F.hierarchy k) (initialBody k) 1) <= 1)
    (k : Fin (X.depth + 1)) :
    let F := refinedExactFamily C gap_nonneg delta_pos X bad hfine
    let B := refinedCanonicalBufferedFamily C gap_nonneg delta_pos X bad
      hfine initialBody initialVolume_pos terminal_top_le_one
    (B.datum k).dimensionalLoss 0 *
        (((B.hierarchy k).step 0 (by omega)).combinatorics.branchingFactor :
          ENNReal) =
      exactDimensionalLoss (F.hierarchy k) (by omega) (initialBody k) 0 *
        (((F.chain k).intervalCover C 0 (by omega)).activeFine.card :
          ENNReal) := by
  dsimp [refinedCanonicalBufferedFamily]
  rw [canonicalBufferedChainFamily_dimensionalLoss]
  congr 1
  exact_mod_cast coherentHierarchy_step_branchingFactor_eq_activeFine_card
    (refinedExactFamily C gap_nonneg delta_pos X bad hfine) k 0 (by omega)

/-- Once the two new intervals have atomic loss/branching/endpoint estimates,
their two envelope fields are automatic.  The untouched-interval comparisons
remain exactly the transport premises of the local assembler. -/
def localEnvelopeRefinementCertificate_of_canonical_atoms
    (hfine : fine.refinement.refined.Nonempty)
    (initialBody : Fin (X.depth + 1) -> ConvexBody Space)
    (initialVolume_pos : forall k,
      0 < volume (initialBody k : Set Space))
    (terminal_top_le_one : forall k,
      let F := refinedExactFamily C gap_nonneg delta_pos X bad hfine
      concentration (effectiveActiveFamily (F.hierarchy k) 1)
          (canonicalTestBody (F.hierarchy k) (initialBody k) 1) <= 1)
    (beforeEnvelope_le : forall j : Fin X.depth, j < bad.selectedStep ->
      hierarchyGlobalEnvelopeAt
          (refinedCanonicalBufferedFamily C gap_nonneg delta_pos X bad hfine
            initialBody initialVolume_pos terminal_top_le_one)
          (beforeIntervalEmbedding X.depth j) <=
        hierarchyGlobalEnvelopeAt X.buffered j)
    (afterEnvelope_le : forall j : Fin X.depth, bad.selectedStep < j ->
      hierarchyGlobalEnvelopeAt
          (refinedCanonicalBufferedFamily C gap_nonneg delta_pos X bad hfine
            initialBody initialVolume_pos terminal_top_le_one)
          (afterIntervalEmbedding X.depth j) <=
        hierarchyGlobalEnvelopeAt X.buffered j)
    (upperAtoms : OneStepHierarchyEnvelopeAtoms
      (refinedCanonicalBufferedFamily C gap_nonneg delta_pos X bad hfine
        initialBody initialVolume_pos terminal_top_le_one)
      (bad.refinedScales C X gap_nonneg delta_pos) eta (X.stage + 1)
      (upperChildIndex bad.selectedStep))
    (lowerAtoms : OneStepHierarchyEnvelopeAtoms
      (refinedCanonicalBufferedFamily C gap_nonneg delta_pos X bad hfine
        initialBody initialVolume_pos terminal_top_le_one)
      (bad.refinedScales C X gap_nonneg delta_pos) eta (X.stage + 1)
      (lowerChildIndex bad.selectedStep)) :
    LocalEnvelopeRefinementCertificate C gap_nonneg delta_pos X bad where
  newChainDepth := 1
  newBuffered := refinedCanonicalBufferedFamily C gap_nonneg delta_pos X bad
    hfine initialBody initialVolume_pos terminal_top_le_one
  beforeEnvelope_le := beforeEnvelope_le
  afterEnvelope_le := afterEnvelope_le
  upperChildEnvelope_upper :=
    hierarchyGlobalEnvelopeAt_le_requiredGlobalPowerAt_of_atoms
      _ _ eta _ delta_pos upperAtoms
  lowerChildEnvelope_upper :=
    hierarchyGlobalEnvelopeAt_le_requiredGlobalPowerAt_of_atoms
      _ _ eta _ delta_pos lowerAtoms
/-- Final bad-aware reduction: the lower terminal top is no longer an input.
Only non-lower terminal normalization, untouched envelopes, and the three
atomic quantitative estimates for each new child remain. -/
def localEnvelopeRefinementCertificate_of_bad_canonical_atoms
    (hfine : fine.refinement.refined.Nonempty)
    (initialBody : Fin (X.depth + 1) -> ConvexBody Space)
    (initialVolume_pos : forall k,
      0 < volume (initialBody k : Set Space))
    (threshold_le_one :
      splitThreshold X.scales eta X.stage bad.selectedStep bad.rho <= 1)
    (top_other : forall k, k ≠ lowerChildIndex bad.selectedStep ->
      let F := refinedExactFamily C gap_nonneg delta_pos X bad hfine
      concentration (effectiveActiveFamily (F.hierarchy k) 1)
          (canonicalTestBody (F.hierarchy k) (initialBody k) 1) <= 1)
    (beforeEnvelope_le : forall j : Fin X.depth, j < bad.selectedStep ->
      hierarchyGlobalEnvelopeAt
          (refinedCanonicalBufferedFamily_of_bad C gap_nonneg delta_pos X bad
            hfine initialBody initialVolume_pos threshold_le_one top_other)
          (beforeIntervalEmbedding X.depth j) <=
        hierarchyGlobalEnvelopeAt X.buffered j)
    (afterEnvelope_le : forall j : Fin X.depth, bad.selectedStep < j ->
      hierarchyGlobalEnvelopeAt
          (refinedCanonicalBufferedFamily_of_bad C gap_nonneg delta_pos X bad
            hfine initialBody initialVolume_pos threshold_le_one top_other)
          (afterIntervalEmbedding X.depth j) <=
        hierarchyGlobalEnvelopeAt X.buffered j)
    (upperAtoms : OneStepHierarchyEnvelopeAtoms
      (refinedCanonicalBufferedFamily_of_bad C gap_nonneg delta_pos X bad
        hfine initialBody initialVolume_pos threshold_le_one top_other)
      (bad.refinedScales C X gap_nonneg delta_pos) eta (X.stage + 1)
      (upperChildIndex bad.selectedStep))
    (lowerAtoms : OneStepHierarchyEnvelopeAtoms
      (refinedCanonicalBufferedFamily_of_bad C gap_nonneg delta_pos X bad
        hfine initialBody initialVolume_pos threshold_le_one top_other)
      (bad.refinedScales C X gap_nonneg delta_pos) eta (X.stage + 1)
      (lowerChildIndex bad.selectedStep)) :
    LocalEnvelopeRefinementCertificate C gap_nonneg delta_pos X bad :=
  localEnvelopeRefinementCertificate_of_canonical_atoms C gap_nonneg delta_pos
    X bad hfine initialBody initialVolume_pos
      (refined_terminalTop_of_bad C gap_nonneg delta_pos X bad hfine
        initialBody threshold_le_one top_other)
      beforeEnvelope_le afterEnvelope_le upperAtoms lowerAtoms


#print axioms refinedExactFamily
#print axioms upperChild_effectiveRadius_zero
#print axioms lowerChild_effectiveRadius_one
#print axioms refined_normalizedSourceCover_eq_intervalCover
#print axioms lowerChild_normalized_coarseDeltaMax_eq_badValue
#print axioms lowerChild_normalized_coarseDeltaMax_lt_splitThreshold
#print axioms refined_effective_activeCoarseFamily_eq_normalized
#print axioms refined_effective_coarseDeltaMax_eq_normalized
#print axioms lowerChild_terminal_concentration_le_one
#print axioms refined_terminalTop_of_bad
#print axioms hierarchyGlobalEnvelopeAt_le_requiredGlobalPowerAt_of_atoms
#print axioms refinedCanonicalBufferedFamily_of_bad
#print axioms refinedCanonical_localHierarchyFactor_eq
#print axioms localEnvelopeRefinementCertificate_of_canonical_atoms
#print axioms localEnvelopeRefinementCertificate_of_bad_canonical_atoms

end
end FamilyStickyScaleChainBadSplitChildEnvelopeReductionV2
