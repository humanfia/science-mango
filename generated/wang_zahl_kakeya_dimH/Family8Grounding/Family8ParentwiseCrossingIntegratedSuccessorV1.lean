import Family8Grounding.Family8FirstParentwiseNormalizedCrossingWitnessV1
import Family8Grounding.Family8ParentwiseBadParentPointwiseMassAwareSuccessorV1
import Family8Grounding.Family8ParentwiseBadParentIntegratedFactorStateV1
import Family8Grounding.Family8ParentwiseBadParentDualChildOrchestrationCertificateV1
import Mathlib.Tactic

/-!
# First parentwise crossing to a cross-scale integrated successor

The raw crossing lives on the literal interval cover from `tau` to `rho`.
The actual factor successor lives on the base cover at `rho`.  This module
keeps those objects separate and joins them only through the exact pointwise
parent-mass comparison on the same dependent parent `q`.

The base-cover same-`q` state is selected once by the pointwise mass-aware
producer.  The independent active-parent child is then built from that base
cover, and the existing dual-child certificate is assembled directly.  Thus
neither the interval cover nor the dual-child wrapper reruns the q-fibre
selector.  No `CFMax` branch is used.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8ParentwiseCrossingIntegratedSuccessorV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8Def212ConvexWolffAtEveryScaleV2.ScaleCover
open Family8FirstParentwiseNormalizedCrossingWitnessV1
open Family8FiniteRandomRigidMotionB2FreshGreedyV1
open Family8GeneralizedKatzTaoMultiplicityV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8NormalizedCFDividingWitnessBridgeV2.StickyScaleCover
open Family8NormalizedCFDividingWitnessFiniteSelectionV4.CoherentStickyMultiscaleCover
open Family8NormalizedCFDividingWitnessParentwiseFiniteSelectionV1.CoherentStickyMultiscaleCover
open Family8NormalizedLongIntervalFrostmanInheritanceV1
open Family8NormalizedLongIntervalPointwiseFrostmanInheritanceV1
open Family8ParentwiseBadParentDualChildOrchestrationCertificateV1
open Family8ParentwiseBadParentActualFactorListSuccessorV1
open Family8ParentwiseBadParentIntegratedFactorStateV1
open Family8ParentwiseBadParentMassAwareActiveCoarseConnectorV1
open Family8ParentwiseBadParentMassAwareFactorListStateV2
open Family8ParentwiseBadParentPointwiseMassAwareSuccessorV1
open Family8StickyActiveCoarseAdmissibleChildV1
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainCoherentIntervalProducerV1

noncomputable section

variable {delta : NNReal} {iota : Type}
  [Fintype iota] [DecidableEq iota]
  {depth : Nat}


variable {D : ActualTubeDatum delta iota} {hD : D.IsAdmissible}
  {C : CoherentStickyMultiscaleCover D.family}
  {S : FiniteScaleSequence delta depth}
  {epsilon : Real} {hepsilon : 0 ≤ epsilon}
  {eta : Nat → Real} {N : Nat}

/-- The exact stopping threshold stored by the raw crossing. -/
def crossingStopLower
    (W : FirstParentwiseNormalizedCrossingWitness
      D hD C S epsilon hepsilon eta N) : ENNReal :=
  (((W.rho / S.tau W.m : NNReal) : ENNReal) ^ eta W.stage)

/-- Buffered legality gives the literal `tau ≤ rho` relation used by both
the raw interval cover and the base-cover pointwise composer. -/
theorem crossingTauLeRho
    (W : FirstParentwiseNormalizedCrossingWitness
      D hD C S epsilon hepsilon eta N) :
    S.tau W.m ≤ W.rho :=
  actualDatum_tau_le_of_isBuffered
    D hD S hepsilon W.m W.rho W.buffered

/-- Buffered legality also fixes the exact upper-radius proof. -/
theorem crossingRhoLeOne
    (W : FirstParentwiseNormalizedCrossingWitness
      D hD C S epsilon hepsilon eta N) :
    W.rho ≤ 1 :=
  buffered_le_one S hepsilon W.m W.rho W.buffered

/-- The actual source scale is positive, hence so is the selected base
radius. -/
theorem crossingRhoPos
    (W : FirstParentwiseNormalizedCrossingWitness
      D hD C S epsilon hepsilon eta N) :
    0 < W.rho :=
  hD.delta_pos.trans_le
    ((S.delta_le_tau W.m).trans (crossingTauLeRho W))

/-- The literal base cover at the crossing radius. -/
def crossingBaseCover
    (W : FirstParentwiseNormalizedCrossingWitness
      D hD C S epsilon hepsilon eta N) :=
  C.base.cover W.rho
    ((S.delta_le_tau W.m).trans (crossingTauLeRho W)) (crossingRhoLeOne W)

/-- The interval cover kept by the raw witness, written with the same
legality proofs used by the pointwise composer. -/
def crossingIntervalCover
    (W : FirstParentwiseNormalizedCrossingWitness
      D hD C S epsilon hepsilon eta N) :=
  C.intervalScaleCover (S.tau W.m) W.rho
    (S.delta_le_tau W.m) (crossingTauLeRho W) (crossingRhoLeOne W)

/-- The same parent value, now viewed in the definitionally identical active
coarse family of the base cover at `rho`. -/
def crossingBaseQ
    (W : FirstParentwiseNormalizedCrossingWitness
      D hD C S epsilon hepsilon eta N) :
    {q // q ∈ (crossingBaseCover W).activeCoarse} :=
  W.q

@[simp] theorem crossingBaseQ_val
    (W : FirstParentwiseNormalizedCrossingWitness
      D hD C S epsilon hepsilon eta N) :
    (crossingBaseQ W).1 = W.q.1 :=
  rfl

/-- The raw interval strict crossing remains available independently of the
base-cover successor construction. -/
theorem crossingRawIntervalStrict
    (W : FirstParentwiseNormalizedCrossingWitness
      D hD C S epsilon hepsilon eta N) :
    parentNormalizedFiberCFAt
        (paperBufferedIntervalCover
          D hD C S epsilon hepsilon W.m W.rho W.buffered) W.q <
      (crossingStopLower W) :=
  W.strict_crossing


/-- Explicit readiness for the cross-scale successor.  The base-CF bound
and strict scalar comparison are separate fields; the raw interval strict
crossing is not reused as a base-cover hypothesis. -/
structure ParentwiseCrossingSuccessorReadiness
    {D : ActualTubeDatum delta iota} {hD : D.IsAdmissible}
    {C : CoherentStickyMultiscaleCover D.family}
    {S : FiniteScaleSequence delta depth}
    {epsilon : Real} {hepsilon : 0 ≤ epsilon}
    {eta : Nat → Real} {N : Nat}
    (W : FirstParentwiseNormalizedCrossingWitness
      D hD C S epsilon hepsilon eta N) where
  left : List ActualFactorDatum
  right : List ActualFactorDatum
  baseError : ENNReal
  massLower : ENNReal
  massUpper : ENNReal
  massLower_ne_zero : massLower ≠ 0
  massLower_ne_top : massLower ≠ ∞
  parentMassComparison : IntervalParentMassComparison
    C (S.tau W.m) (S.delta_le_tau W.m)
      ((crossingTauLeRho W).trans (crossingRhoLeOne W)) massLower massUpper
  base_bound : parentNormalizedFiberCFAt (crossingBaseCover W) (crossingBaseQ W) ≤ baseError
  base_strict : baseError < (crossingStopLower W)
  stopLower_ne_top : (crossingStopLower W) ≠ ∞
  factorC : ENNReal
  factor_uniform : IsCUniform (crossingBaseCover W) factorC
  rho_le_half : W.rho ≤ (2 : NNReal)⁻¹
  rho_le_sixteenth : W.rho ≤ (1 / 16 : NNReal)
  conflictThreshold : Nat
  conflict_cap : ∀ a : {q // q ∈ (crossingBaseCover W).activeCoarse},
    (normalizedConflictIndices
      (activeCoarseAggregatedDatum D (crossingBaseCover W)) a).card ≤
        conflictThreshold
  activeC : ENNReal
  katzTao_at_scale : (crossingBaseCover W).IsKatzTaoAtScale activeC

/-- Definitionally forget the V2 scale ledger while preserving its exact
base state, selected subtype, proxy Frostman certificate, and coarse shading. -/
def integratedStateOfMassAware
    {D : ActualTubeDatum delta iota}
    {rho : NNReal} {R : StickyScaleCover D.family rho}
    {left right : List ActualFactorDatum}
    {hrho : 0 < rho} {hrhoOne : rho ≤ 1}
    {q : {q // q ∈ R.activeCoarse}} {lower factorC : ENNReal}
    (X : ParentwiseBadParentMassAwareFactorListState
      D R left right hrho hrhoOne q lower factorC) :
    IntegratedBadParentFactorState
      D R left right hrho hrhoOne q lower factorC :=
  { factorState := X.base
    fresh_unitBall_frostman := X.child_proxy_frostman
    coarse_shadingMass_le_source := X.coarse_shadingMass_le_source
    coarse_shadedUnion_eq_source := X.coarse_shadedUnion_eq_source
    coarse_averageMultiplicity_le_source :=
      X.coarse_averageMultiplicity_le_source }

/-- One raw first crossing together with a single same-`q` base successor,
its independent active-parent child, and the correlated interval upper bound. -/
structure ParentwiseCrossingIntegratedSuccessor
    {D : ActualTubeDatum delta iota} {hD : D.IsAdmissible}
    {C : CoherentStickyMultiscaleCover D.family}
    {S : FiniteScaleSequence delta depth}
    {epsilon : Real} {hepsilon : 0 ≤ epsilon}
    {eta : Nat → Real} {N : Nat}
    (W : FirstParentwiseNormalizedCrossingWitness
      D hD C S epsilon hepsilon eta N) where
  readiness : ParentwiseCrossingSuccessorReadiness W
  dualChild : ParentwiseBadParentDualChildCertificate
    D (crossingBaseCover W) readiness.left readiness.right (crossingRhoPos W) (crossingRhoLeOne W)
      (crossingBaseQ W) (crossingStopLower W) readiness.factorC readiness.conflictThreshold
      readiness.activeC
  integrated : IntegratedBadParentFactorState
    D (crossingBaseCover W) readiness.left readiness.right (crossingRhoPos W) (crossingRhoLeOne W)
      (crossingBaseQ W) (crossingStopLower W) readiness.factorC
  same_qFibre_base :
    integrated.factorState = dualChild.qFibreState.base
  base_bad : parentNormalizedFiberCFAt (crossingBaseCover W) (crossingBaseQ W) < (crossingStopLower W)
  interval_upper : parentNormalizedFiberCFAt (crossingIntervalCover W) (crossingBaseQ W) ≤
    readiness.baseError * readiness.massUpper * readiness.massLower⁻¹
  raw_interval_strict : parentNormalizedFiberCFAt
      (paperBufferedIntervalCover
        D hD C S epsilon hepsilon W.m W.rho W.buffered) W.q <
      (crossingStopLower W)

namespace ParentwiseCrossingIntegratedSuccessor

variable {D : ActualTubeDatum delta iota} {hD : D.IsAdmissible}
  {C : CoherentStickyMultiscaleCover D.family}
  {S : FiniteScaleSequence delta depth}
  {epsilon : Real} {hepsilon : 0 ≤ epsilon}
  {eta : Nat → Real} {N : Nat}
  {W : FirstParentwiseNormalizedCrossingWitness
    D hD C S epsilon hepsilon eta N}

/-- The integrated view and the dual-child view retain exactly the same
same-`q` selected subtype. -/
theorem integrated_selected_eq_qFibreSelected
    (X : ParentwiseCrossingIntegratedSuccessor W) :
    X.integrated.factorState.selected =
      X.dualChild.qFibreState.base.selected := by
  exact congrArg (fun state => state.selected)
    X.same_qFibre_base

/-- The independent active child is attached to the exact base-cover state,
not to the interval cover. -/
theorem activeParent_factor_radius
    (X : ParentwiseCrossingIntegratedSuccessor W) :
    X.dualChild.activeParentChildAtom.radius = W.rho / 8 :=
  X.dualChild.activeParentChildAtom_radius

/-- Every earlier all-parent barrier from the raw first crossing survives. -/
theorem earlier_parentwise_barrier
    (_X : ParentwiseCrossingIntegratedSuccessor W)
    {earlier : Nat} (hearlier : earlier < W.stage)
    (m : Fin depth) (hnotLarge : ¬ S.IsLarge epsilon m)
    (rho : NNReal) (hbuffered : S.IsBuffered epsilon m rho)
    (q : {q // q ∈
      (paperBufferedIntervalCover
        D hD C S epsilon hepsilon m rho hbuffered).activeCoarse}) :
    (((rho / S.tau m : NNReal) : ENNReal) ^ eta earlier) ≤
      parentNormalizedFiberCFAt
        (paperBufferedIntervalCover
          D hD C S epsilon hepsilon m rho hbuffered) q :=
  W.earlier_parentwise_barrier
    earlier hearlier m hnotLarge rho hbuffered q

end ParentwiseCrossingIntegratedSuccessor

/-- Positive cross-scale orchestration.  The q-fibre state is produced once
from `base_bound ≤ baseError < stopLower`; the interval theorem only transports
that same parent bound.  The active-parent state is built independently and
then paired with the already produced q-state. -/
theorem exists_parentwiseCrossingIntegratedSuccessor
    {D : ActualTubeDatum delta iota} {hD : D.IsAdmissible}
    {C : CoherentStickyMultiscaleCover D.family}
    {S : FiniteScaleSequence delta depth}
    {epsilon : Real} {hepsilon : 0 ≤ epsilon}
    {eta : Nat → Real} {N : Nat}
    (W : FirstParentwiseNormalizedCrossingWitness
      D hD C S epsilon hepsilon eta N)
    (readiness : ParentwiseCrossingSuccessorReadiness W) :
    Nonempty (ParentwiseCrossingIntegratedSuccessor W) := by
  obtain ⟨hstate, hbaseBad, hIntervalUpper⟩ :=
    exists_parentwiseBadParentPointwiseMassAwareSuccessor
      D C readiness.left readiness.right hD.delta_pos hD.delta_le_half
        (S.delta_le_tau W.m) (crossingTauLeRho W) (crossingRhoLeOne W) (crossingRhoPos W)
        readiness.massLower_ne_zero readiness.massLower_ne_top
        readiness.parentMassComparison (crossingBaseQ W) readiness.base_bound
        readiness.base_strict readiness.stopLower_ne_top
        readiness.factor_uniform
  obtain ⟨qState⟩ := hstate
  obtain ⟨activeParentState⟩ :=
    exists_activeCoarseAdmissibleFactorState
      D hD (crossingBaseCover W) (crossingRhoPos W) readiness.rho_le_half
        readiness.rho_le_sixteenth ⟨(crossingBaseQ W).1, (crossingBaseQ W).2⟩
        readiness.conflictThreshold readiness.conflict_cap
        readiness.activeC readiness.katzTao_at_scale
  let dualChild : ParentwiseBadParentDualChildCertificate
      D (crossingBaseCover W) readiness.left readiness.right (crossingRhoPos W) (crossingRhoLeOne W)
        (crossingBaseQ W) (crossingStopLower W) readiness.factorC readiness.conflictThreshold
        readiness.activeC :=
    { qFibreState := qState
      activeParentState := activeParentState }
  let integrated := integratedStateOfMassAware qState
  exact ⟨
    { readiness := readiness
      dualChild := dualChild
      integrated := integrated
      same_qFibre_base := rfl
      base_bad := hbaseBad
      interval_upper := hIntervalUpper
      raw_interval_strict := (crossingRawIntervalStrict W) }⟩

#print axioms crossingStopLower
#print axioms crossingBaseCover
#print axioms crossingIntervalCover
#print axioms crossingBaseQ
#print axioms ParentwiseCrossingSuccessorReadiness
#print axioms integratedStateOfMassAware
#print axioms ParentwiseCrossingIntegratedSuccessor
#print axioms ParentwiseCrossingIntegratedSuccessor.integrated_selected_eq_qFibreSelected
#print axioms ParentwiseCrossingIntegratedSuccessor.activeParent_factor_radius
#print axioms ParentwiseCrossingIntegratedSuccessor.earlier_parentwise_barrier
#print axioms exists_parentwiseCrossingIntegratedSuccessor

end
end Family8ParentwiseCrossingIntegratedSuccessorV1
