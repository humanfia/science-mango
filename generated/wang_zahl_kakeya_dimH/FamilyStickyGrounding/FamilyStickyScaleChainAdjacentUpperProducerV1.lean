import FamilyStickyGrounding.FamilyStickyScaleChainExponentProductBudgetV1

set_option autoImplicit false

open Set
open scoped BigOperators ENNReal NNReal

namespace FamilyStickyScaleChainAdjacentUpperProducerV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDeltaMaxFiniteChainV2
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyDividingScalesChainAtEveryAdapterV1
open FamilyStickyScaleChainActualValuesV1
open FamilyStickyScaleChainActualDividingRunV1
open FamilyStickyScaleChainExponentProductBudgetV1
open FamilyStickyScaleChainBufferedHierarchyProducerV1.MultiscaleTubeHierarchy
open FamilyStickyScaleChainBufferedTelescopeV1.MultiscaleTubeHierarchy
open FamilyStickyScaleChainBufferedTelescopeV1.MultiscaleTubeHierarchy.BufferedTestBodyChain

noncomputable section

/-!
# Sticky Kakeya: actual buffered producer for the adjacent upper bound

The adjacent value is a supremum over all convex test bodies.  Consequently
one fixed test-body chain cannot bound it.  Here an honest buffered hierarchy
is equipped with a generated test-body chain for every positive-volume test
body.  A threshold-free equality of contained masses identifies its bottom
family with the actual adjacent coarse family.  Pointwise local-factor and
endpoint exponent estimates then bound every concentration and hence the
supremum.
-/

namespace AdjacentActualValues

variable {delta : NNReal} {outerDepth : Nat}
  {S : FiniteScaleSequence delta outerDepth}

/-- The literal active coarse family at the upper endpoint of interval `m`. -/
def adjacentActiveCoarseFamily (A : ActualIntervalCovers S)
    (m : Fin outerDepth) :
    ConvexFamily {k // k ∈
      ((A.multiscale m).cover (S.theta m) (S.tau_le_theta m)
        (S.theta_le_one m)).activeCoarse} :=
  ((A.multiscale m).cover (S.theta m) (S.tau_le_theta m)
    (S.theta_le_one m)).activeCoarseFamily

/-- The actual adjacent value is the maximal concentration of the displayed
endpoint family. -/
theorem adjacentCoarseValue_eq_maximalConcentration
    (A : ActualIntervalCovers S) (m : Fin outerDepth) :
    A.adjacentCoarseValue m =
      maximalConcentration (AdjacentActualValues.adjacentActiveCoarseFamily A m) := by
  rw [A.adjacentCoarseValue_eq m]
  rfl

end AdjacentActualValues

/-- Buffered hierarchy and measure data realizing every positive-volume test
body for the actual adjacent coarse family.  The mass-identification field
contains no exponent or threshold inequality. -/
structure AdjacentBufferedHierarchyFamily
    {delta : NNReal} {outerDepth : Nat}
    (S : FiniteScaleSequence delta outerDepth)
    (A : ActualIntervalCovers S) (adjacentDepth : Nat) where
  nominalRadius : Fin outerDepth -> Nat -> NNReal
  card : Fin outerDepth -> Nat -> Nat
  hierarchy : (m : Fin outerDepth) ->
    MultiscaleTubeHierarchy adjacentDepth (nominalRadius m)
      (fun l => Fin (card m l))
  datum : (m : Fin outerDepth) -> (K : ConvexBody Space) ->
    MeasureTheory.volume (K : Set Space) ≠ 0 ->
      BufferedTestBodyChain (hierarchy m)
  testBody_zero : forall m K hK,
    (datum m K hK).testBody 0 = K
  bottomContainedMass_eq : forall m K,
    containedMass (effectiveActiveFamily (hierarchy m) 0) K =
      containedMass (AdjacentActualValues.adjacentActiveCoarseFamily A m) K

namespace AdjacentBufferedHierarchyFamily

variable {delta : NNReal} {outerDepth adjacentDepth chainDepth N stage : Nat}
  {epsilon : Real} {eta : Nat -> Real}
  {S : FiniteScaleSequence delta outerDepth}
  {A : ActualIntervalCovers S}

/-- Literal endpoint normalization for the chain generated from `K`. -/
def endpointRatio
    (G : AdjacentBufferedHierarchyFamily S A adjacentDepth)
    (m : Fin outerDepth) (K : ConvexBody Space)
    (hK : MeasureTheory.volume (K : Set Space) ≠ 0) : ENNReal :=
  (MeasureTheory.volume ((G.datum m K hK).testBody adjacentDepth : Set Space) /
      MeasureTheory.volume ((G.datum m K hK).testBody 0 : Set Space)) *
    ((G.datum m K hK).tubeVolume 0 /
      (G.datum m K hK).tubeVolume adjacentDepth)

/-- Primitive adjacent exponent data.  Its bounds concern only actual local
factors and the literal endpoint volume ratio, separately for each test
body; the final adjacent supremum bound is not a field. -/
structure ExponentBudgetData
    (G : AdjacentBufferedHierarchyFamily S A adjacentDepth)
    (stage : Nat) (eta : Nat -> Real) where
  tau_pos : forall m, 0 < S.tau m
  localExponent : Fin outerDepth -> ConvexBody Space -> Nat -> Real
  endpointExponent : Fin outerDepth -> ConvexBody Space -> Real
  localFactor_upper : forall m K hK l, l < adjacentDepth ->
    BufferedTestBodyChain.localFactor
        (G.hierarchy m) (G.datum m K hK) l <=
      (((S.theta m / S.tau m : NNReal) : ENNReal) ^
        localExponent m K l)
  endpointRatio_upper : forall m K hK,
    G.endpointRatio m K hK <=
      (((S.theta m / S.tau m : NNReal) : ENNReal) ^
        endpointExponent m K)
  exponent_balance : forall m K,
    (∑ l ∈ Finset.range adjacentDepth, localExponent m K l) +
      endpointExponent m K = eta (stage - 1)

/-- The actual endpoint-family concentration is identified with the bottom
of its generated buffered chain. -/
theorem concentration_eq_bottom
    (G : AdjacentBufferedHierarchyFamily S A adjacentDepth)
    (m : Fin outerDepth) (K : ConvexBody Space)
    (hK : MeasureTheory.volume (K : Set Space) ≠ 0) :
    concentration (AdjacentActualValues.adjacentActiveCoarseFamily A m) K =
      concentration (effectiveActiveFamily (G.hierarchy m) 0)
        ((G.datum m K hK).testBody 0) := by
  rw [G.testBody_zero m K hK]
  simp only [concentration_eq_containedMass_div]
  rw [G.bottomContainedMass_eq m K]

/-- Every convex test body satisfies the adjacent exponent bound.  The
zero-volume case is discharged from actual contained mass; the positive
case is the buffered telescope plus finite exponent arithmetic. -/
theorem ExponentBudgetData.concentration_le
    (G : AdjacentBufferedHierarchyFamily S A adjacentDepth)
    (E : ExponentBudgetData G stage eta)
    (m : Fin outerDepth) (K : ConvexBody Space) :
    concentration (AdjacentActualValues.adjacentActiveCoarseFamily A m) K <=
      (((S.theta m / S.tau m : NNReal) : ENNReal) ^
        eta (stage - 1)) := by
  by_cases hK : MeasureTheory.volume (K : Set Space) = 0
  · rw [concentration_eq_containedMass_div,
      containedMass_eq_zero_of_volume_eq_zero _ K hK, hK]
    simp
  · have hratio_pos : 0 < S.theta m / S.tau m := by
      exact div_pos (lt_of_lt_of_le (E.tau_pos m) (S.tau_le_theta m))
        (E.tau_pos m)
    have hbase_zero :
        (((S.theta m / S.tau m : NNReal) : ENNReal)) ≠ 0 :=
      ENNReal.coe_ne_zero.mpr hratio_pos.ne'
    have hbase_top :
        (((S.theta m / S.tau m : NNReal) : ENNReal)) ≠ ∞ :=
      ENNReal.coe_ne_top
    have hproduct :
        (∏ l ∈ Finset.range adjacentDepth,
          BufferedTestBodyChain.localFactor
            (G.hierarchy m) (G.datum m K hK) l) *
          G.endpointRatio m K hK <=
        (((S.theta m / S.tau m : NNReal) : ENNReal) ^
          eta (stage - 1)) := by
      rw [← E.exponent_balance m K]
      exact prod_mul_endpoint_le_rpow_sum_add
        (((S.theta m / S.tau m : NNReal) : ENNReal))
        hbase_zero hbase_top
        (fun l => BufferedTestBodyChain.localFactor
          (G.hierarchy m) (G.datum m K hK) l)
        (E.localExponent m K) adjacentDepth
        (G.endpointRatio m K hK) (E.endpointExponent m K)
        (E.localFactor_upper m K hK) (E.endpointRatio_upper m K hK)
    calc
      concentration (AdjacentActualValues.adjacentActiveCoarseFamily A m) K =
          concentration (effectiveActiveFamily (G.hierarchy m) 0)
            ((G.datum m K hK).testBody 0) :=
        G.concentration_eq_bottom m K hK
      _ <= (∏ l ∈ Finset.range adjacentDepth,
            BufferedTestBodyChain.localFactor
              (G.hierarchy m) (G.datum m K hK) l) *
          G.endpointRatio m K hK := by
        exact BufferedTestBodyChain.global_le_endpointRatio
          (G.hierarchy m) (G.datum m K hK)
      _ <= (((S.theta m / S.tau m : NNReal) : ENNReal) ^
          eta (stage - 1)) := hproduct

/-- Actual buffered hierarchy and measure data automatically produce the
`adjacent_upper` field of the no-split run. -/
theorem ExponentBudgetData.adjacent_upper
    (G : AdjacentBufferedHierarchyFamily S A adjacentDepth)
    (E : ExponentBudgetData G stage eta) : forall m,
    A.adjacentCoarseValue m <=
      (((S.theta m / S.tau m : NNReal) : ENNReal) ^
        eta (stage - 1)) := by
  intro m
  rw [AdjacentActualValues.adjacentCoarseValue_eq_maximalConcentration A m]
  exact iSup_le fun K => E.concentration_le G m K

end AdjacentBufferedHierarchyFamily

namespace BufferedChainFamily

variable {delta : NNReal} {outerDepth chainDepth adjacentDepth N : Nat}
  {epsilon : Real} {eta : Nat -> Real}
  {S : FiniteScaleSequence delta outerDepth}

/-- Actual no-split run with both the global product budget and adjacent
upper bound synthesized from separate actual buffered hierarchy data. -/
def toActualKatzTaoChainNoSplitRun_of_bufferedExponentData
    (A : ActualIntervalCovers S)
    (B : BufferedChainFamily outerDepth chainDepth)
    (G : AdjacentBufferedHierarchyFamily S A adjacentDepth)
    (stage : Nat) (stage_pos : 1 <= stage) (stage_le : stage <= N)
    (eta_monotone : Monotone eta)
    (eta_stage_le_epsilon : eta stage <= epsilon)
    (globalExponent : FamilyStickyScaleChainExponentProductBudgetV1.BufferedChainFamily.ExponentBudgetData B S stage eta)
    (adjacentExponent :
      AdjacentBufferedHierarchyFamily.ExponentBudgetData G stage eta)
    (terminal_noSplit : forall m, ¬ S.IsLarge epsilon m ->
      ¬ (exists rho, S.IsBuffered epsilon m rho ∧
        A.coarseValueAt m rho <
          (((S.theta m / rho : NNReal) : ENNReal) ^ eta stage))) :
    KatzTaoChainNoSplitRun delta outerDepth chainDepth N epsilon eta S :=
  FamilyStickyScaleChainExponentProductBudgetV1.BufferedChainFamily.toActualKatzTaoChainNoSplitRun_of_exponentData A B stage stage_pos stage_le
    eta_monotone eta_stage_le_epsilon globalExponent
    (adjacentExponent.adjacent_upper G) terminal_noSplit

/-- Corresponding all-large versus dividing-witness dichotomy; only the
terminal no-further-split certificate remains after both buffered producers. -/
theorem allLarge_or_witness_of_bufferedExponentData
    (A : ActualIntervalCovers S)
    (B : BufferedChainFamily outerDepth chainDepth)
    (G : AdjacentBufferedHierarchyFamily S A adjacentDepth)
    (stage : Nat) (stage_pos : 1 <= stage) (stage_le : stage <= N)
    (eta_monotone : Monotone eta)
    (eta_stage_le_epsilon : eta stage <= epsilon)
    (globalExponent : FamilyStickyScaleChainExponentProductBudgetV1.BufferedChainFamily.ExponentBudgetData B S stage eta)
    (adjacentExponent :
      AdjacentBufferedHierarchyFamily.ExponentBudgetData G stage eta)
    (terminal_noSplit : forall m, ¬ S.IsLarge epsilon m ->
      ¬ (exists rho, S.IsBuffered epsilon m rho ∧
        A.coarseValueAt m rho <
          (((S.theta m / rho : NNReal) : ENNReal) ^ eta stage))) :
    S.AllStepsLarge epsilon ∨
      Nonempty (KatzTaoDividingWitness delta N epsilon eta) := by
  exact (toActualKatzTaoChainNoSplitRun_of_bufferedExponentData A B G stage
    stage_pos stage_le eta_monotone eta_stage_le_epsilon globalExponent
    adjacentExponent terminal_noSplit).allLarge_or_witness

end BufferedChainFamily

#print axioms AdjacentActualValues.adjacentCoarseValue_eq_maximalConcentration
#print axioms AdjacentBufferedHierarchyFamily.concentration_eq_bottom
#print axioms AdjacentBufferedHierarchyFamily.ExponentBudgetData.concentration_le
#print axioms AdjacentBufferedHierarchyFamily.ExponentBudgetData.adjacent_upper
#print axioms BufferedChainFamily.toActualKatzTaoChainNoSplitRun_of_bufferedExponentData
#print axioms BufferedChainFamily.allLarge_or_witness_of_bufferedExponentData

end
end FamilyStickyScaleChainAdjacentUpperProducerV1
