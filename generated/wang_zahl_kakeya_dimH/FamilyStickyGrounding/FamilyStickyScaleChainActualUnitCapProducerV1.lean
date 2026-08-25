import FamilyStickyGrounding.FamilyStickyScaleChainSelectedNumericalAllocationProducerV1
import FamilyStickyGrounding.FamilyStickyFiniteFamilyMaximalConcentrationV1

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 300000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace FamilyStickyScaleChainActualUnitCapProducerV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDeltaMaxFiniteChainV2
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainActualValuesV1
open FamilyStickyScaleChainActualDividingRunV1
open FamilyStickyScaleChainActualDividingRunV1.BufferedChainFamily
open FamilyStickyScaleChainCoherentIntervalProducerV1
open FamilyStickyScaleChainTerminalFiniteSearchV1
open FamilyStickyScaleChainRootedRefinementTreeV1
open FamilyStickyScaleChainConstantBearingStoppingEndpointV1
open FamilyStickyScaleChainReservedExponentProfileV1
open FamilyStickyScaleChainSmallDeltaExponentBudgetProducerV1
open FamilyStickyScaleChainActualSmallDeltaRecoveredEndpointV1
open FamilyStickyScaleChainActualStoppingUpstreamClosureV1
open FamilyStickyScaleChainDividingFiniteNodeProducerV1
open FamilyStickyScaleChainSelectedNumericalAllocationProducerV1
open FamilyStickyFiniteFamilyMaximalConcentrationV1

noncomputable section

/-!
# Actual unit-cap producers at the selected stopping interval

The buffered telescope controls the initial concentration by a product; its
fields do not assert that the product itself is at most one.  The most general
factorwise certificate below bounds the literal local factors and literal
endpoint ratio by independently supplied caps whose combined product is at
most one.

The adjacent value is an unnormalised maximal concentration of an indexed
family.  It is automatically at most one when the actual active coarse index
set has cardinality at most one.  Repeated active positive-volume tubes show
sharply why no such conclusion follows for an arbitrary actual cover.
-/

variable {delta : NNReal} {outerDepth chainDepth : Nat}
  {S : FiniteScaleSequence delta outerDepth}

/-! ## The actual buffered global product -/

/-- Factorwise upper bounds for the literal buffered telescope at one actual
interval.  Unlike a bare product inequality, the fields expose exactly which
local scale or endpoint ratio is responsible for the cap. -/
structure ActualGlobalFactorCaps
    (B : BufferedChainFamily outerDepth chainDepth)
    (m : Fin outerDepth) where
  localCap : Nat -> ENNReal
  endpointCap : ENNReal
  localFactor_le : forall l, l < chainDepth ->
    FamilyStickyScaleChainBufferedTelescopeV1.MultiscaleTubeHierarchy.BufferedTestBodyChain.localFactor
      (B.hierarchy m) (B.datum m) l <= localCap l
  endpointRatio_le :
    actualGlobalEndpointRatioAt B m <= endpointCap
  capProduct_le_one :
    (∏ l ∈ Finset.range chainDepth, localCap l) * endpointCap <= 1

/-- The factorwise certificate produces the first selected unit cap. -/
theorem actualGlobalProductAt_le_one_of_factorCaps
    (B : BufferedChainFamily outerDepth chainDepth)
    (m : Fin outerDepth) (D : ActualGlobalFactorCaps B m) :
    actualGlobalProductAt B m <= 1 := by
  calc
    actualGlobalProductAt B m <=
        (∏ l ∈ Finset.range chainDepth, D.localCap l) * D.endpointCap := by
      unfold actualGlobalProductAt
      gcongr with l hl
      · exact D.localFactor_le l (Finset.mem_range.mp hl)
      · exact D.endpointRatio_le
    _ <= 1 := D.capProduct_le_one

/-- A convenient specialization when every actual local factor and the actual
endpoint ratio are separately at most one. -/
def ActualGlobalFactorCaps.ofUnitFactors
    (B : BufferedChainFamily outerDepth chainDepth)
    (m : Fin outerDepth)
    (local_le_one : forall l, l < chainDepth ->
      FamilyStickyScaleChainBufferedTelescopeV1.MultiscaleTubeHierarchy.BufferedTestBodyChain.localFactor
        (B.hierarchy m) (B.datum m) l <= 1)
    (endpoint_le_one : actualGlobalEndpointRatioAt B m <= 1) :
    ActualGlobalFactorCaps B m where
  localCap := fun _ => 1
  endpointCap := 1
  localFactor_le := local_le_one
  endpointRatio_le := endpoint_le_one
  capProduct_le_one := by simp

/-! ## A genuine buffered-family deformation showing non-automaticity -/

open FamilyStickyScaleChainBufferedHierarchyProducerV1.MultiscaleTubeHierarchy
open FamilyStickyScaleChainBufferedTelescopeV1.MultiscaleTubeHierarchy

variable {depth : Nat} {nominalRadius : Nat -> NNReal}
  {card : Nat -> Nat}
  {H : MultiscaleTubeHierarchy depth nominalRadius (fun l => Fin (card l))}

/-- Increasing every dimensional envelope loss by a finite factor at least
one preserves all geometric, measure, nesting, and top-normalization fields of
an actual buffered test-body chain. -/
def scaleBufferedTestBodyChainDimensionalLoss
    (D : BufferedTestBodyChain H) (c : ENNReal)
    (one_le_c : 1 <= c) (c_ne_top : c ≠ ⊤) :
    BufferedTestBodyChain H where
  testBody := D.testBody
  tubeVolume := D.tubeVolume
  dimensionalLoss := fun l => c * D.dimensionalLoss l
  bodyVolume_ne_zero := D.bodyVolume_ne_zero
  tubeVolume_ne_zero := D.tubeVolume_ne_zero
  tubeVolume_ne_top := D.tubeVolume_ne_top
  loss_mul_tube_ne_zero := by
    intro l hl
    rw [mul_assoc]
    exact mul_ne_zero (ne_of_gt (zero_lt_one.trans_le one_le_c))
      (D.loss_mul_tube_ne_zero l hl)
  loss_mul_tube_ne_top := by
    intro l hl
    rw [mul_assoc]
    exact ENNReal.mul_ne_top c_ne_top (D.loss_mul_tube_ne_top l hl)
  bodyVolume_envelope := by
    intro l hl
    calc
      volume (D.testBody l : Set Space) <=
          D.dimensionalLoss l * D.tubeVolume l := D.bodyVolume_envelope l hl
      _ = 1 * (D.dimensionalLoss l * D.tubeVolume l) := by simp
      _ <= c * (D.dimensionalLoss l * D.tubeVolume l) := by gcongr
      _ = (c * D.dimensionalLoss l) * D.tubeVolume l := by ac_rfl
  nextTubeFloor := D.nextTubeFloor
  testBody_succ := D.testBody_succ
  top_le_one := D.top_le_one

@[simp] theorem scaleBufferedTestBodyChainDimensionalLoss_localFactor
    (D : BufferedTestBodyChain H) (c : ENNReal)
    (one_le_c : 1 <= c) (c_ne_top : c ≠ ⊤)
    (l : Nat) (hl : l < depth) :
    BufferedTestBodyChain.localFactor H
        (scaleBufferedTestBodyChainDimensionalLoss
          D c one_le_c c_ne_top) l =
      c * BufferedTestBodyChain.localFactor H D l := by
  simp [BufferedTestBodyChain.localFactor,
    scaleBufferedTestBodyChainDimensionalLoss, hl, mul_assoc]

/-- Apply the same legal loss enlargement to every actual terminal interval,
without changing any hierarchy, test body, tube volume, or active family. -/
def scaleFamilyDimensionalLoss
    (B : BufferedChainFamily outerDepth chainDepth)
    (c : ENNReal) (one_le_c : 1 <= c) (c_ne_top : c ≠ ⊤) :
    BufferedChainFamily outerDepth chainDepth where
  nominalRadius := B.nominalRadius
  card := B.card
  hierarchy := B.hierarchy
  datum := fun m => scaleBufferedTestBodyChainDimensionalLoss
    (B.datum m) c one_le_c c_ne_top

/-- The deformation multiplies the literal global product by exactly one copy
of `c` per scale step; the telescoped endpoint ratio is unchanged. -/
theorem actualGlobalProductAt_scaleFamilyDimensionalLoss
    (B : BufferedChainFamily outerDepth chainDepth)
    (c : ENNReal) (one_le_c : 1 <= c) (c_ne_top : c ≠ ⊤)
    (m : Fin outerDepth) :
    actualGlobalProductAt
        (scaleFamilyDimensionalLoss B c one_le_c c_ne_top) m =
      c ^ chainDepth * actualGlobalProductAt B m := by
  unfold actualGlobalProductAt actualGlobalEndpointRatioAt
  rw [show (∏ l ∈ Finset.range chainDepth,
      BufferedTestBodyChain.localFactor
        ((scaleFamilyDimensionalLoss B c one_le_c c_ne_top).hierarchy m)
        ((scaleFamilyDimensionalLoss B c one_le_c c_ne_top).datum m) l) =
      c ^ chainDepth *
        ∏ l ∈ Finset.range chainDepth,
          BufferedTestBodyChain.localFactor (B.hierarchy m) (B.datum m) l by
    calc
      _ = ∏ l ∈ Finset.range chainDepth,
          c * BufferedTestBodyChain.localFactor
            (B.hierarchy m) (B.datum m) l := by
        apply Finset.prod_congr rfl
        intro l hl
        exact scaleBufferedTestBodyChainDimensionalLoss_localFactor
          (B.datum m) c one_le_c c_ne_top l (Finset.mem_range.mp hl)
      _ = (∏ _l ∈ Finset.range chainDepth, c) *
          ∏ l ∈ Finset.range chainDepth,
            BufferedTestBodyChain.localFactor
              (B.hierarchy m) (B.datum m) l := Finset.prod_mul_distrib
      _ = c ^ chainDepth *
          ∏ l ∈ Finset.range chainDepth,
            BufferedTestBodyChain.localFactor
              (B.hierarchy m) (B.datum m) l := by simp]
  simp only [scaleFamilyDimensionalLoss,
    scaleBufferedTestBodyChainDimensionalLoss]
  ac_rfl

/-- Thus, at every positive-depth interval with nonzero literal product, the
same actual hierarchy and test-body nesting allow a legal finite loss choice
whose global product is strictly larger than one. -/
theorem exists_scaledFamily_one_lt_actualGlobalProductAt
    (B : BufferedChainFamily outerDepth chainDepth) (m : Fin outerDepth)
    (chainDepth_pos : 0 < chainDepth)
    (product_pos : 0 < actualGlobalProductAt B m) :
    ∃ (c : ENNReal) (one_le_c : (1 : ENNReal) <= c)
      (c_ne_top : c ≠ (⊤ : ENNReal)),
      1 < actualGlobalProductAt
        (scaleFamilyDimensionalLoss B c one_le_c c_ne_top) m := by
  have hinv_ne_top :
      (1 / actualGlobalProductAt B m) ≠ (⊤ : ENNReal) :=
    ENNReal.div_ne_top (by norm_num) product_pos.ne'
  obtain ⟨n, hn⟩ := ENNReal.exists_nat_gt hinv_ne_top
  have n_pos : 0 < n := by
    have cast_pos : (0 : ENNReal) < (n : ENNReal) :=
      bot_le.trans_lt hn
    exact_mod_cast cast_pos
  have one_le_n : (1 : ENNReal) <= (n : ENNReal) := by
    exact_mod_cast n_pos
  have n_ne_top : (n : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top n
  refine ⟨(n : ENNReal), one_le_n, n_ne_top, ?_⟩
  rw [actualGlobalProductAt_scaleFamilyDimensionalLoss]
  have hlinear :
      (1 : ENNReal) < (n : ENNReal) * actualGlobalProductAt B m :=
    (ENNReal.div_lt_iff (Or.inl product_pos.ne')
      (Or.inr (by norm_num))).1 hn
  have hpow : (n : ENNReal) <= (n : ENNReal) ^ chainDepth := by
    calc
      (n : ENNReal) = (n : ENNReal) ^ 1 := by simp
      _ <= (n : ENNReal) ^ chainDepth :=
        pow_le_pow_right' one_le_n chainDepth_pos
  exact hlinear.trans_le (by gcongr)

/-- Strict failure of the literal actual product rules out every factorwise
cap certificate.  This is the exact obstruction left by the telescope API. -/
theorem not_nonempty_actualGlobalFactorCaps_of_one_lt
    (B : BufferedChainFamily outerDepth chainDepth)
    (m : Fin outerDepth)
    (failed : 1 < actualGlobalProductAt B m) :
    Not (Nonempty (ActualGlobalFactorCaps B m)) := by
  rintro ⟨D⟩
  exact (not_le_of_gt failed)
    (actualGlobalProductAt_le_one_of_factorCaps B m D)

/-! ## Cardinal-one producer for the actual adjacent coarse family -/

/-- The actual scale cover used by `adjacentCoarseValue`, named so that its
finite active index set can be inspected directly. -/
def actualAdjacentScaleCover
    (A : ActualIntervalCovers S) (m : Fin outerDepth) :
    StickyScaleCover (A.fine m) (S.theta m) :=
  (A.multiscale m).cover (S.theta m)
    (S.tau_le_theta m) (S.theta_le_one m)

theorem adjacentCoarseValue_eq_actualAdjacentScaleCover
    (A : ActualIntervalCovers S) (m : Fin outerDepth) :
    A.adjacentCoarseValue m =
      StickyScaleCover.coarseDeltaMax (actualAdjacentScaleCover A m) := by
  exact A.adjacentCoarseValue_eq m

/-- Cardinality at most one is a structural sufficient condition for a unit
maximal-concentration cap, with repetitions still counted by the index type. -/
theorem coarseDeltaMax_le_one_of_activeCoarse_card_le_one
    {rho : NNReal} {index : Type*} [Fintype index] [DecidableEq index]
    {fine : UniformTubeFamily delta index}
    (Q : StickyScaleCover fine rho)
    (active_card_le_one : Q.activeCoarse.card <= 1) :
    StickyScaleCover.coarseDeltaMax Q <= 1 := by
  unfold StickyScaleCover.coarseDeltaMax
  calc
    maximalConcentration Q.activeCoarseFamily <=
        (Fintype.card {k // k ∈ Q.activeCoarse} : ENNReal) :=
      maximalConcentration_le_card Q.activeCoarseFamily
    _ = (Q.activeCoarse.card : ENNReal) := by
      rw [Fintype.card_coe]
    _ <= 1 := by exact_mod_cast active_card_le_one

/-- The cardinal-one condition applied to the literal cover supplying the
actual adjacent value. -/
theorem adjacentCoarseValue_le_one_of_activeCoarse_card_le_one
    (A : ActualIntervalCovers S) (m : Fin outerDepth)
    (active_card_le_one :
      (actualAdjacentScaleCover A m).activeCoarse.card <= 1) :
    A.adjacentCoarseValue m <= 1 := by
  rw [adjacentCoarseValue_eq_actualAdjacentScaleCover]
  exact coarseDeltaMax_le_one_of_activeCoarse_card_le_one
    (actualAdjacentScaleCover A m) active_card_le_one

/-! ## A repeated-tube obstruction inside the actual model -/

/-- Two distinct indices carrying the same positive-volume body force maximal
concentration at least two.  The proof evaluates concentration on that body,
so repetitions are not discarded. -/
theorem two_le_maximalConcentration_of_two_equal_positive
    {index : Type*} [Fintype index] [DecidableEq index]
    (F : ConvexFamily index) (i j : index) (hne : i ≠ j)
    (heq : F j = F i)
    (hpos : 0 < volume (F i : Set Space)) :
    (2 : ENNReal) <= maximalConcentration F := by
  let K : ConvexBody Space := F i
  have hi : i ∈ containedIndices F K := by
    exact (mem_containedIndices F K i).2 Set.Subset.rfl
  have hj : j ∈ containedIndices F K := by
    apply (mem_containedIndices F K j).2
    simp [K, heq]
  have hpair : ({i, j} : Finset index) ⊆ containedIndices F K := by
    intro k hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with rfl | rfl
    · exact hi
    · exact hj
  have hsum :
      volume (F i : Set Space) + volume (F j : Set Space) <=
        ∑ k ∈ containedIndices F K, volume (F k : Set Space) := by
    calc
      volume (F i : Set Space) + volume (F j : Set Space) =
          ∑ k ∈ ({i, j} : Finset index), volume (F k : Set Space) := by
        symm
        exact Finset.sum_pair hne
      _ <= ∑ k ∈ containedIndices F K, volume (F k : Set Space) :=
        Finset.sum_le_sum_of_subset hpair
  have hconc : (2 : ENNReal) <= concentration F K := by
    rw [concentration]
    apply (ENNReal.le_div_iff_mul_le (Or.inl hpos.ne')
      (Or.inl (F i).isCompact.measure_lt_top.ne)).2
    simpa [K, heq, two_mul] using hsum
  exact hconc.trans (concentration_le_maximalConcentration F K)

/-- The repeated-body obstruction specialized to two genuinely active indices
of one actual sticky scale cover. -/
theorem two_le_coarseDeltaMax_of_repeated_active_tube
    {rho : NNReal} {index : Type*} [Fintype index] [DecidableEq index]
    {fine : UniformTubeFamily delta index}
    (Q : StickyScaleCover fine rho) (rho_pos : 0 < rho)
    (i j : Fin Q.coarseCard) (hi : i ∈ Q.activeCoarse)
    (hj : j ∈ Q.activeCoarse) (hne : i ≠ j)
    (heq : Q.coarse.tubes j = Q.coarse.tubes i) :
    (2 : ENNReal) <= StickyScaleCover.coarseDeltaMax Q := by
  let i' : {k // k ∈ Q.activeCoarse} := ⟨i, hi⟩
  let j' : {k // k ∈ Q.activeCoarse} := ⟨j, hj⟩
  have hne' : i' ≠ j' := by
    intro h
    apply hne
    exact congrArg Subtype.val h
  have heq' : Q.activeCoarseFamily j' = Q.activeCoarseFamily i' := by
    change (Q.coarse.tubes j).body = (Q.coarse.tubes i).body
    rw [heq]
  have hpos :
      0 < volume (Q.activeCoarseFamily i' : Set Space) := by
    change 0 < volume (Q.coarse.tubes i).carrier
    exact (Q.coarse.tubes i).volume_pos rho_pos
  exact two_le_maximalConcentration_of_two_equal_positive
    Q.activeCoarseFamily i' j' hne' heq' hpos

/-- In particular, two repeated active tubes in the literal adjacent cover
make its unit cap false. -/
theorem not_adjacentCoarseValue_le_one_of_repeated_active_tube
    (A : ActualIntervalCovers S) (m : Fin outerDepth)
    (delta_pos : 0 < delta)
    (i j : Fin (actualAdjacentScaleCover A m).coarseCard)
    (hi : i ∈ (actualAdjacentScaleCover A m).activeCoarse)
    (hj : j ∈ (actualAdjacentScaleCover A m).activeCoarse)
    (hne : i ≠ j)
    (heq : (actualAdjacentScaleCover A m).coarse.tubes j =
      (actualAdjacentScaleCover A m).coarse.tubes i) :
    Not (A.adjacentCoarseValue m <= 1) := by
  have theta_pos : 0 < S.theta m :=
    delta_pos.trans_le ((S.delta_le_tau m).trans (S.tau_le_theta m))
  have htwo : (2 : ENNReal) <= A.adjacentCoarseValue m := by
    rw [adjacentCoarseValue_eq_actualAdjacentScaleCover]
    exact two_le_coarseDeltaMax_of_repeated_active_tube
      (actualAdjacentScaleCover A m) theta_pos i j hi hj hne heq
  intro hone
  have : (2 : ENNReal) <= 1 := htwo.trans hone
  norm_num at this

/-! ## Separate and combined recovered endpoints -/

variable {N : Nat} {epsilon : Real} {eta : Nat -> Real}
  {iota : Type*} [Fintype iota] [DecidableEq iota]
  {fine : UniformTubeFamily delta iota}

/-- Close the global unit cap from factorwise actual telescope data, leaving
the adjacent unit cap explicit. -/
theorem exists_recoveredLiteralWitness_of_actualGlobalFactorCaps
    (C : CoherentStickyMultiscaleCover fine)
    (R : IntervalRootedRefinementScaleTree S)
    (B : BufferedChainFamily outerDepth chainDepth)
    (slot : Fin N)
    (eta_monotone : Monotone eta) (two_le_zero : (2 : Real) <= eta 0)
    (strict_room : eta (oneBasedStage slot) < epsilon)
    (not_all_large : Not (S.AllStepsLarge epsilon))
    (globalCaps : ActualGlobalFactorCaps B
      (firstNonLargeStep S epsilon not_all_large))
    (adjacent_value_le_one :
      (C.toActualIntervalCovers S).adjacentCoarseValue
        (firstNonLargeStep S epsilon not_all_large) <= 1)
    (V : VerifiedStepNodeLowerBounds
      (eta := reserveTailLoss eta (oneBasedStage slot)
        (halfReservedExponentRoom eta (oneBasedStage slot) epsilon))
      (stage := oneBasedStage slot)
      (C.toActualIntervalCovers S) R
        (firstNonLargeStep S epsilon not_all_large))
    (delta_pos : 0 < delta)
    (delta_le : delta <=
      actualStrictLossRecoveredSmallDeltaThreshold
        eta (oneBasedStage slot) epsilon iota) :
    Nonempty (KatzTaoDividingWitness delta N epsilon
      (recoveredReservedProfile eta (oneBasedStage slot)
        (halfReservedExponentRoom eta (oneBasedStage slot) epsilon))) := by
  exact exists_recoveredLiteralWitness_of_selectedUnitCaps
    C R B slot eta_monotone two_le_zero strict_room not_all_large
      (actualGlobalProductAt_le_one_of_factorCaps B
        (firstNonLargeStep S epsilon not_all_large) globalCaps)
      adjacent_value_le_one V delta_pos delta_le

/-- Close the adjacent unit cap from the actual active coarse cardinality,
leaving the global product cap explicit. -/
theorem exists_recoveredLiteralWitness_of_adjacentActiveCard
    (C : CoherentStickyMultiscaleCover fine)
    (R : IntervalRootedRefinementScaleTree S)
    (B : BufferedChainFamily outerDepth chainDepth)
    (slot : Fin N)
    (eta_monotone : Monotone eta) (two_le_zero : (2 : Real) <= eta 0)
    (strict_room : eta (oneBasedStage slot) < epsilon)
    (not_all_large : Not (S.AllStepsLarge epsilon))
    (global_product_le_one :
      actualGlobalProductAt B
        (firstNonLargeStep S epsilon not_all_large) <= 1)
    (active_card_le_one :
      (actualAdjacentScaleCover (C.toActualIntervalCovers S)
        (firstNonLargeStep S epsilon not_all_large)).activeCoarse.card <= 1)
    (V : VerifiedStepNodeLowerBounds
      (eta := reserveTailLoss eta (oneBasedStage slot)
        (halfReservedExponentRoom eta (oneBasedStage slot) epsilon))
      (stage := oneBasedStage slot)
      (C.toActualIntervalCovers S) R
        (firstNonLargeStep S epsilon not_all_large))
    (delta_pos : 0 < delta)
    (delta_le : delta <=
      actualStrictLossRecoveredSmallDeltaThreshold
        eta (oneBasedStage slot) epsilon iota) :
    Nonempty (KatzTaoDividingWitness delta N epsilon
      (recoveredReservedProfile eta (oneBasedStage slot)
        (halfReservedExponentRoom eta (oneBasedStage slot) epsilon))) := by
  exact exists_recoveredLiteralWitness_of_selectedUnitCaps
    C R B slot eta_monotone two_le_zero strict_room not_all_large
      global_product_le_one
      (adjacentCoarseValue_le_one_of_activeCoarse_card_le_one
        (C.toActualIntervalCovers S)
        (firstNonLargeStep S epsilon not_all_large) active_card_le_one)
      V delta_pos delta_le

/-- Close both remaining unit caps from their actual structural producers. -/
theorem exists_recoveredLiteralWitness_of_actualUnitCapProducers
    (C : CoherentStickyMultiscaleCover fine)
    (R : IntervalRootedRefinementScaleTree S)
    (B : BufferedChainFamily outerDepth chainDepth)
    (slot : Fin N)
    (eta_monotone : Monotone eta) (two_le_zero : (2 : Real) <= eta 0)
    (strict_room : eta (oneBasedStage slot) < epsilon)
    (not_all_large : Not (S.AllStepsLarge epsilon))
    (globalCaps : ActualGlobalFactorCaps B
      (firstNonLargeStep S epsilon not_all_large))
    (active_card_le_one :
      (actualAdjacentScaleCover (C.toActualIntervalCovers S)
        (firstNonLargeStep S epsilon not_all_large)).activeCoarse.card <= 1)
    (V : VerifiedStepNodeLowerBounds
      (eta := reserveTailLoss eta (oneBasedStage slot)
        (halfReservedExponentRoom eta (oneBasedStage slot) epsilon))
      (stage := oneBasedStage slot)
      (C.toActualIntervalCovers S) R
        (firstNonLargeStep S epsilon not_all_large))
    (delta_pos : 0 < delta)
    (delta_le : delta <=
      actualStrictLossRecoveredSmallDeltaThreshold
        eta (oneBasedStage slot) epsilon iota) :
    Nonempty (KatzTaoDividingWitness delta N epsilon
      (recoveredReservedProfile eta (oneBasedStage slot)
        (halfReservedExponentRoom eta (oneBasedStage slot) epsilon))) := by
  exact exists_recoveredLiteralWitness_of_actualGlobalFactorCaps
    C R B slot eta_monotone two_le_zero strict_room not_all_large globalCaps
      (adjacentCoarseValue_le_one_of_activeCoarse_card_le_one
        (C.toActualIntervalCovers S)
        (firstNonLargeStep S epsilon not_all_large) active_card_le_one)
      V delta_pos delta_le

#print axioms actualGlobalProductAt_le_one_of_factorCaps
#print axioms ActualGlobalFactorCaps.ofUnitFactors
#print axioms scaleBufferedTestBodyChainDimensionalLoss
#print axioms scaleBufferedTestBodyChainDimensionalLoss_localFactor
#print axioms scaleFamilyDimensionalLoss
#print axioms actualGlobalProductAt_scaleFamilyDimensionalLoss
#print axioms exists_scaledFamily_one_lt_actualGlobalProductAt
#print axioms not_nonempty_actualGlobalFactorCaps_of_one_lt
#print axioms adjacentCoarseValue_eq_actualAdjacentScaleCover
#print axioms coarseDeltaMax_le_one_of_activeCoarse_card_le_one
#print axioms adjacentCoarseValue_le_one_of_activeCoarse_card_le_one
#print axioms two_le_maximalConcentration_of_two_equal_positive
#print axioms two_le_coarseDeltaMax_of_repeated_active_tube
#print axioms not_adjacentCoarseValue_le_one_of_repeated_active_tube
#print axioms exists_recoveredLiteralWitness_of_actualGlobalFactorCaps
#print axioms exists_recoveredLiteralWitness_of_adjacentActiveCard
#print axioms exists_recoveredLiteralWitness_of_actualUnitCapProducers

end
end FamilyStickyScaleChainActualUnitCapProducerV1
