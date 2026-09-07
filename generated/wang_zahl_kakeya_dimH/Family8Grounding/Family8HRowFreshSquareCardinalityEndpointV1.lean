import Family8Grounding.Family8Prop66RowCrossScaleAggregationV1
import Family8Grounding.Family8FrostmanOneFromPointwisePackingV1
import Family8Grounding.Family8ThreeScaleFrostmanFactorAlgebraV2
import Mathlib.Tactic

/-!
# Direct square-row cardinality endpoint

For a square plank datum, a nonempty complete-fibre H-row injects into the
original index type.  In the high-exponent range `2 / 3 <= beta`, the literal
cardinality estimate therefore gives the Family-6 plank factor at the original
source-card thickening parameter.  This route does not assert the generally
false forward-power budget.
-/

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 5000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal InnerProductSpace

namespace Family8HRowFreshSquareCardinalityEndpointV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Family6AffinePlankAnalyticHypothesesStableV1
open Family6CanonicalFrostmanConstantCoreV1
open Family8FrostmanOneFromPointwisePackingV1
open Family8ThreeScaleFrostmanFactorAlgebraV2
open Family8PlankThickControlMutualContainmentClusteringV2
open Family8PlankThickControlOwnerFiberLogBucketV2
open Family8PlankThickControlRetainedOwnerFamilyV3
open Family8PlankRetainedOwnerHeavyMassSelectionV3
open Family8PlankHeavyRetainedOwnerActiveCellCommonBallContainerV1
open Family8PlankHeavyActiveSelectedOwnerPropertyReadyTubeDatumV1
open Family8PlankHeavyActiveSelectedOwnerHRowFreshPropertyBundleV1
open Family8Prop66Eq66ComposerFromHRowFreshV1

noncomputable section

local instance (p : Prop) : Decidable p := Classical.propDecidable p

universe v

variable {iota : Type} [Fintype iota] [DecidableEq iota]
variable {a : NNReal}

/-- The canonical constant of the nonempty complete-fibre H-row is at least
one. -/
theorem hRowFreshCanonicalFrostmanConstant_one_le
    (D : ShadedConvexPlankFamily iota a a) {theta : NNReal}
    (C : MutualThickeningClustering D theta)
    (q : Fin (Nat.log 2 (Fintype.card iota) + 1))
    {cellIndex : Type v} (cell : cellIndex → Set Space)
    (hcell : ∀ p, MeasurableSet (cell p)) (selectedCells : Finset cellIndex)
    (hmass : (retainedOwnerPlankFamily D C q).shading.shadingMass ≠ 0)
    (hactive : (activeRetainedOwnerCellIndices
      D C q cell hcell selectedCells).Nonempty)
    {epsilon beta eta : Real}
    (B : HRowFreshPropertyBundle
      D C q cell hcell selectedCells hmass hactive epsilon beta eta) :
    (1 : ENNReal) ≤ hRowFreshCanonicalFrostmanConstant
      D C q cell hcell selectedCells hmass hactive B.tau B.S := by
  let rowD := HRowFreshPlankDatum
    D C q cell hcell selectedCells hmass hactive B.tau B.S
  have hmass0 : containedMass rowD.family rowD.ambient ≠ 0 := by
    rw [containedMass_eq_familyVolume_of_contained
      rowD.family rowD.ambient rowD.contained_in_ambient]
    exact (activeSelectedOwnerRowPlankDatum_familyVolume_pos
      D C q cell hcell selectedCells hmass hactive B.tau B.S B.hrow).ne'
  have hvolume0 : volume (rowD.ambient : Set Space) ≠ 0 := by
    intro hzero
    exact hmass0 (containedMass_eq_zero_of_volume_eq_zero
      rowD.family rowD.ambient hzero)
  have hvolumeTop : volume (rowD.ambient : Set Space) ≠ ∞ :=
    rowD.ambient.isCompact.measure_lt_top.ne
  have hmassTop : containedMass rowD.family rowD.ambient ≠ ∞ :=
    (containedMass_lt_top rowD.family rowD.ambient).ne
  change (1 : ENNReal) ≤ canonicalFrostmanConstant rowD.family rowD.ambient
  unfold canonicalFrostmanConstant
  apply (ENNReal.le_div_iff_mul_le
    (Or.inl hmass0) (Or.inl hmassTop)).2
  simp only [one_mul]
  apply (ENNReal.div_le_iff_le_mul
    (Or.inl hvolume0) (Or.inl hvolumeTop)).1
  exact concentration_le_maximalConcentration rowD.family rowD.ambient

/-- Forgetting the row owner injects every row occurrence into the original
source index type. -/
theorem hRowFreshOccurrence_card_le_sourceCard
    (D : ShadedConvexPlankFamily iota a a) {theta : NNReal}
    (C : MutualThickeningClustering D theta)
    (q : Fin (Nat.log 2 (Fintype.card iota) + 1))
    {cellIndex : Type v} (cell : cellIndex → Set Space)
    (hcell : ∀ p, MeasurableSet (cell p)) (selectedCells : Finset cellIndex)
    (hmass : (retainedOwnerPlankFamily D C q).shading.shadingMass ≠ 0)
    (hactive : (activeRetainedOwnerCellIndices
      D C q cell hcell selectedCells).Nonempty)
    {epsilon beta eta : Real}
    (B : HRowFreshPropertyBundle
      D C q cell hcell selectedCells hmass hactive epsilon beta eta) :
    Fintype.card (HRowFreshOccurrence
      D C q cell hcell selectedCells hmass hactive B.tau B.S) ≤
      Fintype.card iota := by
  exact Fintype.card_le_of_injective
    (fun p : HRowFreshOccurrence
      D C q cell hcell selectedCells hmass hactive B.tau B.S ↦ p.2.1)
    (activeSelectedOwnerRowOccurrence_source_injective
      D C q cell hcell selectedCells hmass hactive B.tau B.S)

/-- Exact square-plank normalization when the thickening parameter need not
equal the datum's own index cardinality. -/
theorem convexPlankFrostmanFactor_square_eq_sectionEightScaleCount_with_M
    {index : Type v} [Fintype index] [DecidableEq index]
    (D : ShadedConvexPlankFamily index a a)
    (epsilon beta : Real) (CF : ENNReal) (M : NNReal)
    (ha : 0 < a) :
    convexPlankFrostmanFactor D epsilon beta CF M =
      (a : ENNReal) ^ (-epsilon) *
        CF ^ (1 - beta / 2) *
        (M : ENNReal) ^ (beta / 2) *
        sectionEightScaleCountFrostmanFactor
          a 1 (Fintype.card index) beta := by
  unfold convexPlankFrostmanFactor
  unfold sectionEightScaleCountFrostmanFactor
  have ha0 : (a : ENNReal) ≠ 0 := ENNReal.coe_ne_zero.mpr ha.ne'
  rw [ENNReal.div_self ha0 ENNReal.coe_ne_top]
  simp only [ENNReal.coe_one, div_one]
  ac_rfl

/-- In the high-beta range, the square-plank factor with a source-card
thickening parameter contains the datum's literal index cardinality together
with the full scale gain `a^(2 - 3*beta - epsilon)`. -/
theorem scaleGain_mul_indexCard_le_convexPlankFrostmanFactor_square
    {index : Type v} [Fintype index] [Nonempty index] [DecidableEq index]
    (D : ShadedConvexPlankFamily index a a)
    (epsilon beta : Real) (CF : ENNReal) (M : NNReal)
    (ha : 0 < a) (hbetaHigh : (2 : Real) / 3 ≤ beta)
    (hbeta2 : beta ≤ 2) (hCF : (1 : ENNReal) ≤ CF)
    (hcardM : (Fintype.card index : ENNReal) ≤ (M : ENNReal)) :
    (a : ENNReal) ^ (2 - 3 * beta - epsilon) *
        (Fintype.card index : ENNReal) ≤
      convexPlankFrostmanFactor D epsilon beta CF M := by
  let n : ENNReal := (Fintype.card index : ENNReal)
  let p : Real := beta / 2
  let r : Real := 1 - beta / 2
  let scaleGain : ENNReal := (a : ENNReal) ^ (2 - 3 * beta - epsilon)
  have hn0 : n ≠ 0 := by
    dsimp only [n]
    exact_mod_cast Fintype.card_ne_zero
  have hnTop : n ≠ ∞ := by simp [n]
  have hp : 0 ≤ p := by dsimp only [p]; linarith
  have hr : 0 ≤ r := by dsimp only [r]; linarith
  have hcountPow : n ^ p ≤ (M : ENNReal) ^ p :=
    ENNReal.rpow_le_rpow hcardM hp
  have hpr : p + r = 1 := by
    dsimp only [p, r]
    ring
  have hcountSplit : n = n ^ p * n ^ r := by
    rw [← ENNReal.rpow_add _ _ hn0 hnTop]
    rw [hpr, ENNReal.rpow_one]
  have hcount : n ≤ (M : ENNReal) ^ p * n ^ r := by
    calc
      n = n ^ p * n ^ r := hcountSplit
      _ ≤ (M : ENNReal) ^ p * n ^ r := mul_le_mul' hcountPow le_rfl
  have hCFpow : (1 : ENNReal) ≤ CF ^ r := by
    simpa only [ENNReal.one_rpow] using ENNReal.rpow_le_rpow hCF hr
  have hcore : n ≤ CF ^ r * ((M : ENNReal) ^ p * n ^ r) := by
    calc
      n = 1 * n := by rw [one_mul]
      _ ≤ CF ^ r * ((M : ENNReal) ^ p * n ^ r) :=
        mul_le_mul' hCFpow hcount
  have ha0 : (a : ENNReal) ≠ 0 := ENNReal.coe_ne_zero.mpr ha.ne'
  have haTop : (a : ENNReal) ≠ ∞ := ENNReal.coe_ne_top
  rw [convexPlankFrostmanFactor_square_eq_sectionEightScaleCount_with_M
    D epsilon beta CF M ha]
  rw [sectionEightScaleCountFrostmanFactor_eq
    ha (by norm_num) hbeta2]
  simp only [ENNReal.coe_one, div_one]
  change scaleGain * n ≤
    (a : ENNReal) ^ (-epsilon) * CF ^ r * (M : ENNReal) ^ p *
      ((a : ENNReal) ^ (-2 * beta + 2 * (1 - beta / 2)) * n ^ r)
  calc
    scaleGain * n ≤
        scaleGain * (CF ^ r * ((M : ENNReal) ^ p * n ^ r)) :=
      mul_le_mul' le_rfl hcore
    _ = (a : ENNReal) ^ (-epsilon) * CF ^ r * (M : ENNReal) ^ p *
        ((a : ENNReal) ^ (-2 * beta + 2 * (1 - beta / 2)) * n ^ r) := by
      dsimp only [scaleGain]
      rw [show 2 - 3 * beta - epsilon =
          -epsilon + (-2 * beta + 2 * (1 - beta / 2)) by ring,
        ENNReal.rpow_add _ _ ha0 haTop]
      ac_rfl

/-- At square geometry and `2 / 3 ≤ beta`, the crude cardinality estimate
already bounds the selected H-row by the original source-card Family-6 factor.
This is the direct endpoint available on the complementary forward-power
branch (and in fact does not need to inspect which side of that dichotomy
holds). -/
theorem hRowFreshPlankDatum_averageMultiplicity_le_sourceCardProp66Factor_highBeta
    (D : ShadedConvexPlankFamily iota a a) {theta : NNReal}
    (C : MutualThickeningClustering D theta)
    (q : Fin (Nat.log 2 (Fintype.card iota) + 1))
    {cellIndex : Type v} (cell : cellIndex → Set Space)
    (hcell : ∀ p, MeasurableSet (cell p)) (selectedCells : Finset cellIndex)
    (hmass : (retainedOwnerPlankFamily D C q).shading.shadingMass ≠ 0)
    (hactive : (activeRetainedOwnerCellIndices
      D C q cell hcell selectedCells).Nonempty)
    {epsilon beta eta : Real}
    (B : HRowFreshPropertyBundle
      D C q cell hcell selectedCells hmass hactive epsilon beta eta)
    (ha : 0 < a) (haOne : a ≤ 1) (hepsilon : 0 ≤ epsilon)
    (hbetaHigh : (2 : Real) / 3 ≤ beta) (hbeta2 : beta ≤ 2) :
    (HRowFreshPlankDatum
        D C q cell hcell selectedCells hmass hactive B.tau B.S).shading.averageMultiplicity ≤
      hRowFreshProp66Factor
        D C q cell hcell selectedCells hmass hactive B
          (Fintype.card iota : NNReal) := by
  let rowD := HRowFreshPlankDatum
    D C q cell hcell selectedCells hmass hactive B.tau B.S
  let occurrence := HRowFreshOccurrence
    D C q cell hcell selectedCells hmass hactive B.tau B.S
  let CF := hRowFreshCanonicalFrostmanConstant
    D C q cell hcell selectedCells hmass hactive B.tau B.S
  let _ : Nonempty occurrence := B.occurrence_nonempty
  have havg : rowD.shading.averageMultiplicity ≤
      (Fintype.card occurrence : ENNReal) :=
    averageMultiplicity_le_indexCard rowD.shading
  have hcardNat : Fintype.card occurrence ≤ Fintype.card iota := by
    simpa only [occurrence] using
      hRowFreshOccurrence_card_le_sourceCard
        D C q cell hcell selectedCells hmass hactive B
  have hcard : (Fintype.card occurrence : ENNReal) ≤
      ((Fintype.card iota : NNReal) : ENNReal) := by
    exact_mod_cast hcardNat
  have hCF : (1 : ENNReal) ≤ CF := by
    simpa only [CF] using
      hRowFreshCanonicalFrostmanConstant_one_le
        D C q cell hcell selectedCells hmass hactive B
  have hfactor :
      (a : ENNReal) ^ (2 - 3 * beta - epsilon) *
          (Fintype.card occurrence : ENNReal) ≤
        convexPlankFrostmanFactor rowD epsilon beta CF
          (Fintype.card iota : NNReal) :=
    scaleGain_mul_indexCard_le_convexPlankFrostmanFactor_square
      rowD epsilon beta CF (Fintype.card iota : NNReal)
        ha hbetaHigh hbeta2 hCF hcard
  have hscaleExp : 2 - 3 * beta - epsilon ≤ 0 := by linarith
  have hscaleOne : (1 : ENNReal) ≤
      (a : ENNReal) ^ (2 - 3 * beta - epsilon) := by
    by_cases hzero : 2 - 3 * beta - epsilon = 0
    · rw [hzero, ENNReal.rpow_zero]
    · exact ENNReal.one_le_rpow_of_pos_of_le_one_of_neg
        (ENNReal.coe_pos.mpr ha)
        (by exact_mod_cast haOne)
        (lt_of_le_of_ne hscaleExp hzero)
  calc
    (HRowFreshPlankDatum
        D C q cell hcell selectedCells hmass hactive B.tau B.S).shading.averageMultiplicity =
        rowD.shading.averageMultiplicity := rfl
    _ ≤ (Fintype.card occurrence : ENNReal) := havg
    _ = 1 * (Fintype.card occurrence : ENNReal) := by rw [one_mul]
    _ ≤ (a : ENNReal) ^ (2 - 3 * beta - epsilon) *
          (Fintype.card occurrence : ENNReal) :=
      mul_le_mul' hscaleOne le_rfl
    _ ≤ convexPlankFrostmanFactor rowD epsilon beta CF
          (Fintype.card iota : NNReal) := hfactor
    _ = hRowFreshProp66Factor
        D C q cell hcell selectedCells hmass hactive B
          (Fintype.card iota : NNReal) := rfl

/-- Direct actual-third endpoint retaining the full high-beta square-scale
gain.  Thus the source-to-row correlation loss may be paid by that gain,
without requiring `effectiveLoss ≤ ownerBucketBranching`. -/
theorem hRowFresh_actualThirdAverage_le_sourceCardProp66Factor_of_correlationPower
    (D : ShadedConvexPlankFamily iota a a) {theta : NNReal}
    (C : MutualThickeningClustering D theta)
    (q : Fin (Nat.log 2 (Fintype.card iota) + 1))
    {cellIndex : Type v} (cell : cellIndex → Set Space)
    (hcell : ∀ p, MeasurableSet (cell p)) (selectedCells : Finset cellIndex)
    (hmass : (retainedOwnerPlankFamily D C q).shading.shadingMass ≠ 0)
    (hactive : (activeRetainedOwnerCellIndices
      D C q cell hcell selectedCells).Nonempty)
    {epsilon beta eta : Real}
    (B : HRowFreshPropertyBundle
      D C q cell hcell selectedCells hmass hactive epsilon beta eta)
    (actualThirdAverage correlationLoss : ENNReal)
    (hActual : HRowFreshActualThirdCorrelationObligation
      D C q cell hcell selectedCells hmass hactive B
        actualThirdAverage correlationLoss)
    (ha : 0 < a) (hbetaHigh : (2 : Real) / 3 ≤ beta)
    (hbeta2 : beta ≤ 2)
    (hCorrelationPower : correlationLoss ≤
      (a : ENNReal) ^ (2 - 3 * beta - epsilon)) :
    actualThirdAverage ≤
      hRowFreshProp66Factor
        D C q cell hcell selectedCells hmass hactive B
          (Fintype.card iota : NNReal) := by
  let rowD := HRowFreshPlankDatum
    D C q cell hcell selectedCells hmass hactive B.tau B.S
  let occurrence := HRowFreshOccurrence
    D C q cell hcell selectedCells hmass hactive B.tau B.S
  let CF := hRowFreshCanonicalFrostmanConstant
    D C q cell hcell selectedCells hmass hactive B.tau B.S
  let _ : Nonempty occurrence := B.occurrence_nonempty
  have havg : rowD.shading.averageMultiplicity ≤
      (Fintype.card occurrence : ENNReal) :=
    averageMultiplicity_le_indexCard rowD.shading
  have hcardNat : Fintype.card occurrence ≤ Fintype.card iota := by
    simpa only [occurrence] using
      hRowFreshOccurrence_card_le_sourceCard
        D C q cell hcell selectedCells hmass hactive B
  have hcard : (Fintype.card occurrence : ENNReal) ≤
      ((Fintype.card iota : NNReal) : ENNReal) := by
    exact_mod_cast hcardNat
  have hCF : (1 : ENNReal) ≤ CF := by
    simpa only [CF] using
      hRowFreshCanonicalFrostmanConstant_one_le
        D C q cell hcell selectedCells hmass hactive B
  have hfactor :
      (a : ENNReal) ^ (2 - 3 * beta - epsilon) *
          (Fintype.card occurrence : ENNReal) ≤
        convexPlankFrostmanFactor rowD epsilon beta CF
          (Fintype.card iota : NNReal) :=
    scaleGain_mul_indexCard_le_convexPlankFrostmanFactor_square
      rowD epsilon beta CF (Fintype.card iota : NNReal)
        ha hbetaHigh hbeta2 hCF hcard
  calc
    actualThirdAverage ≤ correlationLoss * rowD.shading.averageMultiplicity :=
      hActual
    _ ≤ correlationLoss * (Fintype.card occurrence : ENNReal) :=
      mul_le_mul' le_rfl havg
    _ ≤ (a : ENNReal) ^ (2 - 3 * beta - epsilon) *
          (Fintype.card occurrence : ENNReal) :=
      mul_le_mul' hCorrelationPower le_rfl
    _ ≤ convexPlankFrostmanFactor rowD epsilon beta CF
          (Fintype.card iota : NNReal) := hfactor
    _ = hRowFreshProp66Factor
        D C q cell hcell selectedCells hmass hactive B
          (Fintype.card iota : NNReal) := rfl

#print axioms hRowFreshCanonicalFrostmanConstant_one_le
#print axioms hRowFreshOccurrence_card_le_sourceCard
#print axioms convexPlankFrostmanFactor_square_eq_sectionEightScaleCount_with_M
#print axioms scaleGain_mul_indexCard_le_convexPlankFrostmanFactor_square
#print axioms
  hRowFreshPlankDatum_averageMultiplicity_le_sourceCardProp66Factor_highBeta
#print axioms
  hRowFresh_actualThirdAverage_le_sourceCardProp66Factor_of_correlationPower

end
end Family8HRowFreshSquareCardinalityEndpointV1
