import Family8Grounding.Family8SameSelectedQFibreCrossingValueTransportV1
import Family8Grounding.Family8NormalizedCFDividingWitnessBridgeV4
import FamilyStickyGrounding.FamilyStickyFiniteFamilyMaximalConcentrationV1
import Mathlib.Tactic

/-!
# Finite weighted transport between the literal q-fibre crossings

Exact affine reindexing is stronger than is needed for a one-sided crossing
estimate with an explicit finite loss.  The source normalized constant times
the standard parent-fibre mass floor is at most the source fibre's maximal
concentration, hence at most its literal index cardinality.  On the target
side, every nonempty positive-volume fibre has canonical Frostman constant at
least one.  Combining these two facts gives

`source value <= (source fibre card / source mass floor) * target value`.

The loss is computed only from the literal source raw q-fibre and its two
actual crossing radii.  No affine correspondence, body equality, coverage
map, or numerical transport callback is assumed.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000

open Set MeasureTheory
open scoped ENNReal NNReal

namespace Family8SameSelectedQFibreWeightedCrossingValueTransportV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Family6CanonicalFrostmanConstantCoreV1
open Family8FirstParentwiseNormalizedCrossingWitnessV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8NormalizedCFDividingWitnessBridgeV2.StickyScaleCover
open Family8NormalizedCFDividingWitnessBridgeV4.StickyScaleCover
open Family8NormalizedCFDividingWitnessParentwiseFiniteSelectionV1.CoherentStickyMultiscaleCover
open Family8PaperFactorFiniteRunV2
open Family8ParentwiseBadParentFactorProductV1
open Family8ParentwiseCrossingIntegratedSuccessorV1
open Family8SameSelectedQFibreCrossingDestinationV1
open Family8SameSelectedQFibreCrossingValueTransportV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyFiniteFamilyMaximalConcentrationV1
open FamilyStickyScaleChainCoherentIntervalProducerV1

noncomputable section

universe u

/-! ## Generic lower nondegeneracy of the canonical normalization -/

/-- If the ambient body contains positive family mass, the canonical
Frostman normalization is at least one. -/
theorem one_le_canonicalFrostmanConstant_of_containedMass_ne_zero
    {index : Type u} [Fintype index]
    (F : ConvexFamily index) (K : ConvexBody Space)
    (hmass0 : containedMass F K ≠ 0) :
    (1 : ENNReal) <= canonicalFrostmanConstant F K := by
  have hvolume0 : volume (K : Set Space) ≠ 0 := by
    intro hzero
    exact hmass0 (containedMass_eq_zero_of_volume_eq_zero F K hzero)
  have hvolumeTop : volume (K : Set Space) ≠ ∞ :=
    K.isCompact.measure_lt_top.ne
  have hmassTop : containedMass F K ≠ ∞ :=
    (containedMass_lt_top F K).ne
  unfold canonicalFrostmanConstant
  apply (ENNReal.le_div_iff_mul_le
    (Or.inl hmass0) (Or.inl hmassTop)).2
  simp only [one_mul]
  apply (ENNReal.div_le_iff_le_mul
    (Or.inl hvolume0) (Or.inl hvolumeTop)).1
  exact concentration_le_maximalConcentration F K

/-! ## The literal finite source loss -/

variable {delta : NNReal} {iota : Type}
  [Fintype iota] [DecidableEq iota]
  {depth : Nat}
  {D : ActualTubeDatum delta iota} {hD : D.IsAdmissible}
  {C : CoherentStickyMultiscaleCover D.family}
  {S : FiniteScaleSequence delta depth}
  {epsilon : Real} {hepsilon : 0 <= epsilon}
  {eta : Nat -> Real} {N : Nat}
  {Wsrc : FirstParentwiseNormalizedCrossingWitness
    D hD C S epsilon hepsilon eta N}
  {step : SameObjectCrossingPaperStep Wsrc}

/-- The exact cardinal-over-mass-floor loss of the literal source raw
q-fibre. -/
def sourceRawQFibreCardFloorLoss : ENNReal :=
  (Fintype.card
      {i // i ∈ (sourceRawCrossingCover (Wsrc := Wsrc)).fiber Wsrc.q.1} :
      ENNReal) /
    parentFiberMassRatioFloor (S.tau Wsrc.m) Wsrc.rho

theorem sourceMassRatioFloor_ne_zero :
    parentFiberMassRatioFloor (S.tau Wsrc.m) Wsrc.rho ≠ 0 := by
  unfold parentFiberMassRatioFloor
  apply ENNReal.div_ne_zero.2
  constructor
  · apply ENNReal.div_ne_zero.2
    constructor
    · exact pow_ne_zero 2 (by
        exact_mod_cast
          (hD.delta_pos.trans_le (S.delta_le_tau Wsrc.m)).ne')
    · norm_num
  · finiteness

theorem sourceMassRatioFloor_ne_top :
    parentFiberMassRatioFloor (S.tau Wsrc.m) Wsrc.rho ≠ ∞ := by
  unfold parentFiberMassRatioFloor
  exact ENNReal.div_ne_top
    (ENNReal.div_ne_top (by finiteness) (by norm_num))
    (by
      have hrho : 0 < Wsrc.rho := crossingRhoPos Wsrc
      positivity)

/-- The displayed source loss is genuinely finite. -/
theorem sourceRawQFibreCardFloorLoss_ne_top :
    sourceRawQFibreCardFloorLoss (Wsrc := Wsrc) ≠ ∞ := by
  unfold sourceRawQFibreCardFloorLoss
  exact ENNReal.div_ne_top (by finiteness)
    (sourceMassRatioFloor_ne_zero (Wsrc := Wsrc))

/-- The source crossing value is bounded by its literal finite card/floor
loss.  The only geometric range used is the half-scale bound already stored
by the integrated paper step. -/
theorem sourceCrossingValue_le_cardFloorLoss
    (step : SameObjectCrossingPaperStep Wsrc) :
    actualCrossingValue Wsrc <=
      sourceRawQFibreCardFloorLoss (Wsrc := Wsrc) := by
  have htauPos : 0 < S.tau Wsrc.m :=
    hD.delta_pos.trans_le (S.delta_le_tau Wsrc.m)
  have hrhoPos : 0 < Wsrc.rho := crossingRhoPos Wsrc
  have htauHalf : S.tau Wsrc.m <= (2 : NNReal)⁻¹ :=
    (crossingTauLeRho Wsrc).trans step.integrated.readiness.rho_le_half
  have hfloor :=
    parentNormalizedFiberCFAt_mul_floor_le_maximalConcentration
      (sourceRawCrossingCover (Wsrc := Wsrc)) htauPos hrhoPos
      htauHalf step.integrated.readiness.rho_le_half Wsrc.q
  have hcard := maximalConcentration_le_card
    ((sourceRawCrossingCover (Wsrc := Wsrc)).fiberFamily Wsrc.q.1)
  apply (ENNReal.le_div_iff_mul_le
    (Or.inl (sourceMassRatioFloor_ne_zero (Wsrc := Wsrc)))
    (Or.inl (sourceMassRatioFloor_ne_top (Wsrc := Wsrc)))).2
  exact hfloor.trans hcard

/-! ## Target nondegeneracy and the weighted transport -/

variable {Y : SameSelectedQFibreCrossingDestination step}

/-- The destination literal raw q-fibre has canonical normalization at least
one. -/
theorem one_le_destinationCrossingValue
    (Y : SameSelectedQFibreCrossingDestination step) :
    (1 : ENNReal) <= actualCrossingValue Y.destination := by
  have htauPos :
      0 < Y.destinationScales.tau Y.destination.m :=
    step.integrated.dualChild.qFibreChild_admissible.delta_pos.trans_le
      (Y.destinationScales.delta_le_tau Y.destination.m)
  have hmass0 : containedMass
      ((destinationRawCrossingCover Y).fiberFamily Y.destination.q.1)
      ((destinationRawCrossingCover Y).activeCoarseFamily Y.destination.q) ≠
        0 := by
    rw [containedMass_fiberFamily_parent_eq_familyVolume]
    exact (fiberFamilyVolume_pos
      (destinationRawCrossingCover Y) htauPos Y.destination.q).ne'
  unfold actualCrossingValue parentNormalizedFiberCFAt
  exact one_le_canonicalFrostmanConstant_of_containedMass_ne_zero
    ((destinationRawCrossingCover Y).fiberFamily Y.destination.q.1)
    ((destinationRawCrossingCover Y).activeCoarseFamily Y.destination.q)
    hmass0

/-- Callback-free one-sided transport of the two literal crossing values,
with an explicit finite source card/floor loss. -/
theorem crossingValue_le_cardFloorLoss_mul_destination
    (Y : SameSelectedQFibreCrossingDestination step) :
    actualCrossingValue Wsrc <=
      sourceRawQFibreCardFloorLoss (Wsrc := Wsrc) *
        actualCrossingValue Y.destination := by
  calc
    actualCrossingValue Wsrc <=
        sourceRawQFibreCardFloorLoss (Wsrc := Wsrc) :=
      sourceCrossingValue_le_cardFloorLoss step
    _ = sourceRawQFibreCardFloorLoss (Wsrc := Wsrc) * 1 := by simp
    _ <= sourceRawQFibreCardFloorLoss (Wsrc := Wsrc) *
          actualCrossingValue Y.destination := by
      gcongr
      exact one_le_destinationCrossingValue Y

#print axioms one_le_canonicalFrostmanConstant_of_containedMass_ne_zero
#print axioms sourceRawQFibreCardFloorLoss
#print axioms sourceMassRatioFloor_ne_zero
#print axioms sourceMassRatioFloor_ne_top
#print axioms sourceRawQFibreCardFloorLoss_ne_top
#print axioms sourceCrossingValue_le_cardFloorLoss
#print axioms one_le_destinationCrossingValue
#print axioms crossingValue_le_cardFloorLoss_mul_destination

end
end Family8SameSelectedQFibreWeightedCrossingValueTransportV1
