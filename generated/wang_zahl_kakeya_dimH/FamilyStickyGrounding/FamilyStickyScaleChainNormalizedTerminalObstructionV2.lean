import FamilyStickyGrounding.FamilyStickyScaleChainCanonicalOneStepEnvelopeCancellationV2
import FamilyStickyGrounding.FamilyStickyScaleChainCanonicalTerminalUnitBodyProducerV2

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace FamilyStickyScaleChainNormalizedTerminalObstructionV2

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open FamilyStickyDeltaMaxFiniteChainV2.StickyScaleCover
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainCoherentIntervalProducerV1
open FamilyStickyScaleChainCoherentExactHierarchyProducerV2
open FamilyStickyScaleChainCoherentExactHierarchyProducerV2.CoherentExactHierarchyFamily
open FamilyStickyScaleChainBufferedHierarchyProducerV1.MultiscaleTubeHierarchy
open FamilyStickyScaleChainCanonicalBufferedTestBodyChainV2.MultiscaleTubeHierarchy
open FamilyStickyScaleChainCanonicalTerminalUnitBodyProducerV2
open FamilyStickyScaleChainCanonicalTerminalUnitBodyProducerV2.MultiscaleTubeHierarchy
open FamilyStickyScaleChainCanonicalCoherentBufferedFamilyV2
open FamilyStickyScaleChainCanonicalOneStepEnvelopeCancellationV2
open FamilyStickyScaleChainHierarchyRecursiveStoppingDriverV2
open FamilyStickyScaleChainBadSplitChildEnvelopeReductionV2
open FamilyStickyScaleChainTerminalFiniteSearchV1
open FamilyStickyScaleSequenceInsertionTransportV2.FiniteScaleSequence

noncomputable section

/-!
# The normalized-terminal obstruction at a real bad split

The exponent field of `OneStepNormalizedTerminalExponentBound` contains no
hidden slack: because every scale is at most one, such a bound exists exactly
when the literal normalized terminal quantity is below the required power.

The automatic terminal-unit body closes concentration, but its volume
dominates the whole terminal family volume.  Consequently its normalized
terminal quantity is bounded *below* by the product of the initial and
terminal active cardinalities.  Thus that automatic body cannot close the
analytic child estimate without an additional cardinality/power estimate.
-/

universe u

variable {delta : NNReal} {iota : Type u}
  [Fintype iota] [DecidableEq iota]
  {fine : UniformTubeFamily delta iota}
  (C : CoherentStickyMultiscaleCover fine)
  {outerDepth : Nat}

/-! ## The exponent package is equivalent to its literal endpoint -/

/-- There is no gain from choosing an exponent larger than the required
one.  On a base at most one, the largest permitted right-hand side is obtained
at the boundary exponent `-profile (stage - 1)`. -/
theorem nonempty_oneStepNormalizedTerminalExponentBound_iff
    (F : CoherentExactHierarchyFamily C outerDepth 1)
    (initialBody : Fin outerDepth -> ConvexBody Space)
    (S : FiniteScaleSequence delta outerDepth)
    (profile : Nat -> Real) (stage : Nat) (m : Fin outerDepth) :
    Nonempty (OneStepNormalizedTerminalExponentBound C F initialBody
      S profile stage m) <->
      canonicalOneStepNormalizedTerminalAt C F initialBody m <=
        (S.theta m : ENNReal) ^ (-profile (stage - 1)) := by
  constructor
  · rintro ⟨bound⟩
    have theta_le_one : (S.theta m : ENNReal) <= 1 := by
      exact_mod_cast S.theta_le_one m
    exact bound.normalizedTerminal_upper.trans
      (ENNReal.rpow_le_rpow_of_exponent_ge theta_le_one
        bound.exponent_balance)
  · intro h
    exact ⟨{
      exponent := -profile (stage - 1)
      normalizedTerminal_upper := h
      exponent_balance := le_rfl }⟩

/-! ## What the automatic terminal-unit body necessarily costs -/

/-- The canonical automatic initial body on each one-step interval. -/
def automaticTerminalInitialBody
    (F : CoherentExactHierarchyFamily C outerDepth 1)
    (m : Fin outerDepth) : ConvexBody Space :=
  canonicalTerminalUnitBody (F.hierarchy m)

/-- The automatic initial body has positive volume on every interval. -/
theorem automaticTerminalInitialBody_volume_pos
    (F : CoherentExactHierarchyFamily C outerDepth 1)
    (m : Fin outerDepth) :
    0 < volume (automaticTerminalInitialBody C F m : Set Space) := by
  exact canonicalTerminalUnitBody_volume_pos (F.hierarchy m)

/-- Cardinality of the literal active terminal index type. -/
def canonicalTerminalActiveCardAt
    (F : CoherentExactHierarchyFamily C outerDepth 1)
    (m : Fin outerDepth) : Nat :=
  Fintype.card {i // i ∈
    ((F.hierarchy m).effectiveFamily 1).refinement.refined}

/-- At any positive effective radius, terminal cardinality times the attained
tube-volume floor is bounded by the total terminal family volume. -/
theorem terminalCard_mul_canonicalTubeVolume_le_familyVolume
    (F : CoherentExactHierarchyFamily C outerDepth 1)
    (m : Fin outerDepth) :
    (canonicalTerminalActiveCardAt C F m : ENNReal) *
        canonicalTubeVolume (F.hierarchy m) (by omega) 1 <=
      familyVolume (effectiveActiveFamily (F.hierarchy m) 1) := by
  let H := F.hierarchy m
  rw [canonicalTubeVolume_of_le H (by omega) 1 (by omega)]
  unfold canonicalTerminalActiveCardAt familyVolume effectiveActiveFamily
  simp only [UniformTubeFamily.bodyFamily, Tube.coe_body]
  calc
    (Fintype.card {i // i ∈
          (H.effectiveFamily 1).refinement.refined} : ENNReal) *
        activeTubeVolumeFloorAt H (by omega) 1 (by omega) =
      ∑ i : {i // i ∈
          (H.effectiveFamily 1).refinement.refined},
        activeTubeVolumeFloorAt H (by omega) 1 (by omega) := by simp
    _ <= ∑ i : {i // i ∈
          (H.effectiveFamily 1).refinement.refined},
        volume ((H.effectiveFamily 1).tubes i.1).carrier := by
      exact Finset.sum_le_sum fun i _ =>
        activeTubeVolumeFloorAt_le H (by omega) 1 (by omega) i

/-- For the automatic terminal-unit body, the normalized terminal volume is
at least the active terminal cardinality. -/
theorem terminalCard_le_automaticTerminal_normalizedVolume
    (F : CoherentExactHierarchyFamily C outerDepth 1)
    (delta_pos : 0 < delta) (m : Fin outerDepth) :
    (canonicalTerminalActiveCardAt C F m : ENNReal) <=
      volume
          (canonicalTestBody (F.hierarchy m)
            (automaticTerminalInitialBody C F m) 1 : Set Space) /
        canonicalTubeVolume (F.hierarchy m) (by omega) 1 := by
  let H := F.hierarchy m
  have hvolume :
      familyVolume (effectiveActiveFamily H 1) <=
        volume
          (canonicalTestBody H (automaticTerminalInitialBody C F m) 1 :
            Set Space) := by
    exact (terminal_familyVolume_le_canonicalTerminalUnitBody H).trans
      (measure_mono
        (initial_subset_canonicalTestBody H
          (automaticTerminalInitialBody C F m) 1))
  have hmul :
      (canonicalTerminalActiveCardAt C F m : ENNReal) *
          canonicalTubeVolume H (by omega) 1 <=
        volume
          (canonicalTestBody H (automaticTerminalInitialBody C F m) 1 :
            Set Space) :=
    (terminalCard_mul_canonicalTubeVolume_le_familyVolume C F m).trans
      hvolume
  have hfloor_pos : 0 < canonicalTubeVolume H (by omega) 1 := by
    exact canonicalTubeVolume_pos H (by omega)
      (fun l _hl => coherentHierarchy_effectiveRadius_pos F delta_pos m l)
      1 (by omega)
  have hfloor_top : canonicalTubeVolume H (by omega) 1 ≠ ∞ :=
    canonicalTubeVolume_ne_top H (by omega) 1 (by omega)
  exact (ENNReal.le_div_iff_mul_le (Or.inl hfloor_pos.ne')
    (Or.inl hfloor_top)).2 hmul

/-- Hence the full automatic normalized-terminal quantity is bounded below
by the product of the initial and terminal active cardinalities. -/
theorem activeCardProduct_le_automatic_normalizedTerminal
    (F : CoherentExactHierarchyFamily C outerDepth 1)
    (delta_pos : 0 < delta) (m : Fin outerDepth) :
    (((F.chain m).intervalCover C 0 (by omega)).activeFine.card : ENNReal) *
        (canonicalTerminalActiveCardAt C F m : ENNReal) <=
      canonicalOneStepNormalizedTerminalAt C F
        (automaticTerminalInitialBody C F) m := by
  unfold canonicalOneStepNormalizedTerminalAt
  exact mul_le_mul' le_rfl
    (terminalCard_le_automaticTerminal_normalizedVolume C F delta_pos m)

/-- Any claimed automatic-body exponent bound therefore entails an actual
cardinality-power estimate.  This is a necessary condition, not a renamed
analytic hypothesis. -/
theorem activeCardProduct_le_requiredPower_of_automaticBound
    (F : CoherentExactHierarchyFamily C outerDepth 1)
    (delta_pos : 0 < delta)
    (S : FiniteScaleSequence delta outerDepth)
    (profile : Nat -> Real) (stage : Nat) (m : Fin outerDepth)
    (bound : OneStepNormalizedTerminalExponentBound C F
      (automaticTerminalInitialBody C F) S profile stage m) :
    (((F.chain m).intervalCover C 0 (by omega)).activeFine.card : ENNReal) *
        (canonicalTerminalActiveCardAt C F m : ENNReal) <=
      (S.theta m : ENNReal) ^ (-profile (stage - 1)) := by
  have normalized_le :
      canonicalOneStepNormalizedTerminalAt C F
          (automaticTerminalInitialBody C F) m <=
        (S.theta m : ENNReal) ^ (-profile (stage - 1)) :=
    (nonempty_oneStepNormalizedTerminalExponentBound_iff C F
      (automaticTerminalInitialBody C F) S profile stage m).mp ⟨bound⟩
  exact (activeCardProduct_le_automatic_normalizedTerminal C F delta_pos m).trans
    normalized_le

/-! ## Specialization to the two literal bad-split children -/

variable {gapEpsilon : Real} {N : Nat} {eta : Nat -> Real}

/-- The automatic bodies really do close terminal concentration on every
refined interval.  Thus concentration normalization is not the missing child estimate. -/
theorem refinedAutomaticTerminal_top_le_one
    (gap_nonneg : 0 <= gapEpsilon) (delta_pos : 0 < delta)
    (X : HierarchyStoppingState delta N gapEpsilon eta)
    (bad : SelectedActualBadSplit C X)
    (hfine : fine.refinement.refined.Nonempty)
    (k : Fin (X.depth + 1)) :
    let F := refinedExactFamily C gap_nonneg delta_pos X bad hfine
    concentration (effectiveActiveFamily (F.hierarchy k) 1)
        (canonicalTestBody (F.hierarchy k)
          (automaticTerminalInitialBody C F k) 1) <= 1 := by
  dsimp only
  exact canonicalTerminalUnitBody_top_le_one
    ((refinedExactFamily C gap_nonneg delta_pos X bad hfine).hierarchy k)

/-- On the lower child, existence of the exponent package is exactly the
literal estimate at the inserted radius. -/
theorem lowerChild_automaticBound_nonempty_iff_literalPower
    (gap_nonneg : 0 <= gapEpsilon) (delta_pos : 0 < delta)
    (X : HierarchyStoppingState delta N gapEpsilon eta)
    (bad : SelectedActualBadSplit C X)
    (hfine : fine.refinement.refined.Nonempty) :
    let F := refinedExactFamily C gap_nonneg delta_pos X bad hfine
    let S := bad.refinedScales C X gap_nonneg delta_pos
    Nonempty (OneStepNormalizedTerminalExponentBound C F
      (automaticTerminalInitialBody C F) S eta (X.stage + 1)
      (lowerChildIndex bad.selectedStep)) <->
      canonicalOneStepNormalizedTerminalAt C F
          (automaticTerminalInitialBody C F)
          (lowerChildIndex bad.selectedStep) <=
        (bad.rho : ENNReal) ^ (-eta X.stage) := by
  dsimp only
  have href := bad.refinedScales_refinesAt C X gap_nonneg delta_pos
  rw [nonempty_oneStepNormalizedTerminalExponentBound_iff]
  rw [theta_lowerChild_eq href]
  simp

/-- The corresponding upper-child package is exactly the literal estimate at
the old upper endpoint. -/
theorem upperChild_automaticBound_nonempty_iff_literalPower
    (gap_nonneg : 0 <= gapEpsilon) (delta_pos : 0 < delta)
    (X : HierarchyStoppingState delta N gapEpsilon eta)
    (bad : SelectedActualBadSplit C X)
    (hfine : fine.refinement.refined.Nonempty) :
    let F := refinedExactFamily C gap_nonneg delta_pos X bad hfine
    let S := bad.refinedScales C X gap_nonneg delta_pos
    Nonempty (OneStepNormalizedTerminalExponentBound C F
      (automaticTerminalInitialBody C F) S eta (X.stage + 1)
      (upperChildIndex bad.selectedStep)) <->
      canonicalOneStepNormalizedTerminalAt C F
          (automaticTerminalInitialBody C F)
          (upperChildIndex bad.selectedStep) <=
        (X.scales.theta bad.selectedStep : ENNReal) ^ (-eta X.stage) := by
  dsimp only
  have href := bad.refinedScales_refinesAt C X gap_nonneg delta_pos
  rw [nonempty_oneStepNormalizedTerminalExponentBound_iff]
  rw [theta_upperChild_eq href]
  simp

/-- A lower-child automatic-body bound forces a concrete product-cardinality
budget at the inserted radius. -/
theorem lowerChild_activeCardProduct_le_of_automaticBound
    (gap_nonneg : 0 <= gapEpsilon) (delta_pos : 0 < delta)
    (X : HierarchyStoppingState delta N gapEpsilon eta)
    (bad : SelectedActualBadSplit C X)
    (hfine : fine.refinement.refined.Nonempty)
    (bound :
      let F := refinedExactFamily C gap_nonneg delta_pos X bad hfine
      let S := bad.refinedScales C X gap_nonneg delta_pos
      OneStepNormalizedTerminalExponentBound C F
        (automaticTerminalInitialBody C F) S eta (X.stage + 1)
        (lowerChildIndex bad.selectedStep)) :
    let F := refinedExactFamily C gap_nonneg delta_pos X bad hfine
    (((F.chain (lowerChildIndex bad.selectedStep)).intervalCover C 0
          (by omega)).activeFine.card : ENNReal) *
        (canonicalTerminalActiveCardAt C F
          (lowerChildIndex bad.selectedStep) : ENNReal) <=
      (bad.rho : ENNReal) ^ (-eta X.stage) := by
  dsimp only at bound ⊢
  have h := activeCardProduct_le_requiredPower_of_automaticBound C
    (refinedExactFamily C gap_nonneg delta_pos X bad hfine) delta_pos
    (bad.refinedScales C X gap_nonneg delta_pos) eta (X.stage + 1)
    (lowerChildIndex bad.selectedStep) bound
  have href := bad.refinedScales_refinesAt C X gap_nonneg delta_pos
  rw [theta_lowerChild_eq href] at h
  simpa using h

/-- Likewise, an upper-child automatic-body bound forces the corresponding
product-cardinality budget at the old upper endpoint. -/
theorem upperChild_activeCardProduct_le_of_automaticBound
    (gap_nonneg : 0 <= gapEpsilon) (delta_pos : 0 < delta)
    (X : HierarchyStoppingState delta N gapEpsilon eta)
    (bad : SelectedActualBadSplit C X)
    (hfine : fine.refinement.refined.Nonempty)
    (bound :
      let F := refinedExactFamily C gap_nonneg delta_pos X bad hfine
      let S := bad.refinedScales C X gap_nonneg delta_pos
      OneStepNormalizedTerminalExponentBound C F
        (automaticTerminalInitialBody C F) S eta (X.stage + 1)
        (upperChildIndex bad.selectedStep)) :
    let F := refinedExactFamily C gap_nonneg delta_pos X bad hfine
    (((F.chain (upperChildIndex bad.selectedStep)).intervalCover C 0
          (by omega)).activeFine.card : ENNReal) *
        (canonicalTerminalActiveCardAt C F
          (upperChildIndex bad.selectedStep) : ENNReal) <=
      (X.scales.theta bad.selectedStep : ENNReal) ^ (-eta X.stage) := by
  dsimp only at bound ⊢
  have h := activeCardProduct_le_requiredPower_of_automaticBound C
    (refinedExactFamily C gap_nonneg delta_pos X bad hfine) delta_pos
    (bad.refinedScales C X gap_nonneg delta_pos) eta (X.stage + 1)
    (upperChildIndex bad.selectedStep) bound
  have href := bad.refinedScales_refinesAt C X gap_nonneg delta_pos
  rw [theta_upperChild_eq href] at h
  simpa using h

#print axioms nonempty_oneStepNormalizedTerminalExponentBound_iff
#print axioms terminalCard_mul_canonicalTubeVolume_le_familyVolume
#print axioms terminalCard_le_automaticTerminal_normalizedVolume
#print axioms activeCardProduct_le_automatic_normalizedTerminal
#print axioms activeCardProduct_le_requiredPower_of_automaticBound
#print axioms refinedAutomaticTerminal_top_le_one
#print axioms lowerChild_automaticBound_nonempty_iff_literalPower
#print axioms upperChild_automaticBound_nonempty_iff_literalPower
#print axioms lowerChild_activeCardProduct_le_of_automaticBound
#print axioms upperChild_activeCardProduct_le_of_automaticBound

end
end FamilyStickyScaleChainNormalizedTerminalObstructionV2
