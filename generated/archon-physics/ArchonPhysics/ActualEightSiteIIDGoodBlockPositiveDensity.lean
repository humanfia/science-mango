import ArchonPhysics.ActualEightSiteFullIIDPositiveWeightedNearResonancePatch
import ArchonPhysics.FiniteWindowIIDStrongLaw

/-!
# Positive density of genuine iid eight-site good blocks

The full-eight physical near-resonance patch is an event of strictly positive
iid probability.  Applying the finite-window strong law to disjoint
length-eight windows of the canonical mass sequence proves that such blocks
occur with an almost-sure positive asymptotic density.

This is a statement about local windows of the microscopic mass sample.  It
does not yet transport their selected local projectors or collision weights
to the globally coupled periodic operator.
-/

namespace ArchonPhysics.ActualEightSiteIIDGoodBlockPositiveDensity

open ArchonPhysics
open ArchonPhysics.ActualEightSiteExactDecayIVTBridge
open ArchonPhysics.ActualEightSiteFullIIDPositiveWeightedNearResonancePatch
open ArchonPhysics.FiniteWindowIIDStrongLaw
open ArchonPhysics.RandomEnsemble
open Filter MeasureTheory Set Topology

noncomputable section

/-- Real-valued Bernoulli indicator of an eight-mass patch. -/
def fullEightPatchIndicator
    (patch : Set EightMassVector) : EightMassVector → Real :=
  patch.indicator (fun _ ↦ 1)

theorem measurable_fullEightPatchIndicator
    {patch : Set EightMassVector} (hpatch : MeasurableSet patch) :
    Measurable (fullEightPatchIndicator patch) := by
  exact Measurable.indicator measurable_const hpatch

theorem norm_fullEightPatchIndicator_le_one
    (patch : Set EightMassVector) (x : EightMassVector) :
    ‖fullEightPatchIndicator patch x‖ ≤ 1 := by
  by_cases hx : x ∈ patch <;>
    simp [fullEightPatchIndicator, hx]

/-- Fraction of the first `blockCount` disjoint canonical eight-mass windows
which lie in `patch`. -/
def fullEightPatchBlockDensity (patch : Set EightMassVector)
    (blockCount : Nat) (omega : RandomEnsemble.SampleSpace) : Real :=
  (∑ k ∈ Finset.range blockCount,
      windowObservable canonicalIIDMassPhaseEnsemble 8 0
        (fullEightPatchIndicator patch) k omega) /
    (blockCount : Real)

/-- Almost-sure convergence of the good-block density to the exact
eight-coordinate product probability. -/
theorem fullEightPatchBlockDensity_tendsto_ae
    {patch : Set EightMassVector} (hpatch : MeasurableSet patch) :
    ∀ᵐ omega ∂ RandomEnsemble.canonicalLaw,
      Tendsto (fun blockCount : Nat ↦
        fullEightPatchBlockDensity patch blockCount omega) atTop
        (𝓝 ((finiteMassLaw 8).real patch)) := by
  have hstrong :=
    fixedOffset_windowObservable_strongLaw_ae
      canonicalIIDMassPhaseEnsemble 8 0
      (fullEightPatchIndicator patch)
      (measurable_fullEightPatchIndicator hpatch) 1
      (fun x _hx ↦ norm_fullEightPatchIndicator_le_one patch x)
  have hmean :
      (∫ omega,
          windowObservable canonicalIIDMassPhaseEnsemble 8 0
            (fullEightPatchIndicator patch) 0 omega
          ∂ canonicalIIDMassPhaseEnsemble.probability) =
        (finiteMassLaw 8).real patch := by
    calc
      (∫ omega,
          windowObservable canonicalIIDMassPhaseEnsemble 8 0
            (fullEightPatchIndicator patch) 0 omega
          ∂ canonicalIIDMassPhaseEnsemble.probability) =
          ∫ x, fullEightPatchIndicator patch x ∂ finiteMassLaw 8 := by
        exact (massWindow_hasLaw canonicalIIDMassPhaseEnsemble 8 0 0).integral_comp
          (measurable_fullEightPatchIndicator hpatch).aestronglyMeasurable
      _ = (finiteMassLaw 8).real patch := by
        exact integral_indicator_one hpatch
  filter_upwards [hstrong] with omega homega
  rw [hmean] at homega
  simpa [fullEightPatchBlockDensity] using homega

/-- A positive-probability eight-mass patch eventually has empirical density
strictly larger than half its probability on almost every iid sample. -/
theorem fullEightPatchBlockDensity_eventually_half_probability_ae
    {patch : Set EightMassVector} (hpatch : MeasurableSet patch)
    (hpatchPos : 0 < finiteMassLaw 8 patch) :
    ∀ᵐ omega ∂ RandomEnsemble.canonicalLaw,
      ∀ᶠ blockCount : Nat in atTop,
        (finiteMassLaw 8).real patch / 2 <
          fullEightPatchBlockDensity patch blockCount omega := by
  have hprobPos : 0 < (finiteMassLaw 8).real patch := by
    rw [Measure.real]
    exact ENNReal.toReal_pos hpatchPos.ne' (measure_ne_top _ _)
  filter_upwards [fullEightPatchBlockDensity_tendsto_ae hpatch] with omega homega
  exact (tendsto_order.1 homega).1 _ (by linarith)

/-- Consumer-facing positive-density consequence of the exact eight-site
physical decay witness. -/
theorem exists_fullEight_physicalWeightedNearResonancePatch_positiveDensity_ae
    {epsilon : Real} (hepsilon : 0 < epsilon) :
    ∃ patch : Set EightMassVector, ∃ probability : Real,
      IsOpen patch ∧
      probability = (finiteMassLaw 8).real patch ∧
      0 < probability ∧
      patch ⊆ fullEightPhysicalWeightedNearResonanceWithProjectorMinor epsilon ∧
      (∀ᵐ omega ∂ RandomEnsemble.canonicalLaw,
        Tendsto (fun blockCount : Nat ↦
          fullEightPatchBlockDensity patch blockCount omega) atTop
          (𝓝 probability)) ∧
      (∀ᵐ omega ∂ RandomEnsemble.canonicalLaw,
        ∀ᶠ blockCount : Nat in atTop,
          probability / 2 <
            fullEightPatchBlockDensity patch blockCount omega) := by
  obtain ⟨patch, hopen, hpatchPos, hpatchGood⟩ :=
    exists_positive_finiteMassLaw_fullEight_physicalWeightedNearResonancePatch
      hepsilon
  let probability : Real := (finiteMassLaw 8).real patch
  have hprobabilityPos : 0 < probability := by
    dsimp [probability]
    rw [Measure.real]
    exact ENNReal.toReal_pos hpatchPos.ne' (measure_ne_top _ _)
  refine ⟨patch, probability, hopen, rfl, hprobabilityPos, hpatchGood, ?_, ?_⟩
  · simpa [probability] using
      fullEightPatchBlockDensity_tendsto_ae hopen.measurableSet
  · simpa [probability] using
      fullEightPatchBlockDensity_eventually_half_probability_ae
        hopen.measurableSet hpatchPos

end

end ArchonPhysics.ActualEightSiteIIDGoodBlockPositiveDensity
