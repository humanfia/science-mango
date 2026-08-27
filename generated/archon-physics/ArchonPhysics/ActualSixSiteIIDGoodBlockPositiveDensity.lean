import ArchonPhysics.ActualSixSiteFullIIDPositiveWeightedNearResonancePatch
import ArchonPhysics.FiniteWindowIIDStrongLaw
import ArchonPhysics.PeriodicWeightedCycleZeroCutAudit
import ArchonPhysics.RandomMassResultantBridge

/-!
# Positive density of genuine iid six-site good blocks

The full-six physical near-resonance patch is a local event of strictly
positive iid probability.  Sampling that event on disjoint length-six
windows of the actual infinite canonical mass sequence gives iid Bernoulli
observables.  The finite-window strong law therefore makes the empirical
density of good windows converge almost surely to that positive probability.

This closes the block-counting part of a prospective thermodynamic lower
bound without changing the microscopic model.  It deliberately does **not**
claim that a good local six-site window supplies three modes of the globally
coupled periodic operator.  The exact zero-cut route cannot provide that
bridge: every inverse-mass edge of a physical positive-mass chain is strictly
positive, whereas block diagonalization requires two edge weights to vanish.
-/

namespace ArchonPhysics.ActualSixSiteIIDGoodBlockPositiveDensity

open ArchonPhysics
open ArchonPhysics.ActualSixSiteFullIIDPositiveWeightedNearResonancePatch
open ArchonPhysics.FiniteWindowIIDStrongLaw
open ArchonPhysics.GenericSpectrumResultant
open ArchonPhysics.PeriodicWeightedCycleBlockGluing
open ArchonPhysics.RandomEnsemble
open ArchonPhysics.RandomMassResultantBridge
open Filter MeasureTheory Set Topology

noncomputable section

/-- The real-valued Bernoulli indicator of a six-mass patch. -/
def fullSixPatchIndicator (patch : Set SixMassVector) : SixMassVector -> Real :=
  patch.indicator (fun _ => 1)

theorem measurable_fullSixPatchIndicator {patch : Set SixMassVector}
    (hpatch : MeasurableSet patch) :
    Measurable (fullSixPatchIndicator patch) := by
  exact Measurable.indicator measurable_const hpatch

theorem norm_fullSixPatchIndicator_le_one
    (patch : Set SixMassVector) (x : SixMassVector) :
    ‖fullSixPatchIndicator patch x‖ <= 1 := by
  by_cases hx : x ∈ patch <;>
    simp [fullSixPatchIndicator, hx]

/-- Fraction of the first `blockCount` disjoint canonical six-mass windows
which lie in `patch`.  Because the summands are Bernoulli indicators, this is
literally a good-block count divided by `blockCount`. -/
def fullSixPatchBlockDensity (patch : Set SixMassVector)
    (blockCount : Nat) (omega : RandomEnsemble.SampleSpace) : Real :=
  (∑ k ∈ Finset.range blockCount,
      windowObservable canonicalIIDMassPhaseEnsemble 6 0
        (fullSixPatchIndicator patch) k omega) /
    (blockCount : Real)

/-- The iid block strong law identifies the almost-sure limiting density with
the exact finite six-coordinate product probability. -/
theorem fullSixPatchBlockDensity_tendsto_ae
    {patch : Set SixMassVector} (hpatch : MeasurableSet patch) :
    ∀ᵐ omega ∂ RandomEnsemble.canonicalLaw,
      Tendsto (fun blockCount : Nat =>
        fullSixPatchBlockDensity patch blockCount omega) atTop
        (𝓝 ((finiteMassLaw 6).real patch)) := by
  have hstrong :=
    fixedOffset_windowObservable_strongLaw_ae
      canonicalIIDMassPhaseEnsemble 6 0
      (fullSixPatchIndicator patch)
      (measurable_fullSixPatchIndicator hpatch) 1
      (fun x _hx => norm_fullSixPatchIndicator_le_one patch x)
  have hmean :
      (∫ omega,
          windowObservable canonicalIIDMassPhaseEnsemble 6 0
            (fullSixPatchIndicator patch) 0 omega
          ∂ canonicalIIDMassPhaseEnsemble.probability) =
        (finiteMassLaw 6).real patch := by
    calc
      (∫ omega,
          windowObservable canonicalIIDMassPhaseEnsemble 6 0
            (fullSixPatchIndicator patch) 0 omega
          ∂ canonicalIIDMassPhaseEnsemble.probability) =
          ∫ x, fullSixPatchIndicator patch x ∂ finiteMassLaw 6 := by
        exact (massWindow_hasLaw canonicalIIDMassPhaseEnsemble 6 0 0).integral_comp
          (measurable_fullSixPatchIndicator hpatch).aestronglyMeasurable
      _ = (finiteMassLaw 6).real patch := by
        exact integral_indicator_one hpatch
  filter_upwards [hstrong] with omega homega
  rw [hmean] at homega
  simpa [fullSixPatchBlockDensity] using homega

/-- A positive-probability six-mass patch occurs with an eventually positive
empirical density on almost every genuine canonical iid sample. -/
theorem fullSixPatchBlockDensity_eventually_half_probability_ae
    {patch : Set SixMassVector} (hpatch : MeasurableSet patch)
    (hpatchPos : 0 < finiteMassLaw 6 patch) :
    ∀ᵐ omega ∂ RandomEnsemble.canonicalLaw,
      ∀ᶠ blockCount : Nat in atTop,
        (finiteMassLaw 6).real patch / 2 <
          fullSixPatchBlockDensity patch blockCount omega := by
  have hprobPos : 0 < (finiteMassLaw 6).real patch := by
    rw [Measure.real]
    exact ENNReal.toReal_pos hpatchPos.ne' (measure_ne_top _ _)
  filter_upwards [fullSixPatchBlockDensity_tendsto_ae hpatch] with omega homega
  exact (tendsto_order.1 homega).1 _ (by linarith)

/-- Consumer-facing form: every positive mismatch width admits one open
full-six physical weighted near-resonance patch whose disjoint-block density
converges almost surely to a strictly positive number, and is eventually at
least half of that number. -/
theorem exists_fullSix_physicalWeightedNearResonancePatch_positiveDensity_ae
    {epsilon : Real} (hepsilon : 0 < epsilon) :
    ∃ patch : Set SixMassVector, ∃ probability : Real,
      IsOpen patch ∧
      probability = (finiteMassLaw 6).real patch ∧
      0 < probability ∧
      patch ⊆ fullSixPhysicalWeightedNearResonanceWithProjectorMinor epsilon ∧
      (∀ᵐ omega ∂ RandomEnsemble.canonicalLaw,
        Tendsto (fun blockCount : Nat =>
          fullSixPatchBlockDensity patch blockCount omega) atTop
          (𝓝 probability)) ∧
      (∀ᵐ omega ∂ RandomEnsemble.canonicalLaw,
        ∀ᶠ blockCount : Nat in atTop,
          probability / 2 <
            fullSixPatchBlockDensity patch blockCount omega) := by
  obtain ⟨patch, hopen, hpatchPos, hpatchGood⟩ :=
    exists_positive_finiteMassLaw_fullSix_physicalWeightedNearResonancePatch
      hepsilon
  let probability : Real := (finiteMassLaw 6).real patch
  have hprobabilityPos : 0 < probability := by
    dsimp [probability]
    rw [Measure.real]
    exact ENNReal.toReal_pos hpatchPos.ne' (measure_ne_top _ _)
  refine ⟨patch, probability, hopen, rfl, hprobabilityPos, hpatchGood, ?_, ?_⟩
  · simpa [probability] using
      fullSixPatchBlockDensity_tendsto_ae hopen.measurableSet
  · simpa [probability] using
      fullSixPatchBlockDensity_eventually_half_probability_ae
        hopen.measurableSet hpatchPos

/-- Every edge weight of the genuine mass-weighted periodic cycle is
strictly positive. -/
theorem inverseMassCoordinates_pos {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (i : Fin N) :
    0 < inverseMassCoordinates m i := by
  exact inv_pos.mpr (m.mass_pos ((siteEquivFin N).symm i))

/-- Hence no physical positive-mass periodic chain can realize either zero
cut needed by the exact block-diagonal gluing specialization. -/
theorem physical_inverseMassWeights_cannot_zeroCut
    {n m : Nat} [NeZero n] [NeZero m] [NeZero (n + m)]
    (mass : Lattice.PositiveMassConfig (n + m)) :
    inverseMassCoordinates mass (Fin.castAdd m (0 : Fin n)) ≠ 0 ∧
      inverseMassCoordinates mass (Fin.natAdd n (0 : Fin m)) ≠ 0 := by
  exact ⟨(inverseMassCoordinates_pos mass _).ne',
    (inverseMassCoordinates_pos mass _).ne'⟩

end

end ArchonPhysics.ActualSixSiteIIDGoodBlockPositiveDensity
