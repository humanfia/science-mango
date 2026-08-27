import ArchonPhysics.ActualSixSiteIIDGoodBlockPositiveDensity
import ArchonPhysics.CanonicalScalarIDSBlockApproximation
import ArchonPhysics.FiniteMeasureClosedSmallBallLowerWeakLimit

/-!
# From positive-density six-site blocks to a global per-site lower bound

This module isolates the exact deterministic input still needed after the
six-site iid block-counting theorem.  A `GoodSixBlockAdditiveContribution`
does not assume the desired per-site estimate.  It says instead that every
good disjoint six-site window supplies one local contribution of size
`coefficient * delta` to a raw globally coupled mismatch measure, and that
these window contributions add.  The strong law then turns that local input
into an almost-sure thermodynamic `c * delta` lower bound.

The module also records a true shifted two-block spectral-count gluing
estimate for the coupled periodic weighted cycle.  Its defect is four per
cut.  This controls scalar IDS counts, but by itself does not transport the
three selected projectors or their collision weight; that is precisely why
the additive-contribution hypothesis remains separate.
-/

namespace ArchonPhysics.ActualSixSiteGoodBlockGlobalLowerBridge

open ArchonPhysics
open ArchonPhysics.ActualSixSiteIIDGoodBlockPositiveDensity
open ArchonPhysics.ActualSixSiteFullIIDPositiveWeightedNearResonancePatch
open ArchonPhysics.CanonicalScalarIDSCenterLimit
open ArchonPhysics.CanonicalScalarIDSBlockApproximation
open ArchonPhysics.FiniteWindowIIDStrongLaw
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.RepeatedParentChildMismatchSmallBall
open ArchonPhysics.RandomMassAcousticCountingComparison
open ArchonPhysics.PeriodicWeightedCycleBlockGluing
open ArchonPhysics.RandomEnsemble
open Filter MeasureTheory Set Topology

noncomputable section

/-! ## Genuine shifted periodic spectral-count gluing -/

theorem leftWeights_shiftedInverseMassVector
    (shift n m : Nat) (omega : RandomEnsemble.SampleSpace) :
    leftWeights (shiftedInverseMassVector shift (n + m) omega) =
      shiftedInverseMassVector shift n omega := by
  funext i
  rfl

theorem rightWeights_shiftedInverseMassVector
    (shift n m : Nat) (omega : RandomEnsemble.SampleSpace) :
    rightWeights (shiftedInverseMassVector shift (n + m) omega) =
      shiftedInverseMassVector (shift + n) m omega := by
  funext i
  simp [rightWeights, shiftedInverseMassVector, Nat.add_assoc]

/-- Joining two adjacent shifted iid mass blocks into the actual coupled
periodic weighted cycle loses at most four threshold-count units. -/
theorem shiftedPeriodicThresholdCount_gluing_lower
    {shift n m : Nat} [NeZero n] [NeZero m] [NeZero (n + m)]
    (E : Real) (omega : RandomEnsemble.SampleSpace) :
    shiftedPeriodicThresholdCount shift n E omega +
        shiftedPeriodicThresholdCount (shift + n) m E omega <=
      shiftedPeriodicThresholdCount shift (n + m) E omega + 4 := by
  have h := splitFinWeightedCycle_thresholdCount_defect_le_four
    (shiftedInverseMassVector shift (n + m) omega) E
  rw [splitFinWeightedCycle_thresholdCount_eq_fin,
    leftWeights_shiftedInverseMassVector,
    rightWeights_shiftedInverseMassVector] at h
  change (orderedEigenvalueThresholdCount
      (finWeightedCycleHermitian
        (shiftedInverseMassVector shift n omega)) E : Real) +
    (orderedEigenvalueThresholdCount
      (finWeightedCycleHermitian
        (shiftedInverseMassVector (shift + n) m omega)) E : Real) <=
    (orderedEigenvalueThresholdCount
      (finWeightedCycleHermitian
        (shiftedInverseMassVector shift (n + m) omega)) E : Real) + 4
  exact_mod_cast h.2

/-! ## Additive local contributions imply a global per-site lower bound -/

/-- Real count of good disjoint length-six windows among the first
`blockCount` windows.  Each summand is exactly zero or one. -/
def fullSixPatchBlockCountReal (patch : Set SixMassVector)
    (blockCount : Nat) (omega : RandomEnsemble.SampleSpace) : Real :=
  ∑ k ∈ Finset.range blockCount,
    windowObservable canonicalIIDMassPhaseEnsemble 6 0
      (fullSixPatchIndicator patch) k omega

theorem fullSixPatchBlockDensity_eq_count_div
    (patch : Set SixMassVector) (blockCount : Nat)
    (omega : RandomEnsemble.SampleSpace) :
    fullSixPatchBlockDensity patch blockCount omega =
      fullSixPatchBlockCountReal patch blockCount omega /
        (blockCount : Real) := by
  rfl

/-- The missing model-facing localization input.

`rawMismatch blockCount omega` is understood to be the unnormalised global
mismatch measure of the genuinely coupled periodic chain with
`6 * blockCount` sites.  The predicate asks for a sum of one lower
contribution per good disjoint window; it neither divides by volume nor
assumes the final per-site conclusion. -/
def GoodSixBlockAdditiveContribution
    (patch : Set SixMassVector)
    (rawMismatch : Nat -> RandomEnsemble.SampleSpace -> FiniteMeasure Real)
    (coefficient deltaMax : Real) : Prop :=
  ∀ omega blockCount delta,
    0 < blockCount -> 0 < delta -> delta <= deltaMax ->
    coefficient * delta *
        fullSixPatchBlockCountReal patch blockCount omega <=
      ((rawMismatch blockCount omega : Measure Real)
        (absoluteMismatchSublevel delta)).toReal

/-- Positive-density good windows plus an additive local contribution give
an explicit almost-sure thermodynamic small-ball lower bound.  The factor
`12 = 6 * 2` is the six sites per block and the harmless half-probability
margin used in the eventual strong-law estimate. -/
theorem exists_eventual_perSite_linearLower_of_goodSixBlockContribution
    {patch : Set SixMassVector} (hpatch : MeasurableSet patch)
    (hpatchPos : 0 < finiteMassLaw 6 patch)
    (rawMismatch : Nat -> RandomEnsemble.SampleSpace -> FiniteMeasure Real)
    {coefficient deltaMax : Real}
    (hcoefficient : 0 < coefficient) (_hdeltaMax : 0 < deltaMax)
    (hcontribution : GoodSixBlockAdditiveContribution patch rawMismatch
      coefficient deltaMax) :
    ∃ constant : Real, 0 < constant ∧
      ∀ᵐ omega ∂ RandomEnsemble.canonicalLaw,
        ∀ᶠ blockCount : Nat in atTop,
          ∀ delta : Real, 0 < delta -> delta <= deltaMax ->
            constant * delta <=
              ((rawMismatch blockCount omega : Measure Real)
                (absoluteMismatchSublevel delta)).toReal /
                  (6 * (blockCount : Real)) := by
  let probability : Real := (finiteMassLaw 6).real patch
  let constant : Real := coefficient * probability / 12
  have hprobability : 0 < probability := by
    dsimp [probability]
    rw [Measure.real]
    exact ENNReal.toReal_pos hpatchPos.ne' (measure_ne_top _ _)
  have hconstant : 0 < constant := by
    dsimp [constant]
    positivity
  refine ⟨constant, hconstant, ?_⟩
  filter_upwards
      [fullSixPatchBlockDensity_eventually_half_probability_ae
        hpatch hpatchPos] with omega homega
  filter_upwards [homega, eventually_gt_atTop (0 : Nat)] with
      blockCount hdensity hblockCount
  intro delta hdelta hdeltaMax'
  have hblockCountReal : 0 < (blockCount : Real) := by
    exact_mod_cast hblockCount
  have hcountLower :
      probability / 2 * (blockCount : Real) <
        fullSixPatchBlockCountReal patch blockCount omega := by
    rw [fullSixPatchBlockDensity_eq_count_div] at hdensity
    exact (lt_div_iff₀ hblockCountReal).mp hdensity
  have hraw := hcontribution omega blockCount delta hblockCount
    hdelta hdeltaMax'
  apply (le_div_iff₀ (mul_pos (by norm_num : (0 : Real) < 6)
    hblockCountReal)).2
  calc
    constant * delta * (6 * (blockCount : Real)) =
        coefficient * delta *
          (probability / 2 * (blockCount : Real)) := by
      dsimp [constant]
      ring
    _ <= coefficient * delta *
          fullSixPatchBlockCountReal patch blockCount omega := by
      exact mul_le_mul_of_nonneg_left (le_of_lt hcountLower)
        (mul_nonneg hcoefficient.le hdelta.le)
    _ <= ((rawMismatch blockCount omega : Measure Real)
          (absoluteMismatchSublevel delta)).toReal := hraw

end

end ArchonPhysics.ActualSixSiteGoodBlockGlobalLowerBridge
