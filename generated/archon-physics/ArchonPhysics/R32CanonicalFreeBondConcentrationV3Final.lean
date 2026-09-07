import ArchonPhysics.R32FrozenBondCoefficientBoundV2
import ArchonPhysics.R32HaarScalarTailCleanV4
import ArchonPhysics.R32CanonicalProductTailTransferV2
import ArchonPhysics.R32SupervolumeConcentrationAsymptoticV3
import ArchonPhysics.RandomMassPhaseInitialData
import ArchonPhysics.UniformRandomMassHarmonicSpectrumBound

/-!
# Canonical free-bond concentration V2: measurable probability skeleton

This is the corrected-import replacement for the old concentration module.
It contains only the parts which are independent of a choice of ordered
eigenvector signs: the ordered finite phase block, its exact Haar law, the
rescaled kinetic time net, the explicit bad budget, and the exact
circle-angle identification interface.

The mass-dependent field itself is supplied in the signed-eigenframe module.
That separation is essential: the raw Mathlib `eigenvectorBasis` orientation
used by `harmonicNormalizedEdgeFrame` has no established Borel dependence on
the mass realization, whereas the project's first-positive-pivot signed
ordered eigenframe is globally measurable.
-/

namespace ArchonPhysics.R32CanonicalFreeBondConcentrationV3Final

open ArchonPhysics
open ArchonPhysics.CanonicalRandomPhaseMoments
open ArchonPhysics.FiniteEnsemblePhaseMoments
open ArchonPhysics.R32HaarScalarTailCleanV4
open ArchonPhysics.R32SupervolumeConcentrationAsymptotic
open ArchonPhysics.RandomMassPhaseInitialData
open ArchonPhysics.RandomPhaseMoments
open MeasureTheory ProbabilityTheory
open Filter Set Topology
open scoped ENNReal ProbabilityTheory

noncomputable section

local instance : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩

local instance : Measure.IsAddHaarMeasure
    (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-! ## Exact ordered finite Haar block -/

/-- Restrict the complete iid phase sequence to the first `N` coordinates,
relabeled by the ordered harmonic-mode index. -/
def orderedPhaseBlockFromSequence {N : Nat} [NeZero N]
    (phase : RandomEnsemble.PhaseSequence) :
    HarmonicNormalizedEdgeFrame.HarmonicOrderedModeIndex N → UnitAddCircle :=
  fun mode ↦ phase (orderedModeIndexEquivFin N mode).val

theorem measurable_orderedPhaseBlockFromSequence
    {N : Nat} [NeZero N] :
    Measurable (orderedPhaseBlockFromSequence (N := N)) := by
  exact measurable_pi_lambda _ fun mode ↦
    measurable_pi_apply (orderedModeIndexEquivFin N mode).val

/-- The ordered restriction has exactly the finite product Haar law. -/
theorem orderedPhaseBlockFromSequence_hasLaw
    {N : Nat} [NeZero N] :
    HasLaw (orderedPhaseBlockFromSequence (N := N))
      (finitePhaseHaarLaw
        (HarmonicNormalizedEdgeFrame.HarmonicOrderedModeIndex N))
      RandomEnsemble.phaseSequenceLaw := by
  have hinjective : Function.Injective
      (fun mode : HarmonicNormalizedEdgeFrame.HarmonicOrderedModeIndex N ↦
        (orderedModeIndexEquivFin N mode).val) :=
    Fin.val_injective.comp (orderedModeIndexEquivFin N).injective
  have hindep : iIndepFun
      (fun mode : HarmonicNormalizedEdgeFrame.HarmonicOrderedModeIndex N ↦
        fun phase : RandomEnsemble.PhaseSequence ↦
          phase (orderedModeIndexEquivFin N mode).val)
      RandomEnsemble.phaseSequenceLaw := by
    unfold RandomEnsemble.phaseSequenceLaw
    exact (iIndepFun_infinitePi
      (fun _ : Nat ↦ measurable_id)).precomp hinjective
  have hcoord :
      ∀ mode : HarmonicNormalizedEdgeFrame.HarmonicOrderedModeIndex N,
      HasLaw
        (fun phase : RandomEnsemble.PhaseSequence ↦
          phase (orderedModeIndexEquivFin N mode).val)
        RandomEnsemble.phaseCoordinateLaw
        RandomEnsemble.phaseSequenceLaw := by
    intro mode
    unfold RandomEnsemble.phaseSequenceLaw
    exact (measurePreserving_eval_infinitePi
      (fun _ : Nat ↦ RandomEnsemble.phaseCoordinateLaw)
      (orderedModeIndexEquivFin N mode).val).hasLaw
  have hjoint :
      HasLaw (orderedPhaseBlockFromSequence (N := N))
        (Measure.infinitePi
          (fun _ : HarmonicNormalizedEdgeFrame.HarmonicOrderedModeIndex N ↦
            RandomEnsemble.phaseCoordinateLaw))
        RandomEnsemble.phaseSequenceLaw := by
    exact hindep.hasLaw_infinitePi hcoord
      measurable_orderedPhaseBlockFromSequence.aemeasurable
  have hproduct :
      Measure.infinitePi
          (fun _ : HarmonicNormalizedEdgeFrame.HarmonicOrderedModeIndex N ↦
            RandomEnsemble.phaseCoordinateLaw) =
        finitePhaseHaarLaw
          (HarmonicNormalizedEdgeFrame.HarmonicOrderedModeIndex N) := by
    rw [show
      (fun _ : HarmonicNormalizedEdgeFrame.HarmonicOrderedModeIndex N ↦
        RandomEnsemble.phaseCoordinateLaw) =
      (fun _ : HarmonicNormalizedEdgeFrame.HarmonicOrderedModeIndex N ↦
        AddCircle.haarAddCircle) by
        funext mode
        exact phaseCoordinateLaw_eq_haar]
    rw [Measure.infinitePi_eq_pi]
    have hVolumeHaar :
        (volume : Measure UnitAddCircle) = AddCircle.haarAddCircle := rfl
    simpa [finitePhaseHaarLaw, hVolumeHaar] using
      (volume_pi :
        (volume : Measure
          (HarmonicNormalizedEdgeFrame.HarmonicOrderedModeIndex N →
            UnitAddCircle)) =
          Measure.pi
            (fun _ : HarmonicNormalizedEdgeFrame.HarmonicOrderedModeIndex N ↦
              (volume : Measure UnitAddCircle))).symm
  rw [hproduct] at hjoint
  exact hjoint

/-! ## Exact Haar-angle identification interface -/

/-- A real representative is valid when it turns the shifted first Fourier
character into the literal cosine with angular frequency measured in
radians.  V2 supplies a concrete measurable inhabitant in a separate module. -/
def IsHaarAngleRepresentative (angle : UnitAddCircle → Real) : Prop :=
  ∀ (frequency time : Real) (phase : UnitAddCircle),
    fixedTimeHaarCarrier frequency time phase =
      Real.cos (frequency * time + angle phase)

/-! ## Corrected rescaled kinetic time grid -/

/-- Fixed interpolation scale. -/
def freeTimeGridScale : Real := 16

def freeTimeGridCard (T g : Real) : Nat :=
  kineticTimeGridCard
    (T / freeTimeGridScale ^ 2)
    (g / freeTimeGridScale)

def freeTimeGrid (T g : Real) : Fin (freeTimeGridCard T g) → Real :=
  kineticTimeGrid
    (T / freeTimeGridScale ^ 2)
    (g / freeTimeGridScale)

theorem freeTimeGrid_isTimeNet
    (T g : Real) (hT : 0 ≤ T) (hg : 0 < g) :
    IsTimeNet (T / g ^ 2)
      ((g / freeTimeGridScale) ^ 4)
      (freeTimeGrid T g) := by
  have hscale : 0 < freeTimeGridScale := by
    norm_num [freeTimeGridScale]
  have hbase := kineticTimeGrid_isTimeNet
    (T / freeTimeGridScale ^ 2)
    (g / freeTimeGridScale)
    (div_nonneg hT (sq_nonneg freeTimeGridScale)) (div_pos hg hscale)
  change IsTimeNet (T / g ^ 2)
    ((g / freeTimeGridScale) ^ 4)
    (kineticTimeGrid
      (T / freeTimeGridScale ^ 2)
      (g / freeTimeGridScale))
  have hhorizon :
      T / g ^ 2 =
        (T / freeTimeGridScale ^ 2) /
          (g / freeTimeGridScale) ^ 2 := by
    field_simp [ne_of_gt hg, ne_of_gt hscale]
  rw [hhorizon]
  exact hbase

/-- Explicit union-bound budget for `N` bonds and the rescaled time grid. -/
def freeGridBadBudget (T g : Real) (N : Nat) : Real :=
  2 * (N : Real) * (freeTimeGridCard T g : Real) *
    Real.exp (-(N : Real) * g ^ 8 / 96)

#print axioms orderedPhaseBlockFromSequence_hasLaw
#print axioms freeTimeGrid_isTimeNet

end

end ArchonPhysics.R32CanonicalFreeBondConcentrationV3Final
