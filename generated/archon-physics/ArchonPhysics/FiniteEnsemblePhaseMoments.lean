import ArchonPhysics.CanonicalRandomPhaseMoments

/-!
# Finite joint Haar law for ensemble phases

This module connects the finite restriction of any verified
`IIDMassPhaseEnsemble` to the normalized product Haar law used by
`RandomPhaseMoments`.  Independence and the one-coordinate `HasLaw` fields
first identify the joint law as an `infinitePi`; because the site type is
finite, this is the ordinary finite product measure, which is exactly the
normalized Haar `volume` on `UnitAddTorus`.

No Gaussian pairing rule is used: the resulting multivariate expectation is
the exact Haar charge-balance selector, including repeated indices.
-/

namespace ArchonPhysics.FiniteEnsemblePhaseMoments

open MeasureTheory ProbabilityTheory
open UnitAddTorus
open ArchonPhysics
open ArchonPhysics.CanonicalRandomPhaseMoments
open ArchonPhysics.RandomPhaseMoments

noncomputable section

/- Use the same normalized Haar coordinate measure as the multivariate
Fourier API in `RandomPhaseMoments`. -/
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-- The finite product of the ensemble's one-coordinate phase law is the
normalized product Haar law used by `RandomPhaseMoments`. -/
theorem finitePhaseProductLaw_eq_finitePhaseHaarLaw
    {N : Nat} [NeZero N] :
    Measure.infinitePi
        (fun _ : Lattice.Site N ↦ RandomEnsemble.phaseCoordinateLaw) =
      finitePhaseHaarLaw (Lattice.Site N) := by
  rw [show (fun _ : Lattice.Site N ↦ RandomEnsemble.phaseCoordinateLaw) =
      (fun _ : Lattice.Site N ↦ AddCircle.haarAddCircle) by
    funext i
    exact phaseCoordinateLaw_eq_haar]
  rw [Measure.infinitePi_eq_pi]
  have hVolumeHaar :
      (volume : Measure UnitAddCircle) = AddCircle.haarAddCircle := rfl
  simpa [finitePhaseHaarLaw, hVolumeHaar] using
    (volume_pi :
      (volume : Measure (Lattice.Site N → UnitAddCircle)) =
        Measure.pi (fun _ : Lattice.Site N ↦
          (volume : Measure UnitAddCircle))).symm

/-- The full finite phase restriction of any verified ensemble has exactly
the normalized product Haar law. -/
theorem restrictPhase_hasLaw_finitePhaseHaarLaw
    {Omega : Type*} [MeasurableSpace Omega]
    (ensemble : IIDMassPhaseEnsemble Omega) {N : Nat} [NeZero N] :
    HasLaw (ensemble.restrictPhase (N := N))
      (finitePhaseHaarLaw (Lattice.Site N)) ensemble.probability := by
  have hJoint :
      HasLaw (ensemble.restrictPhase (N := N))
        (Measure.infinitePi
          (fun _ : Lattice.Site N ↦ RandomEnsemble.phaseCoordinateLaw))
        ensemble.probability :=
    ensemble.restrictPhase_iIndep.hasLaw_infinitePi
      ensemble.restrictPhase_hasLaw
      ensemble.measurable_restrictPhase.aemeasurable
  rw [finitePhaseProductLaw_eq_finitePhaseHaarLaw] at hJoint
  exact hJoint

/-- Exact multivariate charge balance for the actual finite phase block of
any verified ensemble. -/
theorem restrictPhase_mFourier_expectation
    {Omega : Type*} [MeasurableSpace Omega]
    (ensemble : IIDMassPhaseEnsemble Omega) {N : Nat} [NeZero N]
    (charge : Lattice.Site N → Int) :
    (∫ omega, mFourier charge (ensemble.restrictPhase omega)
      ∂ensemble.probability) =
      if charge = 0 then 1 else 0 := by
  calc
    (∫ omega, mFourier charge (ensemble.restrictPhase omega)
        ∂ensemble.probability) =
        ∫ phase, mFourier charge phase
          ∂finitePhaseHaarLaw (Lattice.Site N) := by
      simpa [Function.comp_def] using
        (restrictPhase_hasLaw_finitePhaseHaarLaw ensemble
          (N := N)).integral_comp
            (mFourier charge).continuous.aestronglyMeasurable
    _ = if charge = 0 then 1 else 0 :=
      integral_mFourier_eq_ite charge

end

end ArchonPhysics.FiniteEnsemblePhaseMoments
