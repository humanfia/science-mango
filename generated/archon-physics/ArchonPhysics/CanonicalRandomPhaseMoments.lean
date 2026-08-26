import ArchonPhysics.RandomEnsemble
import ArchonPhysics.RandomPhaseMoments

/-!
# Haar-character moments on the canonical random-phase ensemble

This module connects the exact Fourier-character moment rule to the phase law
already used by `IIDMassPhaseEnsemble`.  It proves the one-coordinate adapter
directly through `HasLaw`; finite multivariate charge balance remains available
in `RandomPhaseMoments` for the later diagram expansion.
-/

namespace ArchonPhysics.CanonicalRandomPhaseMoments

open MeasureTheory ProbabilityTheory
open ArchonPhysics

noncomputable section

/-- The phase coordinate law in `RandomEnsemble` is normalized Haar measure. -/
theorem phaseCoordinateLaw_eq_haar :
    RandomEnsemble.phaseCoordinateLaw = AddCircle.haarAddCircle := by
  unfold RandomEnsemble.phaseCoordinateLaw
  simpa using
    (AddCircle.volume_eq_smul_haarAddCircle (T := (1 : Real)))

/-- Exact expectation of one Haar Fourier character. -/
theorem integral_fourier_haar_eq_ite (charge : Int) :
    (∫ phase : UnitAddCircle, fourier charge phase ∂(AddCircle.haarAddCircle)) =
      if charge = 0 then 1 else 0 := by
  have h := congrFun (fourierCoeff_fourier (T := (1 : Real)) charge) 0
  simpa [fourierCoeff, Pi.single_apply, eq_comm] using h

/-- Every phase coordinate of any verified ensemble obeys the exact Haar charge rule. -/
theorem phaseCharacter_expectation {Omega : Type*} [MeasurableSpace Omega]
    (ensemble : IIDMassPhaseEnsemble Omega) (index : Nat) (charge : Int) :
    (∫ omega, fourier charge (ensemble.phase index omega) ∂(ensemble.probability)) =
      if charge = 0 then 1 else 0 := by
  calc
    (∫ omega, fourier charge (ensemble.phase index omega) ∂(ensemble.probability)) =
        ∫ phase, fourier charge phase ∂(RandomEnsemble.phaseCoordinateLaw) := by
      simpa [Function.comp_def] using
        (ensemble.phase_hasLaw index).integral_comp
          (fourier charge).continuous.aestronglyMeasurable
    _ = ∫ phase, fourier charge phase ∂(AddCircle.haarAddCircle) := by
      rw [phaseCoordinateLaw_eq_haar]
    _ = if charge = 0 then 1 else 0 :=
      integral_fourier_haar_eq_ite charge

end

end ArchonPhysics.CanonicalRandomPhaseMoments
