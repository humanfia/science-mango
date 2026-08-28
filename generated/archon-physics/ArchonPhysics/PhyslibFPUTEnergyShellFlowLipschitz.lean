import ArchonPhysics.CanonicalRandomMassGlobalFlow

/-!
# Gronwall stability of the common FPUT energy-shell flow

`UniformRandomMassEnergyShell` already chooses one cutoff radius before the
mass realization and initial state are selected.  The corresponding canonical
flow agrees, on every admissible energy-sublevel initial point, with the
genuine untruncated reduced FPUT Hamiltonian trajectory.

This file records the complementary stability fact.  The smooth cutoff vector
field has compact support, hence Mathlib supplies one global Lipschitz
constant `K`.  The fixed-time canonical flow is therefore Lipschitz in its
full parameter--phase initial point with the explicit two-sided Gronwall
factor `exp (K * |t|)`.

No random-phase, kinetic, or thermalization assertion is used here.
-/

namespace ArchonPhysics.PhyslibFPUTEnergyShellFlowLipschitz

open ArchonPhysics
open ArchonPhysics.CanonicalGlobalMeasurableFlow
open ArchonPhysics.CanonicalRandomMassGlobalFlow
open ArchonPhysics.CoerciveHamiltonianGlobalExistence
open ArchonPhysics.ParametricLocalHamiltonianFlow

noncomputable section

variable {N : Nat} [NeZero N]

/-- The cutoff vector field attached to the common random-mass energy shell.
This is merely a name for the vector field underlying
`canonicalRandomMassGlobalFlow`. -/
def energyShellCutoffVectorField
    (shell : UniformRandomMassEnergyShell N) :
    ParametricPhaseSpace N → ParametricPhaseSpace N :=
  normCutoffVectorField parameterizedHamiltonVectorField
    shell.cutoffRadius shell.cutoffRadius_nonneg

/-- Compact support and `C¹` regularity supply a genuine global Lipschitz
constant for the common cutoff vector field. -/
theorem exists_energyShellCutoffVectorField_lipschitzWith
    (shell : UniformRandomMassEnergyShell N) :
    ∃ K : NNReal, LipschitzWith K (energyShellCutoffVectorField shell) := by
  exact ContDiff.lipschitzWith_of_hasCompactSupport
    (normCutoffVectorField_hasCompactSupport
      (parameterizedHamiltonVectorField (N := N))
      shell.cutoffRadius shell.cutoffRadius_nonneg)
    (normCutoffVectorField_contDiff
      (parameterizedHamiltonVectorField_contDiff (N := N))
      shell.cutoffRadius shell.cutoffRadius_nonneg)
    one_ne_zero

/-- A fixed global Lipschitz rate for the common cutoff vector field. -/
def energyShellCutoffLipschitzRate
    (shell : UniformRandomMassEnergyShell N) : NNReal :=
  Classical.choose (exists_energyShellCutoffVectorField_lipschitzWith shell)

theorem energyShellCutoffVectorField_lipschitzWith
    (shell : UniformRandomMassEnergyShell N) :
    LipschitzWith (energyShellCutoffLipschitzRate shell)
      (energyShellCutoffVectorField shell) :=
  Classical.choose_spec
    (exists_energyShellCutoffVectorField_lipschitzWith shell)

/-- The explicit two-sided Gronwall amplification at physical time `t`. -/
def energyShellFlowAmplification
    (shell : UniformRandomMassEnergyShell N) (t : Real) : NNReal :=
  ⟨Real.exp ((energyShellCutoffLipschitzRate shell : Real) * |t|),
    (Real.exp_pos _).le⟩

/-- The full common parameter--phase FPUT flow is Lipschitz in its initial
point at every fixed time.  On admissible energy-shell points this very same
map is the genuine untruncated Hamiltonian flow by
`canonicalRandomMassGlobalFlow_matches_reduced`. -/
theorem canonicalRandomMassGlobalFlow_lipschitz_fixedTime
    (shell : UniformRandomMassEnergyShell N) (t : Real) :
    LipschitzWith (energyShellFlowAmplification shell t)
      (fun x : ParametricPhaseSpace N ↦
        canonicalRandomMassGlobalFlow shell (x, t)) := by
  let truncated : ParametricPhaseSpace N → ParametricPhaseSpace N :=
    energyShellCutoffVectorField shell
  have hglobal : ∀ x : ParametricPhaseSpace N,
      ∃ gamma : Real → ParametricPhaseSpace N,
        gamma 0 = x ∧
          ∀ s : Real, HasDerivAt gamma (truncated (gamma s)) s :=
    fun x ↦ exists_global_integralCurve_of_contDiff_hasCompactSupport
      (normCutoffVectorField_contDiff
        (parameterizedHamiltonVectorField_contDiff (N := N))
        shell.cutoffRadius shell.cutoffRadius_nonneg)
      (normCutoffVectorField_hasCompactSupport
        (parameterizedHamiltonVectorField (N := N))
        shell.cutoffRadius shell.cutoffRadius_nonneg) x
  have hflow := canonicalGlobalCurve_lipschitz_fixedTime
    hglobal (energyShellCutoffVectorField_lipschitzWith shell) t
  simpa only [energyShellFlowAmplification, canonicalRandomMassGlobalFlow,
    canonicalCutoffFlow, canonicalCompactSupportFlow, truncated,
    energyShellCutoffVectorField] using hflow

end

end ArchonPhysics.PhyslibFPUTEnergyShellFlowLipschitz
