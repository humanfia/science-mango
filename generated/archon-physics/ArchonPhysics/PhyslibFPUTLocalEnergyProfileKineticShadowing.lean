import ArchonPhysics.PhyslibFPUTEnergyProfileCollisionLipschitz

/-!
# Orbit-local energy-profile kinetic shadowing

The canonical finite FPUT energy collision is quadratic, so it is not globally
Lipschitz on the full profile space.  This module replaces the global
Lipschitz hypothesis in `PhyslibFPUTEnergyProfileKineticShadowing` by explicit
nonnegative sup-norm ball envelopes along the profiles which are actually
compared:

* the coherent microscopic profile orbit,
* the kinetic Euler orbit, and
* the fresh canonical-Haar reference input at each restart block.

Given a `CanonicalHaarQuadraticKernelCertificate`, the local Lipschitz constant
on the radius-`R` ball is

`2 * R * finiteQuadraticKernelL1Mass kernel`.

The endpoint residual transfer and the discrete Gronwall estimate are reproved
with only pairwise orbit-local collision estimates.  Consequently both the
finite-block bound and its kinetic-time `O(|g|)` specialization no longer
assume a global collision Lipschitz bound.

The nonnegativity and radius envelopes, and the exact quadratic-kernel
representation, remain transparent hypotheses.  This module does not claim
that Hamiltonian dynamics automatically preserves them.
-/

namespace ArchonPhysics.PhyslibFPUTLocalEnergyProfileKineticShadowing

open ArchonPhysics
open ArchonPhysics.PhyslibFPUTEnergyProfileCollisionLipschitz
open ArchonPhysics.PhyslibFPUTEnergyProfileKineticShadowing
open ArchonPhysics.PhyslibFPUTMomentKineticEulerShadowing
open ArchonPhysics.PhyslibFPUTMultiblockRPAMomentPropagation

noncomputable section

/-! ## Pairwise-local endpoint transfer and Gronwall -/

/-- Endpoint transfer needs collision Lipschitz control only for the reference
and actual initial profiles occurring in this block. -/
theorem energyProfileResidual_of_reference_endpoint_control_at
    {mode : Type*} [Fintype mode]
    (actualInitial actualFinal referenceInitial referenceFinal : mode → Real)
    (Q : (mode → Real) → mode → Real)
    {step L referenceDefect initialEndpointDefect finalEndpointDefect : Real}
    (hstep : 0 ≤ step) (hL : 0 ≤ L)
    (hreference : EnergyProfileKineticEulerResidual
      referenceInitial referenceFinal step (Q referenceInitial)
        referenceDefect)
    (hinitial : ‖actualInitial - referenceInitial‖ ≤ initialEndpointDefect)
    (hfinal : ‖actualFinal - referenceFinal‖ ≤ finalEndpointDefect)
    (hQat : ‖Q referenceInitial - Q actualInitial‖ ≤
      L * ‖referenceInitial - actualInitial‖) :
    EnergyProfileKineticEulerResidual actualInitial actualFinal step
      (Q actualInitial)
      (referenceDefect + finalEndpointDefect +
        (1 + step * L) * initialEndpointDefect) := by
  have hQinitial :
      ‖Q referenceInitial - Q actualInitial‖ ≤
        L * initialEndpointDefect := by
    calc
      ‖Q referenceInitial - Q actualInitial‖ ≤
          L * ‖referenceInitial - actualInitial‖ := hQat
      _ = L * ‖actualInitial - referenceInitial‖ := by
        rw [norm_sub_rev]
      _ ≤ L * initialEndpointDefect :=
        mul_le_mul_of_nonneg_left hinitial hL
  have hcollision :
      ‖step • (Q referenceInitial - Q actualInitial)‖ ≤
        step * (L * initialEndpointDefect) := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hstep]
    exact mul_le_mul_of_nonneg_left hQinitial hstep
  have hidentity :
      actualFinal - actualInitial - step • Q actualInitial =
        (referenceFinal - referenceInitial - step • Q referenceInitial) +
          ((actualFinal - referenceFinal) +
            ((referenceInitial - actualInitial) +
              step • (Q referenceInitial - Q actualInitial))) := by
    ext i
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  unfold EnergyProfileKineticEulerResidual at hreference ⊢
  rw [hidentity]
  calc
    ‖(referenceFinal - referenceInitial - step • Q referenceInitial) +
        ((actualFinal - referenceFinal) +
          ((referenceInitial - actualInitial) +
            step • (Q referenceInitial - Q actualInitial)))‖ ≤
        ‖referenceFinal - referenceInitial - step • Q referenceInitial‖ +
          ‖(actualFinal - referenceFinal) +
            ((referenceInitial - actualInitial) +
              step • (Q referenceInitial - Q actualInitial))‖ :=
      norm_add_le _ _
    _ ≤ ‖referenceFinal - referenceInitial - step • Q referenceInitial‖ +
          (‖actualFinal - referenceFinal‖ +
            ‖(referenceInitial - actualInitial) +
              step • (Q referenceInitial - Q actualInitial)‖) := by
      gcongr
      exact norm_add_le _ _
    _ ≤ ‖referenceFinal - referenceInitial - step • Q referenceInitial‖ +
          (‖actualFinal - referenceFinal‖ +
            (‖referenceInitial - actualInitial‖ +
              ‖step • (Q referenceInitial - Q actualInitial)‖)) := by
      gcongr
      exact norm_add_le _ _
    _ ≤ referenceDefect +
          (finalEndpointDefect +
            (initialEndpointDefect + step * (L * initialEndpointDefect))) := by
      exact add_le_add hreference
        (add_le_add hfinal
          (add_le_add (by simpa only [norm_sub_rev] using hinitial)
            hcollision))
    _ = referenceDefect + finalEndpointDefect +
          (1 + step * L) * initialEndpointDefect := by ring

/-- One affine error step needs collision Lipschitz control only at the actual
and kinetic profiles at this discrete time. -/
theorem norm_energyProfile_sub_kinetic_next_le_at
    {mode : Type*} [Fintype mode]
    (E V : Nat → mode → Real)
    (Q : (mode → Real) → mode → Real)
    (step L : Real) (defect : Nat → Real)
    (hstep : 0 ≤ step)
    (hkinetic : IsEnergyProfileKineticEulerTrajectory V step Q)
    (hresidual : ∀ j, EnergyProfileKineticEulerResidual
      (E j) (E (j + 1)) step (Q (E j)) (defect j))
    (hQorbit : ∀ j,
      ‖Q (E j) - Q (V j)‖ ≤ L * ‖E j - V j‖)
    (j : Nat) :
    ‖E (j + 1) - V (j + 1)‖ ≤
      (1 + L * step) * ‖E j - V j‖ + defect j := by
  have hdecomposition :
      E (j + 1) - V (j + 1) =
        (E (j + 1) - E j - step • Q (E j)) +
          ((E j - V j) + step • (Q (E j) - Q (V j))) := by
    rw [hkinetic j]
    ext i
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [hdecomposition]
  calc
    ‖(E (j + 1) - E j - step • Q (E j)) +
        ((E j - V j) + step • (Q (E j) - Q (V j)))‖ ≤
        ‖E (j + 1) - E j - step • Q (E j)‖ +
          ‖(E j - V j) + step • (Q (E j) - Q (V j))‖ :=
      norm_add_le _ _
    _ ≤ defect j +
          (‖E j - V j‖ + ‖step • (Q (E j) - Q (V j))‖) := by
      gcongr
      · exact hresidual j
      · exact norm_add_le _ _
    _ ≤ defect j +
          (‖E j - V j‖ + step * (L * ‖E j - V j‖)) := by
      gcongr
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hstep]
      exact mul_le_mul_of_nonneg_left (hQorbit j) hstep
    _ = (1 + L * step) * ‖E j - V j‖ + defect j := by ring

/-- Finite-block Gronwall with pairwise collision estimates supplied only
along the two discrete orbits. -/
theorem energyProfile_kineticEuler_shadowing_uniform_bound_of_orbitLipschitz
    {mode : Type*} [Fintype mode]
    (E V : Nat → mode → Real)
    (Q : (mode → Real) → mode → Real)
    (step L defectMax : Real) (defect : Nat → Real)
    (hstep : 0 ≤ step) (hL : 0 ≤ L)
    (hdefect : ∀ j, 0 ≤ defect j)
    (hdefectMax : ∀ j, defect j ≤ defectMax)
    (hkinetic : IsEnergyProfileKineticEulerTrajectory V step Q)
    (hresidual : ∀ j, EnergyProfileKineticEulerResidual
      (E j) (E (j + 1)) step (Q (E j)) (defect j))
    (hQorbit : ∀ j,
      ‖Q (E j) - Q (V j)‖ ≤ L * ‖E j - V j‖)
    (K : Nat) :
    ‖E K - V K‖ ≤
      (‖E 0 - V 0‖ + (K : Real) * defectMax) *
        Real.exp (L * step * (K : Real)) := by
  apply discrete_affine_error_uniform_defect_bound
      (e := fun j ↦ ‖E j - V j‖) (defect := defect)
      (L := L) (h := step) (defectMax := defectMax)
  · exact norm_nonneg _
  · exact hL
  · exact hstep
  · exact hdefect
  · exact hdefectMax
  · exact fun j ↦ norm_energyProfile_sub_kinetic_next_le_at
      E V Q step L defect hstep hkinetic hresidual hQorbit j

/-! ## Canonical quadratic collision on an orbit-local ball -/

/-- The exact local Lipschitz coefficient supplied by a finite quadratic
kernel on the radius-`R` sup-norm ball. -/
def localCollisionLipschitzConstant
    {N : Nat} [NeZero N]
    {m : Lattice.PositiveMassConfig N} {kappa beta T : Real}
    (kernelCertificate :
      CanonicalHaarQuadraticKernelCertificate m kappa beta T)
    (R : Real) : Real :=
  2 * R * finiteQuadraticKernelL1Mass kernelCertificate.kernel

theorem localCollisionLipschitzConstant_nonneg
    {N : Nat} [NeZero N]
    {m : Lattice.PositiveMassConfig N} {kappa beta T : Real}
    (kernelCertificate :
      CanonicalHaarQuadraticKernelCertificate m kappa beta T)
    {R : Real} (hR : 0 ≤ R) :
    0 ≤ localCollisionLipschitzConstant kernelCertificate R := by
  unfold localCollisionLipschitzConstant
  exact mul_nonneg (mul_nonneg (by norm_num) hR)
    (finiteQuadraticKernelL1Mass_nonneg kernelCertificate.kernel)

/-- Transparent orbit and restart-input envelope for one microscopic index
`n`.  The three families listed here are exactly those used in local collision
comparisons. -/
structure LocalEnergyProfileKineticOrbitEnvelope
    {N : Nat} [NeZero N]
    {m : Lattice.PositiveMassConfig N} {kappa beta T : Real}
    {g : Nat → Real}
    {E : Nat → Nat → PositiveEnergyProfile m}
    {Cref Ccoupling : Real}
    (certificate : FPUTCanonicalHaarEnergyProfileBlockwiseCertificate
      m kappa beta T g E Cref Ccoupling)
    (n : Nat) (V : Nat → PositiveEnergyProfile m) (R : Real) : Prop where
  R_nonneg : 0 ≤ R
  actual_nonneg : ∀ j mode, 0 ≤ E n j mode
  actual_norm_le : ∀ j, ‖E n j‖ ≤ R
  kinetic_nonneg : ∀ j mode, 0 ≤ V j mode
  kinetic_norm_le : ∀ j, ‖V j‖ ≤ R
  reference_norm_le : ∀ j, ‖certificate.referenceEnergy n j‖ ≤ R

namespace LocalEnergyProfileKineticOrbitEnvelope

variable {N : Nat} [NeZero N]
  {m : Lattice.PositiveMassConfig N} {kappa beta T : Real}
  {g : Nat → Real}
  {E : Nat → Nat → PositiveEnergyProfile m}
  {Cref Ccoupling : Real}
  {certificate : FPUTCanonicalHaarEnergyProfileBlockwiseCertificate
    m kappa beta T g E Cref Ccoupling}
  {n : Nat} {V : Nat → PositiveEnergyProfile m} {R : Real}

theorem referenceInitial_eq (_envelope :
    LocalEnergyProfileKineticOrbitEnvelope certificate n V R) (j : Nat) :
    canonicalHaarEnergyBlockInitial m (certificate.referenceEnergy n j) =
      certificate.referenceEnergy n j :=
  canonicalHaarEnergyBlockInitial_eq m (certificate.referenceEnergy n j)
    (certificate.referenceEnergy_nonneg n j)

theorem referenceInitial_nonneg (envelope :
    LocalEnergyProfileKineticOrbitEnvelope certificate n V R)
    (j : Nat) (mode : PositiveFrequencyMode m) :
    0 ≤ canonicalHaarEnergyBlockInitial m
      (certificate.referenceEnergy n j) mode := by
  rw [envelope.referenceInitial_eq j]
  exact certificate.referenceEnergy_nonneg n j mode

theorem referenceInitial_norm_le (envelope :
    LocalEnergyProfileKineticOrbitEnvelope certificate n V R) (j : Nat) :
    ‖canonicalHaarEnergyBlockInitial m
        (certificate.referenceEnergy n j)‖ ≤ R := by
  rw [envelope.referenceInitial_eq j]
  exact envelope.reference_norm_le j

/-- Local collision comparison used only in the endpoint residual transfer. -/
theorem collision_reference_actual_le (envelope :
    LocalEnergyProfileKineticOrbitEnvelope certificate n V R)
    (kernelCertificate :
      CanonicalHaarQuadraticKernelCertificate m kappa beta T)
    (j : Nat) :
    ‖canonicalHaarEnergyCollision m kappa beta T
          (canonicalHaarEnergyBlockInitial m
            (certificate.referenceEnergy n j)) -
        canonicalHaarEnergyCollision m kappa beta T (E n j)‖ ≤
      localCollisionLipschitzConstant kernelCertificate R *
        ‖canonicalHaarEnergyBlockInitial m
            (certificate.referenceEnergy n j) - E n j‖ := by
  exact norm_canonicalHaarEnergyCollision_sub_le_of_quadraticKernel
    m kappa beta T R kernelCertificate
      (canonicalHaarEnergyBlockInitial m (certificate.referenceEnergy n j))
      (E n j) envelope.R_nonneg (envelope.referenceInitial_nonneg j)
      (envelope.actual_nonneg j) (envelope.referenceInitial_norm_le j)
      (envelope.actual_norm_le j)

/-- Local collision comparison used only in the Gronwall recurrence. -/
theorem collision_actual_kinetic_le (envelope :
    LocalEnergyProfileKineticOrbitEnvelope certificate n V R)
    (kernelCertificate :
      CanonicalHaarQuadraticKernelCertificate m kappa beta T)
    (j : Nat) :
    ‖canonicalHaarEnergyCollision m kappa beta T (E n j) -
        canonicalHaarEnergyCollision m kappa beta T (V j)‖ ≤
      localCollisionLipschitzConstant kernelCertificate R *
        ‖E n j - V j‖ := by
  exact norm_canonicalHaarEnergyCollision_sub_le_of_quadraticKernel
    m kappa beta T R kernelCertificate (E n j) (V j)
      envelope.R_nonneg (envelope.actual_nonneg j)
      (envelope.kinetic_nonneg j) (envelope.actual_norm_le j)
      (envelope.kinetic_norm_le j)

/-- Actual all-mode residual using only the local reference/actual collision
comparison on the declared ball. -/
theorem actual_is_profileKineticEulerResidual_of_quadraticKernel
    (envelope : LocalEnergyProfileKineticOrbitEnvelope certificate n V R)
    (kernelCertificate :
      CanonicalHaarQuadraticKernelCertificate m kappa beta T)
    (hT : 0 < T) (j : Nat) :
    EnergyProfileKineticEulerResidual
      (E n j) (E n (j + 1)) (g n ^ 2 * T)
      (canonicalHaarEnergyCollision m kappa beta T (E n j))
      (certificate.actualResidualDefect
        (localCollisionLipschitzConstant kernelCertificate R) n) := by
  exact energyProfileResidual_of_reference_endpoint_control_at
    (E n j) (E n (j + 1))
    (canonicalHaarEnergyBlockInitial m (certificate.referenceEnergy n j))
    (canonicalHaarEnergyBlockFinal m kappa beta (g n)
      (certificate.referenceEnergy n j) T)
    (canonicalHaarEnergyCollision m kappa beta T)
    (mul_nonneg (sq_nonneg _) hT.le)
    (localCollisionLipschitzConstant_nonneg kernelCertificate envelope.R_nonneg)
    (certificate.reference_is_profileKineticEulerResidual hT n j)
    (certificate.initial_endpoint_control n j)
    (certificate.final_endpoint_control n j)
    (envelope.collision_reference_actual_le kernelCertificate j)

/-- Finite-block profile shadowing on a transparent local invariant region.
No global Lipschitz property of the quadratic collision is assumed. -/
theorem actual_energyProfile_kineticEuler_shadowing_local_bound
    (envelope : LocalEnergyProfileKineticOrbitEnvelope certificate n V R)
    (kernelCertificate :
      CanonicalHaarQuadraticKernelCertificate m kappa beta T)
    (hT : 0 < T)
    (hkinetic : IsEnergyProfileKineticEulerTrajectory V
      (g n ^ 2 * T) (canonicalHaarEnergyCollision m kappa beta T))
    (K : Nat) :
    ‖E n K - V K‖ ≤
      (‖E n 0 - V 0‖ +
          (K : Real) * certificate.actualResidualDefect
            (localCollisionLipschitzConstant kernelCertificate R) n) *
        Real.exp
          (localCollisionLipschitzConstant kernelCertificate R *
            (g n ^ 2 * T) * (K : Real)) := by
  let L := localCollisionLipschitzConstant kernelCertificate R
  exact energyProfile_kineticEuler_shadowing_uniform_bound_of_orbitLipschitz
    (E n) V (canonicalHaarEnergyCollision m kappa beta T)
      (g n ^ 2 * T) L (certificate.actualResidualDefect L n)
      (fun _ ↦ certificate.actualResidualDefect L n)
      (mul_nonneg (sq_nonneg _) hT.le)
      (localCollisionLipschitzConstant_nonneg kernelCertificate envelope.R_nonneg)
      (fun _ ↦ certificate.actualResidualDefect_nonneg hT.le
        (localCollisionLipschitzConstant_nonneg kernelCertificate envelope.R_nonneg) n)
      (fun _ ↦ le_rfl) hkinetic
      (fun j ↦ envelope.actual_is_profileKineticEulerResidual_of_quadraticKernel
        kernelCertificate hT j)
      (fun j ↦ envelope.collision_actual_kinetic_le kernelCertificate j) K

/-- Kinetic-time specialization of the local finite-block result.  Cubic
microscopic error accumulated over `K = O(|g|^-2)` blocks is `O(|g|)`, with
the local amplification `exp ((2 R ||kernel||_1) tau)`. -/
theorem actual_energyProfile_kineticTime_local_bound
    (envelope : LocalEnergyProfileKineticOrbitEnvelope certificate n V R)
    (kernelCertificate :
      CanonicalHaarQuadraticKernelCertificate m kappa beta T)
    (hT : 0 < T)
    (hkinetic : IsEnergyProfileKineticEulerTrajectory V
      (g n ^ 2 * T) (canonicalHaarEnergyCollision m kappa beta T))
    (K : Nat) (tau : Real)
    (hkineticBudget : (g n ^ 2 * T) * (K : Real) ≤ tau) :
    let L := localCollisionLipschitzConstant kernelCertificate R
    ‖E n K - V K‖ ≤
      (‖E n 0 - V 0‖ +
          (tau / T) * certificate.kineticCubicConstant L * |g n|) *
        Real.exp (L * tau) := by
  dsimp only
  let L := localCollisionLipschitzConstant kernelCertificate R
  have hL : 0 ≤ L :=
    localCollisionLipschitzConstant_nonneg kernelCertificate envelope.R_nonneg
  have hbase := envelope.actual_energyProfile_kineticEuler_shadowing_local_bound
    kernelCertificate hT hkinetic K
  have hCtotal : 0 ≤ certificate.kineticCubicConstant L :=
    certificate.kineticCubicConstant_nonneg hT.le hL
  have hdefect :=
    certificate.actualResidualDefect_le_kineticCubicConstant_mul_abs_cube
      hT.le hL n
  have htau : 0 ≤ tau :=
    (mul_nonneg (mul_nonneg (sq_nonneg _) hT.le)
      (Nat.cast_nonneg _)).trans hkineticBudget
  have hcumulative :
      (K : Real) * certificate.actualResidualDefect L n ≤
        (tau / T) * certificate.kineticCubicConstant L * |g n| := by
    by_cases hgzero : g n = 0
    · simp [FPUTCanonicalHaarEnergyProfileBlockwiseCertificate.actualResidualDefect,
        hgzero]
    · have hratio :
          0 ≤ certificate.kineticCubicConstant L * |g n| / T :=
        div_nonneg (mul_nonneg hCtotal (abs_nonneg _)) hT.le
      calc
        (K : Real) * certificate.actualResidualDefect L n ≤
            (K : Real) *
              (certificate.kineticCubicConstant L * |g n| ^ 3) :=
          mul_le_mul_of_nonneg_left hdefect (Nat.cast_nonneg _)
        _ = ((g n ^ 2 * T) * (K : Real)) *
              (certificate.kineticCubicConstant L * |g n| / T) := by
          field_simp [hT.ne', hgzero]
          rw [sq_abs]
        _ ≤ tau *
              (certificate.kineticCubicConstant L * |g n| / T) :=
          mul_le_mul_of_nonneg_right hkineticBudget hratio
        _ = (tau / T) * certificate.kineticCubicConstant L * |g n| := by
          ring
  have hexponent :
      L * (g n ^ 2 * T) * (K : Real) ≤ L * tau := by
    calc
      L * (g n ^ 2 * T) * (K : Real) =
          L * ((g n ^ 2 * T) * (K : Real)) := by ring
      _ ≤ L * tau := mul_le_mul_of_nonneg_left hkineticBudget hL
  have hprefixNonneg :
      0 ≤ ‖E n 0 - V 0‖ +
        (tau / T) * certificate.kineticCubicConstant L * |g n| := by
    exact add_nonneg (norm_nonneg _)
      (mul_nonneg
        (mul_nonneg (div_nonneg htau hT.le) hCtotal)
        (abs_nonneg _))
  change ‖E n K - V K‖ ≤
    (‖E n 0 - V 0‖ +
        (tau / T) * certificate.kineticCubicConstant L * |g n|) *
      Real.exp (L * tau)
  calc
    ‖E n K - V K‖ ≤
        (‖E n 0 - V 0‖ +
            (K : Real) * certificate.actualResidualDefect L n) *
          Real.exp (L * (g n ^ 2 * T) * (K : Real)) := by
      simpa only [L] using hbase
    _ ≤ (‖E n 0 - V 0‖ +
            (tau / T) * certificate.kineticCubicConstant L * |g n|) *
          Real.exp (L * (g n ^ 2 * T) * (K : Real)) :=
      mul_le_mul_of_nonneg_right (add_le_add le_rfl hcumulative)
        (Real.exp_pos _).le
    _ ≤ (‖E n 0 - V 0‖ +
            (tau / T) * certificate.kineticCubicConstant L * |g n|) *
          Real.exp (L * tau) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexponent)
        hprefixNonneg

end LocalEnergyProfileKineticOrbitEnvelope

end


end ArchonPhysics.PhyslibFPUTLocalEnergyProfileKineticShadowing
