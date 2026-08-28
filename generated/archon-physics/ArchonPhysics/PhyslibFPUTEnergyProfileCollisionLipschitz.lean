import ArchonPhysics.PhyslibFPUTEnergyProfileKineticShadowing

/-!
# Local Lipschitz control for finite FPUT energy-profile collisions

The canonical Haar collision acts on a complete finite modal-energy profile.
Its second-order character expansion is quadratic in the nonnegative modal
energies, not globally linear.  This module isolates the exact finite
quadratic-kernel certificate needed to turn that algebraic fact into the
sup-norm Lipschitz estimate used by blockwise kinetic shadowing.

The estimate is deliberately local: on the closed sup-norm ball of radius
`R`, a quadratic field has Lipschitz constant
`2 * R * finiteQuadraticKernelL1Mass kernel`.  No global Lipschitz claim is
made.  The only remaining model-specific obligation is the displayed exact
quadratic representation of `canonicalHaarEnergyCollision` on the
nonnegative orthant.
-/

namespace ArchonPhysics.PhyslibFPUTEnergyProfileCollisionLipschitz

open ArchonPhysics
open ArchonPhysics.PhyslibFPUTEnergyProfileKineticShadowing

noncomputable section

/-! ## A finite quadratic collision field -/

/-- A finite three-index kernel: output mode, first input mode, second input
mode. -/
abbrev FiniteQuadraticCollisionKernel (mode : Type*) :=
  mode → mode → mode → Real

/-- The quadratic vector field represented by a finite kernel. -/
def finiteQuadraticCollisionField
    {mode : Type*} [Fintype mode]
    (kernel : FiniteQuadraticCollisionKernel mode)
    (energy : mode → Real) : mode → Real :=
  fun output ↦
    ∑ first : mode, ∑ second : mode,
      kernel output first second * energy first * energy second

/-- A deliberately simple explicit kernel norm.  It is the `l1` mass over
all three finite indices; hence it bounds every output-row mass without a
choice of a maximizing row. -/
def finiteQuadraticKernelL1Mass
    {mode : Type*} [Fintype mode]
    (kernel : FiniteQuadraticCollisionKernel mode) : Real :=
  ∑ output : mode, ∑ first : mode, ∑ second : mode,
    |kernel output first second|

theorem finiteQuadraticKernelL1Mass_nonneg
    {mode : Type*} [Fintype mode]
    (kernel : FiniteQuadraticCollisionKernel mode) :
    0 ≤ finiteQuadraticKernelL1Mass kernel := by
  unfold finiteQuadraticKernelL1Mass
  positivity

/-- One output row is bounded by the full finite `l1` kernel mass. -/
theorem finiteQuadraticKernel_rowMass_le_l1Mass
    {mode : Type*} [Fintype mode]
    (kernel : FiniteQuadraticCollisionKernel mode) (output : mode) :
    (∑ first : mode, ∑ second : mode,
        |kernel output first second|) ≤
      finiteQuadraticKernelL1Mass kernel := by
  classical
  unfold finiteQuadraticKernelL1Mass
  exact Finset.single_le_sum (s := Finset.univ)
    (f := fun index : mode ↦
      ∑ first : mode, ∑ second : mode,
        |kernel index first second|)
    (fun index _ ↦ by positivity) (Finset.mem_univ output)

/-- Coordinatewise product telescoping on a radius-`R` sup-norm ball. -/
private theorem abs_energyProduct_sub_energyProduct_le
    {mode : Type*} [Fintype mode]
    (energy₁ energy₂ : mode → Real) (R : Real)
    (hR : 0 ≤ R) (henergy₁ : ‖energy₁‖ ≤ R)
    (henergy₂ : ‖energy₂‖ ≤ R) (first second : mode) :
    |energy₁ first * energy₁ second -
        energy₂ first * energy₂ second| ≤
      2 * R * ‖energy₁ - energy₂‖ := by
  have hfirst₁ : |energy₁ first| ≤ R :=
    ((pi_norm_le_iff_of_nonneg (norm_nonneg energy₁)).mp le_rfl first).trans
      henergy₁
  have hsecond₁ : |energy₁ second| ≤ R :=
    ((pi_norm_le_iff_of_nonneg (norm_nonneg energy₁)).mp le_rfl second).trans
      henergy₁
  have hfirst₂ : |energy₂ first| ≤ R :=
    ((pi_norm_le_iff_of_nonneg (norm_nonneg energy₂)).mp le_rfl first).trans
      henergy₂
  have hsecond₂ : |energy₂ second| ≤ R :=
    ((pi_norm_le_iff_of_nonneg (norm_nonneg energy₂)).mp le_rfl second).trans
      henergy₂
  have hfirstSub : |energy₁ first - energy₂ first| ≤
      ‖energy₁ - energy₂‖ := by
    simpa only [Pi.sub_apply, Real.norm_eq_abs] using
      ((pi_norm_le_iff_of_nonneg (norm_nonneg (energy₁ - energy₂))).mp
        le_rfl first)
  have hsecondSub : |energy₁ second - energy₂ second| ≤
      ‖energy₁ - energy₂‖ := by
    simpa only [Pi.sub_apply, Real.norm_eq_abs] using
      ((pi_norm_le_iff_of_nonneg (norm_nonneg (energy₁ - energy₂))).mp
        le_rfl second)
  rw [show energy₁ first * energy₁ second -
      energy₂ first * energy₂ second =
        (energy₁ first - energy₂ first) * energy₁ second +
          energy₂ first * (energy₁ second - energy₂ second) by ring]
  calc
    |(energy₁ first - energy₂ first) * energy₁ second +
        energy₂ first * (energy₁ second - energy₂ second)| ≤
      |energy₁ first - energy₂ first| * |energy₁ second| +
        |energy₂ first| * |energy₁ second - energy₂ second| := by
          simpa only [abs_mul] using
            (abs_add_le
              ((energy₁ first - energy₂ first) * energy₁ second)
              (energy₂ first * (energy₁ second - energy₂ second)))
    _ ≤ ‖energy₁ - energy₂‖ * R +
        R * ‖energy₁ - energy₂‖ := by
      gcongr
    _ = 2 * R * ‖energy₁ - energy₂‖ := by ring

/-- A finite quadratic collision field is locally Lipschitz on a closed
sup-norm ball.  The constant is explicit and finite, but intentionally crude:
it uses the total three-index `l1` mass rather than the maximum output-row
mass. -/
theorem norm_finiteQuadraticCollisionField_sub_le
    {mode : Type*} [Fintype mode]
    (kernel : FiniteQuadraticCollisionKernel mode)
    (energy₁ energy₂ : mode → Real) (R : Real)
    (hR : 0 ≤ R) (henergy₁ : ‖energy₁‖ ≤ R)
    (henergy₂ : ‖energy₂‖ ≤ R) :
    ‖finiteQuadraticCollisionField kernel energy₁ -
        finiteQuadraticCollisionField kernel energy₂‖ ≤
      (2 * R * finiteQuadraticKernelL1Mass kernel) *
        ‖energy₁ - energy₂‖ := by
  classical
  refine (pi_norm_le_iff_of_nonneg
    (mul_nonneg
      (mul_nonneg (mul_nonneg (by positivity) hR)
        (finiteQuadraticKernelL1Mass_nonneg kernel))
      (norm_nonneg _))).2 ?_
  intro output
  simp only [finiteQuadraticCollisionField, Pi.sub_apply, Real.norm_eq_abs]
  rw [← Finset.sum_sub_distrib]
  calc
    |∑ first : mode,
        ((∑ second : mode,
            kernel output first second * energy₁ first * energy₁ second) -
          ∑ second : mode,
            kernel output first second * energy₂ first * energy₂ second)| ≤
      ∑ first : mode,
        |(∑ second : mode,
            kernel output first second * energy₁ first * energy₁ second) -
          ∑ second : mode,
            kernel output first second * energy₂ first * energy₂ second| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ first : mode,
        |∑ second : mode,
          (kernel output first second * energy₁ first * energy₁ second -
            kernel output first second * energy₂ first * energy₂ second)| := by
      congr 1
      funext first
      rw [Finset.sum_sub_distrib]
    _ ≤ ∑ first : mode, ∑ second : mode,
        |kernel output first second * energy₁ first * energy₁ second -
          kernel output first second * energy₂ first * energy₂ second| := by
      gcongr with first
      exact Finset.abs_sum_le_sum_abs _ _
    _ = ∑ first : mode, ∑ second : mode,
        |kernel output first second| *
          |energy₁ first * energy₁ second -
            energy₂ first * energy₂ second| := by
      congr 1
      funext first
      congr 1
      funext second
      rw [show kernel output first second * energy₁ first * energy₁ second -
          kernel output first second * energy₂ first * energy₂ second =
        kernel output first second *
          (energy₁ first * energy₁ second -
            energy₂ first * energy₂ second) by ring,
        abs_mul]
    _ ≤ ∑ first : mode, ∑ second : mode,
        |kernel output first second| *
          (2 * R * ‖energy₁ - energy₂‖) := by
      gcongr with first second
      exact abs_energyProduct_sub_energyProduct_le
        energy₁ energy₂ R hR henergy₁ henergy₂ first second
    _ = (∑ first : mode, ∑ second : mode,
        |kernel output first second|) *
          (2 * R * ‖energy₁ - energy₂‖) := by
      rw [Finset.sum_mul]
      congr 1
      funext first
      rw [Finset.sum_mul]
    _ ≤ finiteQuadraticKernelL1Mass kernel *
          (2 * R * ‖energy₁ - energy₂‖) := by
      apply mul_le_mul_of_nonneg_right
        (finiteQuadraticKernel_rowMass_le_l1Mass kernel output)
      positivity
    _ = (2 * R * finiteQuadraticKernelL1Mass kernel) *
          ‖energy₁ - energy₂‖ := by ring

/-- A coordinatewise nonnegative radius-`R` box is contained in the Pi
sup-norm ball of radius `R`. -/
theorem norm_energyProfile_le_of_mem_nonnegativeBox
    {mode : Type*} [Fintype mode]
    (energy : mode → Real) (R : Real) (hR : 0 ≤ R)
    (henergyNonneg : ∀ mode, 0 ≤ energy mode)
    (henergyUpper : ∀ mode, energy mode ≤ R) :
    ‖energy‖ ≤ R := by
  refine (pi_norm_le_iff_of_nonneg hR).2 ?_
  intro mode
  rw [Real.norm_eq_abs, abs_of_nonneg (henergyNonneg mode)]
  exact henergyUpper mode

/-- Coordinatewise-box form of the local quadratic Lipschitz estimate. -/
theorem norm_finiteQuadraticCollisionField_sub_le_of_mem_nonnegativeBox
    {mode : Type*} [Fintype mode]
    (kernel : FiniteQuadraticCollisionKernel mode)
    (energy₁ energy₂ : mode → Real) (R : Real)
    (hR : 0 ≤ R)
    (henergy₁Nonneg : ∀ mode, 0 ≤ energy₁ mode)
    (henergy₂Nonneg : ∀ mode, 0 ≤ energy₂ mode)
    (henergy₁Upper : ∀ mode, energy₁ mode ≤ R)
    (henergy₂Upper : ∀ mode, energy₂ mode ≤ R) :
    ‖finiteQuadraticCollisionField kernel energy₁ -
        finiteQuadraticCollisionField kernel energy₂‖ ≤
      (2 * R * finiteQuadraticKernelL1Mass kernel) *
        ‖energy₁ - energy₂‖ := by
  exact norm_finiteQuadraticCollisionField_sub_le
    kernel energy₁ energy₂ R hR
      (norm_energyProfile_le_of_mem_nonnegativeBox
        energy₁ R hR henergy₁Nonneg henergy₁Upper)
      (norm_energyProfile_le_of_mem_nonnegativeBox
        energy₂ R hR henergy₂Nonneg henergy₂Upper)

/-! ## Canonical Haar specialization -/

/-- Exact algebraic certificate that a canonical finite-time Haar collision
is a quadratic field of the full nonnegative energy profile.  The
representation is required only on the physical nonnegative orthant, since
`phaseEnergyRadius` totalizes square roots outside that domain. -/
structure CanonicalHaarQuadraticKernelCertificate
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa beta T : Real) where
  kernel : FiniteQuadraticCollisionKernel (PositiveFrequencyMode m)
  represents_nonnegative : ∀ energy : PositiveEnergyProfile m,
    (∀ mode, 0 ≤ energy mode) →
      canonicalHaarEnergyCollision m kappa beta T energy =
        finiteQuadraticCollisionField kernel energy

/-- Once the exact second-order character algebra is supplied as a finite
quadratic-kernel certificate, the canonical Haar energy collision has an
explicit local sup-norm Lipschitz bound on every nonnegative radius-`R` box.
This is the precise replacement for an unjustified global `hQ`. -/
theorem norm_canonicalHaarEnergyCollision_sub_le_of_quadraticKernel
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa beta T R : Real)
    (certificate :
      CanonicalHaarQuadraticKernelCertificate m kappa beta T)
    (energy₁ energy₂ : PositiveEnergyProfile m)
    (hR : 0 ≤ R)
    (henergy₁Nonneg : ∀ mode, 0 ≤ energy₁ mode)
    (henergy₂Nonneg : ∀ mode, 0 ≤ energy₂ mode)
    (henergy₁ : ‖energy₁‖ ≤ R) (henergy₂ : ‖energy₂‖ ≤ R) :
    ‖canonicalHaarEnergyCollision m kappa beta T energy₁ -
        canonicalHaarEnergyCollision m kappa beta T energy₂‖ ≤
      (2 * R * finiteQuadraticKernelL1Mass certificate.kernel) *
        ‖energy₁ - energy₂‖ := by
  rw [certificate.represents_nonnegative energy₁ henergy₁Nonneg,
    certificate.represents_nonnegative energy₂ henergy₂Nonneg]
  exact norm_finiteQuadraticCollisionField_sub_le
    certificate.kernel energy₁ energy₂ R hR henergy₁ henergy₂

/-- Closed nonnegative energy-box form of the canonical local Lipschitz
bound.  This is the form directly consumed by an energy-envelope argument. -/
theorem norm_canonicalHaarEnergyCollision_sub_le_on_nonnegativeBox
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa beta T R : Real)
    (certificate :
      CanonicalHaarQuadraticKernelCertificate m kappa beta T)
    (energy₁ energy₂ : PositiveEnergyProfile m)
    (hR : 0 ≤ R)
    (henergy₁Nonneg : ∀ mode, 0 ≤ energy₁ mode)
    (henergy₂Nonneg : ∀ mode, 0 ≤ energy₂ mode)
    (henergy₁Upper : ∀ mode, energy₁ mode ≤ R)
    (henergy₂Upper : ∀ mode, energy₂ mode ≤ R) :
    ‖canonicalHaarEnergyCollision m kappa beta T energy₁ -
        canonicalHaarEnergyCollision m kappa beta T energy₂‖ ≤
      (2 * R * finiteQuadraticKernelL1Mass certificate.kernel) *
        ‖energy₁ - energy₂‖ := by
  rw [certificate.represents_nonnegative energy₁ henergy₁Nonneg,
    certificate.represents_nonnegative energy₂ henergy₂Nonneg]
  exact norm_finiteQuadraticCollisionField_sub_le_of_mem_nonnegativeBox
    certificate.kernel energy₁ energy₂ R hR henergy₁Nonneg
      henergy₂Nonneg henergy₁Upper henergy₂Upper

end

end ArchonPhysics.PhyslibFPUTEnergyProfileCollisionLipschitz
