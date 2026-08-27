import ArchonPhysics.RegularizedMarkedLegWeierstrass
import ArchonPhysics.ThreeWaveCollisionFourierFactorization

/-!
# Complex collision legs and regularized real spectral weights

The finite collision Fourier transform uses complex one-leg weights with an
inverse harmonic frequency.  This module splits those weights and their
projected-bond kernels into real cosine and sine parts.  Multiplication by the
squared frequency then gives exactly the continuous regularized weights used
by the zero-constant polynomial locality bridge.

These are finite exact identities.  No thermodynamic limit or approximation
error estimate is asserted here.
-/

open scoped Matrix ComplexConjugate

namespace ArchonPhysics.ComplexRegularizedMarkedLegBridge

open ArchonPhysics
open ArchonPhysics.HarmonicModes
open ArchonPhysics.MeasurableOrderedModeCoupling.Harmonic
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.OrderedInteractionSpectralFactorization
open ArchonPhysics.RandomMassPositiveCollisionData
open ArchonPhysics.RegularizedMarkedLegPolynomialLocality
open ArchonPhysics.ThreeWaveCollisionFourierFactorization

noncomputable section

/-- Real part of one normalized complex phase leg. -/
theorem orderedNormalizedPhaseLeg_re {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N)
    (sign : Fin 3 → InteractionSign) (time : Real)
    (r : Fin 3) (k : OrderedModeIndex N) :
    (orderedNormalizedPhaseLeg m sign time r k).re =
      (2 * orderedModeFrequency (harmonicHermitian m) k)⁻¹ *
        Real.cos ((sign r).coefficient * time *
          orderedModeFrequency (harmonicHermitian m) k) := by
  unfold orderedNormalizedPhaseLeg orderedPhaseLeg
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.exp_re, Complex.mul_im, Complex.I_re, Complex.I_im,
    zero_mul, one_mul, sub_zero, mul_zero, Real.exp_zero, one_mul]
  congr 2
  ring

/-- Imaginary part of one normalized complex phase leg. -/
theorem orderedNormalizedPhaseLeg_im {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N)
    (sign : Fin 3 → InteractionSign) (time : Real)
    (r : Fin 3) (k : OrderedModeIndex N) :
    (orderedNormalizedPhaseLeg m sign time r k).im =
      (2 * orderedModeFrequency (harmonicHermitian m) k)⁻¹ *
        Real.sin ((sign r).coefficient * time *
          orderedModeFrequency (harmonicHermitian m) k) := by
  unfold orderedNormalizedPhaseLeg orderedPhaseLeg
  simp only [Complex.mul_im, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, Complex.exp_im, Complex.I_re, Complex.I_im,
    zero_mul, one_mul, add_zero, sub_zero, Real.exp_zero]
  congr 2
  ring

/-- Every eigenvalue of the deterministic harmonic Gram matrix is
nonnegative. -/
theorem harmonicHermitian_orderedEigenvalue_nonneg
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (k : OrderedModeIndex N) :
    0 ≤ orderedEigenvalue (harmonicHermitian m) k := by
  simpa [harmonicOrderedEigenvalue, harmonicHermitianSample,
    harmonicHermitian] using
      (harmonicOrderedEigenvalue_nonneg (fun _ : Unit ↦ m) () k)

/-- The squared-frequency factor converts the real normalized phase leg to
the regularized cosine weight, including at the translation mode. -/
theorem orderedNormalizedPhaseLeg_re_mul_eigenvalue
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (sign : Fin 3 → InteractionSign) (time : Real)
    (r : Fin 3) (k : OrderedModeIndex N) :
    (orderedNormalizedPhaseLeg m sign time r k).re *
        orderedEigenvalue (harmonicHermitian m) k =
      regularizedCosineLegWeight time (sign r).coefficient
        (orderedEigenvalue (harmonicHermitian m) k) := by
  rw [orderedNormalizedPhaseLeg_re]
  simpa [orderedModeFrequency] using
    (normalizedCosineLeg_mul_eigenvalue
      (lambda := orderedEigenvalue (harmonicHermitian m) k)
      (time := time) (sign := (sign r).coefficient)
      (harmonicHermitian_orderedEigenvalue_nonneg m k))

/-- The corresponding exact sine identity for the imaginary phase leg. -/
theorem orderedNormalizedPhaseLeg_im_mul_eigenvalue
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (sign : Fin 3 → InteractionSign) (time : Real)
    (r : Fin 3) (k : OrderedModeIndex N) :
    (orderedNormalizedPhaseLeg m sign time r k).im *
        orderedEigenvalue (harmonicHermitian m) k =
      regularizedSineLegWeight time (sign r).coefficient
        (orderedEigenvalue (harmonicHermitian m) k) := by
  rw [orderedNormalizedPhaseLeg_im]
  simpa [orderedModeFrequency] using
    (normalizedSineLeg_mul_eigenvalue
      (lambda := orderedEigenvalue (harmonicHermitian m) k)
      (time := time) (sign := (sign r).coefficient)
      (harmonicHermitian_orderedEigenvalue_nonneg m k))

variable {iota bond : Type*}
variable [Fintype iota] [DecidableEq iota]

/-- The real part of a complex weighted projected-bond kernel is the real
weighted kernel of the pointwise real parts. -/
theorem complexWeightedProjectedBondKernel_re
    (B : Matrix bond iota Real) (A : HermitianMatrix iota)
    (weight : Fin (Fintype.card iota) → Complex) (j l : bond) :
    (complexWeightedProjectedBondKernel B A weight j l).re =
      weightedProjectedBondKernel B A (fun k ↦ (weight k).re) j l := by
  unfold complexWeightedProjectedBondKernel weightedProjectedBondKernel
  simp [Complex.mul_re]

/-- The imaginary part of a complex weighted projected-bond kernel is the
real weighted kernel of the pointwise imaginary parts. -/
theorem complexWeightedProjectedBondKernel_im
    (B : Matrix bond iota Real) (A : HermitianMatrix iota)
    (weight : Fin (Fintype.card iota) → Complex) (j l : bond) :
    (complexWeightedProjectedBondKernel B A weight j l).im =
      weightedProjectedBondKernel B A (fun k ↦ (weight k).im) j l := by
  unfold complexWeightedProjectedBondKernel weightedProjectedBondKernel
  simp [Complex.mul_im]

/-- Harmonic specialization: the real part of the finite complex one-leg
kernel is exactly the cosine-weighted real projected-bond kernel. -/
theorem harmonicComplexKernel_re
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (sign : Fin 3 → InteractionSign) (time : Real)
    (r : Fin 3) (j l : Lattice.Site N) :
    (complexWeightedProjectedBondKernel (massWeightedDifferenceMatrix m)
        (harmonicHermitian m) (orderedNormalizedPhaseLeg m sign time r) j l).re =
      weightedProjectedBondKernel (massWeightedDifferenceMatrix m)
        (harmonicHermitian m)
        (fun k ↦ (2 * orderedModeFrequency (harmonicHermitian m) k)⁻¹ *
          Real.cos ((sign r).coefficient * time *
            orderedModeFrequency (harmonicHermitian m) k)) j l := by
  rw [complexWeightedProjectedBondKernel_re]
  congr 1
  funext k
  exact orderedNormalizedPhaseLeg_re m sign time r k

/-- Harmonic specialization for the imaginary/sine component. -/
theorem harmonicComplexKernel_im
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (sign : Fin 3 → InteractionSign) (time : Real)
    (r : Fin 3) (j l : Lattice.Site N) :
    (complexWeightedProjectedBondKernel (massWeightedDifferenceMatrix m)
        (harmonicHermitian m) (orderedNormalizedPhaseLeg m sign time r) j l).im =
      weightedProjectedBondKernel (massWeightedDifferenceMatrix m)
        (harmonicHermitian m)
        (fun k ↦ (2 * orderedModeFrequency (harmonicHermitian m) k)⁻¹ *
          Real.sin ((sign r).coefficient * time *
            orderedModeFrequency (harmonicHermitian m) k)) j l := by
  rw [complexWeightedProjectedBondKernel_im]
  congr 1
  funext k
  exact orderedNormalizedPhaseLeg_im m sign time r k

end

end ArchonPhysics.ComplexRegularizedMarkedLegBridge
