import ArchonPhysics.PhysicalHarmonicEnergyIdentity
import ArchonPhysics.R32CanonicalExactFreeBridgeV3
import ArchonPhysics.R32DiluteBootstrapClosureCompleteV3
import ArchonPhysics.R32DiluteNonlinearStability
import ArchonPhysics.R32HarmonicErrorEnergyDuhamelV5

/-!
# R32 canonical Duhamel and nonlinear-force bridge

This module instantiates the kernel-safe harmonic energy estimate on the
canonical mass-weighted exact-minus-free equations.  It proves that the
canonical harmonic operator is self-adjoint and nonnegative, identifies its
quadratic form with the physical bond error, and combines the resulting
energy inequality with the dimension-free dilute nonlinear-force estimate.

The final prefix theorem has exactly the form consumed by the complete
first-exit bootstrap.  It assumes only free-orbit dilute bounds and a
nonnegative prefix bound on the error.  No persistence or asymptotic
small-coupling conclusion is assumed here.
-/

namespace ArchonPhysics.R32CanonicalDuhamelForceBridgeV3

open ArchonPhysics
open ArchonPhysics.CanonicalRandomMicroscopicCertificate
open ArchonPhysics.CoerciveHamiltonianPhyslib
open ArchonPhysics.HarmonicModes
open ArchonPhysics.MassWeightedHamiltonianDynamics
open ArchonPhysics.PhysicalHarmonicEnergyIdentity
open ArchonPhysics.R32CanonicalExactFreeBridgeV3
open ArchonPhysics.R32DiluteBootstrapClosureCompleteV3
open ArchonPhysics.R32DiluteNonlinearStability
open ArchonPhysics.R32HarmonicErrorEnergyDuhamelV5
open ArchonPhysics.ReducedModeTransform
open MeasureTheory Set
open scoped RealInnerProductSpace

noncomputable section

variable {N : Nat} [NeZero N]
/- The derivative predicate in the canonical producer deliberately fixes
these low-level PiLp instances. Installing the identical instances here
makes its HasMassWeightedDerivAt fields definitionally usable by the abstract
HasDerivAt energy theorem. -/
local instance canonicalWeightedAddCommGroup :
    AddCommGroup (WeightedConfiguration N) :=
  (PiLp.normedAddCommGroup 2
    (fun _ : Lattice.Site N => Real)).toAddCommGroup

local instance canonicalWeightedModule :
    Module Real (WeightedConfiguration N) :=
  (PiLp.normedSpace 2 Real
    (fun _ : Lattice.Site N => Real)).toModule

local instance canonicalWeightedTopologicalSpace :
    TopologicalSpace (WeightedConfiguration N) :=
  (PiLp.normedAddCommGroup 2
    (fun _ : Lattice.Site N => Real)).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace

/-- The weighted periodic incidence operator applied to a mass-weighted
configuration. -/
def massWeightedBond
    (m : Lattice.PositiveMassConfig N) (x : WeightedConfiguration N) :
    WeightedConfiguration N :=
  WithLp.toLp 2
    (Matrix.mulVec (massWeightedDifferenceMatrix m) (WithLp.ofLp x))

@[simp] theorem massWeightedBond_apply
    (m : Lattice.PositiveMassConfig N) (x : WeightedConfiguration N)
    (i : Lattice.Site N) :
    massWeightedBond m x i =
      Matrix.mulVec (massWeightedDifferenceMatrix m) (WithLp.ofLp x) i := by
  rfl

/-- The canonical harmonic operator is self-adjoint. -/
theorem harmonicOperatorCLM_isSelfAdjoint
    (m : Lattice.PositiveMassConfig N) :
    IsSelfAdjointOperator (harmonicOperatorCLM m) := by
  intro x y
  let D := massWeightedDifferenceMatrix m
  let ux : Lattice.Configuration N := WithLp.ofLp x
  let uy : Lattice.Configuration N := WithLp.ofLp y
  have hmatrix :
      Matrix.mulVec (massWeightedHarmonicMatrix m) ux ⬝ᵥ uy =
        ux ⬝ᵥ Matrix.mulVec (massWeightedHarmonicMatrix m) uy := by
    rw [massWeightedHarmonicMatrix_eq_transpose_mul_self]
    simp only [← Matrix.mulVec_mulVec]
    change
      Matrix.mulVec (Matrix.transpose D) (Matrix.mulVec D ux) ⬝ᵥ uy =
        ux ⬝ᵥ
          Matrix.mulVec (Matrix.transpose D) (Matrix.mulVec D uy)
    calc
      Matrix.mulVec (Matrix.transpose D) (Matrix.mulVec D ux) ⬝ᵥ uy =
          uy ⬝ᵥ
            Matrix.mulVec (Matrix.transpose D) (Matrix.mulVec D ux) := by
        rw [dotProduct_comm]
      _ = Matrix.mulVec D ux ⬝ᵥ Matrix.mulVec D uy :=
        Matrix.dotProduct_transpose_mulVec D uy (Matrix.mulVec D ux)
      _ = Matrix.mulVec D uy ⬝ᵥ Matrix.mulVec D ux := by
        rw [dotProduct_comm]
      _ = ux ⬝ᵥ
          Matrix.mulVec (Matrix.transpose D) (Matrix.mulVec D uy) :=
        (Matrix.dotProduct_transpose_mulVec D ux (Matrix.mulVec D uy)).symm
  simpa [harmonicOperatorCLM_apply, harmonicOperator_apply,
    PiLp.inner_apply, dotProduct, ux, uy, mul_comm] using hmatrix

/-- The canonical harmonic operator is nonnegative, including on its
translation kernel. -/
theorem harmonicOperatorCLM_isNonnegative
    (m : Lattice.PositiveMassConfig N) :
    IsNonnegativeOperator (harmonicOperatorCLM m) := by
  intro x
  rw [real_inner_comm]
  change 0 ≤ harmonicQuadraticForm m x
  rw [harmonicQuadraticForm_eq_modal_sum]
  exact Finset.sum_nonneg fun k _hk =>
    mul_nonneg (modeFrequencySq_nonneg m k)
      (sq_nonneg (modalCoordinates m x k))

/-- The squared weighted-bond norm is exactly the harmonic quadratic form. -/
theorem norm_massWeightedBond_sq
    (m : Lattice.PositiveMassConfig N) (x : WeightedConfiguration N) :
    ‖massWeightedBond m x‖ ^ 2 =
      @inner Real (WeightedConfiguration N) _ x
        (harmonicOperatorCLM m x) := by
  let D := massWeightedDifferenceMatrix m
  let ux : Lattice.Configuration N := WithLp.ofLp x
  calc
    ‖massWeightedBond m x‖ ^ 2 =
        ∑ i : Lattice.Site N, (Matrix.mulVec D ux i) ^ 2 := by
      simpa [massWeightedBond, D, ux] using
        (EuclideanSpace.real_norm_sq_eq (massWeightedBond m x))
    _ = Matrix.mulVec D ux ⬝ᵥ Matrix.mulVec D ux := by
      simp [dotProduct, pow_two]
    _ = ux ⬝ᵥ
        Matrix.mulVec (Matrix.transpose D) (Matrix.mulVec D ux) :=
      (Matrix.dotProduct_transpose_mulVec D ux (Matrix.mulVec D ux)).symm
    _ = ux ⬝ᵥ Matrix.mulVec (massWeightedHarmonicMatrix m) ux := by
      rw [massWeightedHarmonicMatrix_eq_transpose_mul_self,
        ← Matrix.mulVec_mulVec]
    _ = @inner Real (WeightedConfiguration N) _ x
        (harmonicOperatorCLM m x) := by
      simp [harmonicOperatorCLM_apply, harmonicOperator_apply,
        PiLp.inner_apply, dotProduct, ux, mul_comm]

/-- Weighted incidence after square-root mass weighting is the physical bond
vector, with no loss in the number of sites. -/
theorem massWeightedBond_sqrtMassTransform
    (m : Lattice.PositiveMassConfig N) (q : HilbertConfiguration N) :
    massWeightedBond m (sqrtMassTransform m q) = bondVector q := by
  ext i
  change
    Matrix.mulVec (massWeightedDifferenceMatrix m)
        (WithLp.ofLp (sqrtMassTransform m q)) i =
      Lattice.forwardDifference (asConfiguration q) i
  exact congrFun (massWeightedDifference_mulVec_sqrtMassTransform m q) i

/-- The physical exact-minus-free bond vector. -/
def canonicalPhysicalBondError
    (kappa beta g : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (a : Real) (omega : RandomEnsemble.SampleSpace) :
    Real → HilbertConfiguration N :=
  fun time =>
    bondVector
      (canonicalPhysicalPositionPath (N := N)
          kappa beta g hbeta a omega time -
        canonicalPhysicalPositionPath (N := N)
          kappa beta 0 hbeta a omega time)

/-- The mass-weighted position error is the square-root mass transform of the
physical position error. -/
theorem canonicalExactFreePositionError_eq_sqrtMassTransform
    (kappa beta g : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (a : Real) (omega : RandomEnsemble.SampleSpace) (time : Real) :
    canonicalExactFreePositionError (N := N)
        kappa beta g hbeta a omega time =
      sqrtMassTransform (canonicalMass (N := N) omega)
        (canonicalPhysicalPositionPath (N := N)
            kappa beta g hbeta a omega time -
          canonicalPhysicalPositionPath (N := N)
            kappa beta 0 hbeta a omega time) := by
  simp [canonicalExactFreePositionError,
    canonicalMassWeightedPositionPath, massWeightedPosition]

/-- The canonical weighted bond of the mass-weighted error is exactly the
physical bond error. -/
theorem massWeightedBond_canonicalExactFreePositionError
    (kappa beta g : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (a : Real) (omega : RandomEnsemble.SampleSpace) (time : Real) :
    massWeightedBond (canonicalMass (N := N) omega)
        (canonicalExactFreePositionError (N := N)
          kappa beta g hbeta a omega time) =
      canonicalPhysicalBondError (N := N)
        kappa beta g hbeta a omega time := by
  rw [canonicalExactFreePositionError_eq_sqrtMassTransform]
  exact massWeightedBond_sqrtMassTransform
    (canonicalMass (N := N) omega) _

/-- The concrete canonical error-energy seminorm. -/
def canonicalErrorEnergy
    (kappa beta g : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (a : Real) (omega : RandomEnsemble.SampleSpace) (time : Real) : Real :=
  harmonicEnergySeminorm
    (harmonicOperatorCLM (canonicalMass (N := N) omega))
    (canonicalExactFreePositionError (N := N)
      kappa beta g hbeta a omega time)
    (canonicalExactFreeMomentumError (N := N)
      kappa beta g hbeta a omega time)

theorem canonicalErrorEnergy_nonneg
    (kappa beta g : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (a : Real) (omega : RandomEnsemble.SampleSpace) (time : Real) :
    0 ≤ canonicalErrorEnergy (N := N)
      kappa beta g hbeta a omega time :=
  harmonicEnergySeminorm_nonneg _ _ _

/-- Physical bond error is bounded by the canonical energy with sharp
constant one. -/
theorem norm_canonicalPhysicalBondError_le_canonicalErrorEnergy
    (kappa beta g : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (a : Real) (omega : RandomEnsemble.SampleSpace) (time : Real) :
    ‖canonicalPhysicalBondError (N := N)
        kappa beta g hbeta a omega time‖ ≤
      canonicalErrorEnergy (N := N)
        kappa beta g hbeta a omega time := by
  rw [← massWeightedBond_canonicalExactFreePositionError]
  exact norm_bond_le_harmonicEnergySeminorm
    (harmonicOperatorCLM (canonicalMass (N := N) omega))
    (harmonicOperatorCLM_isNonnegative
      (canonicalMass (N := N) omega))
    (massWeightedBond (canonicalMass (N := N) omega))
    (fun x => (norm_massWeightedBond_sq
      (canonicalMass (N := N) omega) x).le)
    (canonicalExactFreePositionError (N := N)
      kappa beta g hbeta a omega time)
    (canonicalExactFreeMomentumError (N := N)
      kappa beta g hbeta a omega time)

/-- The actual canonical Duhamel inequality.  Its only analytic side
condition is integrability of the explicit forcing norm. -/
theorem canonicalErrorEnergy_le_intervalIntegral_norm_of_equations
    (kappa beta g : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (a : Real) (omega : RandomEnsemble.SampleSpace)
    (equations : CanonicalExactFreeErrorEquations (N := N)
      kappa beta g hbeta a omega)
    (time : Real) (htime : 0 ≤ time)
    (hforce : IntervalIntegrable
      (fun s => ‖canonicalExactNonlinearForcePath (N := N)
        kappa beta g hbeta a omega s‖) volume 0 time) :
    canonicalErrorEnergy (N := N)
        kappa beta g hbeta a omega time ≤
      ∫ s in 0..time,
        ‖canonicalExactNonlinearForcePath (N := N)
          kappa beta g hbeta a omega s‖ := by
  exact harmonicEnergySeminorm_le_intervalIntegral_norm
    (harmonicOperatorCLM (canonicalMass (N := N) omega))
    (harmonicOperatorCLM_isSelfAdjoint
      (canonicalMass (N := N) omega))
    (harmonicOperatorCLM_isNonnegative
      (canonicalMass (N := N) omega))
    (canonicalExactFreePositionError (N := N)
      kappa beta g hbeta a omega)
    (canonicalExactFreeMomentumError (N := N)
      kappa beta g hbeta a omega)
    (canonicalExactNonlinearForcePath (N := N)
      kappa beta g hbeta a omega)
    time htime equations.position_zero equations.momentum_zero
    (fun s _hs => by
      simpa only [HasMassWeightedDerivAt] using
        equations.position_derivative s)
    (fun s _hs => by
      simpa only [HasMassWeightedDerivAt] using
        equations.momentum_derivative s)
    hforce

/-- The explicit force is strongly measurable.  This follows from the
equation itself and measurability of the derivative; it is not an additional
regularity assumption on the forcing. -/
theorem canonicalExactNonlinearForcePath_aestronglyMeasurable_of_equations
    (kappa beta g : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (a : Real) (omega : RandomEnsemble.SampleSpace)
    (equations : CanonicalExactFreeErrorEquations (N := N)
      kappa beta g hbeta a omega) :
    AEStronglyMeasurable
      (canonicalExactNonlinearForcePath (N := N)
        kappa beta g hbeta a omega) volume := by
  let deltaX := canonicalExactFreePositionError (N := N)
    kappa beta g hbeta a omega
  let deltaY := canonicalExactFreeMomentumError (N := N)
    kappa beta g hbeta a omega
  let force := canonicalExactNonlinearForcePath (N := N)
    kappa beta g hbeta a omega
  let H := harmonicOperatorCLM (canonicalMass (N := N) omega)
  have hXcontinuous : Continuous deltaX :=
    continuous_iff_continuousAt.mpr fun s =>
      (equations.position_derivative s).continuousAt
  have hforceEq : force = fun s => deriv deltaY s + H (deltaX s) := by
    funext s
    have hderiv := (equations.momentum_derivative s).deriv
    change deriv deltaY s = -H (deltaX s) + force s at hderiv
    rw [hderiv]
    abel
  change AEStronglyMeasurable force volume
  rw [hforceEq]
  exact (aestronglyMeasurable_deriv deltaY volume).add
    ((H.continuous.comp hXcontinuous).aestronglyMeasurable)

/-- Uniform lower mass support for the frozen canonical sample. -/
theorem canonicalMass_lower_four_fifths
    (omega : RandomEnsemble.SampleSpace) :
    ∀ i, (4 / 5 : Real) ≤
      (canonicalMass (N := N) omega).mass i := by
  intro i
  simpa [canonicalMass, RandomEnsemble.massLower] using
    (canonicalIIDMassPhaseEnsemble.mass_mem_support i.val omega).1

/-- The N-uniform coefficient multiplying the scalar forcing polynomial. -/
def canonicalDuhamelConstant (kappa beta : Real) : Real :=
  4 * (|kappa| + |beta|)

theorem canonicalDuhamelConstant_nonneg (kappa beta : Real) :
    0 ≤ canonicalDuhamelConstant kappa beta := by
  unfold canonicalDuhamelConstant
  positivity

/-- Pointwise explicit nonlinear-force bound in terms of the canonical error
energy. -/
theorem norm_canonicalExactNonlinearForcePath_le_forcingPolynomial
    (kappa beta g : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (initialAmplitude : Real) (omega : RandomEnsemble.SampleSpace)
    (time aFree EFree R : Real)
    (haFree : 0 ≤ aFree) (hEFree : 0 ≤ EFree) (hR : 0 ≤ R)
    (hfreeSup : ∀ i,
      |bondVector
        (canonicalPhysicalPositionPath (N := N)
          kappa beta 0 hbeta initialAmplitude omega time) i| ≤ aFree)
    (hfreeL2 :
      ‖bondVector
        (canonicalPhysicalPositionPath (N := N)
          kappa beta 0 hbeta initialAmplitude omega time)‖ ≤ EFree)
    (herror :
      canonicalErrorEnergy (N := N)
        kappa beta g hbeta initialAmplitude omega time ≤ R) :
    ‖canonicalExactNonlinearForcePath (N := N)
        kappa beta g hbeta initialAmplitude omega time‖ ≤
      canonicalDuhamelConstant kappa beta *
        forcingPolynomial |g| aFree EFree R := by
  have hbondError :
      ‖bondVector
        (canonicalPhysicalPositionPath (N := N)
            kappa beta g hbeta initialAmplitude omega time -
          canonicalPhysicalPositionPath (N := N)
            kappa beta 0 hbeta initialAmplitude omega time)‖ ≤ R := by
    exact (norm_canonicalPhysicalBondError_le_canonicalErrorEnergy
      (N := N) kappa beta g hbeta initialAmplitude omega time).trans herror
  have hraw :=
    norm_transformedNonlinearForce_le_dilute_free_error
      (canonicalMass (N := N) omega)
      (canonicalMass_lower_four_fifths (N := N) omega)
      kappa beta g
      (canonicalPhysicalPositionPath (N := N)
        kappa beta 0 hbeta initialAmplitude omega time)
      (canonicalPhysicalPositionPath (N := N)
        kappa beta g hbeta initialAmplitude omega time)
      haFree hR hfreeSup hfreeL2 hbondError
  let quadratic := aFree * EFree + 2 * aFree * R + R ^ 2
  let cubic :=
    aFree ^ 2 * EFree + 3 * aFree ^ 2 * R +
      3 * aFree * R ^ 2 + R ^ 3
  have hquadratic : 0 ≤ quadratic := by
    dsimp [quadratic]
    positivity
  have hcubic : 0 ≤ cubic := by
    dsimp [cubic]
    positivity
  have hkappa : |kappa| ≤ |kappa| + |beta| :=
    le_add_of_nonneg_right (abs_nonneg beta)
  have hbetaCoeff : |beta| ≤ |kappa| + |beta| :=
    le_add_of_nonneg_left (abs_nonneg kappa)
  have hquadraticTerm :
      |kappa| * |g| * quadratic ≤
        (|kappa| + |beta|) * |g| * quadratic :=
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hkappa (abs_nonneg g)) hquadratic
  have hcubicTerm :
      |beta| * |g| ^ 2 * cubic ≤
        (|kappa| + |beta|) * |g| ^ 2 * cubic :=
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hbetaCoeff (sq_nonneg |g|)) hcubic
  calc
    ‖canonicalExactNonlinearForcePath (N := N)
        kappa beta g hbeta initialAmplitude omega time‖ ≤
        4 * (|kappa| * |g| * quadratic +
          |beta| * g ^ 2 * cubic) := by
      simpa [canonicalExactNonlinearForcePath, quadratic, cubic] using hraw
    _ = 4 * (|kappa| * |g| * quadratic +
          |beta| * |g| ^ 2 * cubic) := by
      rw [sq_abs]
    _ ≤ 4 * ((|kappa| + |beta|) * |g| * quadratic +
          (|kappa| + |beta|) * |g| ^ 2 * cubic) := by
      exact mul_le_mul_of_nonneg_left
        (add_le_add hquadraticTerm hcubicTerm) (by norm_num)
    _ = canonicalDuhamelConstant kappa beta *
          forcingPolynomial |g| aFree EFree R := by
      unfold canonicalDuhamelConstant forcingPolynomial
      dsimp [quadratic, cubic]
      ring

/-- Prefix bounds make the explicit forcing norm interval-integrable. -/
theorem canonicalForceNorm_intervalIntegrable_of_prefix_bounds
    (kappa beta g : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (initialAmplitude : Real) (omega : RandomEnsemble.SampleSpace)
    (equations : CanonicalExactFreeErrorEquations (N := N)
      kappa beta g hbeta initialAmplitude omega)
    (time aFree EFree R : Real) (htime : 0 ≤ time)
    (haFree : 0 ≤ aFree) (hEFree : 0 ≤ EFree) (hR : 0 ≤ R)
    (hfreeSup : ∀ s ∈ Icc (0 : Real) time, ∀ i,
      |bondVector
        (canonicalPhysicalPositionPath (N := N)
          kappa beta 0 hbeta initialAmplitude omega s) i| ≤ aFree)
    (hfreeL2 : ∀ s ∈ Icc (0 : Real) time,
      ‖bondVector
        (canonicalPhysicalPositionPath (N := N)
          kappa beta 0 hbeta initialAmplitude omega s)‖ ≤ EFree)
    (herror : ∀ s ∈ Icc (0 : Real) time,
      canonicalErrorEnergy (N := N)
        kappa beta g hbeta initialAmplitude omega s ≤ R) :
    IntervalIntegrable
      (fun s => ‖canonicalExactNonlinearForcePath (N := N)
        kappa beta g hbeta initialAmplitude omega s‖)
      volume 0 time := by
  let bound := canonicalDuhamelConstant kappa beta *
    forcingPolynomial |g| aFree EFree R
  have hmeasurable :
      AEStronglyMeasurable
        (fun s => ‖canonicalExactNonlinearForcePath (N := N)
          kappa beta g hbeta initialAmplitude omega s‖)
        (volume.restrict (Ioc (0 : Real) time)) :=
    ((canonicalExactNonlinearForcePath_aestronglyMeasurable_of_equations
      (N := N) kappa beta g hbeta initialAmplitude omega equations).norm).mono_measure
      Measure.restrict_le_self
  have hmeasurableUIoc :
      AEStronglyMeasurable
        (fun s => ‖canonicalExactNonlinearForcePath (N := N)
          kappa beta g hbeta initialAmplitude omega s‖)
        (volume.restrict (uIoc (0 : Real) time)) := by
    rw [uIoc_of_le htime]
    exact hmeasurable
  apply (intervalIntegrable_const :
    IntervalIntegrable (fun _s : Real => bound) volume 0 time).mono_fun'
      hmeasurableUIoc
  rw [uIoc_of_le htime]
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
  have hpoint :=
    norm_canonicalExactNonlinearForcePath_le_forcingPolynomial
      (N := N) kappa beta g hbeta initialAmplitude omega
      s aFree EFree R haFree hEFree hR
      (hfreeSup s ⟨hs.1.le, hs.2⟩)
      (hfreeL2 s ⟨hs.1.le, hs.2⟩)
      (herror s ⟨hs.1.le, hs.2⟩)
  simpa only [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _), bound]
    using hpoint

/-- Actual time-times-polynomial energy inequality under a nonnegative prefix
bound. -/
theorem canonicalErrorEnergy_le_time_mul_forcingPolynomial_of_equations
    (kappa beta g : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (initialAmplitude : Real) (omega : RandomEnsemble.SampleSpace)
    (equations : CanonicalExactFreeErrorEquations (N := N)
      kappa beta g hbeta initialAmplitude omega)
    (time aFree EFree R : Real) (htime : 0 ≤ time)
    (haFree : 0 ≤ aFree) (hEFree : 0 ≤ EFree) (hR : 0 ≤ R)
    (hfreeSup : ∀ s ∈ Icc (0 : Real) time, ∀ i,
      |bondVector
        (canonicalPhysicalPositionPath (N := N)
          kappa beta 0 hbeta initialAmplitude omega s) i| ≤ aFree)
    (hfreeL2 : ∀ s ∈ Icc (0 : Real) time,
      ‖bondVector
        (canonicalPhysicalPositionPath (N := N)
          kappa beta 0 hbeta initialAmplitude omega s)‖ ≤ EFree)
    (herror : ∀ s ∈ Icc (0 : Real) time,
      canonicalErrorEnergy (N := N)
        kappa beta g hbeta initialAmplitude omega s ≤ R) :
    canonicalErrorEnergy (N := N)
        kappa beta g hbeta initialAmplitude omega time ≤
      canonicalDuhamelConstant kappa beta * time *
        forcingPolynomial |g| aFree EFree R := by
  have hforce :=
    canonicalForceNorm_intervalIntegrable_of_prefix_bounds
      (N := N) kappa beta g hbeta initialAmplitude omega equations
      time aFree EFree R htime haFree hEFree hR
      hfreeSup hfreeL2 herror
  have hduhamel :=
    canonicalErrorEnergy_le_intervalIntegral_norm_of_equations
      (N := N) kappa beta g hbeta initialAmplitude omega
      equations time htime hforce
  have hconstant : IntervalIntegrable
      (fun _s : Real =>
        canonicalDuhamelConstant kappa beta *
          forcingPolynomial |g| aFree EFree R)
      volume 0 time :=
    intervalIntegrable_const
  have hmono :
      (∫ s in 0..time,
        ‖canonicalExactNonlinearForcePath (N := N)
          kappa beta g hbeta initialAmplitude omega s‖) ≤
        ∫ _s in 0..time,
          canonicalDuhamelConstant kappa beta *
            forcingPolynomial |g| aFree EFree R := by
    apply intervalIntegral.integral_mono_on htime hforce hconstant
    intro s hs
    exact norm_canonicalExactNonlinearForcePath_le_forcingPolynomial
      (N := N) kappa beta g hbeta initialAmplitude omega
      s aFree EFree R haFree hEFree hR
      (hfreeSup s hs) (hfreeL2 s hs) (herror s hs)
  calc
    canonicalErrorEnergy (N := N)
        kappa beta g hbeta initialAmplitude omega time ≤
        ∫ s in 0..time,
          ‖canonicalExactNonlinearForcePath (N := N)
            kappa beta g hbeta initialAmplitude omega s‖ := hduhamel
    _ ≤ ∫ _s in 0..time,
        canonicalDuhamelConstant kappa beta *
          forcingPolynomial |g| aFree EFree R := hmono
    _ = canonicalDuhamelConstant kappa beta * time *
        forcingPolynomial |g| aFree EFree R := by
      simp
      ring

/-- Prefix domination in exactly the Complete bootstrap interface. -/
theorem canonical_prefixDuhamelDomination_of_equations
    (kappa beta g : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (initialAmplitude : Real) (omega : RandomEnsemble.SampleSpace)
    (equations : CanonicalExactFreeErrorEquations (N := N)
      kappa beta g hbeta initialAmplitude omega)
    (aFree EFree horizon : Real)
    (haFree : 0 ≤ aFree) (hEFree : 0 ≤ EFree)
    (hfreeSup : ∀ s ∈ Icc (0 : Real) horizon, ∀ i,
      |bondVector
        (canonicalPhysicalPositionPath (N := N)
          kappa beta 0 hbeta initialAmplitude omega s) i| ≤ aFree)
    (hfreeL2 : ∀ s ∈ Icc (0 : Real) horizon,
      ‖bondVector
        (canonicalPhysicalPositionPath (N := N)
          kappa beta 0 hbeta initialAmplitude omega s)‖ ≤ EFree) :
    PrefixDuhamelDomination
      (canonicalErrorEnergy (N := N)
        kappa beta g hbeta initialAmplitude omega)
      (canonicalDuhamelConstant kappa beta) |g| aFree EFree horizon := by
  intro time htime R hR hprefix
  exact canonicalErrorEnergy_le_time_mul_forcingPolynomial_of_equations
    (N := N) kappa beta g hbeta initialAmplitude omega equations
    time aFree EFree R htime.1 haFree hEFree hR
    (fun s hs i => hfreeSup s ⟨hs.1, hs.2.trans htime.2⟩ i)
    (fun s hs => hfreeL2 s ⟨hs.1, hs.2.trans htime.2⟩)
    hprefix

/-- Physical realization supplies the equations, hence the Complete prefix
domination, without assuming a Duhamel estimate. -/
theorem canonical_prefixDuhamelDomination_of_physicalRealization
    (hN : 3 ≤ N) {initialAmplitude : Real}
    (hAmplitude0 : 0 ≤ initialAmplitude)
    (hAmplitude1 : initialAmplitude ≤ 1 / 4)
    (kappa beta g : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (omega : RandomEnsemble.SampleSpace)
    (hphysical : PhysicalRealization (N := N)
      kappa beta g hbeta initialAmplitude omega)
    (aFree EFree horizon : Real)
    (haFree : 0 ≤ aFree) (hEFree : 0 ≤ EFree)
    (hfreeSup : ∀ s ∈ Icc (0 : Real) horizon, ∀ i,
      |bondVector
        (canonicalPhysicalPositionPath (N := N)
          kappa beta 0 hbeta initialAmplitude omega s) i| ≤ aFree)
    (hfreeL2 : ∀ s ∈ Icc (0 : Real) horizon,
      ‖bondVector
        (canonicalPhysicalPositionPath (N := N)
          kappa beta 0 hbeta initialAmplitude omega s)‖ ≤ EFree) :
    PrefixDuhamelDomination
      (canonicalErrorEnergy (N := N)
        kappa beta g hbeta initialAmplitude omega)
      (canonicalDuhamelConstant kappa beta) |g| aFree EFree horizon := by
  apply canonical_prefixDuhamelDomination_of_equations
    (N := N) kappa beta g hbeta initialAmplitude omega
    (canonicalExactFreeErrorEquations_of_physicalRealization
      (N := N) hN hAmplitude0 hAmplitude1
      kappa beta g hbeta omega hphysical)
    aFree EFree horizon haFree hEFree hfreeSup hfreeL2

/-! ## Direct V3 scalar-bootstrap compositor -/

/-- The concrete V3 harmonic error energy is continuous whenever the exact
and free paths satisfy the V3 error equations. -/
theorem continuous_canonicalErrorEnergy_of_equations
    (kappa beta g : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (initialAmplitude : Real) (omega : RandomEnsemble.SampleSpace)
    (equations : CanonicalExactFreeErrorEquations (N := N)
      kappa beta g hbeta initialAmplitude omega) :
    Continuous
      (canonicalErrorEnergy (N := N)
        kappa beta g hbeta initialAmplitude omega) := by
  let deltaX := canonicalExactFreePositionError (N := N)
    kappa beta g hbeta initialAmplitude omega
  let deltaY := canonicalExactFreeMomentumError (N := N)
    kappa beta g hbeta initialAmplitude omega
  let H := harmonicOperatorCLM (canonicalMass (N := N) omega)
  have hdeltaX : Continuous deltaX :=
    continuous_iff_continuousAt.mpr fun s =>
      (equations.position_derivative s).continuousAt
  have hdeltaY : Continuous deltaY :=
    continuous_iff_continuousAt.mpr fun s =>
      (equations.momentum_derivative s).continuousAt
  change Continuous (fun time =>
    harmonicEnergySeminorm H (deltaX time) (deltaY time))
  unfold harmonicEnergySeminorm harmonicEnergySq
  exact ((hdeltaY.norm.pow 2).add
    (hdeltaX.inner (H.continuous.comp hdeltaX))).sqrt

/-- The V3 error energy vanishes initially, directly from the exact/free
zero-error equations. -/
theorem canonicalErrorEnergy_zero_of_equations
    (kappa beta g : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (initialAmplitude : Real) (omega : RandomEnsemble.SampleSpace)
    (equations : CanonicalExactFreeErrorEquations (N := N)
      kappa beta g hbeta initialAmplitude omega) :
    canonicalErrorEnergy (N := N)
      kappa beta g hbeta initialAmplitude omega 0 = 0 := by
  unfold canonicalErrorEnergy
  rw [equations.position_zero, equations.momentum_zero]
  simp [harmonicEnergySeminorm, harmonicEnergySq]

/-- Coefficient-faithful microscopic stability on the full inverse-square
window.  The only pathwise inputs beyond the actual V3 equations are the
free-bond dilute bounds `sup_i |r_i| <= g^4` and `‖r‖_2 <= EFree <= C`.
Every constant is independent of `N`. -/
theorem canonicalErrorEnergy_le_kineticScale_of_equations
    (kappa beta : Real) (g C T : Real)
    (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (initialAmplitude : Real) (omega : RandomEnsemble.SampleSpace)
    (equations : CanonicalExactFreeErrorEquations (N := N)
      kappa beta g hbeta initialAmplitude omega)
    (hg : 0 < g) (hC : 0 <= C) (hT : 0 <= T)
    (hgSmall : g <= couplingThreshold
      (canonicalDuhamelConstant kappa beta) C T)
    (EFree : Real) (hEFree0 : 0 <= EFree) (hEFreeC : EFree <= C)
    (hfreeSup : ∀ s ∈ Icc (0 : Real) (T / g ^ 2), ∀ i,
      |bondVector
        (canonicalPhysicalPositionPath (N := N)
          kappa beta 0 hbeta initialAmplitude omega s) i| <= g ^ 4)
    (hfreeL2 : ∀ s ∈ Icc (0 : Real) (T / g ^ 2),
      ‖bondVector
        (canonicalPhysicalPositionPath (N := N)
          kappa beta 0 hbeta initialAmplitude omega s)‖ <= EFree) :
    ∀ time ∈ Icc (0 : Real) (T / g ^ 2),
      canonicalErrorEnergy (N := N)
          kappa beta g hbeta initialAmplitude omega time <=
        kineticConstant (canonicalDuhamelConstant kappa beta) C T * g ^ 3 := by
  have hK : 0 <= canonicalDuhamelConstant kappa beta :=
    canonicalDuhamelConstant_nonneg kappa beta
  have hdomAbs : PrefixDuhamelDomination
      (canonicalErrorEnergy (N := N)
        kappa beta g hbeta initialAmplitude omega)
      (canonicalDuhamelConstant kappa beta) |g| (g ^ 4) EFree
      (T / g ^ 2) := by
    apply canonical_prefixDuhamelDomination_of_equations
      (N := N) kappa beta g hbeta initialAmplitude omega equations
      (g ^ 4) EFree (T / g ^ 2) (pow_nonneg hg.le 4) hEFree0
      hfreeSup hfreeL2
  have hdom : PrefixDuhamelDomination
      (canonicalErrorEnergy (N := N)
        kappa beta g hbeta initialAmplitude omega)
      (canonicalDuhamelConstant kappa beta) g (g ^ 4) EFree
      (T / g ^ 2) := by
    simpa only [abs_of_pos hg] using hdomAbs
  exact dilute_bootstrap_closure_of_prefix_domination
    hK hC hT hg hgSmall rfl hEFree0 hEFreeC
    (continuous_canonicalErrorEnergy_of_equations
      (N := N) kappa beta g hbeta initialAmplitude omega equations)
    (canonicalErrorEnergy_zero_of_equations
      (N := N) kappa beta g hbeta initialAmplitude omega equations)
    hdom

/-- Actual-flow form of the microscopic stability theorem.  The trajectory
premise is the repository's existing `PhysicalRealization`; the V3 bridge
produces the exact/free equations rather than assuming them. -/
theorem canonicalErrorEnergy_le_kineticScale_of_physicalRealization
    (hN : 3 <= N) (kappa beta : Real) (g C T : Real)
    (hbeta : 2 * kappa ^ 2 / 9 < beta)
    {initialAmplitude : Real}
    (hAmplitude0 : 0 <= initialAmplitude)
    (hAmplitude1 : initialAmplitude <= 1 / 4)
    (omega : RandomEnsemble.SampleSpace)
    (hphysical : PhysicalRealization (N := N)
      kappa beta g hbeta initialAmplitude omega)
    (hg : 0 < g) (hC : 0 <= C) (hT : 0 <= T)
    (hgSmall : g <= couplingThreshold
      (canonicalDuhamelConstant kappa beta) C T)
    (EFree : Real) (hEFree0 : 0 <= EFree) (hEFreeC : EFree <= C)
    (hfreeSup : ∀ s ∈ Icc (0 : Real) (T / g ^ 2), ∀ i,
      |bondVector
        (canonicalPhysicalPositionPath (N := N)
          kappa beta 0 hbeta initialAmplitude omega s) i| <= g ^ 4)
    (hfreeL2 : ∀ s ∈ Icc (0 : Real) (T / g ^ 2),
      ‖bondVector
        (canonicalPhysicalPositionPath (N := N)
          kappa beta 0 hbeta initialAmplitude omega s)‖ <= EFree) :
    ∀ time ∈ Icc (0 : Real) (T / g ^ 2),
      canonicalErrorEnergy (N := N)
          kappa beta g hbeta initialAmplitude omega time <=
        kineticConstant (canonicalDuhamelConstant kappa beta) C T * g ^ 3 := by
  apply canonicalErrorEnergy_le_kineticScale_of_equations
    kappa beta g C T hbeta initialAmplitude omega
    (canonicalExactFreeErrorEquations_of_physicalRealization
      (N := N) hN hAmplitude0 hAmplitude1
      kappa beta g hbeta omega hphysical)
    hg hC hT hgSmall EFree hEFree0 hEFreeC hfreeSup hfreeL2

#print axioms harmonicOperatorCLM_isSelfAdjoint
#print axioms harmonicOperatorCLM_isNonnegative
#print axioms canonicalErrorEnergy_le_intervalIntegral_norm_of_equations
#print axioms canonical_prefixDuhamelDomination_of_physicalRealization
#print axioms canonicalErrorEnergy_le_kineticScale_of_physicalRealization

end

end ArchonPhysics.R32CanonicalDuhamelForceBridgeV3
