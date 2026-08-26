import ArchonPhysics.ConcreteHamiltonGradients
import ArchonPhysics.ModalForcedDynamics
import ArchonPhysics.ModalNonlinearForce

/-!
# Mass-weighted explicit Hamiltonian dynamics

This module connects the concrete stabilized lattice Hamilton equations to the
mass-weighted harmonic operator.  It uses

`X = sqrt(M) q`, `Y = M^(-1/2) p`

and proves that derivative witnesses for the explicit Hamilton equations imply
`X' = Y` and

`Y' = -H X + G_nl`.

The nonlinear force `G_nl` is defined before the evolution theorem as the
inverse-square-root mass transform of the explicit quadratic/cubic bond
gradient.  It is not defined from `Y' + H X`.  Its modal projection is then
identified with the existing finite bond-polynomial and interaction-tensor
forcing API.  No solution-existence, limiting, resonance, or thermalization
claim is made.
-/

namespace ArchonPhysics.MassWeightedHamiltonianDynamics

open ArchonPhysics
open ArchonPhysics.CoerciveHamiltonianPhyslib
open ArchonPhysics.ConcreteHamiltonGradients
open ArchonPhysics.HarmonicModes
open ArchonPhysics.ModalForcedDynamics
open ArchonPhysics.ModalNonlinearForce
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.ModeCoupling
open ArchonPhysics.ReducedModeTransform
open scoped InnerProductSpace RealInnerProductSpace

noncomputable section

/-- Multiplication by `sqrt(M)` as a finite-dimensional linear map. -/
def sqrtMassLinearMap {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) :
    HilbertConfiguration N →ₗ[Real] WeightedConfiguration N :=
  Matrix.toLpLin 2 2 (Matrix.diagonal fun i => Real.sqrt (m.mass i))

/-- Multiplication by `M^(-1/2)` as a finite-dimensional linear map. -/
def inverseSqrtMassLinearMap {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) :
    HilbertConfiguration N →ₗ[Real] WeightedConfiguration N :=
  Matrix.toLpLin 2 2
    (Matrix.diagonal fun i => (Real.sqrt (m.mass i))⁻¹)

/-- Continuous `sqrt(M)` action obtained from finite dimensionality. -/
def sqrtMassTransform {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) :
    HilbertConfiguration N →L[Real] WeightedConfiguration N :=
  LinearMap.toContinuousLinearMap (sqrtMassLinearMap m)

/-- Continuous `M^(-1/2)` action obtained from finite dimensionality. -/
def inverseSqrtMassTransform {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) :
    HilbertConfiguration N →L[Real] WeightedConfiguration N :=
  LinearMap.toContinuousLinearMap (inverseSqrtMassLinearMap m)

@[simp] theorem sqrtMassTransform_apply {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (q : HilbertConfiguration N)
    (i : Lattice.Site N) :
    sqrtMassTransform m q i = Real.sqrt (m.mass i) * q i := by
  change Matrix.mulVec (Matrix.diagonal fun i => Real.sqrt (m.mass i))
    (WithLp.ofLp q) i = _
  rw [Matrix.mulVec_diagonal]

@[simp] theorem inverseSqrtMassTransform_apply {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (p : HilbertConfiguration N)
    (i : Lattice.Site N) :
    inverseSqrtMassTransform m p i =
      (Real.sqrt (m.mass i))⁻¹ * p i := by
  change Matrix.mulVec
    (Matrix.diagonal fun i => (Real.sqrt (m.mass i))⁻¹)
    (WithLp.ofLp p) i = _
  rw [Matrix.mulVec_diagonal]

/-- The bundled transform agrees exactly with `Lattice.sqrtMassAction`. -/
theorem sqrtMassTransform_eq_latticeAction {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (q : HilbertConfiguration N) :
    sqrtMassTransform m q =
      WithLp.toLp 2 (Lattice.sqrtMassAction m (asConfiguration q)) := by
  ext i
  simp [Lattice.sqrtMassAction, asConfiguration]

/-- The bundled transform agrees exactly with
`Lattice.inverseSqrtMassAction`. -/
theorem inverseSqrtMassTransform_eq_latticeAction
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (p : HilbertConfiguration N) :
    inverseSqrtMassTransform m p =
      WithLp.toLp 2
        (Lattice.inverseSqrtMassAction m (asConfiguration p)) := by
  ext i
  simp [Lattice.inverseSqrtMassAction, asConfiguration]

/-- Applying `sqrt(M)` to the inverse-mass Hamiltonian velocity gives
`M^(-1/2) p`. -/
theorem sqrtMassTransform_inverseMassMomentum {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (p : HilbertConfiguration N) :
    sqrtMassTransform m (inverseMassMomentum m p) =
      inverseSqrtMassTransform m p := by
  ext i
  simp only [sqrtMassTransform_apply, inverseMassMomentum_apply,
    inverseSqrtMassTransform_apply]
  have hs : Real.sqrt (m.mass i) ≠ 0 :=
    Real.sqrt_ne_zero'.2 (m.mass_pos i)
  have hm : m.mass i ≠ 0 := ne_of_gt (m.mass_pos i)
  have hscalar :
      Real.sqrt (m.mass i) * (m.mass i)⁻¹ =
        (Real.sqrt (m.mass i))⁻¹ := by
    field_simp [hs, hm]
    rw [Real.sq_sqrt (le_of_lt (m.mass_pos i))]
  calc
    Real.sqrt (m.mass i) * ((m.mass i)⁻¹ * p i) =
        (Real.sqrt (m.mass i) * (m.mass i)⁻¹) * p i := by ring
    _ = _ := by rw [hscalar]

/-- The polynomial part of the bond derivative beyond its harmonic term. -/
def nonlinearPotentialDerivative (kappa beta g x : Real) : Real :=
  kappa * g * x ^ 2 + beta * g ^ 2 * x ^ 3

/-- Exact harmonic/nonlinear split of the stabilized potential derivative. -/
theorem potentialDerivative_eq_harmonic_add_nonlinear
    (kappa beta g x : Real) :
    potentialDerivative kappa beta g x =
      x + nonlinearPotentialDerivative kappa beta g x := by
  unfold potentialDerivative nonlinearPotentialDerivative
  ring

/-- Explicit harmonic bond gradient, before mass weighting. -/
def harmonicPotentialGradient {N : Nat} [NeZero N]
    (q : HilbertConfiguration N) : HilbertConfiguration N :=
  ∑ i : Lattice.Site N,
    Lattice.forwardDifference (asConfiguration q) i • bondDirection i

/-- Explicit quadratic/cubic residual bond gradient, before mass weighting. -/
def nonlinearPotentialGradient {N : Nat} [NeZero N]
    (kappa beta g : Real)
    (q : HilbertConfiguration N) : HilbertConfiguration N :=
  ∑ i : Lattice.Site N,
    nonlinearPotentialDerivative kappa beta g
        (Lattice.forwardDifference (asConfiguration q) i) •
      bondDirection i

/-- The concrete potential gradient is exactly harmonic plus its explicit
quadratic/cubic residual. -/
theorem potentialGradient_eq_harmonic_add_nonlinear
    {N : Nat} [NeZero N] (kappa beta g : Real)
    (q : HilbertConfiguration N) :
    potentialGradient kappa beta g q =
      harmonicPotentialGradient q +
        nonlinearPotentialGradient kappa beta g q := by
  unfold potentialGradient harmonicPotentialGradient
    nonlinearPotentialGradient
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [potentialDerivative_eq_harmonic_add_nonlinear, add_smul]

/-- A bond direction is one row of the periodic difference matrix. -/
theorem bondDirection_apply_eq_differenceMatrix
    {N : Nat} [NeZero N] (i j : Lattice.Site N) :
    bondDirection i j = differenceMatrix i j := by
  simp [bondDirection, differenceMatrix]

/-- The explicit harmonic bond gradient is the Gram action `D transpose D`. -/
theorem harmonicPotentialGradient_eq_differenceGram
    {N : Nat} [NeZero N] (q : HilbertConfiguration N) :
    harmonicPotentialGradient q =
      WithLp.toLp 2
        (Matrix.mulVec
          (Matrix.transpose (differenceMatrix (N := N)) * differenceMatrix)
          (WithLp.ofLp q)) := by
  ext j
  simp only [harmonicPotentialGradient, WithLp.ofLp_sum,
    WithLp.ofLp_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [← Matrix.mulVec_mulVec, differenceMatrix_mulVec]
  simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply]
  apply Finset.sum_congr rfl
  intro i hi
  rw [bondDirection_apply_eq_differenceMatrix]
  rw [show asConfiguration q = WithLp.ofLp q by rfl]
  ring

/-- After the two square-root mass transforms, the explicit harmonic gradient
is exactly the existing mass-weighted harmonic operator. -/
theorem inverseSqrtMassTransform_harmonicPotentialGradient
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (q : HilbertConfiguration N) :
    inverseSqrtMassTransform m (harmonicPotentialGradient q) =
      harmonicOperator m (sqrtMassTransform m q) := by
  rw [harmonicPotentialGradient_eq_differenceGram]
  ext j
  change Matrix.mulVec
      (Matrix.diagonal fun i => (Real.sqrt (m.mass i))⁻¹)
      (Matrix.mulVec
        (Matrix.transpose differenceMatrix * differenceMatrix)
        (WithLp.ofLp q)) j =
    Matrix.mulVec (massWeightedHarmonicMatrix m)
      (Matrix.mulVec
        (Matrix.diagonal fun i => Real.sqrt (m.mass i))
        (WithLp.ofLp q)) j
  have hcancel :
      Matrix.mulVec
          (Matrix.diagonal fun i => (Real.sqrt (m.mass i))⁻¹)
          (Matrix.mulVec
            (Matrix.diagonal fun i => Real.sqrt (m.mass i))
            (WithLp.ofLp q)) =
        WithLp.ofLp q := by
    ext i
    simp only [Matrix.mulVec_diagonal]
    have hs : Real.sqrt (m.mass i) ≠ 0 :=
      Real.sqrt_ne_zero'.2 (m.mass_pos i)
    field_simp
  unfold massWeightedHarmonicMatrix massWeightedDifferenceMatrix
  rw [Matrix.transpose_mul, Matrix.diagonal_transpose]
  simp only [← Matrix.mulVec_mulVec]
  rw [hcancel]

/-- The nonlinear forcing in mass-weighted configuration coordinates.  Its
definition is the explicit transformed residual gradient, including the
Hamiltonian minus sign. -/
def transformedNonlinearForce {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa beta g : Real)
    (q : HilbertConfiguration N) : WeightedConfiguration N :=
  -inverseSqrtMassTransform m
    (nonlinearPotentialGradient kappa beta g q)

/-- The transformed full potential force is harmonic plus the independently
defined explicit nonlinear forcing. -/
theorem transformedPotentialForce_eq_harmonic_add_nonlinear
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa beta g : Real)
    (q : HilbertConfiguration N) :
    inverseSqrtMassTransform m (-potentialGradient kappa beta g q) =
      -harmonicOperator m (sqrtMassTransform m q) +
        transformedNonlinearForce m kappa beta g q := by
  rw [potentialGradient_eq_harmonic_add_nonlinear]
  simp only [map_neg, map_add]
  rw [inverseSqrtMassTransform_harmonicPotentialGradient]
  simp only [transformedNonlinearForce]
  abel

/-- The mass-weighted position path `X = sqrt(M) q`. -/
def massWeightedPosition {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N)
    (q : Real → HilbertConfiguration N) :
    Real → WeightedConfiguration N :=
  fun t => sqrtMassTransform m (q t)

/-- The mass-weighted momentum path `Y = M^(-1/2) p`. -/
def massWeightedMomentum {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N)
    (p : Real → HilbertConfiguration N) :
    Real → WeightedConfiguration N :=
  fun t => inverseSqrtMassTransform m (p t)

@[simp] theorem massWeightedPosition_apply
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N)
    (q : Real → HilbertConfiguration N) (t : Real) (i : Lattice.Site N) :
    massWeightedPosition m q t i = Real.sqrt (m.mass i) * q t i := by
  exact sqrtMassTransform_apply m (q t) i

@[simp] theorem massWeightedMomentum_apply
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N)
    (p : Real → HilbertConfiguration N) (t : Real) (i : Lattice.Site N) :
    massWeightedMomentum m p t i =
      (Real.sqrt (m.mass i))⁻¹ * p t i := by
  exact inverseSqrtMassTransform_apply m (p t) i

/-- Derivative predicate with the canonical PiLp normed additive and module
instances fixed explicitly.  This avoids exposing the reducible WithLp
representation of EuclideanSpace to instance synthesis. -/
def HasMassWeightedDerivAt {N : Nat} [NeZero N]
    (f : Real → WeightedConfiguration N)
    (f' : WeightedConfiguration N) (t : Real) : Prop :=
  letI : AddCommGroup (WeightedConfiguration N) :=
    (PiLp.normedAddCommGroup 2 (fun _ : Lattice.Site N => Real)).toAddCommGroup
  letI : Module Real (WeightedConfiguration N) :=
    (PiLp.normedSpace 2 Real (fun _ : Lattice.Site N => Real)).toModule
  let canonicalPseudoMetricSpace :
      PseudoMetricSpace (WeightedConfiguration N) :=
    (PiLp.normedAddCommGroup 2
      (fun _ : Lattice.Site N => Real)).toPseudoMetricSpace
  letI : TopologicalSpace (WeightedConfiguration N) :=
    canonicalPseudoMetricSpace.toUniformSpace.toTopologicalSpace
  HasDerivAt f f' t

/-- Explicit Hamilton dynamics with actual derivative witnesses.  This is the
differentiable refinement of the formula-level equations exposed by
`satisfiesHamiltonEquations_iff_explicit`. -/
def HasExplicitHamiltonDerivatives {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa beta g : Real)
    (p q : Real → HilbertConfiguration N) : Prop :=
  ∀ t,
    HasDerivAt q (inverseMassMomentum m (p t)) t ∧
      HasDerivAt p (-potentialGradient kappa beta g (q t)) t

/-- Explicit Hamilton derivative witnesses imply the exact mass-weighted
forced harmonic equations `X' = Y`, `Y' = -H X + G_nl`. -/
theorem massWeightedEquations_of_explicitHamiltonDerivatives
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa beta g : Real)
    {p q : Real → HilbertConfiguration N}
    (hDynamics : HasExplicitHamiltonDerivatives m kappa beta g p q)
    (t : Real) :
    HasMassWeightedDerivAt (massWeightedPosition m q)
        (massWeightedMomentum m p t) t ∧
      HasMassWeightedDerivAt (massWeightedMomentum m p)
        (-harmonicOperator m (massWeightedPosition m q t) +
          transformedNonlinearForce m kappa beta g (q t)) t := by
  constructor
  · have hX := (sqrtMassTransform m).hasFDerivAt.comp_hasDerivAt
      t (hDynamics t).1
    change HasMassWeightedDerivAt (fun s => sqrtMassTransform m (q s))
      (inverseSqrtMassTransform m (p t)) t
    simpa only [HasMassWeightedDerivAt,
      Function.comp_def, sqrtMassTransform_inverseMassMomentum] using hX
  · have hY := (inverseSqrtMassTransform m).hasFDerivAt.comp_hasDerivAt
      t (hDynamics t).2
    change HasMassWeightedDerivAt (fun s => inverseSqrtMassTransform m (p s))
      (-harmonicOperator m (sqrtMassTransform m (q t)) +
        transformedNonlinearForce m kappa beta g (q t)) t
    simpa only [HasMassWeightedDerivAt,
      Function.comp_def, transformedPotentialForce_eq_harmonic_add_nonlinear] using hY

/-- One inverse-weighted bond direction projects to the existing
`bondModeCoefficient`. -/
theorem modalCoordinates_inverseSqrtMassTransform_bondDirection
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (j k : Lattice.Site N) :
    modalCoordinates m
        (inverseSqrtMassTransform m (bondDirection j)) k =
      bondModeCoefficient m j k := by
  rw [modalCoordinates_apply, bondModeCoefficient_eq_forwardDifference]
  simp only [bondDirection, map_sub, PiLp.inner_apply, PiLp.sub_apply,
    inverseSqrtMassTransform_apply, PiLp.single_apply, mul_comm, ite_mul,
    one_mul, zero_mul, RCLike.inner_apply, Real.ringHom_apply,
    Lattice.forwardDifference, Lattice.inverseSqrtMassAction]
  simp_rw [sub_mul]
  rw [Finset.sum_sub_distrib]
  simp

/-- Modal reconstruction of `sqrt(M) q`, followed by inverse mass weighting,
returns the original physical configuration. -/
theorem physicalReconstruction_modalCoordinates_sqrtMassTransform
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (q : HilbertConfiguration N) :
    physicalReconstruction m
        (modalCoordinates m (sqrtMassTransform m q)) =
      asConfiguration q := by
  unfold physicalReconstruction
  rw [reconstruct_modalCoordinates]
  ext i
  simp only [Lattice.inverseSqrtMassAction, sqrtMassTransform_apply]
  have hs : Real.sqrt (m.mass i) ≠ 0 :=
    Real.sqrt_ne_zero'.2 (m.mass_pos i)
  field_simp
  rfl

/-- Projection of the explicit transformed nonlinear gradient is precisely the
finite bond-polynomial force already expanded by `ModalNonlinearForce`. -/
theorem modalCoordinates_transformedNonlinearForce
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa beta g : Real)
    (q : HilbertConfiguration N) (k : Lattice.Site N) :
    modalCoordinates m
        (transformedNonlinearForce m kappa beta g q) k =
      projectedNonlinearBondForce m kappa beta g
        (modalCoordinates m (sqrtMassTransform m q)) k := by
  unfold transformedNonlinearForce nonlinearPotentialGradient
  simp only [map_neg, map_sum, map_smul, WithLp.ofLp_neg,
    WithLp.ofLp_sum, WithLp.ofLp_smul, Pi.neg_apply,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  simp_rw [modalCoordinates_inverseSqrtMassTransform_bondDirection]
  unfold projectedNonlinearBondForce distinguishedBondPolynomial
    nonlinearPotentialDerivative
  rw [physicalReconstruction_modalCoordinates_sqrtMassTransform]
  rw [Finset.mul_sum, Finset.mul_sum]
  simp_rw [add_mul]
  rw [Finset.sum_add_distrib]
  simp only [mul_assoc, mul_comm]
  abel

/-- The explicit mass-weighted Hamilton dynamics project to the scalar forced
oscillator equation with the verified nonlinear bond-polynomial force. -/
theorem modalScalarEquations_of_explicitHamiltonDerivatives
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa beta g : Real)
    (k : Lattice.Site N) {p q : Real → HilbertConfiguration N}
    (hDynamics : HasExplicitHamiltonDerivatives m kappa beta g p q)
    (t : Real) :
    HasDerivAt
        (fun s => modalCoordinates m (massWeightedPosition m q s) k)
        (modalCoordinates m (massWeightedMomentum m p t) k) t ∧
      HasDerivAt
        (fun s => modalCoordinates m (massWeightedMomentum m p s) k)
        (-(modeFrequency m k) ^ 2 *
            modalCoordinates m (massWeightedPosition m q t) k +
          projectedNonlinearBondForce m kappa beta g
            (modalCoordinates m (massWeightedPosition m q t)) k) t := by
  have hWeighted := massWeightedEquations_of_explicitHamiltonDerivatives
    m kappa beta g hDynamics t
  have hX := hWeighted.1
  have hY := hWeighted.2
  simp only [HasMassWeightedDerivAt] at hX hY
  have hModal := modalEquations_of_forcedDynamics m k
    (G := fun s => transformedNonlinearForce m kappa beta g (q s))
    hX hY
  refine ⟨hModal.1, ?_⟩
  convert hModal.2 using 1
  rw [massWeightedPosition, modalCoordinates_transformedNonlinearForce]

/-- Equivalent scalar equation with the nonlinear forcing written as the
existing exact three- and four-leg tensor contractions. -/
theorem modalScalarTensorEquations_of_explicitHamiltonDerivatives
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa beta g : Real)
    (k : Lattice.Site N) {p q : Real → HilbertConfiguration N}
    (hDynamics : HasExplicitHamiltonDerivatives m kappa beta g p q)
    (t : Real) :
    HasDerivAt
        (fun s => modalCoordinates m (massWeightedPosition m q s) k)
        (modalCoordinates m (massWeightedMomentum m p t) k) t ∧
      HasDerivAt
        (fun s => modalCoordinates m (massWeightedMomentum m p s) k)
        (-(modeFrequency m k) ^ 2 *
            modalCoordinates m (massWeightedPosition m q t) k +
          tensorNonlinearForce m kappa beta g
            (modalCoordinates m (massWeightedPosition m q t)) k) t := by
  have hModal := modalScalarEquations_of_explicitHamiltonDerivatives
    m kappa beta g k hDynamics t
  refine ⟨hModal.1, ?_⟩
  convert hModal.2 using 1
  rw [projectedNonlinearBondForce_eq_tensorNonlinearForce]

end

end ArchonPhysics.MassWeightedHamiltonianDynamics
