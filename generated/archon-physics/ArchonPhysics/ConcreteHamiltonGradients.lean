import ArchonPhysics.CoerciveHamiltonianPhyslib
import Physlib.ClassicalMechanics.HarmonicOscillator.Basic

/-!
# Concrete gradients for the stabilized lattice Hamiltonian

This module lowers the Physlib Hamilton-equation adapter to explicit finite-
lattice gradients.  The assembly uses Mathlib's `HasFDerivAt.fun_sum` and
Fréchet chain rule, together with Physlib's Euclidean gradient infrastructure.
-/

namespace ArchonPhysics.ConcreteHamiltonGradients

open InnerProductSpace
open CoerciveCubicPotential
open CoerciveHamiltonianPhyslib
open Time

noncomputable section

/-- A finite sum of gradient witnesses is again a gradient witness. -/
theorem hasGradientAt_finset_sum
    {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
    [CompleteSpace E]
    {s : Finset ι} {f : ι → E → Real} {f' : ι → E} {x : E}
    (h : ∀ i ∈ s, HasGradientAt (f i) (f' i) x) :
    HasGradientAt (fun y => ∑ i ∈ s, f i y) (∑ i ∈ s, f' i) x := by
  classical
  rw [hasGradientAt_iff_hasFDerivAt]
  simpa only [map_sum] using
    (HasFDerivAt.fun_sum fun i hi => (h i hi).hasFDerivAt)

/-- Chain rule for a scalar function after a Riesz-represented linear functional. -/
theorem HasDerivAt.hasGradientAt_comp_clm
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
    [CompleteSpace E] {f : Real → Real} {f' : Real}
    (L : E →L[Real] Real) (v x : E)
    (hL : L = InnerProductSpace.toDual Real E v)
    (hf : HasDerivAt f f' (L x)) :
    HasGradientAt (f ∘ L) (f' • v) x := by
  have hcomp := hf.comp_hasFDerivAt x L.hasFDerivAt
  have hcanonical := hcomp.differentiableAt.hasGradientAt
  have hgradient : gradient (f ∘ L) x = f' • v := by
    refine ext_inner_right (𝕜 := Real) fun y => ?_
    rw [← hcanonical.fderiv_apply, hcomp.fderiv]
    simp [hL, InnerProductSpace.toDual_apply_apply, real_inner_smul_left]
  rw [hgradient] at hcanonical
  exact hcanonical

/-- Derivative of the stabilized cubic-leading bond potential. -/
def potentialDerivative (kappa beta g x : Real) : Real :=
  x + kappa * g * x ^ 2 + beta * g ^ 2 * x ^ 3

/-- The polynomial derivative formula, proved from Mathlib's one-variable rules. -/
theorem hasDerivAt_potential (kappa beta g x : Real) :
    HasDerivAt (potential kappa beta g)
      (potentialDerivative kappa beta g x) x := by
  have hd : DifferentiableAt Real (potential kappa beta g) x := by
    unfold potential
    fun_prop
  apply hd.hasDerivAt.congr_deriv
  unfold potential potentialDerivative
  rw [deriv_fun_add (by fun_prop) (by fun_prop)]
  rw [deriv_fun_add (by fun_prop) (by fun_prop)]
  rw [deriv_div_const, deriv_const_mul_field, deriv_const_mul_field]
  simp only [deriv_pow_field]
  norm_num
  ring

/-- The Euclidean inverse-mass velocity vector. -/
def inverseMassMomentum {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (p : HilbertConfiguration N) : HilbertConfiguration N :=
  WithLp.toLp 2 fun i => (m.mass i)⁻¹ * p i

@[simp]
theorem inverseMassMomentum_apply {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (p : HilbertConfiguration N)
    (i : Lattice.Site N) :
    inverseMassMomentum m p i = (m.mass i)⁻¹ * p i := by
  rfl

/-- The directional vector associated with the forward bond at `i`. -/
def bondDirection {N : Nat} [NeZero N]
    (i : Lattice.Site N) : HilbertConfiguration N :=
  EuclideanSpace.single (i + 1) 1 - EuclideanSpace.single i 1

/-- The forward bond difference as a continuous linear functional. -/
def bondFunctional {N : Nat} [NeZero N] (i : Lattice.Site N) :
    HilbertConfiguration N →L[Real] Real :=
  EuclideanSpace.proj (𝕜 := Real) (i + 1) - EuclideanSpace.proj (𝕜 := Real) i

@[simp]
theorem bondFunctional_apply {N : Nat} [NeZero N] (i : Lattice.Site N)
    (q : HilbertConfiguration N) :
    bondFunctional i q = Lattice.forwardDifference (asConfiguration q) i := by
  simp [bondFunctional, Lattice.forwardDifference, asConfiguration]

/-- The bond functional is represented by its two-site Euclidean direction. -/
theorem bondFunctional_eq_toDual {N : Nat} [NeZero N] (i : Lattice.Site N) :
    bondFunctional i =
      InnerProductSpace.toDual Real (HilbertConfiguration N) (bondDirection i) := by
  ext q
  simp [bondFunctional, bondDirection, EuclideanSpace.inner_single_left]

/-- Explicit finite sum representing the gradient of the bond potential energy. -/
def potentialGradient {N : Nat} [NeZero N] (kappa beta g : Real)
    (q : HilbertConfiguration N) : HilbertConfiguration N :=
  ∑ i : Lattice.Site N,
    potentialDerivative kappa beta g
        (Lattice.forwardDifference (asConfiguration q) i) •
      bondDirection i

/-- The kinetic-energy gradient is the inverse-mass momentum vector. -/
theorem hasGradientAt_kineticEnergy {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (p : HilbertConfiguration N) :
    HasGradientAt
      (fun y : HilbertConfiguration N =>
        Lattice.kineticEnergy m (asConfiguration y))
      (inverseMassMomentum m p) p := by
  have hterms : ∀ i : Lattice.Site N,
      HasGradientAt
        (fun y : HilbertConfiguration N => y i ^ 2 / (2 * m.mass i))
        (((m.mass i)⁻¹ * p i) • EuclideanSpace.single i 1) p := by
    intro i
    have hm_ne : m.mass i ≠ 0 := ne_of_gt (m.mass_pos i)
    have hscalar : HasDerivAt (fun x : Real => x ^ 2 / (2 * m.mass i))
        ((m.mass i)⁻¹ * p i) (p i) := by
      have hd : DifferentiableAt Real
          (fun x : Real => x ^ 2 / (2 * m.mass i)) (p i) := by
        fun_prop
      apply hd.hasDerivAt.congr_deriv
      rw [deriv_div_const, deriv_pow_field]
      norm_num
      field_simp [hm_ne]
    have hdiff : DifferentiableAt Real
        (fun y : HilbertConfiguration N => y i ^ 2 / (2 * m.mass i)) p := by
      fun_prop
    have hgradient := gradient_comp_coord i p hscalar
    have hhas := hdiff.hasGradientAt
    rw [hgradient] at hhas
    exact hhas
  have hsum := hasGradientAt_finset_sum
    (E := HilbertConfiguration N) (ι := Lattice.Site N)
    (s := Finset.univ)
    (f := fun (i : Lattice.Site N) (y : HilbertConfiguration N) =>
      y i ^ 2 / (2 * m.mass i))
    (f' := fun (i : Lattice.Site N) =>
      ((m.mass i)⁻¹ * p i) • EuclideanSpace.single i 1)
    (x := p) (fun i _ => hterms i)
  change HasGradientAt
    (fun y : HilbertConfiguration N =>
      ∑ i : Lattice.Site N, y i ^ 2 / (2 * m.mass i))
    (inverseMassMomentum m p) p
  convert hsum using 1
  ext j
  simp [Pi.single_apply]

/-- Formula for the Physlib/Mathlib gradient of the finite kinetic energy. -/
theorem gradient_kineticEnergy {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (p : HilbertConfiguration N) :
    gradient
      (fun y : HilbertConfiguration N =>
        Lattice.kineticEnergy m (asConfiguration y)) p =
      inverseMassMomentum m p :=
  (hasGradientAt_kineticEnergy m p).gradient

/-- Each bond term has the expected two-site gradient. -/
theorem hasGradientAt_bondPotential {N : Nat} [NeZero N]
    (kappa beta g : Real) (q : HilbertConfiguration N)
    (i : Lattice.Site N) :
    HasGradientAt
      (fun y : HilbertConfiguration N =>
        potential kappa beta g
          (Lattice.forwardDifference (asConfiguration y) i))
      (potentialDerivative kappa beta g
          (Lattice.forwardDifference (asConfiguration q) i) • bondDirection i) q := by
  have h := HasDerivAt.hasGradientAt_comp_clm
    (bondFunctional i) (bondDirection i) q (bondFunctional_eq_toDual i)
    (hasDerivAt_potential kappa beta g (bondFunctional i q))
  apply h.congr_of_eventuallyEq
  exact Filter.Eventually.of_forall fun y => by
    simp

/-- The potential-energy gradient is the sum of the explicit bond gradients. -/
theorem hasGradientAt_potentialEnergy {N : Nat} [NeZero N]
    (kappa beta g : Real) (q : HilbertConfiguration N) :
    HasGradientAt
      (fun y : HilbertConfiguration N =>
        CoerciveLatticeEnergy.potentialEnergy kappa beta g (asConfiguration y))
      (potentialGradient kappa beta g q) q := by
  unfold CoerciveLatticeEnergy.potentialEnergy potentialGradient
  exact hasGradientAt_finset_sum
    (fun i _ => hasGradientAt_bondPotential kappa beta g q i)

/-- Formula for the Physlib/Mathlib gradient of the finite potential energy. -/
theorem gradient_potentialEnergy {N : Nat} [NeZero N]
    (kappa beta g : Real) (q : HilbertConfiguration N) :
    gradient
      (fun y : HilbertConfiguration N =>
        CoerciveLatticeEnergy.potentialEnergy kappa beta g (asConfiguration y)) q =
      potentialGradient kappa beta g q :=
  (hasGradientAt_potentialEnergy kappa beta g q).gradient

/-- The concrete Hamiltonian momentum gradient. -/
theorem gradient_hamiltonian_momentum {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa beta g : Real)
    (t : Time) (p q : HilbertConfiguration N) :
    gradient (fun p' => hamiltonian m kappa beta g t p' q) p =
      inverseMassMomentum m p := by
  change gradient
    (fun p' : HilbertConfiguration N =>
      Lattice.kineticEnergy m (asConfiguration p') +
        CoerciveLatticeEnergy.potentialEnergy kappa beta g (asConfiguration q)) p = _
  rw [gradient_add_const, gradient_kineticEnergy]

/-- The concrete Hamiltonian position gradient. -/
theorem gradient_hamiltonian_position {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa beta g : Real)
    (t : Time) (p q : HilbertConfiguration N) :
    gradient (fun q' => hamiltonian m kappa beta g t p q') q =
      potentialGradient kappa beta g q := by
  have hfun :
      (fun q' : HilbertConfiguration N => hamiltonian m kappa beta g t p q') =
        fun q' => CoerciveLatticeEnergy.potentialEnergy kappa beta g
          (asConfiguration q') + Lattice.kineticEnergy m (asConfiguration p) := by
    funext q'
    simp [hamiltonian, CoerciveLatticeEnergy.hamiltonian, add_comm]
  rw [hfun, gradient_add_const, gradient_potentialEnergy]

/-- Physlib's abstract Hamilton equations are exactly the explicit lattice equations. -/
theorem satisfiesHamiltonEquations_iff_explicit {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa beta g : Real)
    (p q : Time → HilbertConfiguration N) :
    SatisfiesHamiltonEquations m kappa beta g p q ↔
      (∀ t, ∂ₜ q t = inverseMassMomentum m (p t)) ∧
      (∀ t, ∂ₜ p t = -potentialGradient kappa beta g (q t)) := by
  rw [satisfiesHamiltonEquations_iff]
  simp_rw [gradient_hamiltonian_momentum, gradient_hamiltonian_position]

end

end ArchonPhysics.ConcreteHamiltonGradients
