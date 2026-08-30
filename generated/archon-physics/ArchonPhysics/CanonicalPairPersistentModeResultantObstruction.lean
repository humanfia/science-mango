import ArchonPhysics.CanonicalPairCharacteristicJacobianResultant
import ArchonPhysics.PathLaplacianSpecialization

/-!
# Persistent-mode obstruction for the canonical pair resultant

For a two-edge fiber, a nonzero eigenvector which retains one fixed nonzero
energy for every value of both varied coordinates is invisible to those
variations.  The fixed energy is then a common root of the reduced positive
characteristic polynomial and its vertical mass partial.  Consequently the
canonical characteristic-Jacobian resultant is the zero polynomial.

This is a sufficient obstruction, not a converse.  It isolates the exact
mechanism behind symmetric opposite-edge counterexamples and gives a rigorous
site-pair audit rule for larger volumes: candidate pairs with such a
persistent nonzero-energy mode cannot provide the desired canonical
certificate.
-/

namespace ArchonPhysics.CanonicalPairPersistentModeResultantObstruction

open ArchonPhysics
open ArchonPhysics.CanonicalPairCharacteristicJacobianResultant
open ArchonPhysics.FiniteExactDecayResonanceObstruction
open ArchonPhysics.GenericSpectrumResultant
open ArchonPhysics.PathLaplacianSpecialization
open ArchonPhysics.PhyslibFPUTIteratedA2PairFiberAlgebraicBadSet
open ArchonPhysics.TwoParameterSpectralPolynomialAvoidance
open Filter Set

noncomputable section

/-- Evaluating the coefficient ring after substituting a constant energy is
the same as mapping coefficients first and then evaluating that energy. -/
theorem eval_eval_constant_eq_eval_map
    (p : Polynomial (MvPolynomial (Fin 2) Real))
    (coordinates : Fin 2 → Real) (energy : Real) :
    MvPolynomial.eval coordinates (p.eval (MvPolynomial.C energy)) =
      (p.map (MvPolynomial.eval coordinates)).eval energy := by
  rw [Polynomial.eval_map]
  symm
  convert Polynomial.eval₂_at_apply
    (p := p) (MvPolynomial.eval coordinates) (MvPolynomial.C energy) using 1 <;>
    simp

/-- Every weighted cycle has the acoustic root at zero. -/
theorem weightedCycleLaplacian_charpoly_eval_zero
    {N : Nat} [NeZero N] (weights : Lattice.Configuration N) :
    (weightedCycleLaplacian weights).charpoly.eval 0 = 0 := by
  let A := weightedCycleLaplacian weights
  let constant : Lattice.Configuration N := fun _ ↦ 1
  have hconstant_ne : constant ≠ 0 := by
    intro hzero
    have hcoordinate := congrFun hzero (0 : Lattice.Site N)
    norm_num [constant] at hcoordinate
  have heigen : A.mulVec constant = (0 : Real) • constant := by
    rw [weightedCycleLaplacian_mulVec]
    funext i
    simp [constant]
  let T : Module.End Real (Lattice.Configuration N) := A.toLin'
  have hv : T.HasEigenvector 0 constant := by
    rw [Module.End.hasEigenvector_iff, Module.End.mem_eigenspace_iff]
    refine ⟨?_, hconstant_ne⟩
    change A.mulVec constant = (0 : Real) • constant
    exact heigen
  have hroot : T.charpoly.IsRoot 0 :=
    (Module.End.hasEigenvalue_iff_isRoot_charpoly T 0).mp
      (Module.End.hasEigenvalue_of_hasEigenvector hv)
  simpa [T, A, Matrix.charpoly_toLin'] using hroot

/-- A persistent nonzero eigenmode on the concrete pair fiber remains a root
after removing the acoustic factor. -/
theorem reduced_charpoly_eval_eq_zero_of_persistent_mode
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (site₁ site₂ : Lattice.Site N) (energy : Real)
    (vector : Lattice.Configuration N) (hvector : vector ≠ 0)
    (henergy : energy ≠ 0)
    (heigen : ∀ pair : Real × Real,
      Matrix.mulVec
          (weightedCycleLaplacian
            (weightsOfCoordinates
              (twoSiteInverseMassSliceCoordinates fixed site₁ site₂ pair)))
          vector =
        energy • vector) (pair : Real × Real) :
    ((weightedCycleLaplacian
      (weightsOfCoordinates
        (twoSiteInverseMassSliceCoordinates fixed site₁ site₂ pair))).charpoly.divX).eval
        energy = 0 := by
  let A := weightedCycleLaplacian
    (weightsOfCoordinates
      (twoSiteInverseMassSliceCoordinates fixed site₁ site₂ pair))
  let T : Module.End Real (Lattice.Configuration N) := A.toLin'
  have hv : T.HasEigenvector energy vector := by
    rw [Module.End.hasEigenvector_iff, Module.End.mem_eigenspace_iff]
    refine ⟨?_, hvector⟩
    change A.mulVec vector = energy • vector
    exact heigen pair
  have hroot : A.charpoly.eval energy = 0 := by
    have : T.charpoly.IsRoot energy :=
      (Module.End.hasEigenvalue_iff_isRoot_charpoly T energy).mp
        (Module.End.hasEigenvalue_of_hasEigenvector hv)
    simpa [T, Matrix.charpoly_toLin'] using this
  exact eval_divX_eq_zero_of_zero_root_of_ne_zero_root
    (weightedCycleLaplacian_charpoly_eval_zero
      (weightsOfCoordinates
        (twoSiteInverseMassSliceCoordinates fixed site₁ site₂ pair)))
    hroot henergy

/-- The canonical symbolic reduced characteristic polynomial has the fixed
energy root when the concrete fiber has a persistent mode. -/
theorem positiveCharacteristic_eval_eq_zero_of_persistent_mode
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (site₁ site₂ : Lattice.Site N) (energy : Real)
    (vector : Lattice.Configuration N) (hvector : vector ≠ 0)
    (henergy : energy ≠ 0)
    (heigen : ∀ pair : Real × Real,
      Matrix.mulVec
          (weightedCycleLaplacian
            (weightsOfCoordinates
              (twoSiteInverseMassSliceCoordinates fixed site₁ site₂ pair)))
          vector =
        energy • vector) :
    (twoSitePositiveCharacteristicPolynomial fixed site₁ site₂).eval
        (MvPolynomial.C energy) = 0 := by
  apply MvPolynomial.funext_set (fun _ : Fin 2 ↦ Set.Ioi (0 : Real))
  · intro i
    exact Set.Ioi_infinite (0 : Real)
  · intro coordinates _
    let pair : Real × Real :=
      ((coordinates 0)⁻¹, (coordinates 1)⁻¹)
    have hpairCoordinates :
        iidInverseMassPairCoordinates pair = coordinates := by
      funext i
      fin_cases i <;> simp [pair, iidInverseMassPairCoordinates]
    have hmap := evaluate_twoSitePositiveCharacteristicPolynomial
      fixed site₁ site₂ pair
    rw [hpairCoordinates] at hmap
    have heval := congrArg (Polynomial.eval energy) hmap
    have hroot := reduced_charpoly_eval_eq_zero_of_persistent_mode
      fixed site₁ site₂ energy vector hvector henergy heigen pair
    rw [hroot] at heval
    rw [eval_eval_constant_eq_eval_map]
    exact heval

theorem verticalMassPartial_add
    (p q : Polynomial (MvPolynomial (Fin 2) Real)) :
    verticalMassPartial (p + q) =
      verticalMassPartial p + verticalMassPartial q := by
  ext n
  simp [coeff_verticalMassPartial]

theorem verticalMassPartial_monomial
    (n : Nat) (a : MvPolynomial (Fin 2) Real) :
    verticalMassPartial (Polynomial.monomial n a) =
      Polynomial.monomial n (MvPolynomial.pderiv (1 : Fin 2) a) := by
  apply Polynomial.ext
  intro k
  by_cases h : k = n
  · subst k
    simp [coeff_verticalMassPartial]
  · have hn : n ≠ k := Ne.symm h
    simp [coeff_verticalMassPartial, Polynomial.coeff_monomial, hn]

/-- Evaluation in energy commutes with the coefficientwise vertical partial
when the energy is constant in the mass variables. -/
theorem eval_verticalMassPartial_at_constant
    (p : Polynomial (MvPolynomial (Fin 2) Real)) (energy : Real) :
    (verticalMassPartial p).eval (MvPolynomial.C energy) =
      MvPolynomial.pderiv (1 : Fin 2)
        (p.eval (MvPolynomial.C energy)) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      rw [verticalMassPartial_add, Polynomial.eval_add, Polynomial.eval_add,
        map_add, hp, hq]
  | monomial n a =>
      rw [verticalMassPartial_monomial]
      simp
      ring

/-- The vertical mass partial shares the persistent nonzero-energy root. -/
theorem positiveCharacteristicVerticalPartial_eval_eq_zero_of_persistent_mode
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (site₁ site₂ : Lattice.Site N) (energy : Real)
    (vector : Lattice.Configuration N) (hvector : vector ≠ 0)
    (henergy : energy ≠ 0)
    (heigen : ∀ pair : Real × Real,
      Matrix.mulVec
          (weightedCycleLaplacian
            (weightsOfCoordinates
              (twoSiteInverseMassSliceCoordinates fixed site₁ site₂ pair)))
          vector =
        energy • vector) :
    (twoSitePositiveCharacteristicVerticalMassPartial fixed site₁ site₂).eval
        (MvPolynomial.C energy) = 0 := by
  rw [twoSitePositiveCharacteristicVerticalMassPartial,
    eval_verticalMassPartial_at_constant,
    positiveCharacteristic_eval_eq_zero_of_persistent_mode
      fixed site₁ site₂ energy vector hvector henergy heigen]
  exact map_zero _

/-- Main general obstruction: a fixed nonzero-energy mode which is present
for every point of the full algebraic pair fiber (all real raw-mass pairs,
not merely the physical positive support) forces the canonical resultant to
be the zero polynomial. -/
theorem positiveCharacteristicJacobianResultant_eq_zero_of_persistent_mode
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (site₁ site₂ : Lattice.Site N) (energy : Real)
    (vector : Lattice.Configuration N) (hvector : vector ≠ 0)
    (henergy : energy ≠ 0)
    (heigen : ∀ pair : Real × Real,
      Matrix.mulVec
          (weightedCycleLaplacian
            (weightsOfCoordinates
              (twoSiteInverseMassSliceCoordinates fixed site₁ site₂ pair)))
          vector =
        energy • vector) :
    twoSitePositiveCharacteristicJacobianResultant fixed site₁ site₂ = 0 := by
  have hroot := positiveCharacteristic_eval_eq_zero_of_persistent_mode
    fixed site₁ site₂ energy vector hvector henergy heigen
  have hpartial :=
    positiveCharacteristicVerticalPartial_eval_eq_zero_of_persistent_mode
      fixed site₁ site₂ energy vector hvector henergy heigen
  apply MvPolynomial.funext_set (fun _ : Fin 2 ↦ Set.Ioi (0 : Real))
  · intro i
    exact Set.Ioi_infinite (0 : Real)
  · intro coordinates _
    apply
      twoSitePositiveCharacteristicJacobianResultant_eval_eq_zero_of_common_energy
        fixed site₁ site₂ coordinates energy
    · have heval := congrArg (MvPolynomial.eval coordinates) hroot
      rw [← eval_eval_constant_eq_eval_map]
      exact heval
    · have heval := congrArg (MvPolynomial.eval coordinates) hpartial
      rw [← eval_eval_constant_eq_eval_map]
      exact heval

end

end ArchonPhysics.CanonicalPairPersistentModeResultantObstruction
