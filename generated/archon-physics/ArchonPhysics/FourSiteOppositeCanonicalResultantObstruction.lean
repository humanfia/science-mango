import ArchonPhysics.CanonicalPairCharacteristicJacobianResultant
import ArchonPhysics.PathLaplacianSpecialization

/-!
# Four-site obstruction to unconditional canonical-resultant nonvanishing

On the four-cycle, vary the opposite weights at sites zero and two and freeze
the other two masses at one.  The vector (1, -1, -1, 1) has zero difference
across both varied edges, so it retains eigenvalue 2 for every value of both
varied inverse masses.  The reduced positive characteristic polynomial and
its second-mass coefficientwise partial therefore share the fixed root 2.

The final theorem proves that the canonical Jacobian resultant is identically
zero although the frozen background is positive and the two sites are
distinct.  Thus positivity and site distinctness alone cannot imply the
proposed general nonvanishing condition.
-/

namespace ArchonPhysics.FourSiteOppositeCanonicalResultantObstruction

open ArchonPhysics
open ArchonPhysics.CanonicalPairCharacteristicJacobianResultant
open ArchonPhysics.FiniteExactDecayResonanceObstruction
open ArchonPhysics.GenericSpectrumResultant
open ArchonPhysics.PathLaplacianSpecialization
open ArchonPhysics.TwoParameterSpectralPolynomialAvoidance
open ArchonPhysics.PhyslibFPUTIteratedA2PairFiberAlgebraicBadSet
open Filter Set

noncomputable section

def unitMassFour : Lattice.PositiveMassConfig 4 where
  mass _ := 1
  mass_pos _ := by norm_num

def alternatingPairVector : Lattice.Configuration 4 :=
  fun i => if i.val = 0 ∨ i.val = 3 then 1 else -1

theorem alternatingPairVector_ne_zero : alternatingPairVector ≠ 0 := by
  intro h
  have hzero := congrFun h (0 : Lattice.Site 4)
  norm_num [alternatingPairVector] at hzero

theorem opposite_slice_mulVec_alternating
    (pair : Real × Real) :
    Matrix.mulVec
        (weightedCycleLaplacian
          (weightsOfCoordinates
            (twoSiteInverseMassSliceCoordinates unitMassFour
              (0 : Lattice.Site 4) (2 : Lattice.Site 4) pair)))
        alternatingPairVector =
      (2 : Real) • alternatingPairVector := by
  rw [weightedCycleLaplacian_mulVec]
  funext i
  change _ = 2 * alternatingPairVector i
  fin_cases i <;>
    norm_num +decide [alternatingPairVector, weightsOfCoordinates,
      twoSiteInverseMassSliceCoordinates, unitMassFour, siteEquivFin]

theorem opposite_slice_charpoly_eval_two
    (pair : Real × Real) :
    (weightedCycleLaplacian
      (weightsOfCoordinates
        (twoSiteInverseMassSliceCoordinates unitMassFour
          (0 : Lattice.Site 4) (2 : Lattice.Site 4) pair))).charpoly.eval 2 = 0 := by
  let A := weightedCycleLaplacian
    (weightsOfCoordinates
      (twoSiteInverseMassSliceCoordinates unitMassFour
        (0 : Lattice.Site 4) (2 : Lattice.Site 4) pair))
  have heigen : A.mulVec alternatingPairVector =
      (2 : Real) • alternatingPairVector :=
    opposite_slice_mulVec_alternating pair
  let T : Module.End Real (Lattice.Configuration 4) := A.toLin'
  have hv : T.HasEigenvector 2 alternatingPairVector := by
    rw [Module.End.hasEigenvector_iff, Module.End.mem_eigenspace_iff]
    refine ⟨?_, alternatingPairVector_ne_zero⟩
    change A.mulVec alternatingPairVector = (2 : Real) • alternatingPairVector
    exact heigen
  have hroot : T.charpoly.IsRoot 2 :=
    (Module.End.hasEigenvalue_iff_isRoot_charpoly T 2).mp
      (Module.End.hasEigenvalue_of_hasEigenvector hv)
  simpa [T, Matrix.charpoly_toLin'] using hroot

theorem opposite_slice_reduced_charpoly_eval_two
    (pair : Real × Real) :
    ((weightedCycleLaplacian
      (weightsOfCoordinates
        (twoSiteInverseMassSliceCoordinates unitMassFour
          (0 : Lattice.Site 4) (2 : Lattice.Site 4) pair))).charpoly.divX).eval 2 = 0 := by
  let A := weightedCycleLaplacian
    (weightsOfCoordinates
      (twoSiteInverseMassSliceCoordinates unitMassFour
        (0 : Lattice.Site 4) (2 : Lattice.Site 4) pair))
  have hzero : A.charpoly.eval 0 = 0 := by
    let constant : Lattice.Configuration 4 := fun _ => 1
    have hconstant_ne : constant ≠ 0 := by
      intro h
      have := congrFun h (0 : Lattice.Site 4)
      norm_num [constant] at this
    have heigen : A.mulVec constant = (0 : Real) • constant := by
      rw [weightedCycleLaplacian_mulVec]
      funext i
      simp [constant]
    let T : Module.End Real (Lattice.Configuration 4) := A.toLin'
    have hv : T.HasEigenvector 0 constant := by
      rw [Module.End.hasEigenvector_iff, Module.End.mem_eigenspace_iff]
      refine ⟨?_, hconstant_ne⟩
      change A.mulVec constant = (0 : Real) • constant
      exact heigen
    have hroot : T.charpoly.IsRoot 0 :=
      (Module.End.hasEigenvalue_iff_isRoot_charpoly T 0).mp
        (Module.End.hasEigenvalue_of_hasEigenvector hv)
    simpa [T, Matrix.charpoly_toLin'] using hroot
  exact eval_divX_eq_zero_of_zero_root_of_ne_zero_root hzero
    (opposite_slice_charpoly_eval_two pair) (by norm_num)

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

/-- Evaluating the energy after taking the coefficientwise vertical partial
is the same as taking the vertical partial after evaluating the energy at a
constant. -/
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

/-- The positive reduced symbolic characteristic polynomial has the fixed root
E = 2 on the opposite-edge unit-background slice. -/
theorem opposite_positiveCharacteristic_eval_two_eq_zero :
    (twoSitePositiveCharacteristicPolynomial unitMassFour
      (0 : Lattice.Site 4) (2 : Lattice.Site 4)).eval
        (MvPolynomial.C 2) = 0 := by
  apply MvPolynomial.funext_set (fun _ : Fin 2 => Set.Ioi (0 : Real))
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
      unitMassFour (0 : Lattice.Site 4) (2 : Lattice.Site 4) pair
    rw [hpairCoordinates] at hmap
    have heval := congrArg (Polynomial.eval 2) hmap
    have hroot := opposite_slice_reduced_charpoly_eval_two pair
    rw [hroot] at heval
    rw [show MvPolynomial.C (2 : Real) =
      (2 : MvPolynomial (Fin 2) Real) by
        exact map_ofNat
          (MvPolynomial.C : Real →+* MvPolynomial (Fin 2) Real) 2]
    simpa [Polynomial.eval_map, Polynomial.eval₂_at_apply] using heval

/-- The coefficientwise y-partial has the same fixed positive root. -/
theorem opposite_positiveCharacteristicVerticalPartial_eval_two_eq_zero :
    (twoSitePositiveCharacteristicVerticalMassPartial unitMassFour
      (0 : Lattice.Site 4) (2 : Lattice.Site 4)).eval
        (MvPolynomial.C 2) = 0 := by
  rw [twoSitePositiveCharacteristicVerticalMassPartial,
    eval_verticalMassPartial_at_constant,
    opposite_positiveCharacteristic_eval_two_eq_zero]
  exact map_zero _

/-- The canonical Jacobian resultant is identically zero on the four-site
opposite-edge unit frozen background. -/
theorem opposite_positiveCharacteristicJacobianResultant_eq_zero :
    twoSitePositiveCharacteristicJacobianResultant unitMassFour
      (0 : Lattice.Site 4) (2 : Lattice.Site 4) = 0 := by
  apply MvPolynomial.funext_set (fun _ : Fin 2 => Set.Ioi (0 : Real))
  · intro i
    exact Set.Ioi_infinite (0 : Real)
  · intro coordinates _
    have htwo : MvPolynomial.C (2 : Real) =
        (2 : MvPolynomial (Fin 2) Real) := by
      exact map_ofNat
        (MvPolynomial.C : Real →+* MvPolynomial (Fin 2) Real) 2
    apply
      twoSitePositiveCharacteristicJacobianResultant_eval_eq_zero_of_common_energy
        unitMassFour (0 : Lattice.Site 4) (2 : Lattice.Site 4)
        coordinates 2
    · have hroot := congrArg (MvPolynomial.eval coordinates)
        opposite_positiveCharacteristic_eval_two_eq_zero
      simp only [map_zero] at hroot
      rw [htwo] at hroot
      simpa [Polynomial.eval_map, Polynomial.eval₂_at_apply] using hroot
    · have hroot := congrArg (MvPolynomial.eval coordinates)
        opposite_positiveCharacteristicVerticalPartial_eval_two_eq_zero
      simp only [map_zero] at hroot
      rw [htwo] at hroot
      simpa [Polynomial.eval_map, Polynomial.eval₂_at_apply] using hroot

end

end ArchonPhysics.FourSiteOppositeCanonicalResultantObstruction
