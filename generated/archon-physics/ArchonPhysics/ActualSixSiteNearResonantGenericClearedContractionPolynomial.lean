import ArchonPhysics.ActualSixSiteNearResonantClearedContraction

/-!
# Generic polynomial for the cleared six-site contraction

The four variables are ordered as `t, E₀, E₁, E₂`.  This module constructs
the genuine multivariate polynomial obtained by taking the three
shifted-matrix adjugates and contracting their entries, and proves its exact
specialization to the real finite-coordinate contraction.
-/

open scoped BigOperators Matrix

namespace ArchonPhysics.ActualSixSiteNearResonantGenericClearedContractionPolynomial

open ArchonPhysics
open ArchonPhysics.ActualSixSiteNearResonantClearedContraction
open ArchonPhysics.ActualSixSiteNearResonantInteractionAlgebra

noncomputable section

/-- The denominator-cleared shifted matrix over an arbitrary commutative
ring. -/
def sixSiteClearedShiftedMatrix {R : Type*} [CommRing R]
    (t energy : R) : Matrix (Fin 6) (Fin 6) R :=
  let d := 1 - t ^ 2
  !![d * energy - 2, 1 - t, 0, 0, 0, 1 + t;
     1 - t, d * energy - (1 - t) - d, d, 0, 0, 0;
     0, d, d * (energy - 2), d, 0, 0;
     0, 0, d, d * (energy - 2), d, 0;
     0, 0, 0, d, d * (energy - 2), d;
     1 + t, 0, 0, 0, d, d * energy - d - (1 + t)]

theorem sixSiteClearedShiftedMatrix_real (t energy : Real) :
    sixSiteClearedShiftedMatrix t energy =
      sixSiteNearResonantClearedShiftedLiteral t energy := rfl

/-- Ring homomorphisms commute with the full adjugate-entry contraction. -/
theorem map_adjugateEntryProductContraction
    {R S ι : Type*} [CommRing R] [CommRing S]
    [Fintype ι] [DecidableEq ι] {n : Nat}
    (f : R →+* S) (family : Fin n → Matrix ι ι R) :
    f (adjugateEntryProductContraction family) =
      adjugateEntryProductContraction (fun r ↦ f.mapMatrix (family r)) := by
  unfold adjugateEntryProductContraction
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  apply Finset.sum_congr rfl
  intro j _hj
  rw [map_prod]
  apply Finset.prod_congr rfl
  intro r _hr
  have hmap := congrArg (fun M => M i j) (f.map_adjugate (family r))
  simpa only [RingHom.mapMatrix_apply, Matrix.map_apply] using hmap

/-- Variable order for the generic collision polynomial: path parameter
followed by the three selected squared energies. -/
abbrev CollisionVariable := Fin 4

def genericPathParameter : MvPolynomial CollisionVariable Real :=
  MvPolynomial.X 0

def genericSelectedEnergy (r : Fin 3) :
    MvPolynomial CollisionVariable Real :=
  MvPolynomial.X r.succ

def genericSixSiteClearedShiftedFamily (r : Fin 3) :
    Matrix (Fin 6) (Fin 6) (MvPolynomial CollisionVariable Real) :=
  sixSiteClearedShiftedMatrix genericPathParameter
    (genericSelectedEnergy r)

/-- The actual four-variable cleared contraction polynomial. -/
def genericSixSiteClearedAdjugateInteractionPolynomial :
    MvPolynomial CollisionVariable Real :=
  adjugateEntryProductContraction genericSixSiteClearedShiftedFamily

def collisionSpectralEvaluation (t : Real) (energy : Fin 3 → Real) :
    CollisionVariable → Real :=
  ![t, energy 0, energy 1, energy 2]

theorem evaluate_genericSixSiteClearedShiftedFamily
    (t : Real) (energy : Fin 3 → Real) (r : Fin 3) :
    (MvPolynomial.eval (collisionSpectralEvaluation t energy)).mapMatrix
        (genericSixSiteClearedShiftedFamily r) =
      sixSiteNearResonantClearedShiftedLiteral t (energy r) := by
  ext i j
  fin_cases r <;> fin_cases i <;> fin_cases j <;>
    norm_num [genericSixSiteClearedShiftedFamily,
      sixSiteClearedShiftedMatrix, genericPathParameter,
      genericSelectedEnergy, collisionSpectralEvaluation,
      sixSiteNearResonantClearedShiftedLiteral,
      RingHom.mapMatrix_apply]
  all_goals simp

/-- Exact specialization of the generic polynomial to the real cleared
finite-coordinate contraction. -/
theorem evaluate_genericSixSiteClearedAdjugateInteractionPolynomial
    (t : Real) (energy : Fin 3 → Real) :
    MvPolynomial.eval (collisionSpectralEvaluation t energy)
        genericSixSiteClearedAdjugateInteractionPolynomial =
      sixSiteNearResonantClearedAdjugateInteractionContraction t energy := by
  rw [genericSixSiteClearedAdjugateInteractionPolynomial,
    map_adjugateEntryProductContraction]
  unfold sixSiteNearResonantClearedAdjugateInteractionContraction
  congr 1
  funext r
  exact evaluate_genericSixSiteClearedShiftedFamily t energy r

end

end ArchonPhysics.ActualSixSiteNearResonantGenericClearedContractionPolynomial
