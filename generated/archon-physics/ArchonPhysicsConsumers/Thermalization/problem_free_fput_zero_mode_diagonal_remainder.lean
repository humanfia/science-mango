import ArchonPhysics.FreeFPUTZeroModeDiagonalRemainder

/-!
# Consumer checks for the zero-mode diagonal remainder

These contracts expose the structural elimination of the nonpositive-mode
diagonal sector in the finite-volume free quadratic first-Picard formula.
They use vanishing of the interaction tensor on a zero-frequency leg and do
not use the totalized value of an energy radius at zero frequency.  The
same-charge off-diagonal coherent remainder remains untouched.
-/

namespace ArchonPhysicsConsumers.Thermalization.FreeFPUTZeroModeDiagonalRemainder

open ArchonPhysics
open ArchonPhysics.FreeFPUTDiagonalCollisionDecomposition
open ArchonPhysics.FreeFPUTZeroModeDiagonalRemainder

noncomputable section

/-- Every term in the nonpositive-frequency diagonal sector has a zero
interaction tensor, so the complete remainder vanishes for arbitrary radii
and frequency labels. -/
theorem nonpositive_diagonal_remainder_zero_contract
    {N : Nat} [NeZero N] (coupling : Complex)
    (m : Lattice.PositiveMassConfig N) (observed : Lattice.Site N)
    (radius frequency : Lattice.Site N → Real) (time : Real) :
    nonpositiveFreeQuadraticDiagonalRemainder
      coupling m observed radius frequency time = 0 :=
  nonpositiveFreeQuadraticDiagonalRemainder_eq_zero
    coupling m observed radius frequency time

/-- Hence the full diagonal resonance sum is exactly its strictly positive
three-leg sector. -/
theorem full_diagonal_eq_positive_contract
    {N : Nat} [NeZero N] (coupling : Complex)
    (m : Lattice.PositiveMassConfig N) (observed : Lattice.Site N)
    (radius frequency : Lattice.Site N → Real) (time : Real) :
    freeQuadraticDiagonalResonanceSum
        coupling m observed radius frequency time =
      positiveFreeQuadraticDiagonalResonanceSum
        coupling m observed radius frequency time :=
  freeQuadraticDiagonalResonanceSum_eq_positive
    coupling m observed radius frequency time

#check physical_nonpositiveFreeQuadraticDiagonalRemainder_eq_zero

#print axioms nonpositive_diagonal_remainder_zero_contract
#print axioms full_diagonal_eq_positive_contract

end

end ArchonPhysicsConsumers.Thermalization.FreeFPUTZeroModeDiagonalRemainder
