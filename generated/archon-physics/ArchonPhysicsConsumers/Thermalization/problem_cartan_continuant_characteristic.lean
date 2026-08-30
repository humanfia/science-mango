import ArchonPhysics.CartanContinuantCharacteristic

/-!
# Consumer: type-A Cartan characteristic continuant

This consumer records the exact matrix bridge for the continuant used by the
adjacent-unit-fiber resultant calculation and its concrete broken-cycle path
specialization.  It makes no claim yet that a canonical two-site slice or its
vertical partial specializes to these polynomials.
-/

namespace ArchonPhysicsConsumers.Thermalization

open ArchonPhysics.AdjacentUnitFiberContinuantResultant
open ArchonPhysics.CartanContinuantCharacteristic
open ArchonPhysics.PathLaplacianSpecialization
open ArchonPhysics.PeriodicWeightedCycleBlockGluing

noncomputable section

/-- Mathlib's rank-`n` type-A Cartan matrix has the adjacent-fiber continuant
as its characteristic polynomial. -/
theorem type_A_cartan_characteristic_is_adjacent_continuant (n : Nat) :
    cartanContinuant n = (CartanMatrix.A n).charpoly :=
  cartanContinuant_eq_cartanMatrix_A_charpoly n


/-- The one-broken-edge periodic weighted-cycle matrix realizes `X` times the
mapped continuant as its actual characteristic polynomial. -/
theorem broken_cycle_path_characteristic_is_adjacent_continuant (n : Nat) :
    (finWeightedCycleLaplacian
      (pathWeightCoordinates (n + 1))).charpoly =
      Polynomial.X * (cartanContinuant n).map (Int.castRingHom Real) :=
  finWeightedCycleLaplacian_path_charpoly_eq_cartanContinuant n

/-- Removing the translation zero mode from the broken-cycle path leaves the
mapped continuant exactly. -/
theorem broken_cycle_path_reduced_characteristic_is_adjacent_continuant
    (n : Nat) :
    (finWeightedCycleLaplacian
      (pathWeightCoordinates (n + 1))).charpoly.divX =
      (cartanContinuant n).map (Int.castRingHom Real) :=
  finWeightedCycleLaplacian_path_charpoly_divX_eq_cartanContinuant n

#print axioms type_A_cartan_characteristic_is_adjacent_continuant
#print axioms broken_cycle_path_characteristic_is_adjacent_continuant
#print axioms broken_cycle_path_reduced_characteristic_is_adjacent_continuant

end

end ArchonPhysicsConsumers.Thermalization
