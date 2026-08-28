import ArchonPhysics.OddConstantScaleRootsResultant

/-!
# Consumer: odd-constant fourfold root-ratio obstruction

This endpoint exposes the unconditional algebraic obstruction.  It does not
assert that any particular lattice reduced characteristic polynomial has an
odd constant coefficient; that specialization remains a separate theorem.
-/

namespace ArchonPhysicsConsumers.Thermalization

open ArchonPhysics.OddConstantScaleRootsResultant

noncomputable section

/-- Consumer-facing form of the mod-two resultant obstruction. -/
theorem problem_int_resultant_scaleRoots_four_ne_zero_of_odd_constant
    (p : Polynomial Int) (hp : p.Monic) (hodd : Odd (p.coeff 0)) :
    Polynomial.resultant p (p.scaleRoots 4) p.natDegree p.natDegree ≠ 0 :=
  int_resultant_scaleRoots_four_ne_zero_of_odd_constant p hp hodd

#print axioms
  problem_int_resultant_scaleRoots_four_ne_zero_of_odd_constant

end

end ArchonPhysicsConsumers.Thermalization
