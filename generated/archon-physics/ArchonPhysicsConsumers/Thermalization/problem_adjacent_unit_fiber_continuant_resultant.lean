import ArchonPhysics.AdjacentUnitFiberContinuantResultant

/-!
# Consumer: adjacent unit-fiber continuant resultant

This consumer records the exact real endpoint identity and its nonvanishing.
It consumes only the abstract continuant/resultant theorem.  It does not claim
that the canonical two-site sliced cycle has already been specialized to these
two polynomials; that matrix-specialization bridge remains a separate theorem.
-/

namespace ArchonPhysicsConsumers.Thermalization

open ArchonPhysics.AdjacentUnitFiberContinuantResultant

noncomputable section

/-- At the algebraic endpoint corresponding to volume `N = n+2`, the
continuant model has resultant `(-1)^(N.choose 2) * N`. -/
theorem adjacent_unit_fiber_continuant_resultant_exact (n : Nat) :
    Polynomial.resultant (realAdjacentEndpointCharacteristic n)
        (realAdjacentEndpointVerticalPartial n) (n + 1) n =
      (-1 : Real) ^ ((n + 2).choose 2) * (n + 2 : Nat) :=
  realAdjacentEndpoint_resultant n

/-- In particular, the continuant endpoint resultant is nonzero for every
volume `N = n+2`. -/
theorem adjacent_unit_fiber_continuant_resultant_nonzero (n : Nat) :
    Polynomial.resultant (realAdjacentEndpointCharacteristic n)
        (realAdjacentEndpointVerticalPartial n) (n + 1) n ≠ 0 :=
  realAdjacentEndpoint_resultant_ne_zero n

#print axioms adjacent_unit_fiber_continuant_resultant_exact
#print axioms adjacent_unit_fiber_continuant_resultant_nonzero

end


end ArchonPhysicsConsumers.Thermalization
