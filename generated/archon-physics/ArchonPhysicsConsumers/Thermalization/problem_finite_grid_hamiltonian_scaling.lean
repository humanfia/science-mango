import ArchonPhysics.FiniteGridHamiltonianScaling

/-!
# Consumer: finite-graph and multidimensional-grid Hamiltonian scaling

This target locks the arbitrary finite-edge theorem, the explicit 2D/3D
open and periodic endpoints, and both cubic and quartic inverse-square laws.
-/

namespace ArchonPhysicsConsumers.Thermalization

open ArchonPhysics.FiniteGridHamiltonianScaling

#check FiniteUndirectedEdges
#check FiniteDirectedEdges
#check openGrid2Hamiltonian_rescale
#check openGrid3Hamiltonian_rescale
#check periodicGrid2Hamiltonian_rescale
#check periodicGrid3Hamiltonian_rescale

theorem problem_any_finite_graph_hamiltonian_rescale :
    (@finiteEdgeHamiltonian_rescale) =
      @finiteEdgeHamiltonian_rescale :=
  rfl

theorem problem_open_grid_2d_hamiltonian_rescale :
    (@openGrid2Hamiltonian_rescale) =
      @openGrid2Hamiltonian_rescale :=
  rfl

theorem problem_open_grid_3d_hamiltonian_rescale :
    (@openGrid3Hamiltonian_rescale) =
      @openGrid3Hamiltonian_rescale :=
  rfl

theorem problem_periodic_grid_2d_hamiltonian_rescale :
    (@periodicGrid2Hamiltonian_rescale) =
      @periodicGrid2Hamiltonian_rescale :=
  rfl

theorem problem_periodic_grid_3d_hamiltonian_rescale :
    (@periodicGrid3Hamiltonian_rescale) =
      @periodicGrid3Hamiltonian_rescale :=
  rfl

theorem problem_finite_grid_cubic_inverse_square
    (lambda epsilon : Real) (hepsilon : 0 < epsilon)
    (hlambda : lambda ≠ 0) :
    (graphEffectiveCoupling lambda epsilon 3)⁻¹ ^ 2 =
      lambda⁻¹ ^ 2 * epsilon⁻¹ := by
  exact graphEffectiveCoupling_cubic_inv_sq
    lambda epsilon hepsilon hlambda

theorem problem_finite_grid_quartic_inverse_square
    (lambda epsilon : Real) :
    (graphEffectiveCoupling lambda epsilon 4)⁻¹ ^ 2 =
      lambda⁻¹ ^ 2 * epsilon⁻¹ ^ 2 := by
  exact graphEffectiveCoupling_quartic_inv_sq lambda epsilon

#print axioms problem_any_finite_graph_hamiltonian_rescale
#print axioms problem_open_grid_2d_hamiltonian_rescale
#print axioms problem_open_grid_3d_hamiltonian_rescale
#print axioms problem_periodic_grid_2d_hamiltonian_rescale
#print axioms problem_periodic_grid_3d_hamiltonian_rescale
#print axioms problem_finite_grid_cubic_inverse_square
#print axioms problem_finite_grid_quartic_inverse_square

end ArchonPhysicsConsumers.Thermalization
