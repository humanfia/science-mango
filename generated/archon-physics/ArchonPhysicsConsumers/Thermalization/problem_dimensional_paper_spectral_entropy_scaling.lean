import ArchonPhysics.DimensionalPaperSpectralEntropyScaling

/-!
# Consumer: dimensional all-mode paper spectral entropy

This consumer locks the arbitrary-finite-mode formula, exact kinetic-time
rescaling, all four published lattice thresholds, and the cubic/quartic
energy-density endpoints.
-/

namespace ArchonPhysicsConsumers.Thermalization

open ArchonPhysics.DimensionalPaperSpectralEntropyScaling

/-- Kernel-lock the full-mode entropy formula. -/
theorem problem_dimensionalAllModeXi_formula :
    (@highDimensionalAllModeXi_eq_expEntropy_div_card) =
      @highDimensionalAllModeXi_eq_expEntropy_div_card := rfl

/-- Kernel-lock the dimension-independent exact threshold-hit rescaling. -/
theorem problem_dimensionalAllModeXi_thresholdHittingTime_kineticScale :
    (@highDimensionalAllModeXiThresholdHittingTime_kineticScale) =
      @highDimensionalAllModeXiThresholdHittingTime_kineticScale := rfl

/-- The hexagonal 2D paper threshold is 0.65. -/
theorem problem_hexagonal2D_threshold :
    (@highDimensionalThreshold_hexagonal2D) =
      @highDimensionalThreshold_hexagonal2D := rfl

/-- The square 2D paper threshold is 0.95. -/
theorem problem_square2D_threshold :
    (@highDimensionalThreshold_square2D) =
      @highDimensionalThreshold_square2D := rfl

/-- The FCC 3D paper threshold is 0.65. -/
theorem problem_faceCenteredCubic3D_threshold :
    (@highDimensionalThreshold_faceCenteredCubic3D) =
      @highDimensionalThreshold_faceCenteredCubic3D := rfl

/-- The simple-cubic 3D paper threshold is 0.95. -/
theorem problem_simpleCubic3D_threshold :
    (@highDimensionalThreshold_simpleCubic3D) =
      @highDimensionalThreshold_simpleCubic3D := rfl

/-- Kernel-lock the general-degree hexagonal 2D endpoint. -/
theorem problem_hexagonal2DFullModeXi_general :
    (@hexagonal2DFullModeXi_energyDensity_corollary) =
      @hexagonal2DFullModeXi_energyDensity_corollary := rfl

/-- Kernel-lock the general-degree square 2D endpoint. -/
theorem problem_square2DFullModeXi_general :
    (@square2DFullModeXi_energyDensity_corollary) =
      @square2DFullModeXi_energyDensity_corollary := rfl

/-- Kernel-lock the general-degree FCC 3D endpoint. -/
theorem problem_faceCenteredCubic3DFullModeXi_general :
    (@faceCenteredCubic3DFullModeXi_energyDensity_corollary) =
      @faceCenteredCubic3DFullModeXi_energyDensity_corollary := rfl

/-- Kernel-lock the general-degree simple-cubic 3D endpoint. -/
theorem problem_simpleCubic3DFullModeXi_general :
    (@simpleCubic3DFullModeXi_energyDensity_corollary) =
      @simpleCubic3DFullModeXi_energyDensity_corollary := rfl

/-- Kernel-lock the hexagonal 2D cubic-leading endpoint. -/
theorem problem_hexagonal2DFullModeXi_cubic :
    (@hexagonal2DFullModeXi_cubic_energyDensity_corollary) =
      @hexagonal2DFullModeXi_cubic_energyDensity_corollary := rfl

/-- Kernel-lock the hexagonal 2D quartic endpoint. -/
theorem problem_hexagonal2DFullModeXi_quartic :
    (@hexagonal2DFullModeXi_quartic_energyDensity_corollary) =
      @hexagonal2DFullModeXi_quartic_energyDensity_corollary := rfl

/-- Kernel-lock the square 2D cubic-leading endpoint. -/
theorem problem_square2DFullModeXi_cubic :
    (@square2DFullModeXi_cubic_energyDensity_corollary) =
      @square2DFullModeXi_cubic_energyDensity_corollary := rfl

/-- Kernel-lock the square 2D quartic endpoint. -/
theorem problem_square2DFullModeXi_quartic :
    (@square2DFullModeXi_quartic_energyDensity_corollary) =
      @square2DFullModeXi_quartic_energyDensity_corollary := rfl

/-- Kernel-lock the FCC 3D cubic-leading endpoint. -/
theorem problem_faceCenteredCubic3DFullModeXi_cubic :
    (@faceCenteredCubic3DFullModeXi_cubic_energyDensity_corollary) =
      @faceCenteredCubic3DFullModeXi_cubic_energyDensity_corollary := rfl

/-- Kernel-lock the FCC 3D quartic endpoint. -/
theorem problem_faceCenteredCubic3DFullModeXi_quartic :
    (@faceCenteredCubic3DFullModeXi_quartic_energyDensity_corollary) =
      @faceCenteredCubic3DFullModeXi_quartic_energyDensity_corollary := rfl

/-- Kernel-lock the simple-cubic 3D cubic-leading endpoint. -/
theorem problem_simpleCubic3DFullModeXi_cubic :
    (@simpleCubic3DFullModeXi_cubic_energyDensity_corollary) =
      @simpleCubic3DFullModeXi_cubic_energyDensity_corollary := rfl

/-- Kernel-lock the simple-cubic 3D quartic endpoint. -/
theorem problem_simpleCubic3DFullModeXi_quartic :
    (@simpleCubic3DFullModeXi_quartic_energyDensity_corollary) =
      @simpleCubic3DFullModeXi_quartic_energyDensity_corollary := rfl

#print axioms problem_dimensionalAllModeXi_formula
#print axioms problem_dimensionalAllModeXi_thresholdHittingTime_kineticScale
#print axioms problem_simpleCubic3DFullModeXi_quartic

end ArchonPhysicsConsumers.Thermalization
