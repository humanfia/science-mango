import ArchonPhysics.AlphaBetaPotential
import ArchonPhysics.LennardJonesPotential

/-!
# Local Lennard--Jones to FPUT alpha-beta bridge

The fourth-order displacement polynomial determined by the Lennard--Jones
equilibrium derivatives can be normalized by its positive harmonic stiffness.
The resulting dimensionless quadratic coefficient is one, while its alpha and
beta coefficients are computed exactly below.

This is a bridge between the equilibrium Taylor jet and an alpha-beta
polynomial. It does not identify the exact inverse-power Lennard--Jones
potential with that finite polynomial.
-/

namespace ArchonPhysics.LennardJonesAlphaBetaBridge

noncomputable section

/-- The local alpha coefficient divided by the LJ harmonic stiffness. -/
def normalizedAlpha (depth r₀ : Real) : Real :=
  LennardJonesPotential.alphaCoefficient depth r₀ /
    LennardJonesPotential.harmonicStiffness depth r₀

/-- The local beta coefficient divided by the LJ harmonic stiffness. -/
def normalizedBeta (depth r₀ : Real) : Real :=
  LennardJonesPotential.betaCoefficient depth r₀ /
    LennardJonesPotential.harmonicStiffness depth r₀

/-- The local fourth-order LJ polynomial divided by its harmonic stiffness. -/
def normalizedLocalQuarticPotential (depth r₀ x : Real) : Real :=
  LennardJonesPotential.localAlphaBetaPotential depth r₀ x /
    LennardJonesPotential.harmonicStiffness depth r₀

/-- Exact normalized cubic coefficient for positive physical LJ parameters. -/
theorem normalizedAlpha_eq {depth r₀ : Real}
    (hdepth : 0 < depth) (hr₀ : 0 < r₀) :
    normalizedAlpha depth r₀ = -21 / (2 * r₀) := by
  have hdepthNe : depth ≠ 0 := ne_of_gt hdepth
  have hr₀Ne : r₀ ≠ 0 := ne_of_gt hr₀
  unfold normalizedAlpha LennardJonesPotential.alphaCoefficient
  unfold LennardJonesPotential.harmonicStiffness
  field_simp [hdepthNe, hr₀Ne]
  ring

/-- Exact normalized quartic coefficient for positive physical LJ parameters. -/
theorem normalizedBeta_eq {depth r₀ : Real}
    (hdepth : 0 < depth) (hr₀ : 0 < r₀) :
    normalizedBeta depth r₀ = 371 / (6 * r₀ ^ 2) := by
  have hdepthNe : depth ≠ 0 := ne_of_gt hdepth
  have hr₀Ne : r₀ ≠ 0 := ne_of_gt hr₀
  unfold normalizedBeta LennardJonesPotential.betaCoefficient
  unfold LennardJonesPotential.harmonicStiffness
  field_simp [hdepthNe, hr₀Ne]
  ring

/-- The normalized LJ fourth-order jet lies strictly inside the elementary
coercive alpha-beta parameter regime. -/
theorem normalized_coercive {depth r₀ : Real}
    (hdepth : 0 < depth) (hr₀ : 0 < r₀) :
    2 * normalizedAlpha depth r₀ ^ 2 / 9 <
      normalizedBeta depth r₀ := by
  rw [normalizedAlpha_eq hdepth hr₀, normalizedBeta_eq hdepth hr₀]
  have hr₀Ne : r₀ ≠ 0 := ne_of_gt hr₀
  have hr₀Sq : 0 < r₀ ^ 2 := sq_pos_of_pos hr₀
  have hgap :
      371 / (6 * r₀ ^ 2) - 2 * (-21 / (2 * r₀)) ^ 2 / 9 =
        112 / (3 * r₀ ^ 2) := by
    field_simp [hr₀Ne]
    ring
  have hgapPos : 0 < 112 / (3 * r₀ ^ 2) := by
    exact div_pos (by norm_num) (mul_pos (by norm_num) hr₀Sq)
  linarith

/-- The normalized local quartic polynomial is exactly the standard FPUT
alpha-beta potential with the normalized coefficients. -/
theorem normalizedLocalQuarticPotential_eq_alphaBetaPotential
    {depth r₀ : Real} (hdepth : 0 < depth) (hr₀ : 0 < r₀)
    (x : Real) :
    normalizedLocalQuarticPotential depth r₀ x =
      AlphaBetaPotential.potential
        (normalizedAlpha depth r₀) (normalizedBeta depth r₀) x := by
  have hr₀Ne : r₀ ≠ 0 := ne_of_gt hr₀
  have hstiffPos :
      0 < LennardJonesPotential.harmonicStiffness depth r₀ := by
    unfold LennardJonesPotential.harmonicStiffness
    exact div_pos (mul_pos (by norm_num) hdepth) (sq_pos_of_ne_zero hr₀Ne)
  have hstiffNe :
      LennardJonesPotential.harmonicStiffness depth r₀ ≠ 0 :=
    ne_of_gt hstiffPos
  unfold normalizedLocalQuarticPotential normalizedAlpha normalizedBeta
  unfold LennardJonesPotential.localAlphaBetaPotential
  unfold AlphaBetaPotential.potential
  field_simp [hstiffNe]

/-- The first four LJ equilibrium derivatives supply exactly the harmonic,
cubic, and quartic coefficients used by the local alpha-beta polynomial. -/
theorem equilibriumTaylorJet_spec {depth r₀ : Real} (hr₀ : r₀ ≠ 0) :
    LennardJonesPotential.radialDerivative depth r₀ r₀ = 0 ∧
      LennardJonesPotential.radialSecondDerivative depth r₀ r₀ =
        LennardJonesPotential.harmonicStiffness depth r₀ ∧
      LennardJonesPotential.radialThirdDerivative depth r₀ r₀ =
        2 * LennardJonesPotential.alphaCoefficient depth r₀ ∧
      LennardJonesPotential.radialFourthDerivative depth r₀ r₀ =
        6 * LennardJonesPotential.betaCoefficient depth r₀ := by
  constructor
  · exact LennardJonesPotential.radialDerivative_equilibrium hr₀
  constructor
  · rw [LennardJonesPotential.radialSecondDerivative_equilibrium hr₀]
    rfl
  constructor
  · rw [LennardJonesPotential.radialThirdDerivative_equilibrium hr₀]
    unfold LennardJonesPotential.alphaCoefficient
    ring
  · rw [LennardJonesPotential.radialFourthDerivative_equilibrium hr₀]
    unfold LennardJonesPotential.betaCoefficient
    ring

end

end ArchonPhysics.LennardJonesAlphaBetaBridge
