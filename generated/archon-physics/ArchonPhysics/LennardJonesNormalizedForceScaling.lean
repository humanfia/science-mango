import ArchonPhysics.LennardJonesAlphaBetaBridge
import ArchonPhysics.LennardJonesForceTaylorTube

/-!
# Weak-amplitude scaling of the exact Lennard--Jones force

After the displacement rescaling `x ↦ g*x` and division by the harmonic
force scale `k*g`, the LJ force is the normalized FPUT alpha-beta force plus
an exact remainder proportional to `g^3`.  A relative-strain tube supplies a
uniform quantitative bound for that remainder.

This pointwise `O(g^3)` statement is a necessary input to a kinetic-time
comparison, not by itself a proof of random-phase propagation or a
microscopic-to-kinetic limit.
-/

namespace ArchonPhysics.LennardJonesNormalizedForceScaling

open ArchonPhysics.BondPotentialHamiltonianPhyslib
open ArchonPhysics.LennardJonesAlphaBetaBridge
open ArchonPhysics.LennardJonesForceTaylorTube
open ArchonPhysics.LennardJonesPotential

noncomputable section

/-- Positive physical LJ parameters give a positive harmonic stiffness. -/
theorem harmonicStiffness_pos {depth r₀ : Real}
    (hdepth : 0 < depth) (hr₀ : 0 < r₀) :
    0 < harmonicStiffness depth r₀ := by
  unfold harmonicStiffness
  exact div_pos (mul_pos (by norm_num) hdepth) (sq_pos_of_pos hr₀)

/-- Exact LJ force after weak-amplitude and harmonic-force normalization. -/
def normalizedRescaledForce (depth r₀ g x : Real) : Real :=
  lennardJonesDerivative depth r₀ (g * x) /
    (harmonicStiffness depth r₀ * g)

/-- Normalized force remainder after subtracting the local alpha-beta jet. -/
def normalizedForceRemainder (depth r₀ g x : Real) : Real :=
  (lennardJonesDerivative depth r₀ (g * x) -
      localAlphaBetaForce depth r₀ (g * x)) /
    (harmonicStiffness depth r₀ * g)

/-- Exact normalized decomposition into harmonic, cubic, quartic, and
higher-order LJ forces. -/
theorem normalizedRescaledForce_eq_fput_add_remainder
    {depth r₀ g : Real} (hdepth : 0 < depth) (hr₀ : 0 < r₀)
    (hg : g ≠ 0) (x : Real) :
    normalizedRescaledForce depth r₀ g x =
      x + normalizedAlpha depth r₀ * g * x ^ 2 +
        normalizedBeta depth r₀ * g ^ 2 * x ^ 3 +
          normalizedForceRemainder depth r₀ g x := by
  have hk : harmonicStiffness depth r₀ ≠ 0 :=
    ne_of_gt (harmonicStiffness_pos hdepth hr₀)
  unfold normalizedRescaledForce normalizedForceRemainder
  unfold localAlphaBetaForce normalizedAlpha normalizedBeta
  field_simp [hk, hg]
  ring

/-- The normalized remainder has an exact `g^3` factor. -/
theorem normalizedForceRemainder_eq_g_cubed
    {depth r₀ g x : Real} (hdepth : 0 < depth) (hr₀ : 0 < r₀)
    (hg : g ≠ 0) (hbond : r₀ + g * x ≠ 0) :
    normalizedForceRemainder depth r₀ g x =
      -(r₀ / 72) * g ^ 3 * (x / r₀) ^ 4 *
        dimensionlessForceRemainderNumerator (g * x / r₀) /
          (1 + g * x / r₀) ^ 13 := by
  have hdepthNe : depth ≠ 0 := ne_of_gt hdepth
  have hr₀Ne : r₀ ≠ 0 := ne_of_gt hr₀
  unfold normalizedForceRemainder
  rw [lennardJonesDerivative_sub_localAlphaBetaForce_eq_dimensionless
    hr₀Ne hbond]
  unfold harmonicStiffness
  field_simp [hdepthNe, hr₀Ne, hg]

/-- On a fixed relative tube, the normalized force remainder is bounded by
an explicit constant times `|g|^3`, uniformly in the amplitude parameter. -/
theorem abs_normalizedForceRemainder_le_g_cubed
    {depth r₀ g rho x : Real}
    (hdepth : 0 < depth) (hr₀ : 0 < r₀) (hg : g ≠ 0)
    (hrho0 : 0 ≤ rho) (hrho1 : rho < 1)
    (htube : |g * x| ≤ rho * r₀) :
    |normalizedForceRemainder depth r₀ g x| ≤
      r₀ / 72 * forceRemainderTubeConstant rho * |g| ^ 3 *
        (|x| / r₀) ^ 4 := by
  have hkpos : 0 < harmonicStiffness depth r₀ :=
    harmonicStiffness_pos hdepth hr₀
  have habsg : 0 < |g| := abs_pos.mpr hg
  have hdenpos : 0 < harmonicStiffness depth r₀ * |g| :=
    mul_pos hkpos habsg
  have hforce :=
    abs_lennardJonesDerivative_sub_localAlphaBetaForce_le
      hdepth.le hr₀ hrho0 hrho1 htube
  unfold normalizedForceRemainder
  rw [abs_div, abs_mul, abs_of_pos hkpos]
  calc
    |lennardJonesDerivative depth r₀ (g * x) -
          localAlphaBetaForce depth r₀ (g * x)| /
        (harmonicStiffness depth r₀ * |g|) ≤
      (depth / r₀ * forceRemainderTubeConstant rho *
          (|g * x| / r₀) ^ 4) /
        (harmonicStiffness depth r₀ * |g|) :=
      (div_le_div_iff_of_pos_right hdenpos).2 hforce
    _ = r₀ / 72 * forceRemainderTubeConstant rho * |g| ^ 3 *
        (|x| / r₀) ^ 4 := by
      rw [abs_mul]
      unfold harmonicStiffness
      field_simp [ne_of_gt hdepth, ne_of_gt hr₀, ne_of_gt habsg]

end

end ArchonPhysics.LennardJonesNormalizedForceScaling
