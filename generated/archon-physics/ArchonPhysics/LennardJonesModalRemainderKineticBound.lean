import ArchonPhysics.LennardJonesHamiltonianDuhamel
import ArchonPhysics.LennardJonesKineticTimeForceRemainder

/-!
# Finite-mode kinetic-time bound for the higher LJ force remainder

This module projects the exact LJ force remainder beyond the local FPUT
alpha-beta jet onto one random-mass normal mode.  The finite bond sum is
controlled by an explicit `l1` weight of the bond--mode coefficients.  On a
relative strain tube, its integral over `L/g^2` is `O(g)`.

The coefficient is kept explicitly finite-volume.  No uniform-in-volume
bound, persistence of the strain tube, random-phase propagation, or kinetic
limit is asserted.
-/

namespace ArchonPhysics.LennardJonesModalRemainderKineticBound

open Set
open ArchonPhysics
open ArchonPhysics.BondPotentialHamiltonianPhyslib
open ArchonPhysics.CoerciveHamiltonianPhyslib
open ArchonPhysics.LennardJonesForceTaylorTube
open ArchonPhysics.LennardJonesHamiltonianDuhamel
open ArchonPhysics.LennardJonesKineticTimeForceRemainder
open ArchonPhysics.LennardJonesNormalizedForceScaling
open ArchonPhysics.MassWeightedHamiltonianDynamics
open ArchonPhysics.ModeCoupling
open ArchonPhysics.ReducedModeTransform

noncomputable section

/-- Finite `l1` size of the bond coefficients entering one normal mode. -/
def modalBondL1Weight {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (k : Lattice.Site N) : Real :=
  ∑ i : Lattice.Site N, |bondModeCoefficient m i k|

/-- The normalized physical-space gradient of the exact LJ force remainder
beyond the local alpha-beta force. -/
def normalizedHigherResidualGradient {N : Nat} [NeZero N]
    (depth r₀ g : Real) (q : HilbertConfiguration N) :
    HilbertConfiguration N :=
  BondPotentialHamiltonianPhyslib.potentialGradient
    (normalizedForceRemainder depth r₀ g) q

/-- The same higher residual force in mass-weighted coordinates, with the
Hamiltonian minus sign. -/
def transformedNormalizedHigherResidualForce {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (depth r₀ g : Real)
    (q : HilbertConfiguration N) : WeightedConfiguration N :=
  -inverseSqrtMassTransform m
    (normalizedHigherResidualGradient depth r₀ g q)

/-- Explicit finite bond formula for the selected modal higher residual. -/
def normalizedHigherResidualModalForce {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (depth r₀ g : Real)
    (q : HilbertConfiguration N) (k : Lattice.Site N) : Real :=
  -∑ i : Lattice.Site N,
    normalizedForceRemainder depth r₀ g
        (Lattice.forwardDifference (asConfiguration q) i) *
      bondModeCoefficient m i k

/-- The explicit finite bond sum is exactly the modal projection of the
mass-weighted higher LJ force. -/
theorem modalCoordinates_transformedNormalizedHigherResidualForce
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (depth r₀ g : Real)
    (q : HilbertConfiguration N) (k : Lattice.Site N) :
    modalCoordinates m
        (transformedNormalizedHigherResidualForce m depth r₀ g q) k =
      normalizedHigherResidualModalForce m depth r₀ g q k := by
  unfold transformedNormalizedHigherResidualForce
    normalizedHigherResidualGradient normalizedHigherResidualModalForce
    BondPotentialHamiltonianPhyslib.potentialGradient
  simp only [map_neg, map_sum, map_smul, WithLp.ofLp_neg,
    WithLp.ofLp_sum, WithLp.ofLp_smul, Pi.neg_apply,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  simp_rw [modalCoordinates_inverseSqrtMassTransform_bondDirection]

/-- Coupling-independent finite-mode coefficient in the pointwise and
kinetic-time bounds. -/
def modalHigherRemainderCoefficient {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (k : Lattice.Site N)
    (r₀ rho amplitudeBound : Real) : Real :=
  kineticForceRemainderCoefficient r₀ rho amplitudeBound *
    modalBondL1Weight m k

/-- The selected modal higher residual is pointwise `O(g^3)` on a uniform
relative strain tube. -/
theorem abs_normalizedHigherResidualModalForce_le_g_cubed
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (k : Lattice.Site N)
    {depth r₀ g rho amplitudeBound : Real}
    (hdepth : 0 < depth) (hr₀ : 0 < r₀) (hg : 0 < g)
    (hrho0 : 0 ≤ rho) (hrho1 : rho < 1)
    (_hAmplitude : 0 ≤ amplitudeBound)
    (q : HilbertConfiguration N)
    (htube : ∀ i : Lattice.Site N,
      |g * Lattice.forwardDifference (asConfiguration q) i| ≤ rho * r₀)
    (hamplitude : ∀ i : Lattice.Site N,
      |Lattice.forwardDifference (asConfiguration q) i| ≤ amplitudeBound) :
    |normalizedHigherResidualModalForce m depth r₀ g q k| ≤
      modalHigherRemainderCoefficient m k r₀ rho amplitudeBound * g ^ 3 := by
  have hgNe : g ≠ 0 := ne_of_gt hg
  have hprefactor :
      0 ≤ r₀ / 72 * forceRemainderTubeConstant rho * |g| ^ 3 := by
    exact mul_nonneg
      (mul_nonneg (div_nonneg hr₀.le (by norm_num))
        (forceRemainderTubeConstant_pos hrho0 hrho1).le)
      (pow_nonneg (abs_nonneg g) 3)
  unfold normalizedHigherResidualModalForce
  rw [abs_neg]
  calc
    |∑ i : Lattice.Site N,
        normalizedForceRemainder depth r₀ g
            (Lattice.forwardDifference (asConfiguration q) i) *
          bondModeCoefficient m i k| ≤
      ∑ i : Lattice.Site N,
        |normalizedForceRemainder depth r₀ g
            (Lattice.forwardDifference (asConfiguration q) i) *
          bondModeCoefficient m i k| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : Lattice.Site N,
        (kineticForceRemainderCoefficient r₀ rho amplitudeBound * g ^ 3) *
          |bondModeCoefficient m i k| := by
      apply Finset.sum_le_sum
      intro i hi
      rw [abs_mul]
      have hpoint := abs_normalizedForceRemainder_le_g_cubed
        hdepth hr₀ hgNe hrho0 hrho1 (htube i)
      have hratio :
          |Lattice.forwardDifference (asConfiguration q) i| / r₀ ≤
            amplitudeBound / r₀ :=
        (div_le_div_iff_of_pos_right hr₀).2 (hamplitude i)
      have hpow :
          (|Lattice.forwardDifference (asConfiguration q) i| / r₀) ^ 4 ≤
            (amplitudeBound / r₀) ^ 4 :=
        pow_le_pow_left₀
          (div_nonneg (abs_nonneg _) hr₀.le) hratio 4
      have hres := hpoint.trans
        (mul_le_mul_of_nonneg_left hpow hprefactor)
      have hres' :
          |normalizedForceRemainder depth r₀ g
              (Lattice.forwardDifference (asConfiguration q) i)| ≤
            kineticForceRemainderCoefficient r₀ rho amplitudeBound * g ^ 3 := by
        simpa [kineticForceRemainderCoefficient, abs_of_pos hg,
          mul_comm, mul_left_comm, mul_assoc] using hres
      exact mul_le_mul_of_nonneg_right hres'
        (abs_nonneg (bondModeCoefficient m i k))
    _ = modalHigherRemainderCoefficient m k r₀ rho amplitudeBound *
        g ^ 3 := by
      unfold modalHigherRemainderCoefficient modalBondL1Weight
      rw [← Finset.mul_sum]
      ring

/-- The finite-mode higher residual accumulates to `O(g)` on the kinetic
window.  Integrability is explicit and returned with the estimate. -/
theorem intervalIntegrable_and_norm_integral_modalHigherResidual_le_kinetic
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (k : Lattice.Site N)
    {depth r₀ g rho L amplitudeBound : Real}
    (hdepth : 0 < depth) (hr₀ : 0 < r₀) (hg : 0 < g)
    (hrho0 : 0 ≤ rho) (hrho1 : rho < 1)
    (hL : 0 ≤ L) (hAmplitude : 0 ≤ amplitudeBound)
    (q : Real → HilbertConfiguration N)
    (hIntegrable : IntervalIntegrable
      (fun t => normalizedHigherResidualModalForce
        m depth r₀ g (q t) k)
      MeasureTheory.volume 0 (kineticWindowTime g L))
    (htube : ∀ t ∈ Icc 0 (kineticWindowTime g L),
      ∀ i : Lattice.Site N,
        |g * Lattice.forwardDifference (asConfiguration (q t)) i| ≤ rho * r₀)
    (hamplitude : ∀ t ∈ Icc 0 (kineticWindowTime g L),
      ∀ i : Lattice.Site N,
        |Lattice.forwardDifference (asConfiguration (q t)) i| ≤ amplitudeBound) :
    IntervalIntegrable
        (fun t => normalizedHigherResidualModalForce
          m depth r₀ g (q t) k)
        MeasureTheory.volume 0 (kineticWindowTime g L) ∧
      ‖∫ t in 0..kineticWindowTime g L,
          normalizedHigherResidualModalForce m depth r₀ g (q t) k‖ ≤
        modalHigherRemainderCoefficient m k r₀ rho amplitudeBound * L * g := by
  refine ⟨hIntegrable, ?_⟩
  have htime : 0 ≤ kineticWindowTime g L := by
    unfold kineticWindowTime
    exact div_nonneg hL (sq_nonneg g)
  calc
    ‖∫ t in 0..kineticWindowTime g L,
        normalizedHigherResidualModalForce m depth r₀ g (q t) k‖ ≤
      (modalHigherRemainderCoefficient m k r₀ rho amplitudeBound * g ^ 3) *
        |kineticWindowTime g L - 0| := by
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro t ht
      have htIcc : t ∈ Icc 0 (kineticWindowTime g L) := by
        simpa only [uIcc_of_le htime] using Set.uIoc_subset_uIcc ht
      simpa [Real.norm_eq_abs] using
        abs_normalizedHigherResidualModalForce_le_g_cubed
          m k hdepth hr₀ hg hrho0 hrho1 hAmplitude (q t)
            (htube t htIcc) (hamplitude t htIcc)
    _ = modalHigherRemainderCoefficient m k r₀ rho amplitudeBound * L * g := by
      rw [sub_zero, abs_of_nonneg htime]
      unfold kineticWindowTime
      field_simp [ne_of_gt hg]

end

end ArchonPhysics.LennardJonesModalRemainderKineticBound
