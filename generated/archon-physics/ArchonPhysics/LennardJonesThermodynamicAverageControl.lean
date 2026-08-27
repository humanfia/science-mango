import ArchonPhysics.LennardJonesThermodynamicThreshold
import ArchonPhysics.LennardJonesQuantitativeTaylorTube

/-!
# Thermodynamic-average low-energy control for Lennard--Jones chains

This module combines the exact one-bond energy barrier with the quantitative
fourth-order Taylor estimate.  The resulting estimates are uniform in the
periodic volume `N`: at energy ratio `s = t^7` and relative tube radius
`rho = t^2`, the fraction of bonds outside the tube and the relative Taylor
remainder on the bonds inside the tube both vanish at order `t^3`, up to the
explicit continuous factor `fourthOrderTubeConstant (t^2)`.

These are static spatial-average estimates.  They do not assert stability of
the exact Lennard--Jones flow on kinetic time scales.
-/

namespace ArchonPhysics.LennardJonesThermodynamicAverageControl

open LennardJonesPotential
open LennardJonesThermodynamicThreshold
open LennardJonesQuantitativeTaylorTube
open Filter
open scoped Topology

noncomputable section

/-- The exact tensile LJ barrier dominates the elementary quadratic barrier.
This comparison is valid at every nonnegative relative tube radius. -/
theorem elementaryRelativeTubeBarrier_le_relativeTubeBarrier
    {depth rho : Real} (hdepth : 0 <= depth) (hrho : 0 <= rho) :
    elementaryRelativeTubeBarrier depth rho <=
      relativeTubeBarrier depth rho := by
  have hden : 0 < 1 + rho := by linarith
  let z : Real := 1 / (1 + rho)
  have hz0 : 0 <= z := by
    dsimp [z]
    positivity
  have hz1 : z <= 1 := by
    dsimp [z]
    exact (div_le_one hden).2 (by linarith)
  have honeSub : 0 <= 1 - z := by linarith
  have hsum : 1 <= 1 + z + z ^ 2 + z ^ 3 + z ^ 4 + z ^ 5 := by
    nlinarith [pow_nonneg hz0 2, pow_nonneg hz0 3,
      pow_nonneg hz0 4, pow_nonneg hz0 5]
  have hlinear : 1 - z <= 1 - z ^ 6 := by
    rw [show 1 - z ^ 6 =
      (1 - z) * (1 + z + z ^ 2 + z ^ 3 + z ^ 4 + z ^ 5) by ring]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hsum honeSub
  have hratio : rho / (1 + rho) = 1 - z := by
    dsimp [z]
    field_simp [ne_of_gt hden]
    ring
  have hright : 0 <= 1 - z ^ 6 := honeSub.trans hlinear
  have hsquare : (rho / (1 + rho)) ^ 2 <= (1 - z ^ 6) ^ 2 := by
    rw [hratio]
    exact (sq_le_sq₀ honeSub hright).2 hlinear
  unfold elementaryRelativeTubeBarrier relativeTubeBarrier
  dsimp [z] at hsquare
  exact mul_le_mul_of_nonneg_left hsquare hdepth

/-- The actual periodic Hamiltonian density is nonnegative. -/
theorem periodicEnergyDensity_nonneg
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    {depth r0 : Real} (hdepth : 0 <= depth)
    (p q : Lattice.Configuration N) :
    0 <= periodicEnergyDensity m depth r0 p q := by
  unfold periodicEnergyDensity
  exact div_nonneg
    (periodicRandomMassHamiltonian_nonneg m hdepth p q)
    (Nat.cast_nonneg N)

/-- Fixed energy density controls the fraction of actual periodic bonds
outside the Taylor tube by the elementary closed-form barrier. -/
theorem badBondFraction_le_energyRatio_mul_elementaryFactor
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    {depth r0 rho : Real}
    (hdepth : 0 < depth) (hr0 : 0 < r0) (hrho : 0 < rho)
    (p q : Lattice.Configuration N)
    (hadmissible : AdmissibleConfiguration r0 q) :
    badBondFraction r0 rho q <=
      (periodicEnergyDensity m depth r0 p q / depth) *
        (1 + rho) ^ 2 / rho ^ 2 := by
  have helementary : 0 < elementaryRelativeTubeBarrier depth rho :=
    elementaryRelativeTubeBarrier_pos hdepth hrho
  have hbarrierOrder : elementaryRelativeTubeBarrier depth rho <=
      relativeTubeBarrier depth rho :=
    elementaryRelativeTubeBarrier_le_relativeTubeBarrier hdepth.le hrho.le
  have hsharp : 0 < relativeTubeBarrier depth rho :=
    helementary.trans_le hbarrierOrder
  have hbad := badBondFraction_le_energyDensity_div_barrier
    m hdepth.le hr0 hrho.le hsharp p q hadmissible
  have henergy : 0 <= periodicEnergyDensity m depth r0 p q :=
    periodicEnergyDensity_nonneg m hdepth.le p q
  calc
    badBondFraction r0 rho q <=
        periodicEnergyDensity m depth r0 p q /
          relativeTubeBarrier depth rho := hbad
    _ <= periodicEnergyDensity m depth r0 p q /
          elementaryRelativeTubeBarrier depth rho :=
      div_le_div_of_nonneg_left henergy helementary hbarrierOrder
    _ = (periodicEnergyDensity m depth r0 p q / depth) *
          (1 + rho) ^ 2 / rho ^ 2 := by
      unfold elementaryRelativeTubeBarrier
      have hden : 1 + rho ≠ 0 := ne_of_gt (by linarith)
      field_simp [ne_of_gt hdepth, ne_of_gt hrho, hden]

/-- On the actual forward differences, the Taylor remainder restricted to
good bonds has an `N`-independent per-site bound.  Bad bonds are omitted
explicitly and are controlled separately by the counting estimate above. -/
theorem forwardDifference_goodBondRemainder_le_tubePower
    {N : Nat} [NeZero N]
    {depth r0 rho : Real} (q : Lattice.Configuration N)
    (hdepth : 0 <= depth) (hr0 : 0 < r0)
    (hrho0 : 0 <= rho) (hrho1 : rho < 1) :
    perSiteGoodBondAbsoluteFourthOrderRemainder depth r0 rho
        (fun i => Lattice.forwardDifference q i) <=
      depth * fourthOrderTubeConstant rho * rho ^ 5 := by
  let strain : Lattice.Site N -> Real :=
    fun i => Lattice.forwardDifference q i
  have hrestricted :=
    perSiteGoodBondAbsoluteFourthOrderRemainder_le_cardFraction
      strain hdepth hr0 hrho0 hrho1
  have hN : 0 < (N : Real) := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have hcard :
      ((relativeTaylorGoodBondSet r0 rho strain).card : Real) / (N : Real) <= 1 := by
    apply (div_le_one hN).2
    have hcardNat : (relativeTaylorGoodBondSet r0 rho strain).card <= N := by
      simpa [Lattice.Site] using
        Finset.card_le_univ (relativeTaylorGoodBondSet r0 rho strain)
    exact_mod_cast hcardNat
  have hcoefficient :
      0 <= depth * fourthOrderTubeConstant rho * rho ^ 5 := by
    exact mul_nonneg
      (mul_nonneg hdepth (fourthOrderTubeConstant_nonneg hrho0 hrho1))
      (pow_nonneg hrho0 5)
  dsimp [strain] at hrestricted hcard ⊢
  calc
    perSiteGoodBondAbsoluteFourthOrderRemainder depth r0 rho
        (fun i => Lattice.forwardDifference q i) <=
      depth * fourthOrderTubeConstant rho * rho ^ 5 *
          ((relativeTaylorGoodBondSet r0 rho
            (fun i => Lattice.forwardDifference q i)).card : Real) / (N : Real) :=
      hrestricted
    _ = (depth * fourthOrderTubeConstant rho * rho ^ 5) *
          (((relativeTaylorGoodBondSet r0 rho
            (fun i => Lattice.forwardDifference q i)).card : Real) / (N : Real)) := by
      ring
    _ <= depth * fourthOrderTubeConstant rho * rho ^ 5 := by
      simpa only [mul_one] using
        mul_le_mul_of_nonneg_left hcard hcoefficient

/-- Explicit `N`-independent bad-bond right-hand side in the balanced regime. -/
def balancedBadBondUpperBound (t : Real) : Real :=
  t ^ 3 * (1 + t ^ 2) ^ 2

/-- Explicit relative good-bond Taylor-remainder right-hand side in the same
balanced regime. -/
def balancedGoodBondRelativeRemainderUpperBound (t : Real) : Real :=
  fourthOrderTubeConstant (t ^ 2) * t ^ 3

/-- At energy-density ratio at most `t^7`, actual bad bonds occupy at most
`t^3 (1+t^2)^2` of the periodic lattice, uniformly in `N`. -/
theorem balanced_badBondFraction_le
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    {depth r0 t : Real}
    (hdepth : 0 < depth) (hr0 : 0 < r0)
    (ht0 : 0 < t) (_ht1 : t < 1)
    (p q : Lattice.Configuration N)
    (hadmissible : AdmissibleConfiguration r0 q)
    (henergyRatio : periodicEnergyDensity m depth r0 p q / depth <= t ^ 7) :
    badBondFraction r0 (t ^ 2) q <= balancedBadBondUpperBound t := by
  have hbase := badBondFraction_le_energyRatio_mul_elementaryFactor
    m hdepth hr0 (sq_pos_of_pos ht0) p q hadmissible
  have hfactor : 0 <= (1 + t ^ 2) ^ 2 / (t ^ 2) ^ 2 := by positivity
  have hscaled := mul_le_mul_of_nonneg_right henergyRatio hfactor
  calc
    badBondFraction r0 (t ^ 2) q <=
        (periodicEnergyDensity m depth r0 p q / depth) *
          (1 + t ^ 2) ^ 2 / (t ^ 2) ^ 2 := hbase
    _ <= t ^ 7 * ((1 + t ^ 2) ^ 2 / (t ^ 2) ^ 2) := by
      simpa only [mul_div_assoc] using hscaled
    _ = balancedBadBondUpperBound t := by
      unfold balancedBadBondUpperBound
      field_simp [ne_of_gt ht0]

/-- The good-bond Taylor remainder, divided by the reference energy density
`depth * t^7`, is at most `C(t^2)t^3`, uniformly in `N`. -/
theorem balanced_forwardDifference_goodBondRelativeRemainder_le
    {N : Nat} [NeZero N]
    {depth r0 t : Real} (q : Lattice.Configuration N)
    (hdepth : 0 < depth) (hr0 : 0 < r0)
    (ht0 : 0 < t) (ht1 : t < 1) :
    perSiteGoodBondAbsoluteFourthOrderRemainder depth r0 (t ^ 2)
          (fun i => Lattice.forwardDifference q i) /
        (depth * t ^ 7) <=
      balancedGoodBondRelativeRemainderUpperBound t := by
  have htube : t ^ 2 < 1 := by nlinarith [sq_pos_of_pos ht0]
  have hrem := forwardDifference_goodBondRemainder_le_tubePower
    q hdepth.le hr0 (sq_nonneg t) htube
  have hden : 0 < depth * t ^ 7 :=
    mul_pos hdepth (pow_pos ht0 7)
  apply (div_le_iff₀ hden).2
  calc
    perSiteGoodBondAbsoluteFourthOrderRemainder depth r0 (t ^ 2)
        (fun i => Lattice.forwardDifference q i) <=
      depth * fourthOrderTubeConstant (t ^ 2) * (t ^ 2) ^ 5 := hrem
    _ = balancedGoodBondRelativeRemainderUpperBound t *
          (depth * t ^ 7) := by
      unfold balancedGoodBondRelativeRemainderUpperBound
      ring

/-- The explicit tube constant converges to its fifth-order Taylor coefficient
`3864` as the balanced tube shrinks. -/
theorem fourthOrderTubeConstant_sq_tendsto_3864 :
    Tendsto (fun t : Real => fourthOrderTubeConstant (t ^ 2))
      (nhds 0) (nhds 3864) := by
  have hcontinuous :
      ContinuousAt (fun t : Real => fourthOrderTubeConstant (t ^ 2)) 0 := by
    unfold fourthOrderTubeConstant
    apply ContinuousAt.div
    · unfold dimensionlessFourthOrderNumerator
      fun_prop
    · fun_prop
    · norm_num
  simpa [fourthOrderTubeConstant, dimensionlessFourthOrderNumerator] using
    hcontinuous.tendsto

/-- Both volume-independent balanced error bounds vanish in the low-density
limit. -/
theorem balanced_upperBounds_tendsto_zero :
    Tendsto balancedBadBondUpperBound (nhds 0) (nhds 0) /\
      Tendsto balancedGoodBondRelativeRemainderUpperBound
        (nhds 0) (nhds 0) := by
  constructor
  · have hcontinuous : ContinuousAt balancedBadBondUpperBound 0 := by
      unfold balancedBadBondUpperBound
      fun_prop
    simpa [balancedBadBondUpperBound] using hcontinuous.tendsto
  · have hproduct := fourthOrderTubeConstant_sq_tendsto_3864.mul
      balanced_errorScale_tendsto_zero
    change Tendsto
      (fun t : Real => fourthOrderTubeConstant (t ^ 2) * t ^ 3)
      (nhds 0) (nhds 0)
    simpa only [mul_zero] using hproduct

/-- Epsilon form of the thermodynamic-average threshold.  For every requested
tolerance, sufficiently small positive `t` makes both explicit, `N`-uniform
right-hand sides smaller than that tolerance.  The corresponding admissible
energy-density ratio is `s = t^7`; no universal numerical tolerance is hidden
in this statement. -/
theorem eventually_balanced_upperBounds_lt
    {eta : Real} (heta : 0 < eta) :
    ∀ᶠ t : Real in nhdsWithin 0 (Set.Ioo 0 1),
      balancedBadBondUpperBound t < eta /\
        balancedGoodBondRelativeRemainderUpperBound t < eta := by
  have hlimits := balanced_upperBounds_tendsto_zero
  have hbad : ∀ᶠ t : Real in nhdsWithin 0 (Set.Ioo 0 1),
      balancedBadBondUpperBound t < eta :=
    (hlimits.1.eventually (Iio_mem_nhds heta)).filter_mono inf_le_left
  have hgood : ∀ᶠ t : Real in nhdsWithin 0 (Set.Ioo 0 1),
      balancedGoodBondRelativeRemainderUpperBound t < eta :=
    (hlimits.2.eventually (Iio_mem_nhds heta)).filter_mono inf_le_left
  exact hbad.and hgood

/-- A concrete parameter-threshold form of
`eventually_balanced_upperBounds_lt`.  For every tolerance there is a
nonzero interval of balanced parameters on which both volume-independent
errors meet that tolerance.  Thus `t0 ^ 7` is a strict, tolerance-dependent
energy-density ratio threshold. -/
theorem exists_balanced_parameter_threshold
    {eta : Real} (heta : 0 < eta) :
    ∃ t0 : Real, 0 < t0 ∧ t0 < 1 ∧
      ∀ t : Real, 0 < t → t < t0 →
        balancedBadBondUpperBound t < eta ∧
          balancedGoodBondRelativeRemainderUpperBound t < eta := by
  have hlimits := balanced_upperBounds_tendsto_zero
  have hbadDist : ∀ᶠ t : Real in nhds 0,
      dist (balancedBadBondUpperBound t) 0 < eta :=
    (Metric.tendsto_nhds.mp hlimits.1) eta heta
  have hgoodDist : ∀ᶠ t : Real in nhds 0,
      dist (balancedGoodBondRelativeRemainderUpperBound t) 0 < eta :=
    (Metric.tendsto_nhds.mp hlimits.2) eta heta
  have hboth : {t : Real |
      dist (balancedBadBondUpperBound t) 0 < eta ∧
        dist (balancedGoodBondRelativeRemainderUpperBound t) 0 < eta} ∈ nhds 0 :=
    hbadDist.and hgoodDist
  rw [Metric.mem_nhds_iff] at hboth
  obtain ⟨delta, hdelta, hball⟩ := hboth
  let t0 : Real := min (delta / 2) (1 / 2)
  have ht0pos : 0 < t0 := by
    dsimp [t0]
    exact lt_min (by positivity) (by norm_num)
  have ht0one : t0 < 1 := by
    calc
      t0 <= 1 / 2 := min_le_right _ _
      _ < 1 := by norm_num
  refine ⟨t0, ht0pos, ht0one, ?_⟩
  intro t ht hlt
  have htDelta : dist t 0 < delta := by
    rw [Real.dist_eq, sub_zero, abs_of_pos ht]
    have htHalf : t < delta / 2 :=
      hlt.trans_le (min_le_left (delta / 2) (1 / 2))
    linarith
  have htBall : t ∈ Metric.ball 0 delta := by
    simpa only [Metric.mem_ball, dist_comm] using htDelta
  have herrors := hball htBall
  change dist (balancedBadBondUpperBound t) 0 < eta ∧
    dist (balancedGoodBondRelativeRemainderUpperBound t) 0 < eta at herrors
  constructor
  · have hbadAbs := herrors.1
    rw [Real.dist_eq, sub_zero] at hbadAbs
    exact (le_abs_self (balancedBadBondUpperBound t)).trans_lt hbadAbs
  · have hgoodAbs := herrors.2
    rw [Real.dist_eq, sub_zero] at hgoodAbs
    exact
      (le_abs_self (balancedGoodBondRelativeRemainderUpperBound t)).trans_lt
        hgoodAbs

end

end ArchonPhysics.LennardJonesThermodynamicAverageControl
