import Family8Grounding.Family8StickyMassPopularFixedKatzTaoPowerEnvelopeV1
import Mathlib.Tactic

/-!
# Global-power consequence of a shading-aware density floor

The geometric density floor contains the exact relative-square gain hidden in
`fineDelta^2 / rho^2`.  Its geometry scale may differ from the global small
parameter used to absorb cover, branching, and numerical costs.  Separating
the two is essential on the genuine `tau -> b` LongCore interval.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 700000

open scoped ENNReal NNReal

namespace Family8ShadingAwareDensityFloorGlobalPowerV1

open Family8StickyMassPopularFixedKatzTaoPowerEnvelopeV1

noncomputable section

/-- A cross-multiplied source-density floor plus honest power caps implies
the exact relative density ratio used by the contracted-John endpoint. -/
theorem densityRatio_of_densityFloor_and_globalPowerCaps
    {globalDelta delta rho : NNReal} {sourceA coverLoss branching density : ENNReal}
    {eta p a etaF coverExp branchExp absorbExp scaleExp : Real}
    (hglobal : 0 < globalDelta) (hglobalOne : globalDelta ≤ 1)
    (hdelta : 0 < delta) (hrho : 0 < rho)
    (hcover0 : coverLoss ≠ 0) (hcoverTop : coverLoss ≠ ∞)
    (hbranch0 : branching ≠ 0) (hbranchTop : branching ≠ ∞)
    (hfloor :
      (sourceA * ((rho : ENNReal) ^ 2 / 2)) /
          ((2 * coverLoss) *
            ((2 * branching) * (8 * (delta : ENNReal) ^ 2))) ≤ density)
    (hcover : 2 * coverLoss ≤ (globalDelta : ENNReal) ^ (-coverExp))
    (hbranch : 2 * branching ≤ (globalDelta : ENNReal) ^ (-branchExp))
    (hconstant : (2 * 8 * 93312 * 128 : ENNReal) ≤
      (globalDelta : ENNReal) ^ (-absorbExp))
    (hq : ((delta : ENNReal) / (rho : ENNReal)) ≤
      (globalDelta : ENNReal) ^ scaleExp)
    (hgain : 0 ≤ eta - (p + a) + 2)
    (hbudget : 2 * etaF + coverExp + branchExp + absorbExp ≤
      scaleExp * (eta - (p + a) + 2))
    (hsource : (globalDelta : ENNReal) ^ (2 * etaF) ≤ sourceA) :
    ((delta : ENNReal) / (rho : ENNReal)) ^ (eta - (p + a)) ≤
      density / 93312 / 128 := by
  let q : ENNReal := (delta : ENNReal) / (rho : ENNReal)
  let gain : Real := eta - (p + a) + 2
  let denominator : ENNReal :=
    (2 * coverLoss) *
      ((2 * branching) * (8 * (delta : ENNReal) ^ 2))
  let target : ENNReal := q ^ (eta - (p + a)) * 93312 * 128
  have hq0 : q ≠ 0 := by
    dsimp only [q]
    exact ENNReal.div_ne_zero.mpr
      ⟨ENNReal.coe_ne_zero.mpr hdelta.ne', ENNReal.coe_ne_top⟩
  have hqTop : q ≠ ∞ := by
    dsimp only [q]
    exact ENNReal.div_ne_top ENNReal.coe_ne_top
      (ENNReal.coe_ne_zero.mpr hrho.ne')
  have hrho0 : (rho : ENNReal) ≠ 0 :=
    ENNReal.coe_ne_zero.mpr hrho.ne'
  have hratio : q * (rho : ENNReal) = (delta : ENNReal) := by
    dsimp only [q]
    exact ENNReal.div_mul_cancel hrho0 ENNReal.coe_ne_top
  have hratioSq : q ^ (2 : Nat) * (rho : ENNReal) ^ 2 =
      (delta : ENNReal) ^ 2 := by
    calc
      q ^ (2 : Nat) * (rho : ENNReal) ^ 2 =
          (q * (rho : ENNReal)) ^ 2 := by ring
      _ = (delta : ENNReal) ^ 2 := by rw [hratio]
  have hratioSqR : q ^ (2 : Real) * (rho : ENNReal) ^ 2 =
      (delta : ENNReal) ^ 2 := by
    rw [ENNReal.rpow_two]
    exact hratioSq
  have hqGain : q ^ gain * (rho : ENNReal) ^ 2 =
      q ^ (eta - (p + a)) * (delta : ENNReal) ^ 2 := by
    rw [show gain = (eta - (p + a)) + 2 by simp only [gain]]
    rw [ENNReal.rpow_add _ _ hq0 hqTop]
    calc
      (q ^ (eta - (p + a)) * q ^ (2 : Real)) *
          (rho : ENNReal) ^ 2 =
        q ^ (eta - (p + a)) *
          (q ^ (2 : Real) * (rho : ENNReal) ^ 2) := by ring
      _ = q ^ (eta - (p + a)) * (delta : ENNReal) ^ 2 := by
        rw [hratioSqR]
  have htwoHalf :
      (2 : ENNReal) * ((rho : ENNReal) ^ 2 / 2) =
        (rho : ENNReal) ^ 2 := by
    calc
      (2 : ENNReal) * ((rho : ENNReal) ^ 2 / 2) =
          ((rho : ENNReal) ^ 2 / 2) * 2 := by ring
      _ = (rho : ENNReal) ^ 2 := by
        rw [ENNReal.div_mul_cancel (by norm_num) (by norm_num)]
  have hcore := fixedPowerCore_le_source
    hglobal hglobalOne hcover hbranch hconstant hq hgain hbudget hsource
  have hscaled :
      ((2 * 8 * 93312 * 128 : ENNReal) *
          ((2 * coverLoss) * (2 * branching) * q ^ gain)) *
          ((rho : ENNReal) ^ 2 / 2) ≤
        sourceA * ((rho : ENNReal) ^ 2 / 2) := by
    simpa only [q, gain, mul_assoc] using
      (mul_le_mul' hcore
        (le_refl ((rho : ENNReal) ^ 2 / 2)))
  have hleftIdentity :
      ((2 * 8 * 93312 * 128 : ENNReal) *
          ((2 * coverLoss) * (2 * branching) * q ^ gain)) *
          ((rho : ENNReal) ^ 2 / 2) = denominator * target := by
    calc
      ((2 * 8 * 93312 * 128 : ENNReal) *
          ((2 * coverLoss) * (2 * branching) * q ^ gain)) *
          ((rho : ENNReal) ^ 2 / 2) =
        (8 * 93312 * 128 : ENNReal) *
          ((2 * coverLoss) * (2 * branching)) *
            (q ^ gain *
              ((2 : ENNReal) * ((rho : ENNReal) ^ 2 / 2))) := by ring
      _ = (8 * 93312 * 128 : ENNReal) *
          ((2 * coverLoss) * (2 * branching)) *
            (q ^ gain * (rho : ENNReal) ^ 2) := by rw [htwoHalf]
      _ = (8 * 93312 * 128 : ENNReal) *
          ((2 * coverLoss) * (2 * branching)) *
            (q ^ (eta - (p + a)) * (delta : ENNReal) ^ 2) := by
        rw [hqGain]
      _ = denominator * target := by
        dsimp only [denominator, target]
        ring
  have hcross : denominator * target ≤
      sourceA * ((rho : ENNReal) ^ 2 / 2) := by
    rw [← hleftIdentity]
    exact hscaled
  have hdeltaTop : (delta : ENNReal) ^ 2 ≠ ∞ :=
    ENNReal.pow_ne_top ENNReal.coe_ne_top
  have hdenominator0 : denominator ≠ 0 := by
    dsimp only [denominator]
    exact mul_ne_zero (mul_ne_zero (by norm_num) hcover0)
      (mul_ne_zero (mul_ne_zero (by norm_num) hbranch0)
        (mul_ne_zero (by norm_num)
          (pow_ne_zero 2 (ENNReal.coe_ne_zero.mpr hdelta.ne'))))
  have hdenominatorTop : denominator ≠ ∞ := by
    dsimp only [denominator]
    exact ENNReal.mul_ne_top
      (ENNReal.mul_ne_top (by norm_num) hcoverTop)
      (ENNReal.mul_ne_top
        (ENNReal.mul_ne_top (by norm_num) hbranchTop)
        (ENNReal.mul_ne_top (by norm_num) hdeltaTop))
  have htargetFloor : target ≤
      (sourceA * ((rho : ENNReal) ^ 2 / 2)) / denominator :=
    (ENNReal.le_div_iff_mul_le (Or.inl hdenominator0)
      (Or.inl hdenominatorTop)).2 (by
        simpa only [mul_comm] using hcross)
  have htargetDensity : target ≤ density :=
    htargetFloor.trans (by simpa only [denominator] using hfloor)
  apply (ENNReal.le_div_iff_mul_le (Or.inl (by norm_num))
    (Or.inl (by norm_num))).2
  apply (ENNReal.le_div_iff_mul_le (Or.inl (by norm_num))
    (Or.inl (by norm_num))).2
  simpa only [target, q, mul_assoc, mul_left_comm, mul_comm] using
    htargetDensity

#print axioms densityRatio_of_densityFloor_and_globalPowerCaps

end
end Family8ShadingAwareDensityFloorGlobalPowerV1
