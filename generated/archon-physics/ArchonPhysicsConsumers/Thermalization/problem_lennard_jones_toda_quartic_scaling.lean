import ArchonPhysics.LennardJonesTodaQuarticScaling

/-!
# Consumer: LJ quartic-defect scaling relative to matched Toda

The coefficient identities below are exact.  The hitting-time result is
deliberately conditional on a microscopic convergence certificate and robust
kinetic crossing.  Matched Toda is a valid integrable comparison only in a
setting where the Toda chain itself is integrable, such as the appropriate
equal-mass model; frozen unequal random masses do not gain that property.
-/

namespace ArchonPhysicsConsumers.Thermalization

open Filter MeasureTheory Set Topology
open ArchonPhysics
open ArchonPhysics.ThermalizationTransfer
open ArchonPhysics.LennardJonesTodaQuarticScaling

noncomputable section

theorem problem_lj_toda_quartic_defect_exact
    {depth r₀ e : Real} (hdepth : 0 < depth) (hr₀ : 0 < r₀) :
    positiveTodaBreakingCoupling depth r₀ e =
        (35 / 216 : Real) * (e / depth) ∧
      positiveTodaBreakingCoupling depth r₀ e ^ 2 =
        (35 / 216 : Real) ^ 2 * (e / depth) ^ 2 := by
  exact ⟨positiveTodaBreakingCoupling_eq hdepth hr₀,
    positiveTodaBreakingCoupling_sq hdepth hr₀⟩

theorem problem_lj_toda_quartic_cutoff
    {depth r₀ e deltaStar : Real}
    (hdepth : 0 < depth) (hr₀ : 0 < r₀)
    (hdelta : positiveTodaBreakingCoupling depth r₀ e ≤ deltaStar) :
    e / depth ≤ (216 / 35 : Real) * deltaStar :=
  energyRatio_le_of_positiveTodaBreakingCoupling_le
    hdepth hr₀ hdelta

def problem_lj_toda_toAdmissibleJointLimit
    {sizeCutoff : Real → Nat} {depth r₀ : Real}
    (s : AdmissibleLennardJonesTodaDefectJointLimit sizeCutoff depth r₀)
    (hdepth : 0 < depth) (hr₀ : 0 < r₀) :
    AdmissibleJointLimit sizeCutoff :=
  s.toAdmissibleJointLimit hdepth hr₀

theorem problem_lj_toda_squaredEnergyRatioTime_law
    {Omega : Type*} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (equilibrationTime : Nat → Real → Omega → ENNReal)
    (sizeCutoff : Real → Nat) (kineticDistance : Real → Real)
    (delta tau4 depth r₀ : Real)
    (certificate : LennardJonesTodaQuarticHittingCertificate
      P equilibrationTime sizeCutoff kineticDistance delta tau4 depth r₀)
    (s : AdmissibleLennardJonesTodaDefectJointLimit sizeCutoff depth r₀) :
    ConvergesInProbabilityTo P
      (fun j omega =>
        scaledSquaredEnergyRatioEquilibrationTime equilibrationTime
          depth r₀ (s.systemSize j) (s.energyDensity j) omega)
      (ENNReal.ofReal (((216 / 35 : Real) ^ 2) * tau4)) :=
  certificate.squaredEnergyRatioTime_law P equilibrationTime sizeCutoff
    kineticDistance delta tau4 depth r₀ s

theorem problem_lj_toda_tendsto_measure_window
    {Omega : Type*} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (equilibrationTime : Nat → Real → Omega → ENNReal)
    (sizeCutoff : Real → Nat) (kineticDistance : Real → Real)
    (delta tau4 depth r₀ lower upper : Real)
    (certificate : LennardJonesTodaQuarticHittingCertificate
      P equilibrationTime sizeCutoff kineticDistance delta tau4 depth r₀)
    (s : AdmissibleLennardJonesTodaDefectJointLimit sizeCutoff depth r₀)
    (hlower : lower < (216 / 35 : Real) ^ 2 * tau4)
    (hupper : (216 / 35 : Real) ^ 2 * tau4 < upper) :
    Tendsto
      (fun j => P ((fun omega =>
        scaledSquaredEnergyRatioEquilibrationTime equilibrationTime
          depth r₀ (s.systemSize j) (s.energyDensity j) omega) ⁻¹'
        Icc (ENNReal.ofReal lower) (ENNReal.ofReal upper)))
      atTop (nhds 1) :=
  certificate.tendsto_measure_window P equilibrationTime sizeCutoff
    kineticDistance delta tau4 depth r₀ lower upper s hlower hupper

#print axioms problem_lj_toda_quartic_defect_exact
#print axioms problem_lj_toda_quartic_cutoff
#print axioms problem_lj_toda_toAdmissibleJointLimit
#print axioms problem_lj_toda_squaredEnergyRatioTime_law
#print axioms problem_lj_toda_tendsto_measure_window

end

end ArchonPhysicsConsumers.Thermalization
