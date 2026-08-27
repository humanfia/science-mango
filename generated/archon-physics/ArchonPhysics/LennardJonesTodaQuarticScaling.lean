import ArchonPhysics.LennardJonesThermodynamicHittingTransfer

/-!
# Lennard--Jones scaling relative to the matched-Toda quartic coefficient

This module isolates the fourth-order defect between the normalized
Lennard--Jones jet and the Toda exponential whose quadratic and cubic
coefficients agree with that jet.  If `e` is the energy-density scale, then
the harmonic amplitude squared is `e / k`, and the positive dimensionless
quartic defect is exactly

`delta_T = 35 / 216 * (e / depth)`.

Consequently a kinetic law `delta_T^2 T -> tau4` converts exactly to

`(e / depth)^2 T -> (216 / 35)^2 tau4`.

The conversion is algebraic.  The conditional transfer below keeps the
microscopic-to-kinetic convergence and robust first crossing as explicit
certificate fields, and it makes `N_j -> infinity`, `e_j -> 0`, and the size
cutoff simultaneous.  A Toda-integrable baseline can justify this comparison
in settings where Toda integrability really holds, for example an appropriate
equal-mass chain.  Unequal frozen random masses do not inherit standard Toda
integrability, so this module makes no such claim for that model.  Ordinary
Yukawa nearest-neighbor dynamics is likewise not asserted to be integrable.
-/

namespace ArchonPhysics.LennardJonesTodaQuarticScaling

open Filter MeasureTheory Set Topology
open ThermalizationTransfer
open LennardJonesPotential
open LennardJonesThermodynamicThreshold
open LennardJonesThermodynamicHittingTransfer

noncomputable section

/-- Harmonic displacement amplitude squared at energy-density scale `e`. -/
def harmonicAmplitudeSquared (depth r₀ e : Real) : Real :=
  e / harmonicStiffness depth r₀

/-- Positive signed magnitude of the LJ quartic coefficient defect relative
to the quadratic/cubic-matched Toda exponential. -/
def positiveTodaBreakingCoupling (depth r₀ e : Real) : Real :=
  -(LennardJonesAlphaBetaBridge.normalizedBeta depth r₀ -
      matchedTodaBeta
        (LennardJonesAlphaBetaBridge.normalizedAlpha depth r₀)) *
    harmonicAmplitudeSquared depth r₀ e

/-- The equilibrium length cancels from the dimensionless Toda-breaking
quartic coupling. -/
theorem positiveTodaBreakingCoupling_eq
    {depth r₀ e : Real} (hdepth : 0 < depth) (hr₀ : 0 < r₀) :
    positiveTodaBreakingCoupling depth r₀ e =
      (35 / 216 : Real) * (e / depth) := by
  rw [positiveTodaBreakingCoupling, harmonicAmplitudeSquared,
    normalizedBeta_sub_matchedTodaBeta hdepth hr₀]
  unfold harmonicStiffness
  field_simp [ne_of_gt hdepth, ne_of_gt hr₀]
  ring

/-- At positive energy density the Toda-breaking coupling is positive. -/
theorem positiveTodaBreakingCoupling_pos
    {depth r₀ e : Real} (hdepth : 0 < depth) (hr₀ : 0 < r₀)
    (he : 0 < e) :
    0 < positiveTodaBreakingCoupling depth r₀ e := by
  rw [positiveTodaBreakingCoupling_eq hdepth hr₀]
  exact mul_pos (by norm_num) (div_pos he hdepth)

/-- Exact square law for the quartic defect. -/
theorem positiveTodaBreakingCoupling_sq
    {depth r₀ e : Real} (hdepth : 0 < depth) (hr₀ : 0 < r₀) :
    positiveTodaBreakingCoupling depth r₀ e ^ 2 =
      (35 / 216 : Real) ^ 2 * (e / depth) ^ 2 := by
  rw [positiveTodaBreakingCoupling_eq hdepth hr₀]
  ring

/-- Any cutoff on the positive quartic defect converts into an exact
`N`-independent energy-density-ratio cutoff.  The existence of a dynamical
theorem valid up to `deltaStar` remains an independent input. -/
theorem energyRatio_le_of_positiveTodaBreakingCoupling_le
    {depth r₀ e deltaStar : Real}
    (hdepth : 0 < depth) (hr₀ : 0 < r₀)
    (hdelta : positiveTodaBreakingCoupling depth r₀ e ≤ deltaStar) :
    e / depth ≤ (216 / 35 : Real) * deltaStar := by
  rw [positiveTodaBreakingCoupling_eq hdepth hr₀] at hdelta
  nlinarith

/-- Simultaneous low-energy and thermodynamic path for the quartic defect.

The cutoff is evaluated at the actual energy-dependent Toda-breaking
coupling.  Thus the volume limit, weak-defect limit, and their relative rate
are all visible in the type. -/
structure AdmissibleLennardJonesTodaDefectJointLimit
    (sizeCutoff : Real → Nat) (depth r₀ : Real) where
  systemSize : Nat → Nat
  energyDensity : Nat → Real
  energyDensity_pos : ∀ j, 0 < energyDensity j
  energyDensity_tendsto_zero :
    Tendsto energyDensity atTop (nhdsWithin 0 (Ioi 0))
  systemSize_tendsto_atTop : Tendsto systemSize atTop atTop
  eventually_sizeCutoff :
    ∀ᶠ j in atTop,
      sizeCutoff
          (positiveTodaBreakingCoupling depth r₀ (energyDensity j)) ≤
        systemSize j

/-- Along an admissible LJ path, the positive quartic defect tends to zero
from the positive side. -/
theorem AdmissibleLennardJonesTodaDefectJointLimit.coupling_tendsto_zero
    {sizeCutoff : Real → Nat} {depth r₀ : Real}
    (s : AdmissibleLennardJonesTodaDefectJointLimit sizeCutoff depth r₀)
    (hdepth : 0 < depth) (hr₀ : 0 < r₀) :
    Tendsto
      (fun j => positiveTodaBreakingCoupling depth r₀ (s.energyDensity j))
      atTop (nhdsWithin 0 (Ioi 0)) := by
  have he_zero :
      Tendsto s.energyDensity atTop (nhds (0 : Real)) :=
    s.energyDensity_tendsto_zero.mono_right nhdsWithin_le_nhds
  have hcontinuous :
      ContinuousAt (positiveTodaBreakingCoupling depth r₀) 0 := by
    unfold positiveTodaBreakingCoupling harmonicAmplitudeSquared
    fun_prop
  have hzero : positiveTodaBreakingCoupling depth r₀ 0 = 0 := by
    simp [positiveTodaBreakingCoupling, harmonicAmplitudeSquared]
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · change Tendsto
      (positiveTodaBreakingCoupling depth r₀ ∘ s.energyDensity)
      atTop (nhds 0)
    rw [← hzero]
    exact hcontinuous.tendsto.comp he_zero
  · exact Filter.Eventually.of_forall fun j =>
      positiveTodaBreakingCoupling_pos hdepth hr₀ (s.energyDensity_pos j)

/-- Forgetting the energy coordinate gives the generic weak-coupling path
consumed by the probabilistic hitting-time transfer. -/
def AdmissibleLennardJonesTodaDefectJointLimit.toAdmissibleJointLimit
    {sizeCutoff : Real → Nat} {depth r₀ : Real}
    (s : AdmissibleLennardJonesTodaDefectJointLimit sizeCutoff depth r₀)
    (hdepth : 0 < depth) (hr₀ : 0 < r₀) :
    AdmissibleJointLimit sizeCutoff where
  systemSize := s.systemSize
  coupling := fun j =>
    positiveTodaBreakingCoupling depth r₀ (s.energyDensity j)
  coupling_pos := fun j =>
    positiveTodaBreakingCoupling_pos hdepth hr₀ (s.energyDensity_pos j)
  coupling_tendsto_zero := s.coupling_tendsto_zero hdepth hr₀
  systemSize_tendsto_atTop := s.systemSize_tendsto_atTop
  eventually_sizeCutoff := s.eventually_sizeCutoff

/-- The microscopic hitting time scaled by the squared LJ energy ratio. -/
def scaledSquaredEnergyRatioEquilibrationTime {Omega : Type*}
    (equilibrationTime : Nat → Real → Omega → ENNReal)
    (depth r₀ : Real) (N : Nat) (e : Real) (omega : Omega) : ENNReal :=
  ENNReal.ofReal ((e / depth) ^ 2) *
    equilibrationTime N (positiveTodaBreakingCoupling depth r₀ e) omega

/-- Pointwise conversion from `delta_T^2 T` to `(e / depth)^2 T`.

The equality is in `ENNReal`, so a non-occurring hit remains `top`. -/
theorem scaledSquaredEnergyRatioEquilibrationTime_eq_const_mul_scaled
    {Omega : Type*}
    (equilibrationTime : Nat → Real → Omega → ENNReal)
    {depth r₀ e : Real} (hdepth : 0 < depth) (hr₀ : 0 < r₀)
    (N : Nat) (omega : Omega) :
    scaledSquaredEnergyRatioEquilibrationTime equilibrationTime
        depth r₀ N e omega =
      ENNReal.ofReal ((216 / 35 : Real) ^ 2) *
        scaledEquilibrationTime equilibrationTime N
          (positiveTodaBreakingCoupling depth r₀ e) omega := by
  have hreal :
      (e / depth) ^ 2 =
        (216 / 35 : Real) ^ 2 *
          positiveTodaBreakingCoupling depth r₀ e ^ 2 := by
    rw [positiveTodaBreakingCoupling_sq hdepth hr₀]
    ring
  unfold scaledSquaredEnergyRatioEquilibrationTime scaledEquilibrationTime
  rw [hreal, ENNReal.ofReal_mul (sq_nonneg (216 / 35 : Real))]
  rw [mul_assoc]

/-- Transparent conditional package for the quartic-defect kinetic scaling.

The microscopic field is the long-time LJ-to-kinetic approximation and
physical hitting-time identification.  The crossing field is the independent
kinetic first-crossing theorem.  Neither is inferred from coefficient matching.
-/
structure LennardJonesTodaQuarticHittingCertificate
    {Omega : Type*} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (equilibrationTime : Nat → Real → Omega → ENNReal)
    (sizeCutoff : Real → Nat) (kineticDistance : Real → Real)
    (delta tau4 depth r₀ : Real) where
  depth_pos : 0 < depth
  equilibriumLength_pos : 0 < r₀
  microscopic : ConditionalThermalizationCertificate P equilibrationTime
    sizeCutoff kineticDistance delta
  robustCrossing : RobustKineticFirstCrossing kineticDistance delta tau4

/-- Along every explicit low-energy/large-volume path, a conditional
`delta_T^2 T -> tau4` law becomes
`(e / depth)^2 T -> (216 / 35)^2 tau4` in probability. -/
theorem LennardJonesTodaQuarticHittingCertificate.squaredEnergyRatioTime_law
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
      (ENNReal.ofReal (((216 / 35 : Real) ^ 2) * tau4)) := by
  let jointLimit : AdmissibleJointLimit sizeCutoff :=
    s.toAdmissibleJointLimit certificate.depth_pos
      certificate.equilibriumLength_pos
  have hdelta2 : G2TeqConvergesInProbability P equilibrationTime
      sizeCutoff tau4 :=
    certificate.microscopic.toG2TeqConvergesInProbability
      P equilibrationTime sizeCutoff kineticDistance delta tau4
      certificate.robustCrossing
  have hscaled := ConvergesInProbabilityTo.const_mul P
    (hdelta2.law jointLimit)
    (ENNReal.ofReal_ne_top :
      ENNReal.ofReal ((216 / 35 : Real) ^ 2) ≠ ⊤)
  have hsequence :
      (fun j omega =>
        scaledSquaredEnergyRatioEquilibrationTime equilibrationTime
          depth r₀ (s.systemSize j) (s.energyDensity j) omega) =
      (fun j omega => ENNReal.ofReal ((216 / 35 : Real) ^ 2) *
        scaledEquilibrationTime equilibrationTime
          (jointLimit.systemSize j) (jointLimit.coupling j) omega) := by
    funext j omega
    simpa [jointLimit,
      AdmissibleLennardJonesTodaDefectJointLimit.toAdmissibleJointLimit] using
      (scaledSquaredEnergyRatioEquilibrationTime_eq_const_mul_scaled
        equilibrationTime certificate.depth_pos
        certificate.equilibriumLength_pos (s.systemSize j) omega)
  rw [hsequence]
  simpa only [ENNReal.ofReal_mul (sq_nonneg (216 / 35 : Real))] using hscaled

/-- Every finite interval strictly bracketing the converted target has
probability tending to one. -/
theorem LennardJonesTodaQuarticHittingCertificate.tendsto_measure_window
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
      atTop (nhds 1) := by
  have htarget_pos : 0 < (216 / 35 : Real) ^ 2 * tau4 :=
    mul_pos (sq_pos_of_pos (by norm_num)) certificate.robustCrossing.tauStar_pos
  exact (certificate.squaredEnergyRatioTime_law P equilibrationTime sizeCutoff
    kineticDistance delta tau4 depth r₀ s).tendsto_measure_preimage_Icc
      ((ENNReal.ofReal_lt_ofReal_iff htarget_pos).2 hlower)
      ((ENNReal.ofReal_lt_ofReal_iff (htarget_pos.trans hupper)).2 hupper)

end

end ArchonPhysics.LennardJonesTodaQuarticScaling
