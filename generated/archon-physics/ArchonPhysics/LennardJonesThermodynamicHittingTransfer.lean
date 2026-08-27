import ArchonPhysics.ConditionalThermalizationCertificate
import ArchonPhysics.LennardJonesThermodynamicThreshold

/-!
# Conditional thermodynamic hitting-time transfer for Lennard--Jones chains

This module makes the two limiting variables explicit.  An admissible LJ path
has positive energy densities `e_j -> 0`, sizes `N_j -> infinity`, and eventually
lies above the model-specific cutoff evaluated at the positive magnitude of the
dimensionless cubic LJ coupling.

The microscopic-to-kinetic local-uniform convergence and robust kinetic first
crossing remain transparent certificate fields.  They are not inferred from a
Taylor expansion, a finite-volume calculation, or a Toda comparison.  Once
those inputs are supplied, the existing stable-hitting transfer gives
`g_LJ(e_j)^2 T_eq -> tauStar`; the exact LJ coefficient identity then gives

`(e_j / depth) T_eq -> (32 / 49) tauStar`

in probability, with all random times kept in `ENNReal`.
-/

namespace ArchonPhysics.LennardJonesThermodynamicHittingTransfer

open Filter MeasureTheory Set Topology
open ThermalizationTransfer
open LennardJonesThermodynamicThreshold

noncomputable section

/-- Positive magnitude of the signed dimensionless cubic LJ coupling.

The normalized cubic LJ coefficient is negative.  The thermodynamic joint-limit
API uses a positive weak coupling, so the admitted coupling is its negative.
Only its square enters the kinetic time scaling. -/
def kineticCouplingMagnitude (depth r₀ e : Real) : Real :=
  -dimensionlessEffectiveCubicCoupling depth r₀ e

/-- The LJ kinetic coupling magnitude is positive at positive energy density. -/
theorem kineticCouplingMagnitude_pos
    {depth r₀ e : Real} (hdepth : 0 < depth) (hr₀ : 0 < r₀)
    (he : 0 < e) :
    0 < kineticCouplingMagnitude depth r₀ e := by
  rw [kineticCouplingMagnitude, dimensionlessEffectiveCubicCoupling,
    LennardJonesAlphaBetaBridge.normalizedAlpha_eq hdepth hr₀]
  unfold LennardJonesPotential.harmonicStiffness
  have hk : 0 < 72 * depth / r₀ ^ 2 :=
    div_pos (mul_pos (by norm_num) hdepth) (sq_pos_of_pos hr₀)
  have hsqrt : 0 < Real.sqrt (e / (72 * depth / r₀ ^ 2)) :=
    Real.sqrt_pos.2 (div_pos he hk)
  have hcoefficient : 0 < (21 : Real) / (2 * r₀) :=
    div_pos (by norm_num) (mul_pos (by norm_num) hr₀)
  have hproduct := mul_pos hcoefficient hsqrt
  have heq :
      -((-21 : Real) / (2 * r₀) *
        Real.sqrt (e / (72 * depth / r₀ ^ 2))) =
        (21 : Real) / (2 * r₀) *
          Real.sqrt (e / (72 * depth / r₀ ^ 2)) := by ring
  rw [heq]
  exact hproduct

/-- Negating the signed coefficient does not alter the exact LJ square law. -/
theorem kineticCouplingMagnitude_sq
    {depth r₀ e : Real} (hdepth : 0 < depth) (hr₀ : 0 < r₀)
    (he : 0 ≤ e) :
    kineticCouplingMagnitude depth r₀ e ^ 2 =
      49 * e / (32 * depth) := by
  rw [kineticCouplingMagnitude, neg_sq]
  exact dimensionlessEffectiveCubicCoupling_sq hdepth hr₀ he

/-- A genuine simultaneous thermodynamic/low-energy path for the LJ chain.

The cutoff is evaluated at the actual energy-dependent positive coupling.  No
order of limits is hidden: both `N_j -> infinity` and `e_j -> 0` occur on the
same index, while `eventually_sizeCutoff` records the required relation between
them. -/
structure AdmissibleLennardJonesJointLimit
    (sizeCutoff : Real → Nat) (depth r₀ : Real) where
  /-- Finite periodic system size at the `j`th stage. -/
  systemSize : Nat → Nat
  /-- Energy density at the `j`th stage. -/
  energyDensity : Nat → Real
  /-- Every energy density is strictly positive. -/
  energyDensity_pos : ∀ j, 0 < energyDensity j
  /-- Energy density tends to zero from the positive side. -/
  energyDensity_tendsto_zero :
    Tendsto energyDensity atTop (nhdsWithin 0 (Ioi 0))
  /-- The volume tends to the thermodynamic limit. -/
  systemSize_tendsto_atTop : Tendsto systemSize atTop atTop
  /-- The joint path eventually lies above the microscopic size cutoff. -/
  eventually_sizeCutoff :
    ∀ᶠ j in atTop,
      sizeCutoff (kineticCouplingMagnitude depth r₀ (energyDensity j)) ≤
        systemSize j

/-- The energy-dependent LJ coupling tends to zero from the positive side. -/
theorem AdmissibleLennardJonesJointLimit.coupling_tendsto_zero
    {sizeCutoff : Real → Nat} {depth r₀ : Real}
    (s : AdmissibleLennardJonesJointLimit sizeCutoff depth r₀)
    (hdepth : 0 < depth) (hr₀ : 0 < r₀) :
    Tendsto
      (fun j => kineticCouplingMagnitude depth r₀ (s.energyDensity j))
      atTop (nhdsWithin 0 (Ioi 0)) := by
  have he_zero :
      Tendsto s.energyDensity atTop (nhds (0 : Real)) :=
    s.energyDensity_tendsto_zero.mono_right nhdsWithin_le_nhds
  have hcontinuous :
      ContinuousAt (kineticCouplingMagnitude depth r₀) 0 := by
    unfold kineticCouplingMagnitude dimensionlessEffectiveCubicCoupling
    fun_prop
  have hzero : kineticCouplingMagnitude depth r₀ 0 = 0 := by
    simp [kineticCouplingMagnitude, dimensionlessEffectiveCubicCoupling]
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · change Tendsto (kineticCouplingMagnitude depth r₀ ∘ s.energyDensity) atTop (nhds 0)
    rw [← hzero]
    exact hcontinuous.tendsto.comp he_zero
  · exact Filter.Eventually.of_forall fun j =>
      kineticCouplingMagnitude_pos hdepth hr₀ (s.energyDensity_pos j)

/-- Forgetting the energy coordinate produces the existing admissible
large-volume/weak-coupling path consumed by the kinetic transfer API. -/
def AdmissibleLennardJonesJointLimit.toAdmissibleJointLimit
    {sizeCutoff : Real → Nat} {depth r₀ : Real}
    (s : AdmissibleLennardJonesJointLimit sizeCutoff depth r₀)
    (hdepth : 0 < depth) (hr₀ : 0 < r₀) :
    AdmissibleJointLimit sizeCutoff where
  systemSize := s.systemSize
  coupling := fun j =>
    kineticCouplingMagnitude depth r₀ (s.energyDensity j)
  coupling_pos := fun j =>
    kineticCouplingMagnitude_pos hdepth hr₀ (s.energyDensity_pos j)
  coupling_tendsto_zero := s.coupling_tendsto_zero hdepth hr₀
  systemSize_tendsto_atTop := s.systemSize_tendsto_atTop
  eventually_sizeCutoff := s.eventually_sizeCutoff

/-- Constant finite multiplication preserves the repository's measurable-
neighborhood definition of convergence in probability. -/
theorem ConvergesInProbabilityTo.const_mul
    {Omega : Type*} [MeasurableSpace Omega] (P : Measure Omega)
    [IsProbabilityMeasure P]
    {X : Nat → Omega → ENNReal} {a c : ENNReal}
    (hX : ConvergesInProbabilityTo P X a) (hc : c ≠ ⊤) :
    ConvergesInProbabilityTo P
      (fun j omega => c * X j omega) (c * a) := by
  constructor
  · intro j
    exact (measurable_const_mul c).comp (hX.1 j)
  · intro U hU hUneighborhood
    have hpreimageNeighborhood :
        (fun x : ENNReal => c * x) ⁻¹' U ∈ 𝓝 a :=
      (ENNReal.continuous_const_mul hc).continuousAt hUneighborhood
    have hlimit := hX.2
      ((fun x : ENNReal => c * x) ⁻¹' U)
      (hU.preimage (measurable_const_mul c))
      hpreimageNeighborhood
    simpa only [preimage_preimage, Function.comp_apply] using hlimit

/-- LJ energy-density scaling of the unscaled microscopic hitting time.

The coupling argument of `equilibrationTime` is the positive LJ cubic
magnitude.  Multiplication in `ENNReal` preserves a non-occurring hit `top`. -/
def scaledEnergyDensityEquilibrationTime {Omega : Type*}
    (equilibrationTime : Nat → Real → Omega → ENNReal)
    (depth r₀ : Real) (N : Nat) (e : Real) (omega : Omega) : ENNReal :=
  ENNReal.ofReal (e / depth) *
    equilibrationTime N (kineticCouplingMagnitude depth r₀ e) omega

/-- Exact pointwise conversion from `g_LJ² T` to `(e / depth) T`.

This equality remains valid when the microscopic hitting time is `top`; no
`ENNReal.toReal` conversion is used. -/
theorem scaledEnergyDensityEquilibrationTime_eq_const_mul_scaled
    {Omega : Type*}
    (equilibrationTime : Nat → Real → Omega → ENNReal)
    {depth r₀ e : Real} (hdepth : 0 < depth) (hr₀ : 0 < r₀)
    (he : 0 ≤ e) (N : Nat) (omega : Omega) :
    scaledEnergyDensityEquilibrationTime equilibrationTime
        depth r₀ N e omega =
      ENNReal.ofReal (32 / 49 : Real) *
        scaledEquilibrationTime equilibrationTime N
          (kineticCouplingMagnitude depth r₀ e) omega := by
  have hreal :
      e / depth =
        (32 / 49 : Real) *
          kineticCouplingMagnitude depth r₀ e ^ 2 := by
    rw [kineticCouplingMagnitude_sq hdepth hr₀ he]
    field_simp [ne_of_gt hdepth]
  unfold scaledEnergyDensityEquilibrationTime scaledEquilibrationTime
  rw [hreal, ENNReal.ofReal_mul (by norm_num : (0 : Real) ≤ 32 / 49)]
  rw [mul_assoc]

/-- Transparent LJ-specific package.  The microscopic certificate contains
the local-uniform joint-limit estimate and the physical hitting-time
identification; the crossing field contains the independent kinetic theorem.
Neither field assumes the thermodynamic hitting-time conclusion below. -/
structure LennardJonesThermodynamicHittingCertificate
    {Omega : Type*} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (equilibrationTime : Nat → Real → Omega → ENNReal)
    (sizeCutoff : Real → Nat) (kineticDistance : Real → Real)
    (delta tauStar depth r₀ : Real) where
  depth_pos : 0 < depth
  equilibriumLength_pos : 0 < r₀
  microscopic : ConditionalThermalizationCertificate P equilibrationTime
    sizeCutoff kineticDistance delta
  robustCrossing : RobustKineticFirstCrossing kineticDistance delta tauStar

/-- Along every explicit LJ low-energy/large-volume path, the energy-density
scaled hitting time converges in probability to `(32 / 49) tauStar`.

The result is conditional precisely on the transparent microscopic local-
uniform convergence certificate and robust kinetic crossing above. -/
theorem LennardJonesThermodynamicHittingCertificate.energyDensityTime_law
    {Omega : Type*} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (equilibrationTime : Nat → Real → Omega → ENNReal)
    (sizeCutoff : Real → Nat) (kineticDistance : Real → Real)
    (delta tauStar depth r₀ : Real)
    (certificate : LennardJonesThermodynamicHittingCertificate
      P equilibrationTime sizeCutoff kineticDistance
      delta tauStar depth r₀)
    (s : AdmissibleLennardJonesJointLimit sizeCutoff depth r₀) :
    ConvergesInProbabilityTo P
      (fun j omega => scaledEnergyDensityEquilibrationTime equilibrationTime
        depth r₀ (s.systemSize j) (s.energyDensity j) omega)
      (ENNReal.ofReal ((32 / 49 : Real) * tauStar)) := by
  let jointLimit : AdmissibleJointLimit sizeCutoff :=
    s.toAdmissibleJointLimit certificate.depth_pos
      certificate.equilibriumLength_pos
  have hg2 : G2TeqConvergesInProbability P equilibrationTime
      sizeCutoff tauStar :=
    certificate.microscopic.toG2TeqConvergesInProbability
      P equilibrationTime sizeCutoff kineticDistance delta tauStar
      certificate.robustCrossing
  have hscaled := ConvergesInProbabilityTo.const_mul P
    (hg2.law jointLimit)
    (ENNReal.ofReal_ne_top : ENNReal.ofReal (32 / 49 : Real) ≠ ⊤)
  have hsequence :
      (fun j omega => scaledEnergyDensityEquilibrationTime equilibrationTime
        depth r₀ (s.systemSize j) (s.energyDensity j) omega) =
      (fun j omega => ENNReal.ofReal (32 / 49 : Real) *
        scaledEquilibrationTime equilibrationTime
          (jointLimit.systemSize j) (jointLimit.coupling j) omega) := by
    funext j omega
    simpa [jointLimit,
      AdmissibleLennardJonesJointLimit.toAdmissibleJointLimit] using
      (scaledEnergyDensityEquilibrationTime_eq_const_mul_scaled
        equilibrationTime certificate.depth_pos
        certificate.equilibriumLength_pos
        (s.energyDensity_pos j).le (s.systemSize j) omega)
  rw [hsequence]
  simpa only [ENNReal.ofReal_mul (by norm_num : (0 : Real) ≤ 32 / 49)]
    using hscaled

/-- Energy-density-scaled hitting-time window along an explicit LJ path. -/
def energyDensityWindowEvent {Omega : Type*}
    (equilibrationTime : Nat → Real → Omega → ENNReal)
    (depth r₀ lower upper : Real)
    {sizeCutoff : Real → Nat}
    (s : AdmissibleLennardJonesJointLimit sizeCutoff depth r₀)
    (j : Nat) : Set Omega :=
  (fun omega => scaledEnergyDensityEquilibrationTime equilibrationTime
    depth r₀ (s.systemSize j) (s.energyDensity j) omega) ⁻¹'
      Icc (ENNReal.ofReal lower) (ENNReal.ofReal upper)

/-- Every strictly bracketing two-sided window has asymptotic probability one.

This general form keeps the actual cutoff as a parameter instead of fixing it
to zero as in the convenience event definition above. -/
theorem LennardJonesThermodynamicHittingCertificate.tendsto_measure_window
    {Omega : Type*} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (equilibrationTime : Nat → Real → Omega → ENNReal)
    (sizeCutoff : Real → Nat) (kineticDistance : Real → Real)
    (delta tauStar depth r₀ lower upper : Real)
    (certificate : LennardJonesThermodynamicHittingCertificate
      P equilibrationTime sizeCutoff kineticDistance
      delta tauStar depth r₀)
    (s : AdmissibleLennardJonesJointLimit sizeCutoff depth r₀)
    (hlower : lower < (32 / 49 : Real) * tauStar)
    (hupper : (32 / 49 : Real) * tauStar < upper) :
    Tendsto
      (fun j => P ((fun omega =>
        scaledEnergyDensityEquilibrationTime equilibrationTime
          depth r₀ (s.systemSize j) (s.energyDensity j) omega) ⁻¹'
        Icc (ENNReal.ofReal lower) (ENNReal.ofReal upper)))
      atTop (nhds 1) := by
  have htarget_pos : 0 < (32 / 49 : Real) * tauStar :=
    mul_pos (by norm_num) certificate.robustCrossing.tauStar_pos
  exact (certificate.energyDensityTime_law P equilibrationTime sizeCutoff
    kineticDistance delta tauStar depth r₀ s).tendsto_measure_preimage_Icc
      ((ENNReal.ofReal_lt_ofReal_iff htarget_pos).2 hlower)
      ((ENNReal.ofReal_lt_ofReal_iff (htarget_pos.trans hupper)).2 hupper)

end

end ArchonPhysics.LennardJonesThermodynamicHittingTransfer
