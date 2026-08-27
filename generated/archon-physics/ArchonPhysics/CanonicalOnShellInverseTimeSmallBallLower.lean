import ArchonPhysics.CanonicalOnShellMarkedClusterPositiveBounds
import ArchonPhysics.RepeatedParentChildMismatchSmallBall
import ArchonPhysics.ResonanceKernelLipschitz

/-!
# Inverse-time small balls give a positive on-shell mass lower bound

The normalized finite-time resonance kernel has height `T / (2 * pi)` at
zero.  Its explicit Lipschitz bound shows that it remains at least half that
height on the central window `|mismatch| <= 1 / (4 * T)`.  Consequently a
finite mismatch measure with at least `slope / T` mass in that window has
broadened mass at least `slope / (4 * pi)`.

This is the precise lower small-ball input needed for positivity of a future
canonical on-shell cluster.  It is deliberately separate from an upper mass
bound: a single fixed-volume near-resonant patch does not supply either the
inverse-time estimate uniformly in volume or the required time-uniform upper
bound.
-/

open scoped ENNReal Topology InnerProductSpace RealInnerProductSpace

namespace ArchonPhysics.CanonicalOnShellInverseTimeSmallBallLower

open ArchonPhysics
open ArchonPhysics.BroadenedResonanceMeasure
open ArchonPhysics.CanonicalCollisionMeasureWeakLimit
open ArchonPhysics.CanonicalOnShellMarkedCluster
open ArchonPhysics.CanonicalOnShellMarkedClusterPositiveBounds
open ArchonPhysics.CanonicalRankFrequencyMarkedBroadenedLimit
open ArchonPhysics.CanonicalRankFrequencyMarkedBroadenedMarginal
open ArchonPhysics.CanonicalRankFrequencyMarkedMeasure
open ArchonPhysics.FiniteTimeResonanceWeight
open ArchonPhysics.NormalizedResonancePeakKernel
open ArchonPhysics.RepeatedParentChildMismatchSmallBall
open ArchonPhysics.ResonanceKernelLipschitz
open ArchonPhysics.SincSquareMassExact
open ArchonPhysics.UniformCollisionDensityTransfer
open Filter MeasureTheory Set Topology

noncomputable section

/-! ## Generic central-window lower bound -/

/-- On the inverse-time central window the normalized sinc-squared peak is at
least half of its exact resonant height. -/
theorem normalizedFiniteTimeResonanceKernel_ge_halfHeight_of_abs_le
    {mismatch T : Real} (hT : 0 < T)
    (hmismatch : |mismatch| <= 1 / (4 * T)) :
    T / (4 * Real.pi) <=
      normalizedFiniteTimeResonanceKernel mismatch T := by
  have hzero : normalizedFiniteTimeResonanceKernel 0 T =
      T / (2 * Real.pi) := by
    unfold normalizedFiniteTimeResonanceKernel
    rw [finiteTimeResonanceWeight_zero_of_pos hT, sincSquareMass_eq_pi]
  have hlip :=
    abs_normalizedFiniteTimeResonanceKernel_sub_le mismatch 0 hT
  have hdifference :
      normalizedFiniteTimeResonanceKernel 0 T -
          normalizedFiniteTimeResonanceKernel mismatch T <=
        (T ^ 2 / Real.pi) * |mismatch| := by
    calc
      normalizedFiniteTimeResonanceKernel 0 T -
          normalizedFiniteTimeResonanceKernel mismatch T <=
          |normalizedFiniteTimeResonanceKernel 0 T -
            normalizedFiniteTimeResonanceKernel mismatch T| :=
        le_abs_self _
      _ = |normalizedFiniteTimeResonanceKernel mismatch T -
            normalizedFiniteTimeResonanceKernel 0 T| := abs_sub_comm _ _
      _ <= (T ^ 2 / Real.pi) * |mismatch - 0| := hlip
      _ = (T ^ 2 / Real.pi) * |mismatch| := by simp
  have hfactor : 0 <= T ^ 2 / Real.pi := by positivity
  have hcentral :
      (T ^ 2 / Real.pi) * |mismatch| <= T / (4 * Real.pi) := by
    calc
      (T ^ 2 / Real.pi) * |mismatch| <=
          (T ^ 2 / Real.pi) * (1 / (4 * T)) :=
        mul_le_mul_of_nonneg_left hmismatch hfactor
      _ = T / (4 * Real.pi) := by
        field_simp [hT.ne', Real.pi_ne_zero]
  rw [hzero] at hdifference
  calc
    T / (4 * Real.pi) =
        T / (2 * Real.pi) - T / (4 * Real.pi) := by ring
    _ <= T / (2 * Real.pi) -
        (T ^ 2 / Real.pi) * |mismatch| :=
      sub_le_sub_left hcentral _
    _ <= normalizedFiniteTimeResonanceKernel mismatch T := by
      linarith only [hdifference]

/-- A lower bound on the mass of the inverse-time mismatch window yields a
quantitative lower bound on the total broadened mass. -/
theorem halfHeight_mul_smallBall_le_broadenedResonanceMeasure_mass
    (mu : FiniteMeasure Real) {T : Real} (hT : 0 < T) :
    T / (4 * Real.pi) *
        (mu : Measure Real).real
          (absoluteMismatchSublevel (1 / (4 * T))) <=
      ((broadenedResonanceMeasure mu id measurable_id T hT).mass : Real) := by
  let kernel : Real -> Real := fun mismatch =>
    normalizedFiniteTimeResonanceKernel mismatch T
  have hkernelIntegrable : Integrable kernel (mu : Measure Real) := by
    let kernelBCF := normalizedFiniteTimeResonanceWeightBCF
      id continuous_id T hT
    exact (kernelBCF.integrable (mu : Measure Real)).congr
      (Eventually.of_forall fun mismatch => by rfl)
  have hkernelNonneg :
      ∀ᵐ mismatch ∂(mu : Measure Real), 0 <= kernel mismatch :=
    Eventually.of_forall fun mismatch =>
      normalizedFiniteTimeResonanceKernel_nonneg mismatch T
  have hcentralSubset :
      absoluteMismatchSublevel (1 / (4 * T)) <=
        {mismatch | T / (4 * Real.pi) <= kernel mismatch} := by
    intro mismatch hmismatch
    exact normalizedFiniteTimeResonanceKernel_ge_halfHeight_of_abs_le
      hT hmismatch
  rw [broadenedResonanceMeasure_mass_eq_integral]
  calc
    T / (4 * Real.pi) *
        (mu : Measure Real).real
          (absoluteMismatchSublevel (1 / (4 * T))) <=
      T / (4 * Real.pi) *
        (mu : Measure Real).real
          {mismatch | T / (4 * Real.pi) <= kernel mismatch} := by
        exact mul_le_mul_of_nonneg_left
          (measureReal_mono hcentralSubset) (by positivity)
    _ <= ∫ mismatch, kernel mismatch ∂(mu : Measure Real) :=
      mul_meas_ge_le_integral_of_nonneg
        hkernelNonneg hkernelIntegrable (T / (4 * Real.pi))
    _ = ∫ mismatch,
        normalizedFiniteTimeResonanceKernel (id mismatch) T
          ∂(mu : Measure Real) := by rfl

/-- If the inverse-time window contains at least `slope / T` mass, then the
broadened mass is bounded below by the positive constant
`slope / (4 * pi)`. -/
theorem slope_div_four_pi_le_broadenedResonanceMeasure_mass
    (mu : FiniteMeasure Real) {T slope : Real}
    (hT : 0 < T)
    (hsmallBall : slope / T <=
      (mu : Measure Real).real
        (absoluteMismatchSublevel (1 / (4 * T)))) :
    slope / (4 * Real.pi) <=
      ((broadenedResonanceMeasure mu id measurable_id T hT).mass : Real) := by
  have hheight : 0 <= T / (4 * Real.pi) := by positivity
  calc
    slope / (4 * Real.pi) =
        T / (4 * Real.pi) * (slope / T) := by
      field_simp [hT.ne', Real.pi_ne_zero]
    _ <= T / (4 * Real.pi) *
        (mu : Measure Real).real
          (absoluteMismatchSublevel (1 / (4 * T))) :=
      mul_le_mul_of_nonneg_left hsmallBall hheight
    _ <= ((broadenedResonanceMeasure mu id measurable_id T hT).mass : Real) :=
      halfHeight_mul_smallBall_le_broadenedResonanceMeasure_mass mu hT

/-! ## Volume-domination upper bound -/

/-- Domination of the scalar mismatch measure by `C` times Lebesgue measure
gives the time-uniform broadened-mass upper bound `C`.  The proof uses only
positivity of the resonance kernel and its exact unit Lebesgue mass. -/
theorem broadenedResonanceMeasure_mass_le_of_le_smul_volume
    (mu : FiniteMeasure Real) (C : NNReal)
    (hdomination : (mu : Measure Real) <=
      C • (volume : Measure Real))
    {T : Real} (hT : 0 < T) :
    ((broadenedResonanceMeasure mu id measurable_id T hT).mass : Real) <=
      (C : Real) := by
  let kernel : Real -> Real := fun mismatch =>
    normalizedFiniteTimeResonanceKernel mismatch T
  have hkernelIntegrableVolume :
      Integrable kernel (volume : Measure Real) := by
    simpa [kernel] using
      integrable_normalizedFiniteTimeResonanceKernel hT
  have hkernelIntegrableDominating :
      Integrable kernel (C • (volume : Measure Real)) :=
    hkernelIntegrableVolume.smul_measure_nnreal
  have hkernelNonneg :
      ∀ᵐ mismatch ∂(C • (volume : Measure Real)),
        0 <= kernel mismatch :=
    Eventually.of_forall fun mismatch =>
      normalizedFiniteTimeResonanceKernel_nonneg mismatch T
  have hmono :
      (∫ mismatch, kernel mismatch ∂(mu : Measure Real)) <=
        ∫ mismatch, kernel mismatch
          ∂(C • (volume : Measure Real)) :=
    integral_mono_measure hdomination hkernelNonneg
      hkernelIntegrableDominating
  rw [broadenedResonanceMeasure_mass_eq_integral]
  change (∫ mismatch, kernel mismatch ∂(mu : Measure Real)) <= (C : Real)
  calc
    (∫ mismatch, kernel mismatch ∂(mu : Measure Real)) <=
        ∫ mismatch, kernel mismatch
          ∂(C • (volume : Measure Real)) := hmono
    _ = (C : Real) := by
      rw [integral_smul_nnreal_measure]
      simp [kernel, integral_normalizedFiniteTimeResonanceKernel_eq_one hT,
        NNReal.smul_def]

/-! ## Canonical cluster endpoint -/

variable {Omega : Type*} [MeasurableSpace Omega]

/-- An eventual inverse-time lower small-ball estimate, together with the
still-separate eventual upper broadened-mass bound, produces a nonzero
canonical on-shell marked cluster.  This theorem makes the remaining model
input explicit without postulating a density. -/
theorem exists_positive_canonicalOnShellMarkedCluster_of_inverseTimeSmallBallLower
    (ensemble : IIDMassPhaseEnsemble Omega)
    (time : Nat -> Real) (htime_pos : forall n, 0 < time n)
    (htime : Tendsto time atTop atTop)
    (slope : Real) (hslope : 0 < slope)
    (massUpper : NNReal)
    (hsmallBall : ∀ᶠ n in atTop,
      slope / time n <=
        (canonicalCollisionPerSiteMeasureLimit
          ensemble
            RandomMassThreeWaveCollisionNetwork.decayInteractionSign : Measure Real).real
          (absoluteMismatchSublevel (1 / (4 * time n))))
    (hmassUpper : ∀ᶠ n in atTop,
      (canonicalBroadenedCollisionPerSiteMeasureLimit
        ensemble RandomMassThreeWaveCollisionNetwork.decayInteractionSign
          (time n) (htime_pos n)).mass <=
          massUpper) :
    exists target : FiniteMeasure (Fin 3 -> RankFrequencyMark),
      exists subsequence : Nat -> Nat,
        exists collision : ResonantThreeWaveMeasure RankFrequencyMark,
          StrictMono subsequence /\
          Tendsto
            (fun j =>
              canonicalRankFrequencyMarkedBroadenedPerSiteMeasureLimit
                ensemble RandomMassThreeWaveCollisionNetwork.decayInteractionSign
                  (time (subsequence j))
                  (htime_pos (subsequence j)))
            atTop (nhds target) /\
          collision.collisionMeasure = target /\
          Real.toNNReal (slope / (4 * Real.pi)) <=
            collision.collisionMeasure.mass /\
          collision.collisionMeasure.mass <= massUpper /\
          collision.collisionMeasure ≠ 0 := by
  have hmassLowerPos :
      0 < Real.toNNReal (slope / (4 * Real.pi)) := by
    rw [Real.toNNReal_pos]
    positivity
  have hmassBounds : ∀ᶠ n in atTop,
      Real.toNNReal (slope / (4 * Real.pi)) <=
          (canonicalBroadenedCollisionPerSiteMeasureLimit
            ensemble RandomMassThreeWaveCollisionNetwork.decayInteractionSign
              (time n) (htime_pos n)).mass /\
        (canonicalBroadenedCollisionPerSiteMeasureLimit
            ensemble RandomMassThreeWaveCollisionNetwork.decayInteractionSign
              (time n) (htime_pos n)).mass <=
          massUpper := by
    filter_upwards [hsmallBall, hmassUpper] with n hnSmall hnUpper
    constructor
    · apply NNReal.coe_le_coe.mp
      rw [Real.coe_toNNReal _
        (le_of_lt (div_pos hslope (by positivity)))]
      simpa [canonicalBroadenedCollisionPerSiteMeasureLimit] using
        slope_div_four_pi_le_broadenedResonanceMeasure_mass
          (canonicalCollisionPerSiteMeasureLimit
            ensemble
              RandomMassThreeWaveCollisionNetwork.decayInteractionSign)
          (htime_pos n) hnSmall
    · exact hnUpper
  exact
    exists_positive_canonicalOnShellMarkedCluster_of_eventual_scalarMass_bounds
      ensemble time htime_pos htime
      (Real.toNNReal (slope / (4 * Real.pi))) massUpper
      hmassLowerPos hmassBounds

end

end ArchonPhysics.CanonicalOnShellInverseTimeSmallBallLower
