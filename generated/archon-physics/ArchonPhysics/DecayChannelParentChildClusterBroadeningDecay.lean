import ArchonPhysics.DecayChannelSectorClusterDecomposition
import ArchonPhysics.RepeatedParentChildFractionalBroadeningDecay
import ArchonPhysics.RepeatedParentChildMismatchMeasureBridge

/-!
# Parent--child cluster sectors have zero on-shell contribution

The two parent--child equality sectors already satisfy a volume-uniform
`O(T^{-1/2})` finite-time broadening bound.  This module transports that
bound through an arbitrary finite-measure weak cluster.  Consequently both
parent--child members of the canonical four-sector decomposition have
broadened mass tending to zero along every diverging positive observation
time sequence.

This is stronger than merely removing their exact-resonance atoms: it proves
that their contribution to the limiting on-shell collision coefficient is
zero.
-/

open scoped Topology BoundedContinuousFunction

namespace ArchonPhysics.DecayChannelParentChildClusterBroadeningDecay

open ArchonPhysics
open ArchonPhysics.BroadenedResonanceMeasure
open ArchonPhysics.DecayChannelModeEqualityPartition
open ArchonPhysics.DecayChannelMismatchSectorWeakLimit
open ArchonPhysics.DecayChannelSectorClusterDecomposition
open ArchonPhysics.MeasurableOrderedModeCoupling.Harmonic
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.NormalizedResonancePeakKernel
open ArchonPhysics.RandomMassPositiveCollisionData
open ArchonPhysics.RandomMassThreeWaveCollisionNetwork
open ArchonPhysics.ResonanceKernelLipschitz
open ArchonPhysics.RepeatedParentChildFractionalBroadeningDecay
open ArchonPhysics.RepeatedParentChildMismatchMeasureBridge
open ArchonPhysics.RepeatedParentChildMismatchWeakLimitNull
open ArchonPhysics.UniformCollisionDensityTransfer
open Filter MeasureTheory Set

noncomputable section

variable {Omega : Type*} [MeasurableSpace Omega]

/-- The normalized squared-sinc peak as a globally bounded continuous test
function at one fixed positive observation time. -/
def normalizedFiniteTimeResonanceKernelBoundedContinuous
    (T : Real) (hT : 0 < T) : Real →ᵇ Real :=
  BoundedContinuousFunction.mkOfBound
    ⟨fun mismatch => normalizedFiniteTimeResonanceKernel mismatch T,
      continuous_normalizedFiniteTimeResonanceKernel hT⟩
    (T / Real.pi) (by
      intro x y
      rw [Real.dist_eq]
      calc
        |normalizedFiniteTimeResonanceKernel x T -
            normalizedFiniteTimeResonanceKernel y T| <=
            |normalizedFiniteTimeResonanceKernel x T| +
              |normalizedFiniteTimeResonanceKernel y T| :=
          abs_sub _ _
        _ <= T / (2 * Real.pi) + T / (2 * Real.pi) :=
          add_le_add
            (abs_normalizedFiniteTimeResonanceKernel_le_height x hT)
            (abs_normalizedFiniteTimeResonanceKernel_le_height y hT)
        _ = T / Real.pi := by ring)

@[simp] theorem normalizedFiniteTimeResonanceKernelBoundedContinuous_apply
    (T : Real) (hT : 0 < T) (mismatch : Real) :
    normalizedFiniteTimeResonanceKernelBoundedContinuous T hT mismatch =
      normalizedFiniteTimeResonanceKernel mismatch T := rfl

/-- Integrating the resonance peak over the complete `mode 0 = mode 1`
equality-plane measure recovers its explicit broadened double sum. -/
theorem integral_normalizedKernel_positiveRepeatedZeroOneMismatchMeasure_eq
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (T : Real) :
    (∫ mismatch : Real, normalizedFiniteTimeResonanceKernel mismatch T
      ∂positiveRepeatedZeroOneMismatchMeasure m) =
      positiveRepeatedZeroOneBroadenedInteractionWeight m T := by
  classical
  unfold positiveRepeatedZeroOneMismatchMeasure
    positiveRepeatedZeroOneBroadenedInteractionWeight
  rw [integral_finsetSum_measure]
  · apply Finset.sum_congr rfl
    intro k _hk
    rw [integral_finsetSum_measure]
    · apply Finset.sum_congr rfl
      intro q _hq
      by_cases hpositive : IsPositiveOrderedTriple m ![k, k, q]
      · simp only [if_pos hpositive, integral_smul_measure, integral_dirac]
        rw [ENNReal.toReal_ofReal
          (harmonicOrderedNormalizedInteractionWeight_nonneg m ![k, k, q])]
        simp only [smul_eq_mul]
      · simp [hpositive]
    · intro q _hq
      by_cases hpositive : IsPositiveOrderedTriple m ![k, k, q]
      · rw [if_pos hpositive]
        exact (integrable_dirac (by simp)).smul_measure
          ENNReal.ofReal_ne_top
      · rw [if_neg hpositive]
        exact integrable_zero_measure
  · intro k _hk
    apply integrable_finsetSum_measure.mpr
    intro q _hq
    by_cases hpositive : IsPositiveOrderedTriple m ![k, k, q]
    · rw [if_pos hpositive]
      exact (integrable_dirac (by simp)).smul_measure
        ENNReal.ofReal_ne_top
    · rw [if_neg hpositive]
      exact integrable_zero_measure

/-- The analogous integral identity for the complete `mode 0 = mode 2`
equality plane. -/
theorem integral_normalizedKernel_positiveRepeatedZeroTwoMismatchMeasure_eq
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (T : Real) :
    (∫ mismatch : Real, normalizedFiniteTimeResonanceKernel mismatch T
      ∂positiveRepeatedZeroTwoMismatchMeasure m) =
      positiveRepeatedZeroTwoBroadenedInteractionWeight m T := by
  classical
  unfold positiveRepeatedZeroTwoMismatchMeasure
    positiveRepeatedZeroTwoBroadenedInteractionWeight
  rw [integral_finsetSum_measure]
  · apply Finset.sum_congr rfl
    intro k _hk
    rw [integral_finsetSum_measure]
    · apply Finset.sum_congr rfl
      intro q _hq
      by_cases hpositive : IsPositiveOrderedTriple m ![k, q, k]
      · simp only [if_pos hpositive, integral_smul_measure, integral_dirac]
        rw [ENNReal.toReal_ofReal
          (harmonicOrderedNormalizedInteractionWeight_nonneg m ![k, q, k])]
        simp only [smul_eq_mul]
      · simp [hpositive]
    · intro q _hq
      by_cases hpositive : IsPositiveOrderedTriple m ![k, q, k]
      · rw [if_pos hpositive]
        exact (integrable_dirac (by simp)).smul_measure
          ENNReal.ofReal_ne_top
      · rw [if_neg hpositive]
        exact integrable_zero_measure
  · intro k _hk
    apply integrable_finsetSum_measure.mpr
    intro q _hq
    by_cases hpositive : IsPositiveOrderedTriple m ![k, q, k]
    · rw [if_pos hpositive]
      exact (integrable_dirac (by simp)).smul_measure
        ENNReal.ofReal_ne_top
    · rw [if_neg hpositive]
      exact integrable_zero_measure

/-- Every finite-volume first parent--child sector inherits the complete
equality plane's volume-uniform fractional broadening ceiling. -/
theorem integral_normalizedKernel_iidParentChildOne_le
    (ensemble : IIDMassPhaseEnsemble Omega) (omega : Omega)
    (n : Nat) {T : Real} (hT : 0 < T) :
    (∫ mismatch : Real, normalizedFiniteTimeResonanceKernel mismatch T
      ∂(iidParentChildOneRepeatedPerSiteMismatchFiniteMeasure
        ensemble omega n : Measure Real)) <=
      5 / (2 * Real.pi * Real.sqrt T) := by
  let N := n + 1
  let m := ensemble.restrictPositiveMass (N := N) omega
  have hplaneIntegrable : Integrable
      (fun mismatch : Real => normalizedFiniteTimeResonanceKernel mismatch T)
      (positiveRepeatedZeroOneMismatchMeasure m) := by
    classical
    unfold positiveRepeatedZeroOneMismatchMeasure
    rw [integrable_finsetSum_measure]
    intro k _hk
    rw [integrable_finsetSum_measure]
    intro q _hq
    by_cases hpositive : IsPositiveOrderedTriple m ![k, k, q]
    · rw [if_pos hpositive]
      exact (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top
    · rw [if_neg hpositive]
      exact integrable_zero_measure
  have hraw :
      (∫ mismatch : Real, normalizedFiniteTimeResonanceKernel mismatch T
        ∂positiveWeightedMismatchMeasureWhere
          m decayInteractionSign ParentChildOneRepeated) <=
        ∫ mismatch : Real, normalizedFiniteTimeResonanceKernel mismatch T
          ∂positiveRepeatedZeroOneMismatchMeasure m := by
    exact integral_mono_measure
      (parentChildOneRepeated_mismatchMeasure_le_completePlane m)
      (Eventually.of_forall fun mismatch =>
        normalizedFiniteTimeResonanceKernel_nonneg mismatch T)
      hplaneIntegrable
  unfold iidParentChildOneRepeatedPerSiteMismatchFiniteMeasure
    perSitePositiveWeightedMismatchFiniteMeasureWhere
  rw [FiniteMeasure.toMeasure_smul, integral_smul_nnreal_measure]
  calc
    ((↑((N : NNReal)⁻¹) : ENNReal).toReal) *
        (∫ mismatch : Real, normalizedFiniteTimeResonanceKernel mismatch T
          ∂positiveWeightedMismatchMeasureWhere
            m decayInteractionSign ParentChildOneRepeated) <=
      ((↑((N : NNReal)⁻¹) : ENNReal).toReal) *
        (∫ mismatch : Real, normalizedFiniteTimeResonanceKernel mismatch T
          ∂positiveRepeatedZeroOneMismatchMeasure m) := by
      gcongr
    _ = positiveRepeatedZeroOneBroadenedInteractionWeight m T /
        (N : Real) := by
      rw [integral_normalizedKernel_positiveRepeatedZeroOneMismatchMeasure_eq]
      simp only [ENNReal.toReal, ENNReal.toNNReal_coe, NNReal.coe_inv,
        NNReal.coe_natCast, div_eq_mul_inv]
      ring
    _ <= 5 / (2 * Real.pi * Real.sqrt T) := by
      exact iid_positiveRepeatedZeroOneBroadenedInteractionWeight_div_volume_le
        ensemble omega hT

/-- Uniform finite-volume ceiling for the second parent--child sector. -/
theorem integral_normalizedKernel_iidParentChildTwo_le
    (ensemble : IIDMassPhaseEnsemble Omega) (omega : Omega)
    (n : Nat) {T : Real} (hT : 0 < T) :
    (∫ mismatch : Real, normalizedFiniteTimeResonanceKernel mismatch T
      ∂(iidParentChildTwoRepeatedPerSiteMismatchFiniteMeasure
        ensemble omega n : Measure Real)) <=
      5 / (2 * Real.pi * Real.sqrt T) := by
  let N := n + 1
  let m := ensemble.restrictPositiveMass (N := N) omega
  have hplaneIntegrable : Integrable
      (fun mismatch : Real => normalizedFiniteTimeResonanceKernel mismatch T)
      (positiveRepeatedZeroTwoMismatchMeasure m) := by
    classical
    unfold positiveRepeatedZeroTwoMismatchMeasure
    rw [integrable_finsetSum_measure]
    intro k _hk
    rw [integrable_finsetSum_measure]
    intro q _hq
    by_cases hpositive : IsPositiveOrderedTriple m ![k, q, k]
    · rw [if_pos hpositive]
      exact (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top
    · rw [if_neg hpositive]
      exact integrable_zero_measure
  have hraw :
      (∫ mismatch : Real, normalizedFiniteTimeResonanceKernel mismatch T
        ∂positiveWeightedMismatchMeasureWhere
          m decayInteractionSign ParentChildTwoRepeated) <=
        ∫ mismatch : Real, normalizedFiniteTimeResonanceKernel mismatch T
          ∂positiveRepeatedZeroTwoMismatchMeasure m := by
    exact integral_mono_measure
      (parentChildTwoRepeated_mismatchMeasure_le_completePlane m)
      (Eventually.of_forall fun mismatch =>
        normalizedFiniteTimeResonanceKernel_nonneg mismatch T)
      hplaneIntegrable
  unfold iidParentChildTwoRepeatedPerSiteMismatchFiniteMeasure
    perSitePositiveWeightedMismatchFiniteMeasureWhere
  rw [FiniteMeasure.toMeasure_smul, integral_smul_nnreal_measure]
  calc
    ((↑((N : NNReal)⁻¹) : ENNReal).toReal) *
        (∫ mismatch : Real, normalizedFiniteTimeResonanceKernel mismatch T
          ∂positiveWeightedMismatchMeasureWhere
            m decayInteractionSign ParentChildTwoRepeated) <=
      ((↑((N : NNReal)⁻¹) : ENNReal).toReal) *
        (∫ mismatch : Real, normalizedFiniteTimeResonanceKernel mismatch T
          ∂positiveRepeatedZeroTwoMismatchMeasure m) := by
      gcongr
    _ = positiveRepeatedZeroTwoBroadenedInteractionWeight m T /
        (N : Real) := by
      rw [integral_normalizedKernel_positiveRepeatedZeroTwoMismatchMeasure_eq]
      simp only [ENNReal.toReal, ENNReal.toNNReal_coe, NNReal.coe_inv,
        NNReal.coe_natCast, div_eq_mul_inv]
      ring
    _ <= 5 / (2 * Real.pi * Real.sqrt T) := by
      exact iid_positiveRepeatedZeroTwoBroadenedInteractionWeight_div_volume_le
        ensemble omega hT

/-- The first parent--child weak cluster retains the same explicit
`O(T^{-1/2})` broadened-mass ceiling. -/
theorem parentChildOne_weakLimit_broadened_mass_le
    (ensemble : IIDMassPhaseEnsemble Omega) (omega : Omega)
    (size : Nat -> Nat)
    (target : FiniteMeasure Real)
    (hlimit : Tendsto
      (fun n => iidParentChildOneRepeatedPerSiteMismatchFiniteMeasure
        ensemble omega (size n))
      atTop (nhds target))
    {T : Real} (hT : 0 < T) :
    ((broadenedResonanceMeasure target id measurable_id T hT).mass : Real) <=
      5 / (2 * Real.pi * Real.sqrt T) := by
  rw [broadenedResonanceMeasure_mass_eq_integral]
  simp only [id_eq]
  have htendsto :=
    (FiniteMeasure.tendsto_iff_forall_integral_tendsto).mp hlimit
      (normalizedFiniteTimeResonanceKernelBoundedContinuous T hT)
  apply le_of_tendsto' htendsto
  intro n
  exact integral_normalizedKernel_iidParentChildOne_le
    ensemble omega (size n) hT

/-- The second parent--child weak cluster has the same ceiling. -/
theorem parentChildTwo_weakLimit_broadened_mass_le
    (ensemble : IIDMassPhaseEnsemble Omega) (omega : Omega)
    (size : Nat -> Nat)
    (target : FiniteMeasure Real)
    (hlimit : Tendsto
      (fun n => iidParentChildTwoRepeatedPerSiteMismatchFiniteMeasure
        ensemble omega (size n))
      atTop (nhds target))
    {T : Real} (hT : 0 < T) :
    ((broadenedResonanceMeasure target id measurable_id T hT).mass : Real) <=
      5 / (2 * Real.pi * Real.sqrt T) := by
  rw [broadenedResonanceMeasure_mass_eq_integral]
  simp only [id_eq]
  have htendsto :=
    (FiniteMeasure.tendsto_iff_forall_integral_tendsto).mp hlimit
      (normalizedFiniteTimeResonanceKernelBoundedContinuous T hT)
  apply le_of_tendsto' htendsto
  intro n
  exact integral_normalizedKernel_iidParentChildTwo_le
    ensemble omega (size n) hT

/-- Along every positive diverging observation-time sequence, the first
parent--child cluster has zero limiting on-shell mass. -/
theorem parentChildOne_weakLimit_broadened_mass_tendsto_zero
    (ensemble : IIDMassPhaseEnsemble Omega) (omega : Omega)
    (size : Nat -> Nat)
    (target : FiniteMeasure Real)
    (hlimit : Tendsto
      (fun n => iidParentChildOneRepeatedPerSiteMismatchFiniteMeasure
        ensemble omega (size n))
      atTop (nhds target))
    (time : Nat -> Real) (htime_pos : forall n, 0 < time n)
    (htime : Tendsto time atTop atTop) :
    Tendsto
      (fun n => ((broadenedResonanceMeasure target id measurable_id
        (time n) (htime_pos n)).mass : Real)) atTop (nhds 0) := by
  apply squeeze_zero'
  · exact Eventually.of_forall fun n => by positivity
  · exact Eventually.of_forall fun n =>
      parentChildOne_weakLimit_broadened_mass_le
        ensemble omega size target hlimit (htime_pos n)
  · exact repeatedParentChildFractionalCeiling_tendsto_zero.comp htime

/-- Along every positive diverging observation-time sequence, the second
parent--child cluster also has zero limiting on-shell mass. -/
theorem parentChildTwo_weakLimit_broadened_mass_tendsto_zero
    (ensemble : IIDMassPhaseEnsemble Omega) (omega : Omega)
    (size : Nat -> Nat)
    (target : FiniteMeasure Real)
    (hlimit : Tendsto
      (fun n => iidParentChildTwoRepeatedPerSiteMismatchFiniteMeasure
        ensemble omega (size n))
      atTop (nhds target))
    (time : Nat -> Real) (htime_pos : forall n, 0 < time n)
    (htime : Tendsto time atTop atTop) :
    Tendsto
      (fun n => ((broadenedResonanceMeasure target id measurable_id
        (time n) (htime_pos n)).mass : Real)) atTop (nhds 0) := by
  apply squeeze_zero'
  · exact Eventually.of_forall fun n => by positivity
  · exact Eventually.of_forall fun n =>
      parentChildTwo_weakLimit_broadened_mass_le
        ensemble omega size target hlimit (htime_pos n)
  · exact repeatedParentChildFractionalCeiling_tendsto_zero.comp htime

/-- Both parent--child members of a four-sector cluster decomposition have
zero on-shell coefficient, with no further spectral input. -/
theorem DecaySectorClusterDecomposition.parentChild_broadened_mass_tendsto_zero
    {ensemble : IIDMassPhaseEnsemble Omega} {omega : Omega}
    {target : FiniteMeasure Real}
    (cluster : DecaySectorClusterDecomposition ensemble omega target)
    (time : Nat -> Real) (htime_pos : forall n, 0 < time n)
    (htime : Tendsto time atTop atTop) :
    Tendsto
      (fun n =>
        ((broadenedResonanceMeasure cluster.parentChildOne id measurable_id
          (time n) (htime_pos n)).mass : Real) +
        ((broadenedResonanceMeasure cluster.parentChildTwo id measurable_id
          (time n) (htime_pos n)).mass : Real))
      atTop (nhds 0) := by
  have hone : Tendsto
      (fun n => iidParentChildOneRepeatedPerSiteMismatchFiniteMeasure
        ensemble omega (cluster.subsequence n + 1))
      atTop (nhds cluster.parentChildOne) := by
    simpa only [canonicalDecaySector_parentChildOne_eq_iid_tail] using
      cluster.parentChildOne_tendsto
  have htwo : Tendsto
      (fun n => iidParentChildTwoRepeatedPerSiteMismatchFiniteMeasure
        ensemble omega (cluster.subsequence n + 1))
      atTop (nhds cluster.parentChildTwo) := by
    simpa only [canonicalDecaySector_parentChildTwo_eq_iid_tail] using
      cluster.parentChildTwo_tendsto
  simpa only [zero_add] using
    (parentChildOne_weakLimit_broadened_mass_tendsto_zero
      ensemble omega (fun n => cluster.subsequence n + 1)
      cluster.parentChildOne hone time htime_pos htime).add
    (parentChildTwo_weakLimit_broadened_mass_tendsto_zero
      ensemble omega (fun n => cluster.subsequence n + 1)
      cluster.parentChildTwo htwo time htime_pos htime)

end

end ArchonPhysics.DecayChannelParentChildClusterBroadeningDecay
