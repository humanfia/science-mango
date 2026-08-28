import ArchonPhysics.CleanCycleAcousticCountEnvelope
import ArchonPhysics.FreeFPUTObservedChildAcousticMomentExplicitBound

/-!
# Linear-volume observed-child acoustic moment bound

For masses in the frozen support `[4/5, 6/5]`, the ordered random-mass
harmonic spectrum is bounded below by `5/6` times the clean-cycle spectrum.
The clean cycle has the explicit positive spectral floor `16 / N^2`.
Consequently every positive physical normal-mode frequency is at least
`1 / N`, and fixed-common Parseval bounds the complete observed-child
inverse-frequency moment by `N`.

All statements are deterministic at a frozen mass configuration.  Zero
frequencies remain totalized by Lean's division convention.  No localization,
random gap, or thermodynamic-limit assumption is used.
-/

namespace ArchonPhysics.FreeFPUTObservedChildAcousticMomentLinearVolumeBound

open ArchonPhysics
open ArchonPhysics.CanonicalCollisionSoftLegBound
open ArchonPhysics.CleanCycleAcousticCountEnvelope
open ArchonPhysics.FreeFPUTObservedChildAcousticMomentExplicitBound
open ArchonPhysics.FreeFPUTQLevelCorrectionResonanceIntegration
open ArchonPhysics.FreeFPUTQLevelOffResonantVolumeBound
open ArchonPhysics.HarmonicModes
open ArchonPhysics.HarmonicNormalizedEdgeFrame
open ArchonPhysics.MeasurableOrderedModeCoupling.Harmonic
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.NormalizedModeCoupling
open ArchonPhysics.OrderedSingleModeProjector
open ArchonPhysics.RandomMassPositiveCollisionData
open ArchonPhysics.RepeatedModeTupleInteractionBound
open ArchonPhysics.UniformRandomMassHarmonicSpectrumComparison
open scoped BigOperators

noncomputable section

/-- A positive clean ordered eigenvalue is one of the nonzero Fourier-mode
energies, hence is at least the clean-cycle chord floor `16 / N^2`. -/
theorem sixteen_div_volume_sq_le_clean_orderedEigenvalue_of_pos
    (N : Nat) [NeZero N]
    (k : Fin (Fintype.card (Lattice.Site N)))
    (hpositive :
      0 < orderedEigenvalue (cleanCycleHarmonicHermitian N) k) :
    16 / (N : Real) ^ 2 ≤
      orderedEigenvalue (cleanCycleHarmonicHermitian N) k := by
  let A := cleanCycleHarmonicHermitian N
  have hmem : orderedEigenvalue A k ∈
      Multiset.map A.property.eigenvalues Finset.univ.val := by
    rw [← orderedEigenvalue_equiv A k]
    simp
  have hspectrum := cleanCycle_eigenvalues_multiset_eq_modeEnergy N
  change Multiset.map A.property.eigenvalues Finset.univ.val = _ at hspectrum
  rw [hspectrum] at hmem
  obtain ⟨j, _hj, hj⟩ := Multiset.mem_map.mp hmem
  have hmodePositive : 0 < cleanCycleModeEnergy N j := by
    rw [hj]
    exact hpositive
  have hjval : 0 < j.val := by
    by_contra hnot
    have hjzero : j.val = 0 := Nat.eq_zero_of_not_pos hnot
    rw [cleanCycleModeEnergy, hjzero] at hmodePositive
    norm_num at hmodePositive
  have hradius : 1 ≤ cycleModeRadius N j := by
    unfold cycleModeRadius
    have hsub : 0 < N - j.val := Nat.sub_pos_of_lt j.val_lt
    omega
  have hN : 0 < (N : Real) := by exact_mod_cast NeZero.pos N
  have hradiusReal : (1 : Real) ≤ cycleModeRadius N j := by
    exact_mod_cast hradius
  have hchord := cycleModeRadius_energy_lower N j
  calc
    16 / (N : Real) ^ 2 =
        16 * (1 : Real) ^ 2 / (N : Real) ^ 2 := by ring
    _ ≤ 16 * (cycleModeRadius N j : Real) ^ 2 / (N : Real) ^ 2 := by
      gcongr
    _ ≤ cleanCycleModeEnergy N j := hchord
    _ = orderedEigenvalue (cleanCycleHarmonicHermitian N) k := hj

/-- Under the literal frozen support `[4/5, 6/5]`, every positive physical
squared frequency inherits the stronger floor `(40/3) / N^2`. -/
theorem frozenSupport_modeFrequencySq_ge_fortyThirds_div_volume_sq
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N)
    (hmassLower : ∀ i, (4 / 5 : Real) ≤ m.mass i)
    (hmassUpper : ∀ i, m.mass i ≤ (6 / 5 : Real))
    (mode : Lattice.Site N) (hfrequency : 0 < modeFrequency m mode) :
    (40 / 3 : Real) / (N : Real) ^ 2 ≤ modeFrequencySq m mode := by
  let k : Fin (Fintype.card (Lattice.Site N)) := orderedIndexEquiv.symm mode
  have hcompare := orderedEigenvalue_harmonic_compare_clean
    m (4 / 5 : Real) (6 / 5 : Real) (by norm_num) (by norm_num)
      hmassLower hmassUpper k
  have horderedEq :
      orderedEigenvalue (harmonicHermitian m) k = modeFrequencySq m mode := by
    rw [← orderedEigenvalue_equiv (harmonicHermitian m) k]
    simp only [k, Equiv.apply_symm_apply]
    rfl
  have hrandomPositive :
      0 < orderedEigenvalue (harmonicHermitian m) k := by
    rw [horderedEq, ← modeFrequency_sq]
    positivity
  have hcleanPositive :
      0 < orderedEigenvalue (cleanCycleHarmonicHermitian N) k := by
    have hupper := hcompare.2
    norm_num at hupper
    nlinarith
  have hclean :=
    sixteen_div_volume_sq_le_clean_orderedEigenvalue_of_pos N k hcleanPositive
  calc
    (40 / 3 : Real) / (N : Real) ^ 2 =
        (6 / 5 : Real)⁻¹ * (16 / (N : Real) ^ 2) := by
      norm_num
      ring
    _ ≤ (6 / 5 : Real)⁻¹ *
          orderedEigenvalue (cleanCycleHarmonicHermitian N) k := by
      exact mul_le_mul_of_nonneg_left hclean (by norm_num)
    _ ≤ orderedEigenvalue (harmonicHermitian m) k := hcompare.1
    _ = modeFrequencySq m mode := horderedEq

/-- A convenient frequency form of the clean comparison: every positive
frequency in the frozen support is at least `1/N`. -/
theorem frozenSupport_inv_modeFrequency_le_volume
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N)
    (hmassLower : ∀ i, (4 / 5 : Real) ≤ m.mass i)
    (hmassUpper : ∀ i, m.mass i ≤ (6 / 5 : Real))
    (mode : Lattice.Site N) (hfrequency : 0 < modeFrequency m mode) :
    (modeFrequency m mode)⁻¹ ≤ (N : Real) := by
  have hN : 0 < (N : Real) := by exact_mod_cast NeZero.pos N
  have hstrong := frozenSupport_modeFrequencySq_ge_fortyThirds_div_volume_sq
    m hmassLower hmassUpper mode hfrequency
  have hone : (N : Real)⁻¹ ^ 2 ≤ modeFrequency m mode ^ 2 := by
    rw [modeFrequency_sq]
    calc
      (N : Real)⁻¹ ^ 2 = 1 / (N : Real) ^ 2 := by
        field_simp [ne_of_gt hN]
      _ ≤ (40 / 3 : Real) / (N : Real) ^ 2 := by
        apply div_le_div_of_nonneg_right (by norm_num) (sq_nonneg _)
      _ ≤ modeFrequencySq m mode := hstrong
  have hinvFrequency : (N : Real)⁻¹ ≤ modeFrequency m mode := by
    have hinvN0 : 0 ≤ (N : Real)⁻¹ := inv_nonneg.mpr hN.le
    nlinarith [modeFrequency_nonneg m mode]
  apply (inv_le_iff_one_le_mul₀ hfrequency).2
  calc
    1 = (N : Real) * (N : Real)⁻¹ := by
      exact (mul_inv_cancel₀ (ne_of_gt hN)).symm
    _ ≤ (N : Real) * modeFrequency m mode :=
      mul_le_mul_of_nonneg_left hinvFrequency hN.le

/-- Fixed-common Parseval converts the deterministic positive-frequency
floor into the linear-volume observed-child inverse-frequency moment bound. -/
theorem observedChildAcousticInverseMoment_le_volume
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N)
    (hmassLower : ∀ i, (4 / 5 : Real) ≤ m.mass i)
    (hmassUpper : ∀ i, m.mass i ≤ (6 / 5 : Real))
    (observed : Lattice.Site N) :
    observedChildAcousticInverseMoment m observed ≤ (N : Real) := by
  classical
  let common : OrderedModeIndex N := orderedIndexEquiv.symm observed
  let f : Lattice.Site N → Real := fun mode ↦
    repeatedCubicCoefficient (harmonicNormalizedEdgeFrame m)
        common (orderedIndexEquiv.symm mode) ^ 2
  have hterm (mode : Lattice.Site N) :
      f mode / modeFrequency m mode ≤ (N : Real) * f mode := by
    have hf : 0 ≤ f mode := sq_nonneg _
    by_cases hzero : modeFrequency m mode = 0
    · rw [hzero]
      simp only [div_zero]
      exact mul_nonneg (by positivity) hf
    · have hpositive : 0 < modeFrequency m mode :=
        lt_of_le_of_ne (modeFrequency_nonneg m mode) (Ne.symm hzero)
      have hinv := frozenSupport_inv_modeFrequency_le_volume
        m hmassLower hmassUpper mode hpositive
      rw [div_eq_mul_inv]
      simpa only [mul_comm] using mul_le_mul_of_nonneg_left hinv hf
  rw [← sum_site_repeatedCoefficient_sq_div_frequency_eq_acousticMoment]
  have hsum :
      (∑ mode : Lattice.Site N, f mode / modeFrequency m mode) ≤
        (N : Real) := by
    calc
      (∑ mode : Lattice.Site N, f mode / modeFrequency m mode) ≤
          ∑ mode : Lattice.Site N, (N : Real) * f mode :=
        Finset.sum_le_sum fun mode _ ↦ hterm mode
      _ = (N : Real) * ∑ mode : Lattice.Site N, f mode := by
        rw [Finset.mul_sum]
      _ ≤ (N : Real) * 1 := by
        apply mul_le_mul_of_nonneg_left
        · calc
            (∑ mode : Lattice.Site N, f mode) =
                ∑ other : OrderedModeIndex N,
                  repeatedCubicCoefficient (harmonicNormalizedEdgeFrame m)
                    common other ^ 2 := by
              apply Fintype.sum_equiv orderedIndexEquiv.symm
              intro other
              simp [f]
            _ = inverseParticipationRatio
                (harmonicNormalizedEdgeFrame m) common :=
              sum_harmonicRepeatedCubicCoefficient_sq_eq_ipr m common
            _ ≤ 1 := inverseParticipationRatio_le_one
              (harmonicNormalizedEdgeFrame m)
              (harmonicNormalizedEdgeFrame_orthonormal_unconditional m) common
        · positivity
      _ = (N : Real) := mul_one _
  simpa only [f, common] using hsum

/-- Linear-volume substitution into the complete q-level off-resonant static
mass.  The remaining observed-frequency terms stay explicit. -/
theorem qLevelOffResonantCorrectionStaticMass_le_linear_volume
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa : Real)
    (energy : Lattice.Site N → Real) (observed : Lattice.Site N)
    (energyBound ceiling : Real)
    (hsimple : SimpleOrderedSpectrum (harmonicHermitian m))
    (hEnergyBoundNonneg : 0 ≤ energyBound)
    (hEnergy : ∀ mode, 0 ≤ energy mode)
    (hEnergyBound : ∀ mode, energy mode ≤ energyBound)
    (hObserved : 0 < modeFrequency m observed)
    (hCeiling : 0 ≤ ceiling)
    (hFrequency : ∀ mode,
      orderedModeFrequency (harmonicHermitian m) mode ≤ ceiling)
    (hmassLower : ∀ i, (4 / 5 : Real) ≤ m.mass i)
    (hmassUpper : ∀ i, m.mass i ≤ (6 / 5 : Real)) :
    qLevelOffResonantCorrectionStaticMass m kappa energy observed ≤
      16 * kappa ^ 2 * energyBound ^ 2 * (N : Real) +
        12 * (kappa ^ 2 * energyBound ^ 2 /
          modeFrequency m observed ^ 2) * ceiling +
        8 * kappa ^ 2 * energyBound ^ 2 /
          modeFrequency m observed := by
  have hbase :=
    qLevelOffResonantCorrectionStaticMass_le_acousticMoment_add_uniform
      m kappa energy observed energyBound ceiling hsimple
      hEnergyBoundNonneg hEnergy hEnergyBound hObserved hCeiling hFrequency
  have hmoment := observedChildAcousticInverseMoment_le_volume
    m hmassLower hmassUpper observed
  exact hbase.trans (by gcongr)

/-- Inverse-time endpoint with the deterministic linear-volume acoustic
moment substituted into the exact q-level correction estimate. -/
theorem abs_qLevelOffResonantCorrectionSum_le_linear_volume_over_time
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa : Real)
    (energy : Lattice.Site N → Real) (observed : Lattice.Site N)
    (energyBound ceiling : Real)
    (hsimple : SimpleOrderedSpectrum (harmonicHermitian m))
    (hEnergyBoundNonneg : 0 ≤ energyBound)
    (hEnergy : ∀ mode, 0 ≤ energy mode)
    (hEnergyBound : ∀ mode, energy mode ≤ energyBound)
    (hObserved : 0 < modeFrequency m observed)
    (hCeiling : 0 ≤ ceiling)
    (hFrequency : ∀ mode,
      orderedModeFrequency (harmonicHermitian m) mode ≤ ceiling)
    (hmassLower : ∀ i, (4 / 5 : Real) ≤ m.mass i)
    (hmassUpper : ∀ i, m.mass i ≤ (6 / 5 : Real))
    {time : Real} (hTime : 0 < time) :
    |qLevelOffResonantCorrectionSum m kappa time energy observed| ≤
      (16 * kappa ^ 2 * energyBound ^ 2 * (N : Real) +
        12 * (kappa ^ 2 * energyBound ^ 2 /
          modeFrequency m observed ^ 2) * ceiling +
        8 * kappa ^ 2 * energyBound ^ 2 /
          modeFrequency m observed) / time := by
  have hbase := abs_qLevelOffResonantCorrectionSum_le_inverseTime
    m kappa energy observed hTime hObserved
  exact hbase.trans (div_le_div_of_nonneg_right
    (qLevelOffResonantCorrectionStaticMass_le_linear_volume
      m kappa energy observed energyBound ceiling hsimple
      hEnergyBoundNonneg hEnergy hEnergyBound hObserved hCeiling hFrequency
      hmassLower hmassUpper) hTime.le)

end

end ArchonPhysics.FreeFPUTObservedChildAcousticMomentLinearVolumeBound
