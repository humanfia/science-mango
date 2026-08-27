import ArchonPhysics.CanonicalRankFrequencyMarkedBroadenedMarginal
import Mathlib.MeasureTheory.Measure.Prokhorov

/-!
# Mass bounds and cluster criteria for canonical marked broadenings

The normalized finite-time resonance peak has height `T / (2 * pi)`.  This
gives an unconditional linear-in-time mass bound.  An actual time-uniform
bound requires additional mismatch small-ball information.  We isolate one
sufficient missing input: a nonnegative integrable Lebesgue density for the
scalar per-site collision law which is continuous at zero.

The canonical marked broadened targets retain one common compact support.
Consequently any genuine uniform mass bound gives a finite-measure weak
cluster point.  No scalar-IDS marginal is identified with a collision-weighted
leg marginal here.
-/

namespace ArchonPhysics.CanonicalRankFrequencyMarkedBroadenedMassBounds

open ArchonPhysics
open ArchonPhysics.BroadenedResonanceMeasure
open ArchonPhysics.CanonicalCollisionMeasureWeakLimit
open ArchonPhysics.CanonicalJointFrequencyFiniteMeasureWeakLimit
open ArchonPhysics.CanonicalJointFrequencyMeasureWeakLimit
open ArchonPhysics.CanonicalRankFrequencyMarkedBroadenedLimit
open ArchonPhysics.CanonicalRankFrequencyMarkedBroadenedMarginal
open ArchonPhysics.CanonicalRankFrequencyMarkedCompactness
open ArchonPhysics.CanonicalRankFrequencyMarkedFiniteMeasureWeakLimit
open ArchonPhysics.CanonicalRankFrequencyMarkedMeasure
open ArchonPhysics.CanonicalRankFrequencyMarkedMeasureWeakLimit
open ArchonPhysics.CanonicalRankFrequencyMarkedResonanceLimit
open ArchonPhysics.MeasurableOrderedModeCoupling.Harmonic
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.NormalizedResonancePeakKernel
open ArchonPhysics.OrderedSingleModeProjector
open ArchonPhysics.ResonanceKernelLipschitz
open ArchonPhysics.UniformCollisionDensityTransfer
open Filter MeasureTheory Set Topology
open scoped ENNReal

noncomputable section

variable {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
  [OpensMeasurableSpace X]

/-- Peak height times original mass bounds every broadened total mass. -/
theorem broadenedResonanceMeasure_mass_le_height_mul
    (mu : FiniteMeasure X) (mismatch : X → Real)
    (hmismatch : Continuous mismatch) (T : Real) (hT : 0 < T) :
    ((broadenedResonanceMeasure mu mismatch hmismatch.measurable T hT).mass :
        Real) ≤
      T / (2 * Real.pi) * (mu.mass : Real) := by
  rw [broadenedResonanceMeasure_mass_eq_integral]
  have hbound := norm_integral_le_of_norm_le_const
    (μ := (mu : Measure X))
    (f := fun x ↦ normalizedFiniteTimeResonanceKernel (mismatch x) T)
    (C := T / (2 * Real.pi))
    (ae_of_all (mu : Measure X) fun x ↦ by
      rw [Real.norm_eq_abs, abs_of_nonneg
        (normalizedFiniteTimeResonanceKernel_nonneg (mismatch x) T)]
      exact normalizedFiniteTimeResonanceKernel_le_height (mismatch x) hT)
  have hnonneg : 0 ≤ ∫ x,
      normalizedFiniteTimeResonanceKernel (mismatch x) T
        ∂(mu : Measure X) := by
    apply integral_nonneg
    exact fun x ↦ normalizedFiniteTimeResonanceKernel_nonneg (mismatch x) T
  rw [Real.norm_of_nonneg hnonneg] at hbound
  simpa [FiniteMeasure.mass] using hbound

/-- Unconditional linear-growth bound for the canonical marked target. -/
theorem canonicalRankFrequencyMarkedBroadenedPerSiteMeasureLimit_mass_le_linear
    {Omega : Type*} [MeasurableSpace Omega]
    (ensemble : IIDMassPhaseEnsemble Omega)
    (sign : Fin 3 → InteractionSign) (T : Real) (hT : 0 < T) :
    ((canonicalRankFrequencyMarkedBroadenedPerSiteMeasureLimit
        ensemble sign T hT).mass : Real) ≤
      T / (2 * Real.pi) *
        (canonicalJointFrequencyPerSiteMassLimit ensemble : Real) := by
  simpa [canonicalRankFrequencyMarkedBroadenedPerSiteMeasureLimit] using
    broadenedResonanceMeasure_mass_le_height_mul
      (canonicalRankFrequencyMarkedPerSiteMeasureLimit ensemble)
      (markedFrequencyMismatch sign)
      (continuous_markedFrequencyMismatch sign) T hT

/-- The mass divided by time has a time-independent upper bound. -/
theorem canonicalRankFrequencyMarkedBroadenedPerSiteMeasureLimit_mass_div_time_le
    {Omega : Type*} [MeasurableSpace Omega]
    (ensemble : IIDMassPhaseEnsemble Omega)
    (sign : Fin 3 → InteractionSign) (T : Real) (hT : 0 < T) :
    ((canonicalRankFrequencyMarkedBroadenedPerSiteMeasureLimit
        ensemble sign T hT).mass : Real) / T ≤
      (canonicalJointFrequencyPerSiteMassLimit ensemble : Real) /
        (2 * Real.pi) := by
  rw [div_le_iff₀ hT]
  calc
    ((canonicalRankFrequencyMarkedBroadenedPerSiteMeasureLimit
        ensemble sign T hT).mass : Real) ≤
        T / (2 * Real.pi) *
          (canonicalJointFrequencyPerSiteMassLimit ensemble : Real) :=
      canonicalRankFrequencyMarkedBroadenedPerSiteMeasureLimit_mass_le_linear
        ensemble sign T hT
    _ = (canonicalJointFrequencyPerSiteMassLimit ensemble : Real) /
          (2 * Real.pi) * T := by ring

/-- Along any positive time sequence, the time-normalized masses have bounded
range. -/
theorem canonicalRankFrequencyMarkedBroadenedPerSiteMeasureLimit_mass_div_time_bddAbove
    {Omega : Type*} [MeasurableSpace Omega]
    (ensemble : IIDMassPhaseEnsemble Omega)
    (sign : Fin 3 → InteractionSign)
    (time : Nat → Real) (htime_pos : ∀ n, 0 < time n) :
    BddAbove (Set.range fun n ↦
      ((canonicalRankFrequencyMarkedBroadenedPerSiteMeasureLimit
        ensemble sign (time n) (htime_pos n)).mass : Real) / time n) := by
  refine ⟨(canonicalJointFrequencyPerSiteMassLimit ensemble : Real) /
      (2 * Real.pi), ?_⟩
  rintro value ⟨n, rfl⟩
  exact
    canonicalRankFrequencyMarkedBroadenedPerSiteMeasureLimit_mass_div_time_le
      ensemble sign (time n) (htime_pos n)

/-! ## Common compact support -/

/-- The deterministic canonical marked probability limit retains the common
compact marked box. -/
theorem canonicalRankFrequencyMarkedMeasureLimit_compl_uniformSupport_eq_zero :
    (canonicalRankFrequencyMarkedMeasureLimit
      canonicalIIDMassPhaseEnsemble :
        Measure (Fin 3 → RankFrequencyMark))
      (collisionRankFrequencyTripleSupportᶜ) = 0 := by
  have hevent : ∀ᵐ omega ∂(RandomEnsemble.canonicalLaw),
      Tendsto
        (fun n : Nat ↦ canonicalNormalizedRankFrequencyMarkedMeasure
          canonicalIIDMassPhaseEnsemble (n + 1) omega)
        atTop
        (nhds (canonicalRankFrequencyMarkedMeasureLimit
          canonicalIIDMassPhaseEnsemble)) ∧
      (∀ n : Nat, SimpleOrderedSpectrum
        (harmonicHermitian
          (canonicalIIDMassPhaseEnsemble.restrictPositiveMass
            (N := n + 3) omega))) := by
    filter_upwards
      [canonicalNormalizedRankFrequencyMarkedMeasure_tendsto_limit_ae,
        canonicalJointFrequencyVolumes_simpleOrderedSpectrum_ae
          canonicalIIDMassPhaseEnsemble] with omega hlimit hsimple
    exact ⟨hlimit, hsimple⟩
  obtain ⟨omega, hlimit, hsimple⟩ := hevent.exists
  have hopen :=
    ProbabilityMeasure.le_liminf_measure_open_of_tendsto hlimit
      collisionRankFrequencyTripleSupport_isCompact.isClosed.isOpen_compl
  have hzero :
      (fun n : Nat ↦
        (canonicalNormalizedRankFrequencyMarkedMeasure
          canonicalIIDMassPhaseEnsemble (n + 1) omega :
            Measure (Fin 3 → RankFrequencyMark))
          (collisionRankFrequencyTripleSupportᶜ)) =
      (fun _n : Nat ↦ 0) := by
    funext n
    rw [canonicalNormalizedRankFrequencyMarkedMeasure_compl_uniformSupport_eq_zero]
    exact canonicalRankFrequencyTriplePerSiteFiniteMeasure_mass_ne_zero
      canonicalIIDMassPhaseEnsemble (fun _ ↦ InteractionSign.plus)
      (n + 1) omega (by omega)
      (by simpa [Nat.add_assoc] using hsimple n)
  rw [hzero] at hopen
  simpa using hopen

/-- The unnormalized deterministic marked target has the same support. -/
theorem canonicalRankFrequencyMarkedPerSiteMeasureLimit_compl_uniformSupport_eq_zero :
    (canonicalRankFrequencyMarkedPerSiteMeasureLimit
      canonicalIIDMassPhaseEnsemble :
        Measure (Fin 3 → RankFrequencyMark))
      (collisionRankFrequencyTripleSupportᶜ) = 0 := by
  unfold canonicalRankFrequencyMarkedPerSiteMeasureLimit
  rw [FiniteMeasure.toMeasure_smul, Measure.smul_apply]
  change
    (canonicalJointFrequencyPerSiteMassLimit
        canonicalIIDMassPhaseEnsemble : ENNReal) *
      (canonicalRankFrequencyMarkedMeasureLimit
        canonicalIIDMassPhaseEnsemble :
          Measure (Fin 3 → RankFrequencyMark))
          (collisionRankFrequencyTripleSupportᶜ) = 0
  rw [canonicalRankFrequencyMarkedMeasureLimit_compl_uniformSupport_eq_zero,
    mul_zero]

/-- Broadening preserves the common compact support. -/
theorem canonicalRankFrequencyMarkedBroadenedPerSiteMeasureLimit_compl_uniformSupport_eq_zero
    (sign : Fin 3 → InteractionSign) (T : Real) (hT : 0 < T) :
    (canonicalRankFrequencyMarkedBroadenedPerSiteMeasureLimit
      canonicalIIDMassPhaseEnsemble sign T hT :
        Measure (Fin 3 → RankFrequencyMark))
      (collisionRankFrequencyTripleSupportᶜ) = 0 := by
  unfold canonicalRankFrequencyMarkedBroadenedPerSiteMeasureLimit
    broadenedResonanceMeasure
  exact withDensity_absolutelyContinuous _ _
    canonicalRankFrequencyMarkedPerSiteMeasureLimit_compl_uniformSupport_eq_zero

/-- A uniform mass bound plus the common support gives a weak finite-measure
cluster point. -/
theorem exists_canonicalRankFrequencyMarkedBroadenedPerSiteMeasureLimit_cluster_of_mass_le
    (sign : Fin 3 → InteractionSign)
    (time : Nat → Real) (htime_pos : ∀ n, 0 < time n)
    (C : NNReal)
    (hmass : ∀ n,
      (canonicalRankFrequencyMarkedBroadenedPerSiteMeasureLimit
        canonicalIIDMassPhaseEnsemble sign
          (time n) (htime_pos n)).mass ≤ C) :
    ∃ target : FiniteMeasure (Fin 3 → RankFrequencyMark),
      MapClusterPt target atTop
        (fun n ↦ canonicalRankFrequencyMarkedBroadenedPerSiteMeasureLimit
          canonicalIIDMassPhaseEnsemble sign (time n) (htime_pos n)) := by
  let mu : Nat → FiniteMeasure (Fin 3 → RankFrequencyMark) :=
    fun n ↦ canonicalRankFrequencyMarkedBroadenedPerSiteMeasureLimit
      canonicalIIDMassPhaseEnsemble sign (time n) (htime_pos n)
  let compactFamily : Set (FiniteMeasure (Fin 3 → RankFrequencyMark)) :=
    {nu | nu.mass ≤ C ∧
      nu (collisionRankFrequencyTripleSupportᶜ) = 0}
  have hcompact : IsCompact compactFamily := by
    exact isCompact_setOfPred_finiteMeasure_le_of_isCompact C
      collisionRankFrequencyTripleSupport_isCompact
  have hmem : ∀ n, mu n ∈ compactFamily := by
    intro n
    constructor
    · simpa [mu] using hmass n
    · dsimp only [mu]
      exact (FiniteMeasure.null_iff_toMeasure_null _ _).mpr
        (canonicalRankFrequencyMarkedBroadenedPerSiteMeasureLimit_compl_uniformSupport_eq_zero
          sign (time n) (htime_pos n))
  have hmap : Filter.map mu atTop ≤ Filter.principal compactFamily := by
    rw [le_principal_iff]
    change ∀ᶠ target in Filter.map mu atTop, target ∈ compactFamily
    rw [eventually_map]
    exact Eventually.of_forall hmem
  obtain ⟨target, _htarget, htarget⟩ :=
    hcompact.exists_mapClusterPt hmap
  exact ⟨target, by simpa [mu] using htarget⟩

/-! ## Conditional density bridge -/

/-- A nonnegative Lebesgue density rewrites scalar broadened mass as a
kernel-density integral. -/
theorem broadenedResonanceMeasure_id_mass_eq_density_integral
    (mu : FiniteMeasure Real) (rho : Real → Real)
    (hrho : Measurable rho) (hrho_nonneg : ∀ x, 0 ≤ rho x)
    (hmu : (mu : Measure Real) =
      volume.withDensity (fun x ↦ ENNReal.ofReal (rho x)))
    (T : Real) (hT : 0 < T) :
    ((broadenedResonanceMeasure mu id measurable_id T hT).mass : Real) =
      ∫ x : Real, normalizedFiniteTimeResonanceKernel x T * rho x := by
  rw [broadenedResonanceMeasure_mass_eq_integral, hmu]
  calc
    (∫ x : Real, normalizedFiniteTimeResonanceKernel (id x) T
        ∂volume.withDensity (fun x ↦ ENNReal.ofReal (rho x))) =
        ∫ x : Real, (ENNReal.ofReal (rho x)).toReal •
          normalizedFiniteTimeResonanceKernel (id x) T ∂volume :=
      integral_withDensity_eq_integral_toReal_smul
        (ENNReal.measurable_ofReal.comp hrho)
        (Filter.Eventually.of_forall fun _x ↦ ENNReal.ofReal_lt_top) _
    _ = ∫ x : Real,
        normalizedFiniteTimeResonanceKernel x T * rho x := by
      apply integral_congr_ae
      filter_upwards with x
      rw [ENNReal.toReal_ofReal (hrho_nonneg x)]
      simp only [id_eq, smul_eq_mul]
      ring

/-- For a density continuous at zero, scalar broadened mass converges to its
zero-mismatch value along every time sequence tending to infinity. -/
theorem broadenedResonanceMeasure_id_mass_tendsto_of_density
    (mu : FiniteMeasure Real) (rho : Real → Real)
    (hrho_meas : Measurable rho) (hrho_nonneg : ∀ x, 0 ≤ rho x)
    (hrho_int : Integrable rho) (hrho_zero : ContinuousAt rho 0)
    (hmu : (mu : Measure Real) =
      volume.withDensity (fun x ↦ ENNReal.ofReal (rho x)))
    (time : Nat → Real) (htime_pos : ∀ n, 0 < time n)
    (htime : Tendsto time atTop atTop) :
    Tendsto
      (fun n ↦ ((broadenedResonanceMeasure mu id measurable_id
        (time n) (htime_pos n)).mass : Real))
      atTop (nhds (rho 0)) := by
  apply ((tendsto_integral_normalizedFiniteTimeResonanceKernel
    hrho_int hrho_zero).comp htime).congr'
  exact Eventually.of_forall fun n ↦
    (broadenedResonanceMeasure_id_mass_eq_density_integral
      mu rho hrho_meas hrho_nonneg hmu
      (time n) (htime_pos n)).symm

/-- Conditional canonical mass convergence from a scalar collision density. -/
theorem canonicalRankFrequencyMarkedBroadenedPerSiteMass_tendsto_of_collisionDensity
    (sign : Fin 3 → InteractionSign)
    (rho : Real → Real)
    (hrho_meas : Measurable rho) (hrho_nonneg : ∀ x, 0 ≤ rho x)
    (hrho_int : Integrable rho) (hrho_zero : ContinuousAt rho 0)
    (hdensity :
      (canonicalCollisionPerSiteMeasureLimit
        canonicalIIDMassPhaseEnsemble sign : Measure Real) =
      volume.withDensity (fun x ↦ ENNReal.ofReal (rho x)))
    (time : Nat → Real) (htime_pos : ∀ n, 0 < time n)
    (htime : Tendsto time atTop atTop) :
    Tendsto
      (fun n ↦
        ((canonicalRankFrequencyMarkedBroadenedPerSiteMeasureLimit
          canonicalIIDMassPhaseEnsemble sign
            (time n) (htime_pos n)).mass : Real))
      atTop (nhds (rho 0)) := by
  have hscalar := broadenedResonanceMeasure_id_mass_tendsto_of_density
    (canonicalCollisionPerSiteMeasureLimit
      canonicalIIDMassPhaseEnsemble sign)
    rho hrho_meas hrho_nonneg hrho_int hrho_zero hdensity
    time htime_pos htime
  apply hscalar.congr'
  exact Eventually.of_forall fun n ↦ by
    symm
    simpa [canonicalBroadenedCollisionPerSiteMeasureLimit] using
      canonicalRankFrequencyMarkedBroadenedPerSiteMeasureLimit_mass_eq_scalar
        canonicalIIDMassPhaseEnsemble sign (time n) (htime_pos n)

/-- The density input makes the actual unnormalized mass range bounded. -/
theorem canonicalRankFrequencyMarkedBroadenedPerSiteMass_bddAbove_of_collisionDensity
    (sign : Fin 3 → InteractionSign)
    (rho : Real → Real)
    (hrho_meas : Measurable rho) (hrho_nonneg : ∀ x, 0 ≤ rho x)
    (hrho_int : Integrable rho) (hrho_zero : ContinuousAt rho 0)
    (hdensity :
      (canonicalCollisionPerSiteMeasureLimit
        canonicalIIDMassPhaseEnsemble sign : Measure Real) =
      volume.withDensity (fun x ↦ ENNReal.ofReal (rho x)))
    (time : Nat → Real) (htime_pos : ∀ n, 0 < time n)
    (htime : Tendsto time atTop atTop) :
    BddAbove (Set.range fun n ↦
      (canonicalRankFrequencyMarkedBroadenedPerSiteMeasureLimit
        canonicalIIDMassPhaseEnsemble sign
          (time n) (htime_pos n)).mass) := by
  have hreal :=
    canonicalRankFrequencyMarkedBroadenedPerSiteMass_tendsto_of_collisionDensity
      sign rho hrho_meas hrho_nonneg hrho_int hrho_zero hdensity
      time htime_pos htime
  have hnn : Tendsto
      (fun n ↦
        (canonicalRankFrequencyMarkedBroadenedPerSiteMeasureLimit
          canonicalIIDMassPhaseEnsemble sign
            (time n) (htime_pos n)).mass)
      atTop (nhds (Real.toNNReal (rho 0))) := by
    apply NNReal.tendsto_coe.mp
    simpa [Real.coe_toNNReal (rho 0) (hrho_nonneg 0)] using hreal
  exact hnn.bddAbove_range

/-- Density control plus compact support produces a weak finite-measure
cluster point. -/
theorem exists_canonicalRankFrequencyMarkedBroadenedPerSiteMeasureLimit_cluster_of_collisionDensity
    (sign : Fin 3 → InteractionSign)
    (rho : Real → Real)
    (hrho_meas : Measurable rho) (hrho_nonneg : ∀ x, 0 ≤ rho x)
    (hrho_int : Integrable rho) (hrho_zero : ContinuousAt rho 0)
    (hdensity :
      (canonicalCollisionPerSiteMeasureLimit
        canonicalIIDMassPhaseEnsemble sign : Measure Real) =
      volume.withDensity (fun x ↦ ENNReal.ofReal (rho x)))
    (time : Nat → Real) (htime_pos : ∀ n, 0 < time n)
    (htime : Tendsto time atTop atTop) :
    ∃ target : FiniteMeasure (Fin 3 → RankFrequencyMark),
      MapClusterPt target atTop
        (fun n ↦ canonicalRankFrequencyMarkedBroadenedPerSiteMeasureLimit
          canonicalIIDMassPhaseEnsemble sign (time n) (htime_pos n)) := by
  have hbdd :=
    canonicalRankFrequencyMarkedBroadenedPerSiteMass_bddAbove_of_collisionDensity
      sign rho hrho_meas hrho_nonneg hrho_int hrho_zero hdensity
      time htime_pos htime
  rcases hbdd with ⟨C, hC⟩
  apply
    exists_canonicalRankFrequencyMarkedBroadenedPerSiteMeasureLimit_cluster_of_mass_le
      sign time htime_pos C
  intro n
  exact hC (Set.mem_range_self n)

end

end ArchonPhysics.CanonicalRankFrequencyMarkedBroadenedMassBounds
