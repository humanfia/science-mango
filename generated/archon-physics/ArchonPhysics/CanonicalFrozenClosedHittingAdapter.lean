import ArchonPhysics.CanonicalRandomMassPhasePositiveDenominator
import ArchonPhysics.MeasurableClosedHittingTime
import ArchonPhysics.OrderedPositiveInitialEnergyProfile

/-!
# Closed-threshold adapter for the canonical frozen observable

The repository's late-window average is totalized to zero at `T = 0`, so its
normalized `l1` diagnostic need not be continuous there.  This file proves
exactly the regularity which the positive-time hitting convention needs:

* coordinatewise continuous energy paths give a late-window diagnostic which
  is continuous at every `T > 0` whose normalization denominator is nonzero;
* as `T -> 0+`, the diagnostic converges to the normalized instantaneous
  energy profile;
* on a simple frozen quarter-profile realization, that right limit is at
  least `1 / 8`, hence every threshold `delta < 1 / 8` supplies the compact
  pre-hit separation required by the true closed hitting-time adapter.

No global continuity claim at the totalized value `T = 0` is made.
-/

namespace ArchonPhysics.CanonicalFrozenClosedHittingAdapter

open Filter MeasureTheory Set Topology
open ArchonPhysics
open ArchonPhysics.CanonicalRandomMassPhaseGlobalFlow
open ArchonPhysics.CoerciveHamiltonianContinuation
open ArchonPhysics.CanonicalRandomMassPhasePositiveDenominator
open ArchonPhysics.CanonicalRandomMassPhaseThermalizationObservable
open ArchonPhysics.EquipartitionEntropy
open ArchonPhysics.MeasurableClosedHittingTime
open ArchonPhysics.MeasurableHittingTime
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.MeasurableOrderedHarmonicEnergy
open ArchonPhysics.MassWeightedHamiltonianDynamics
open ArchonPhysics.MeasurableOrderedModeCoupling.Harmonic
open ArchonPhysics.GlobalRandomMassModalObservable
open ArchonPhysics.OrderedPositiveInitialEnergyProfile
open ArchonPhysics.OrderedSingleModeProjector
open ArchonPhysics.OrderedTranslationLastMode
open ArchonPhysics.PositiveHarmonicEnergyAlongCoerciveFlow
open ArchonPhysics.RandomMassMeasurableHarmonicEnergy
open ArchonPhysics.RandomMassPhaseInitialData
open ArchonPhysics.RandomMassPhaseLateWindowObservable
open ArchonPhysics.RandomMassPositiveLateWindowObservable
open ArchonPhysics.RandomMassReducedPhaseInitialData

noncomputable section

/-- A continuous energy path has a continuous late-window average at every
nondegenerate positive window. -/
theorem continuousAt_lateWindowAverage_of_continuous
    {mode : Type} (E : Real -> mode -> Real) (mu T : Real)
    (hmu : mu < 1) (hT : 0 < T)
    (hE : forall i, Continuous (fun t => E t i)) (i : mode) :
    ContinuousAt (fun U => lateWindowAverage E mu U i) T := by
  have hprimitive : Continuous
      (fun x : Real => ∫ t in (0 : Real)..x, E t i) :=
    intervalIntegral.continuous_primitive
      (fun a b => (hE i).intervalIntegrable a b) 0
  have hintegral : Continuous
      (fun U : Real => ∫ t in mu * U..U, E t i) := by
    have heq :
        (fun U : Real => ∫ t in mu * U..U, E t i) =
          fun U =>
            (∫ t in (0 : Real)..U, E t i) -
              ∫ t in (0 : Real)..mu * U, E t i := by
      funext U
      exact eq_sub_iff_add_eq.mpr
        ((add_comm _ _).trans
          (intervalIntegral.integral_add_adjacent_intervals
            ((hE i).intervalIntegrable 0 (mu * U))
            ((hE i).intervalIntegrable (mu * U) U)))
    rw [heq]
    exact hprimitive.sub (hprimitive.comp (continuous_const.mul continuous_id))
  unfold lateWindowAverage
  have hlinear : ContinuousAt (fun U : Real => (1 - mu) * U) T :=
    continuousAt_const.mul continuousAt_id
  exact (hlinear.inv₀
    (mul_ne_zero (sub_ne_zero.mpr (ne_of_gt hmu)) (ne_of_gt hT))).mul
    hintegral.continuousAt

/-- Positive denominator and coordinatewise path continuity make the complete
normalized late-window `l1` diagnostic continuous at a positive time. -/
theorem continuousAt_normalizedLateWindowL1Distance_of_continuous
    {mode : Type} [Fintype mode]
    (E : Real -> mode -> Real) (target : mode -> Real) (mu T : Real)
    (hmu : mu < 1) (hT : 0 < T)
    (hE : forall i, Continuous (fun t => E t i))
    (htotal : totalWeight (lateWindowAverage E mu T) ≠ 0) :
    ContinuousAt (fun U =>
      l1Distance (normalizedWeights (lateWindowAverage E mu U)) target) T := by
  have havg (i : mode) :
      ContinuousAt (fun U => lateWindowAverage E mu U i) T :=
    continuousAt_lateWindowAverage_of_continuous E mu T hmu hT hE i
  have hsum : ContinuousAt
      (fun U => totalWeight (lateWindowAverage E mu U)) T := by
    unfold totalWeight
    exact tendsto_finsetSum Finset.univ fun i _ => havg i
  unfold l1Distance normalizedWeights
  exact tendsto_finsetSum Finset.univ fun i _ =>
    (((havg i).div hsum htotal).sub continuousAt_const).abs

/-- Fixed-endpoint rescaling of a shrinking positive late window. -/
def rescaledLateWindowAverage
    {mode : Type} (E : Real -> mode -> Real) (mu T : Real) : mode -> Real :=
  fun i => (1 - mu)⁻¹ * ∫ s in mu..1, E (s * T) i

theorem lateWindowAverage_eq_rescaled
    {mode : Type} (E : Real -> mode -> Real) (mu T : Real)
    (hmu : mu < 1) (hT : 0 < T) (i : mode) :
    lateWindowAverage E mu T i = rescaledLateWindowAverage E mu T i := by
  have hTne : T ≠ 0 := ne_of_gt hT
  have hwindow_ne : (1 - mu) * T ≠ 0 :=
    mul_ne_zero (sub_ne_zero.mpr (ne_of_gt hmu)) hTne
  unfold lateWindowAverage rescaledLateWindowAverage
  rw [intervalIntegral.integral_comp_mul_right (fun t => E t i) hTne]
  simp only [smul_eq_mul, one_mul]
  rw [show mu * T = mu * T by rfl]
  field_simp [hwindow_ne, hTne, sub_ne_zero.mpr (ne_of_gt hmu)]

/-- The rescaled average is continuous in the scale parameter, including at
zero, because its integration interval is fixed. -/
theorem continuous_rescaledLateWindowAverage
    {mode : Type} (E : Real -> mode -> Real) (mu : Real)
    (hE : forall i, Continuous (fun t => E t i)) (i : mode) :
    Continuous (fun T => rescaledLateWindowAverage E mu T i) := by
  unfold rescaledLateWindowAverage
  apply continuous_const.mul
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (f := fun T s => E (s * T) i)
    ((hE i).comp (continuous_snd.mul continuous_fst)) mu 1

@[simp] theorem rescaledLateWindowAverage_zero
    {mode : Type} (E : Real -> mode -> Real) (mu : Real)
    (hmu : mu < 1) (i : mode) :
    rescaledLateWindowAverage E mu 0 i = E 0 i := by
  have hne : 1 - mu ≠ 0 := sub_ne_zero.mpr (ne_of_gt hmu)
  simp [rescaledLateWindowAverage, hne]

/-- A shrinking late-window average converges from positive times to the
instantaneous energy at time zero. -/
theorem tendsto_lateWindowAverage_nhdsWithin_zero_right
    {mode : Type} (E : Real -> mode -> Real) (mu : Real)
    (hmu : mu < 1) (hE : forall i, Continuous (fun t => E t i)) (i : mode) :
    Tendsto (fun T => lateWindowAverage E mu T i)
      (nhdsWithin 0 (Ioi 0)) (nhds (E 0 i)) := by
  have heq :
      (fun T => lateWindowAverage E mu T i) =ᶠ[nhdsWithin 0 (Ioi 0)]
        (fun T => rescaledLateWindowAverage E mu T i) := by
    filter_upwards [self_mem_nhdsWithin] with T hT
    exact lateWindowAverage_eq_rescaled E mu T hmu hT i
  apply (tendsto_congr' heq).mpr
  have hres : Tendsto (fun T => rescaledLateWindowAverage E mu T i)
      (nhdsWithin 0 (Ioi 0))
      (nhds (rescaledLateWindowAverage E mu 0 i)) :=
    (continuous_rescaledLateWindowAverage E mu hE i).continuousAt.tendsto.mono_left
      inf_le_left
  simpa only [rescaledLateWindowAverage_zero E mu hmu i] using hres


/-- If the instantaneous energy has total one, normalization and the finite
`l1` diagnostic commute with the shrinking-window right limit. -/
theorem tendsto_normalizedLateWindowL1Distance_nhdsWithin_zero_right
    {mode : Type} [Fintype mode]
    (E : Real -> mode -> Real) (target : mode -> Real) (mu : Real)
    (hmu : mu < 1) (hE : forall i, Continuous (fun t => E t i))
    (hsum : totalWeight (E 0) = 1) :
    Tendsto (fun T =>
      l1Distance (normalizedWeights (lateWindowAverage E mu T)) target)
      (nhdsWithin 0 (Ioi 0))
      (nhds (l1Distance (E 0) target)) := by
  let F : Filter Real := nhdsWithin 0 (Ioi 0)
  have havg (i : mode) :
      Tendsto (fun T => lateWindowAverage E mu T i) F (nhds (E 0 i)) :=
    tendsto_lateWindowAverage_nhdsWithin_zero_right E mu hmu hE i
  have htotal : Tendsto
      (fun T => totalWeight (lateWindowAverage E mu T)) F
      (nhds (totalWeight (E 0))) := by
    unfold totalWeight
    exact tendsto_finsetSum Finset.univ fun i _ => havg i
  have hnorm (i : mode) : Tendsto
      (fun T => normalizedWeights (lateWindowAverage E mu T) i) F
      (nhds (E 0 i)) := by
    unfold normalizedWeights
    have hdiv := (havg i).div htotal (by rw [hsum]; norm_num)
    have hfun :
        (fun T => lateWindowAverage E mu T i /
          totalWeight (lateWindowAverage E mu T)) =
        (fun T => lateWindowAverage E mu T i) /
          (fun T => totalWeight (lateWindowAverage E mu T)) := rfl
    rw [hfun]
    simpa only [hsum, div_one] using hdiv
  unfold l1Distance
  exact tendsto_finsetSum Finset.univ fun i _ =>
    ((hnorm i).sub tendsto_const_nhds).abs

/-- Replace a positive-time path by its right limit at and to the left of
zero. This auxiliary extension is not the totalized observable at `T = 0`. -/
def positiveTimeContinuousExtension
    (distance : Real -> Real) (rightLimit : Real) (t : Real) : Real :=
  if 0 < t then distance t else rightLimit

theorem continuous_positiveTimeContinuousExtension
    (distance : Real -> Real) (rightLimit : Real)
    (hcontinuous : forall t, 0 < t -> ContinuousAt distance t)
    (hlimit : Tendsto distance (nhdsWithin 0 (Ioi 0)) (nhds rightLimit)) :
    Continuous (positiveTimeContinuousExtension distance rightLimit) := by
  rw [continuous_iff_continuousAt]
  intro t
  by_cases ht_pos : 0 < t
  · have heq : positiveTimeContinuousExtension distance rightLimit =ᶠ[nhds t]
        distance := by
      filter_upwards [Ioi_mem_nhds ht_pos] with u hu
      change 0 < u at hu
      simp [positiveTimeContinuousExtension, hu]
    exact (hcontinuous t ht_pos).congr_of_eventuallyEq heq
  by_cases ht_neg : t < 0
  · have heq : positiveTimeContinuousExtension distance rightLimit =ᶠ[nhds t]
        (fun _ => rightLimit) := by
      filter_upwards [Iio_mem_nhds ht_neg] with u hu
      change u < 0 at hu
      have hnot : ¬ 0 < u := not_lt.mpr (le_of_lt hu)
      simp [positiveTimeContinuousExtension, hnot]
    exact continuousAt_const.congr_of_eventuallyEq heq
  have ht_zero : t = 0 := by linarith
  subst t
  apply continuousAt_iff_continuous_left'_right'.mpr
  constructor
  · change Tendsto (positiveTimeContinuousExtension distance rightLimit)
      (nhdsWithin 0 (Iio 0))
      (nhds (positiveTimeContinuousExtension distance rightLimit 0))
    have heq : positiveTimeContinuousExtension distance rightLimit =ᶠ[
        nhdsWithin 0 (Iio 0)] (fun _ => rightLimit) := by
      filter_upwards [self_mem_nhdsWithin] with u hu
      change u < 0 at hu
      have hnot : ¬ 0 < u := not_lt.mpr (le_of_lt hu)
      simp [positiveTimeContinuousExtension, hnot]
    rw [show positiveTimeContinuousExtension distance rightLimit 0 = rightLimit by
      simp [positiveTimeContinuousExtension]]
    exact (tendsto_congr' heq).mpr tendsto_const_nhds
  · change Tendsto (positiveTimeContinuousExtension distance rightLimit)
      (nhdsWithin 0 (Ioi 0))
      (nhds (positiveTimeContinuousExtension distance rightLimit 0))
    have heq : positiveTimeContinuousExtension distance rightLimit =ᶠ[
        nhdsWithin 0 (Ioi 0)] distance := by
      filter_upwards [self_mem_nhdsWithin] with u hu
      change 0 < u at hu
      simp [positiveTimeContinuousExtension, hu]
    rw [show positiveTimeContinuousExtension distance rightLimit 0 = rightLimit by
      simp [positiveTimeContinuousExtension]]
    exact (tendsto_congr' heq).mpr hlimit


/-- Changing only the totalized value at real time zero to a value strictly
outside the target does not change a positive-time closed hitting infimum.
The only exceptional `ENNReal` candidate is `top`; adding or removing that
candidate leaves the infimum equal to `top` when no finite hit exists. -/
theorem distanceThresholdHittingTime_positiveTimeContinuousExtension_eq
    (distance : Real -> Real) (rightLimit delta : Real)
    (hdelta : delta < rightLimit) :
    distanceThresholdHittingTime
        (positiveTimeContinuousExtension distance rightLimit) delta =
      distanceThresholdHittingTime distance delta := by
  unfold distanceThresholdHittingTime HittingTime.firstHittingTime
  apply le_antisymm
  · apply le_sInf
    intro time htime
    change 0 < time ∧ distance time.toReal <= delta at htime
    by_cases htop : time = ⊤
    · simp [htop]
    · apply sInf_le
      refine ⟨htime.1, ?_⟩
      have hreal : 0 < time.toReal :=
        ENNReal.toReal_pos (ne_of_gt htime.1) htop
      change positiveTimeContinuousExtension distance rightLimit time.toReal <= delta
      simpa [positiveTimeContinuousExtension, hreal] using htime.2
  · apply le_sInf
    intro time htime
    change 0 < time ∧
      positiveTimeContinuousExtension distance rightLimit time.toReal <= delta at htime
    have htop : time ≠ ⊤ := by
      intro htime_top
      subst time
      simp [positiveTimeContinuousExtension] at htime
      linarith
    apply sInf_le
    refine ⟨htime.1, ?_⟩
    have hreal : 0 < time.toReal :=
      ENNReal.toReal_pos (ne_of_gt htime.1) htop
    change distance time.toReal <= delta
    simpa [positiveTimeContinuousExtension, hreal] using htime.2

/-- Positive-time continuity plus a strictly separated right limit at zero
is sufficient for the compact pre-hit separation used by the closed hitting
adapter. No continuity of the original totalized function at zero is needed. -/
theorem strictlySeparatedBeforeClosedHit_of_positiveTime_of_tendsto_right
    (distance : Real -> Real) (rightLimit delta : Real)
    (hcontinuous : forall t, 0 < t -> ContinuousAt distance t)
    (hlimit : Tendsto distance (nhdsWithin 0 (Ioi 0)) (nhds rightLimit))
    (hdelta : delta < rightLimit) :
    StrictlySeparatedBeforeClosedHit distance delta := by
  let extension := positiveTimeContinuousExtension distance rightLimit
  have hext_cont : Continuous extension :=
    continuous_positiveTimeContinuousExtension distance rightLimit
      hcontinuous hlimit
  have hext_zero : extension 0 = rightLimit := by
    simp [extension, positiveTimeContinuousExtension]
  have hext_sep : StrictlySeparatedBeforeClosedHit extension delta :=
    strictlySeparatedBeforeClosedHit_of_continuous extension delta hext_cont
      (by rw [hext_zero]; exact hdelta)
  have hhit : distanceThresholdHittingTime extension delta =
      distanceThresholdHittingTime distance delta := by
    exact distanceThresholdHittingTime_positiveTimeContinuousExtension_eq
      distance rightLimit delta hdelta
  intro b hb
  obtain ⟨epsilon, hepsilon, hmargin⟩ := hext_sep b (by simpa [hhit] using hb)
  refine ⟨epsilon, hepsilon, ?_⟩
  intro time htime_pos htime_le
  have hb_ne_top : b ≠ ⊤ :=
    ne_top_of_lt (hb.trans_le le_top)
  have htime_ne_top : time ≠ ⊤ := by
    exact ne_top_of_le_ne_top hb_ne_top htime_le
  have hreal_pos : 0 < time.toReal :=
    ENNReal.toReal_pos (ne_of_gt htime_pos) htime_ne_top
  simpa [extension, positiveTimeContinuousExtension, hreal_pos] using
    hmargin time htime_pos htime_le


/-- Coordinate continuity of the reduced positive-mode energy profile follows
from continuity of the genuine reduced phase-space path. -/
theorem continuous_reducedTrajectoryPositiveEnergyProfile
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (z : Real -> ReducedPhaseSpace m) (hz : Continuous z)
    (k : OrderedModeIndex N) :
    Continuous (fun t => reducedTrajectoryPositiveEnergyProfile m z t k) := by
  change Continuous (fun t => reducedPositiveOrderedEnergyProfile m z t k)
  exact continuous_reducedPositiveOrderedEnergyProfile m z hz k

/-- At time zero the canonical sampled unmasked modal energy is exactly the
prescribed target on every simple realization. -/
theorem canonical_sampledPhysicalOrderedModeEnergy_zero_eq_target
    {N : Nat} [NeZero N] (hN : 3 <= N)
    {a : Real} (ha0 : 0 <= a) (ha1 : a <= 1 / 4)
    (kappa beta g : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (omega : RandomEnsemble.SampleSpace)
    (hsimple : SimpleOrderedSpectrum
      (harmonicHermitian
        (canonicalIIDMassPhaseEnsemble.restrictPositiveMass (N := N) omega)))
    (k : OrderedModeIndex N) :
    sampledPhysicalOrderedModeEnergyAlongFlow
        (canonicalIIDMassPhaseEnsemble.restrictPositiveMass (N := N))
        (canonicalPhaseInitialSample (N := N) kappa beta g a)
        (canonicalRandomMassPhaseGlobalFlow N kappa beta g hbeta)
        (omega, 0) k =
      orderedTargetEnergy N a k := by
  unfold sampledPhysicalOrderedModeEnergyAlongFlow sampledFlowPosition
    sampledFlowMomentum harmonicOrderedPhysicalModeEnergy
    massWeightedPositionSample massWeightedMomentumSample
  change orderedHarmonicModeEnergy
      (harmonicHermitianSample
        (canonicalIIDMassPhaseEnsemble.restrictPositiveMass (N := N)) omega) k
      (sqrtMassTransform
        (canonicalIIDMassPhaseEnsemble.restrictPositiveMass (N := N) omega)
        ((canonicalRandomMassPhaseGlobalFlow N kappa beta g hbeta
          (canonicalPhaseInitialSample (N := N) kappa beta g a omega, 0)).2.1))
      (inverseSqrtMassTransform
        (canonicalIIDMassPhaseEnsemble.restrictPositiveMass (N := N) omega)
        ((canonicalRandomMassPhaseGlobalFlow N kappa beta g hbeta
          (canonicalPhaseInitialSample (N := N) kappa beta g a omega, 0)).2.2)) =
        orderedTargetEnergy N a k
  rw [canonicalRandomMassPhaseGlobalFlow_zero]
  change harmonicOrderedPhysicalModeEnergy
      (canonicalIIDMassPhaseEnsemble.restrictPositiveMass (N := N))
      (initialPhysicalPosition canonicalIIDMassPhaseEnsemble a)
      (initialPhysicalMomentum canonicalIIDMassPhaseEnsemble a) omega k =
    orderedTargetEnergy N a k
  exact harmonicOrderedPhysicalModeEnergy_initial_eq_target
    canonicalIIDMassPhaseEnsemble hN ha0 ha1 omega hsimple k


/-- On a simple spectrum, the realization-dependent positive-mode uniform
mask is the deterministic first-`N - 1` ordered uniform profile. -/
theorem simplePositiveUniformProfile_eq_orderedPositiveUniformWeight
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (hsimple : SimpleOrderedSpectrum (harmonicHermitian m))
    (k : OrderedModeIndex N) :
    (if k ∈ positiveModeIndices (harmonicHermitian m) then
        ((N - 1 : Nat) : Real)⁻¹ else 0) =
      orderedPositiveUniformWeight N (orderedModeIndexEquivFin N k) := by
  rw [positiveModeIndices_eq_univ_erase_last m hsimple]
  have hlast : orderedModeIndexEquivFin N
      (lastOrderedIndex (ι := Lattice.Site N)) = lastSiteOrderedIndex N := by
    apply Fin.ext
    simp [orderedModeIndexEquivFin, lastOrderedIndex, lastSiteOrderedIndex]
  by_cases hk : k = lastOrderedIndex (ι := Lattice.Site N)
  · subst k
    simp [hlast]
  · simp only [Finset.mem_erase, ne_eq, hk, not_false_eq_true,
      Finset.mem_univ, and_self, if_true]
    unfold orderedPositiveUniformWeight
    rw [if_pos]
    have hkval : k.val < Fintype.card (Lattice.Site N) - 1 := by
      have hkne : k.val ≠ Fintype.card (Lattice.Site N) - 1 := by
        intro heq
        apply hk
        apply Fin.ext
        simpa [lastOrderedIndex] using heq
      omega
    simpa [orderedModeIndexEquivFin] using hkval

/-- The simple-spectrum frozen quarter target is separated from the actual
positive-mode uniform mask by at least `1 / 8`. -/
theorem quarter_orderedTargetEnergy_l1_positiveUniform_lower
    {N : Nat} [NeZero N] (hN : 3 <= N)
    (m : Lattice.PositiveMassConfig N)
    (hsimple : SimpleOrderedSpectrum (harmonicHermitian m)) :
    (1 / 8 : Real) <=
      ∑ k : OrderedModeIndex N,
        |orderedTargetEnergy N (1 / 4) k -
          (if k ∈ positiveModeIndices (harmonicHermitian m) then
            ((N - 1 : Nat) : Real)⁻¹ else 0)| := by
  have hbase := quarterAmplitude_orderedPositive_l1_lower (N := N) hN
  calc
    (1 / 8 : Real) <=
        ∑ i : Fin N,
          |orderedPositiveInitialEnergyProfile N (1 / 4) i -
            orderedPositiveUniformWeight N i| := hbase
    _ = ∑ k : OrderedModeIndex N,
          |orderedTargetEnergy N (1 / 4) k -
            (if k ∈ positiveModeIndices (harmonicHermitian m) then
              ((N - 1 : Nat) : Real)⁻¹ else 0)| := by
      symm
      exact Fintype.sum_equiv (orderedModeIndexEquivFin N)
        (fun k : OrderedModeIndex N =>
          |orderedTargetEnergy N (1 / 4) k -
            (if k ∈ positiveModeIndices (harmonicHermitian m) then
              ((N - 1 : Nat) : Real)⁻¹ else 0)|)
        (fun i : Fin N =>
          |orderedPositiveInitialEnergyProfile N (1 / 4) i -
            orderedPositiveUniformWeight N i|)
        (fun k => by
          rw [simplePositiveUniformProfile_eq_orderedPositiveUniformWeight
            m hsimple k]
          rfl)


/-- On every simple quarter-profile realization, the canonical frozen
late-window distance is continuous at each positive time. -/
theorem continuousAt_canonicalFrozenQuarterLateWindowL1Distance_of_simple
    {N : Nat} [NeZero N] (hN : 3 <= N)
    (kappa beta g : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (omega : RandomEnsemble.SampleSpace)
    (hsimple : SimpleOrderedSpectrum
      (harmonicHermitian
        (canonicalIIDMassPhaseEnsemble.restrictPositiveMass (N := N) omega)))
    (mu T : Real) (hmu0 : 0 <= mu) (hmu1 : mu < 1) (hT : 0 < T) :
    ContinuousAt (fun U =>
      canonicalFrozenLateWindowL1Distance
        (N := N) kappa beta g hbeta (1 / 4) mu U omega) T := by
  obtain ⟨z, hz0, hz, hmatch, _hmode, _hdistance⟩ :=
    canonicalFrozenLateWindowL1Distance_matches_reduced_of_simple
      (a := (1 / 4 : Real)) hN (by norm_num) (by norm_num) kappa beta g hbeta omega hsimple mu T
  have hzcont : Continuous z :=
    continuous_iff_continuousAt.mpr fun t => (hz t).continuousAt
  have hdistance :
      (fun U => canonicalFrozenLateWindowL1Distance
        (N := N) kappa beta g hbeta (1 / 4) mu U omega) =
      fun U => reducedTrajectoryPositiveLateWindowL1Distance
        (canonicalIIDMassPhaseEnsemble.restrictPositiveMass (N := N) omega)
        z mu U := by
    funext U
    exact sampledPositiveLateWindowL1Distance_eq_reduced_of_match
      (canonicalIIDMassPhaseEnsemble.restrictPositiveMass (N := N))
      (canonicalPhaseInitialSample (N := N) kappa beta g (1 / 4))
      (canonicalRandomMassPhaseGlobalFlow N kappa beta g hbeta)
      kappa beta g omega z hmatch mu U
  rw [hdistance]
  unfold reducedTrajectoryPositiveLateWindowL1Distance
  apply continuousAt_normalizedLateWindowL1Distance_of_continuous
    (hmu := hmu1) (hT := hT)
  · intro k
    exact continuous_reducedTrajectoryPositiveEnergyProfile
      (canonicalIIDMassPhaseEnsemble.restrictPositiveMass (N := N) omega)
      z hzcont k
  · have hunit : reducedPhysicalHarmonicEnergy
        (canonicalIIDMassPhaseEnsemble.restrictPositiveMass (N := N) omega)
        (reducedInitialStateOfSimple canonicalIIDMassPhaseEnsemble
          (1 / 4) omega hsimple) = 1 :=
      reducedPhysicalHarmonicEnergy_reducedInitialStateOfSimple_eq_one
        (a := (1 / 4 : Real)) canonicalIIDMassPhaseEnsemble hN (by norm_num) (by norm_num)
          omega hsimple
    have hpos := reducedPositiveLateWindowTotalWeight_pos
      (canonicalIIDMassPhaseEnsemble.restrictPositiveMass (N := N) omega)
      hbeta g
      (reducedInitialStateOfSimple canonicalIIDMassPhaseEnsemble
        (1 / 4) omega hsimple) z hz0 hz hunit hsimple
      mu T hmu0 hmu1 hT
    have hprofiles :
        reducedTrajectoryPositiveEnergyProfile
            (canonicalIIDMassPhaseEnsemble.restrictPositiveMass (N := N) omega) z =
          reducedPositiveOrderedEnergyProfile
            (canonicalIIDMassPhaseEnsemble.restrictPositiveMass (N := N) omega) z := rfl
    rw [hprofiles]
    exact ne_of_gt hpos


/-- The actual simple-spectrum quarter-profile distance approached by the
totalized late-window observable as `T -> 0+`. -/
def canonicalFrozenQuarterInitialL1Distance
    {N : Nat} [NeZero N] (omega : RandomEnsemble.SampleSpace) : Real :=
  l1Distance (orderedTargetEnergy N (1 / 4))
    (fun k : OrderedModeIndex N =>
      if k ∈ positiveModeIndices
          (harmonicHermitian
            (canonicalIIDMassPhaseEnsemble.restrictPositiveMass
              (N := N) omega)) then
        ((N - 1 : Nat) : Real)⁻¹
      else 0)

theorem canonicalFrozenQuarterInitialL1Distance_lower
    {N : Nat} [NeZero N] (hN : 3 <= N)
    (omega : RandomEnsemble.SampleSpace)
    (hsimple : SimpleOrderedSpectrum
      (harmonicHermitian
        (canonicalIIDMassPhaseEnsemble.restrictPositiveMass (N := N) omega))) :
    (1 / 8 : Real) <= canonicalFrozenQuarterInitialL1Distance (N := N) omega := by
  exact quarter_orderedTargetEnergy_l1_positiveUniform_lower hN
    (canonicalIIDMassPhaseEnsemble.restrictPositiveMass (N := N) omega) hsimple

/-- The positive-time canonical quarter observable converges at zero to its
true frozen two-band distance, rather than to the totalized `T = 0` value. -/
theorem tendsto_canonicalFrozenQuarterLateWindowL1Distance_zero_right_of_simple
    {N : Nat} [NeZero N] (hN : 3 <= N)
    (kappa beta g : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (omega : RandomEnsemble.SampleSpace)
    (hsimple : SimpleOrderedSpectrum
      (harmonicHermitian
        (canonicalIIDMassPhaseEnsemble.restrictPositiveMass (N := N) omega)))
    (mu : Real) (hmu : mu < 1) :
    Tendsto (fun T => canonicalFrozenLateWindowL1Distance
      (N := N) kappa beta g hbeta (1 / 4) mu T omega)
      (nhdsWithin 0 (Ioi 0))
      (nhds (canonicalFrozenQuarterInitialL1Distance (N := N) omega)) := by
  obtain ⟨z, _hz0, hz, hmatch, hmode, _hdistance⟩ :=
    canonicalFrozenLateWindowL1Distance_matches_reduced_of_simple
      (a := (1 / 4 : Real)) hN (by norm_num) (by norm_num)
      kappa beta g hbeta omega hsimple mu 1
  have hzcont : Continuous z :=
    continuous_iff_continuousAt.mpr fun t => (hz t).continuousAt
  have hdistance :
      (fun T => canonicalFrozenLateWindowL1Distance
        (N := N) kappa beta g hbeta (1 / 4) mu T omega) =
      fun T => reducedTrajectoryPositiveLateWindowL1Distance
        (canonicalIIDMassPhaseEnsemble.restrictPositiveMass (N := N) omega)
        z mu T := by
    funext T
    exact sampledPositiveLateWindowL1Distance_eq_reduced_of_match
      (canonicalIIDMassPhaseEnsemble.restrictPositiveMass (N := N))
      (canonicalPhaseInitialSample (N := N) kappa beta g (1 / 4))
      (canonicalRandomMassPhaseGlobalFlow N kappa beta g hbeta)
      kappa beta g omega z hmatch mu T
  have hmode0 (k : OrderedModeIndex N) :
      reducedPhysicalOrderedModeEnergy
          (canonicalIIDMassPhaseEnsemble.restrictPositiveMass (N := N) omega)
          (z 0) k = orderedTargetEnergy N (1 / 4) k := by
    exact (hmode 0 k).symm.trans
      (canonical_sampledPhysicalOrderedModeEnergy_zero_eq_target
        hN (a := (1 / 4 : Real)) (by norm_num) (by norm_num)
        kappa beta g hbeta omega hsimple k)
  have hEzero (k : OrderedModeIndex N) :
      reducedTrajectoryPositiveEnergyProfile
          (canonicalIIDMassPhaseEnsemble.restrictPositiveMass (N := N) omega)
          z 0 k = orderedTargetEnergy N (1 / 4) k := by
    unfold reducedTrajectoryPositiveEnergyProfile
    by_cases hk : k ∈ positiveModeIndices
        (harmonicHermitian
          (canonicalIIDMassPhaseEnsemble.restrictPositiveMass (N := N) omega))
    · rw [if_pos hk, hmode0 k]
    · rw [if_neg hk]
      have hlast : k = lastOrderedIndex (ι := Lattice.Site N) := by
        rw [positiveModeIndices_eq_univ_erase_last
          (canonicalIIDMassPhaseEnsemble.restrictPositiveMass (N := N) omega)
          hsimple] at hk
        simpa using hk
      subst k
      exact (orderedTargetEnergy_last (N := N) (1 / 4)).symm
  have hEfun :
      reducedTrajectoryPositiveEnergyProfile
          (canonicalIIDMassPhaseEnsemble.restrictPositiveMass (N := N) omega) z 0 =
        orderedTargetEnergy N (1 / 4) := funext hEzero
  have hsum : totalWeight
      (reducedTrajectoryPositiveEnergyProfile
        (canonicalIIDMassPhaseEnsemble.restrictPositiveMass (N := N) omega) z 0) = 1 := by
    rw [hEfun]
    exact sum_orderedTargetEnergy_eq_one hN (1 / 4)
  have hlimit :=
    tendsto_normalizedLateWindowL1Distance_nhdsWithin_zero_right
      (reducedTrajectoryPositiveEnergyProfile
        (canonicalIIDMassPhaseEnsemble.restrictPositiveMass (N := N) omega) z)
      (fun k : OrderedModeIndex N =>
        if k ∈ positiveModeIndices
            (harmonicHermitian
              (canonicalIIDMassPhaseEnsemble.restrictPositiveMass
                (N := N) omega)) then
          ((N - 1 : Nat) : Real)⁻¹
        else 0)
      mu hmu
      (fun k => continuous_reducedTrajectoryPositiveEnergyProfile
        (canonicalIIDMassPhaseEnsemble.restrictPositiveMass (N := N) omega)
        z hzcont k) hsum
  rw [hdistance]
  unfold reducedTrajectoryPositiveLateWindowL1Distance
  simpa [canonicalFrozenQuarterInitialL1Distance, hEfun] using hlimit


/-- For the frozen quarter profile, every threshold below `1 / 8` supplies the
compact pre-hit separation required for a true closed first hit. -/
theorem canonicalFrozenQuarter_strictlySeparatedBeforeClosedHit_of_simple
    {N : Nat} [NeZero N] (hN : 3 <= N)
    (kappa beta g : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (omega : RandomEnsemble.SampleSpace)
    (hsimple : SimpleOrderedSpectrum
      (harmonicHermitian
        (canonicalIIDMassPhaseEnsemble.restrictPositiveMass (N := N) omega)))
    (mu delta : Real) (hmu0 : 0 <= mu) (hmu1 : mu < 1)
    (hdelta : delta < 1 / 8) :
    StrictlySeparatedBeforeClosedHit
      (fun T => canonicalFrozenLateWindowL1Distance
        (N := N) kappa beta g hbeta (1 / 4) mu T omega) delta := by
  apply strictlySeparatedBeforeClosedHit_of_positiveTime_of_tendsto_right
    (rightLimit := canonicalFrozenQuarterInitialL1Distance (N := N) omega)
  · intro T hT
    exact continuousAt_canonicalFrozenQuarterLateWindowL1Distance_of_simple
      hN kappa beta g hbeta omega hsimple mu T hmu0 hmu1 hT
  · exact tendsto_canonicalFrozenQuarterLateWindowL1Distance_zero_right_of_simple
      hN kappa beta g hbeta omega hsimple mu hmu1
  · exact hdelta.trans_le
      (canonicalFrozenQuarterInitialL1Distance_lower hN omega hsimple)

/-- The true positive-time closed quarter hitting time. -/
def canonicalFrozenQuarterClosedHittingTime
    {N : Nat} [NeZero N]
    (kappa beta g : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (mu delta : Real) (omega : RandomEnsemble.SampleSpace) : ENNReal :=
  distanceThresholdHittingTime
    (fun T => canonicalFrozenLateWindowL1Distance
      (N := N) kappa beta g hbeta (1 / 4) mu T omega) delta

/-- Its measurable outer rational strict approximation. -/
def canonicalFrozenQuarterOuterRationalClosedHittingTime
    {N : Nat} [NeZero N]
    (kappa beta g : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (mu delta : Real) (omega : RandomEnsemble.SampleSpace) : ENNReal :=
  outerRationalStrictApproximationHittingTime
    (fun T => canonicalFrozenLateWindowL1Distance
      (N := N) kappa beta g hbeta (1 / 4) mu T omega) delta

/-- On every simple realization and for `delta < 1 / 8`, the measurable outer
rational approximation is exactly the true closed first hit. -/
theorem canonicalFrozenQuarterOuterRationalClosedHittingTime_eq_closed_of_simple
    {N : Nat} [NeZero N] (hN : 3 <= N)
    (kappa beta g : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (omega : RandomEnsemble.SampleSpace)
    (hsimple : SimpleOrderedSpectrum
      (harmonicHermitian
        (canonicalIIDMassPhaseEnsemble.restrictPositiveMass (N := N) omega)))
    (mu delta : Real) (hmu0 : 0 <= mu) (hmu1 : mu < 1)
    (hdelta : delta < 1 / 8) :
    canonicalFrozenQuarterOuterRationalClosedHittingTime
        (N := N) kappa beta g hbeta mu delta omega =
      canonicalFrozenQuarterClosedHittingTime
        (N := N) kappa beta g hbeta mu delta omega := by
  unfold canonicalFrozenQuarterOuterRationalClosedHittingTime
    canonicalFrozenQuarterClosedHittingTime
  exact outerRationalStrictApproximationHittingTime_eq_closed_of_separated
    (fun T => canonicalFrozenLateWindowL1Distance
      (N := N) kappa beta g hbeta (1 / 4) mu T omega) delta
    (fun T hT =>
      continuousAt_canonicalFrozenQuarterLateWindowL1Distance_of_simple
        hN kappa beta g hbeta omega hsimple mu T hmu0 hmu1 hT)
    (canonicalFrozenQuarter_strictlySeparatedBeforeClosedHit_of_simple
      hN kappa beta g hbeta omega hsimple mu delta hmu0 hmu1 hdelta)

/-- The outer rational representative is measurable on the whole totalized
sample space, including the null degenerate-spectrum locus. -/
theorem measurable_canonicalFrozenQuarterOuterRationalClosedHittingTime
    {N : Nat} [NeZero N]
    (kappa beta g : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (mu delta : Real) :
    Measurable (canonicalFrozenQuarterOuterRationalClosedHittingTime
      (N := N) kappa beta g hbeta mu delta) := by
  unfold canonicalFrozenQuarterOuterRationalClosedHittingTime
  exact measurable_outerRationalStrictApproximationHittingTime
    (fun omega T => canonicalFrozenLateWindowL1Distance
      (N := N) kappa beta g hbeta (1 / 4) mu T omega) delta
    (fun q => measurable_canonicalFrozenLateWindowL1Distance
      kappa beta g hbeta (1 / 4) mu (q : Real))


/-- The measurable outer representative agrees almost surely with the raw
true closed first hit. -/
theorem canonicalFrozenQuarterOuterRationalClosedHittingTime_eq_closed_ae
    {N : Nat} [NeZero N] (hN : 3 <= N)
    (kappa beta g : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (mu delta : Real) (hmu0 : 0 <= mu) (hmu1 : mu < 1)
    (hdelta : delta < 1 / 8) :
    ∀ᵐ omega ∂canonicalIIDMassPhaseEnsemble.probability,
      canonicalFrozenQuarterOuterRationalClosedHittingTime
          (N := N) kappa beta g hbeta mu delta omega =
        canonicalFrozenQuarterClosedHittingTime
          (N := N) kappa beta g hbeta mu delta omega := by
  have hsimpleAE :=
    RandomMassOrderedProjectorBridge.simpleOrderedSpectrum_ae
      (N := N) canonicalIIDMassPhaseEnsemble (show 2 <= N by omega)
  filter_upwards [hsimpleAE] with omega hsimpleSample
  have hsimple : SimpleOrderedSpectrum
      (harmonicHermitian
        (canonicalIIDMassPhaseEnsemble.restrictPositiveMass (N := N) omega)) := by
    simpa [harmonicHermitianSample, harmonicHermitian] using hsimpleSample
  exact canonicalFrozenQuarterOuterRationalClosedHittingTime_eq_closed_of_simple
    hN kappa beta g hbeta omega hsimple mu delta hmu0 hmu1 hdelta

/-- Consequently the raw true closed hit is almost-everywhere measurable,
with the outer rational construction as an explicit measurable version. -/
theorem aemeasurable_canonicalFrozenQuarterClosedHittingTime
    {N : Nat} [NeZero N] (hN : 3 <= N)
    (kappa beta g : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (mu delta : Real) (hmu0 : 0 <= mu) (hmu1 : mu < 1)
    (hdelta : delta < 1 / 8) :
    AEMeasurable
      (canonicalFrozenQuarterClosedHittingTime
        (N := N) kappa beta g hbeta mu delta)
      canonicalIIDMassPhaseEnsemble.probability := by
  exact (measurable_canonicalFrozenQuarterOuterRationalClosedHittingTime
    (N := N) kappa beta g hbeta mu delta).aemeasurable.congr
      (canonicalFrozenQuarterOuterRationalClosedHittingTime_eq_closed_ae
        hN kappa beta g hbeta mu delta hmu0 hmu1 hdelta)


/-- If the right limit lies strictly inside the closed threshold, hit times
occur arbitrarily close to zero and the positive-time hitting infimum is zero.
The boundary case `rightLimit = delta` is intentionally not asserted. -/
theorem distanceThresholdHittingTime_eq_zero_of_tendsto_right_of_lt
    (distance : Real -> Real) (rightLimit delta : Real)
    (hlimit : Tendsto distance (nhdsWithin 0 (Ioi 0)) (nhds rightLimit))
    (hinside : rightLimit < delta) :
    distanceThresholdHittingTime distance delta = 0 := by
  unfold distanceThresholdHittingTime HittingTime.firstHittingTime
  apply sInf_eq_of_forall_ge_of_forall_gt_exists_lt
  · intro time _htime
    exact bot_le
  · intro bound hbound
    let radius : Real := if bound = ⊤ then 1 else bound.toReal
    have hradius : 0 < radius := by
      dsimp [radius]
      split_ifs with htop
      · norm_num
      · exact ENNReal.toReal_pos (ne_of_gt hbound) htop
    have hhit : ∀ᶠ t in nhdsWithin 0 (Ioi 0), distance t < delta :=
      hlimit.eventually (Iio_mem_nhds hinside)
    have hsmall : ∀ᶠ t in nhdsWithin 0 (Ioi 0), t < radius :=
      mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hradius)
    have hpositive : ∀ᶠ t : Real in nhdsWithin (0 : Real) (Ioi 0), 0 < t :=
      self_mem_nhdsWithin
    obtain ⟨t, ht_hit, ht_small, ht_pos⟩ :=
      (hhit.and (hsmall.and hpositive)).exists
    refine ⟨ENNReal.ofReal t, ?_, ?_⟩
    · refine ⟨ENNReal.ofReal_pos.mpr ht_pos, ?_⟩
      change distance (ENNReal.ofReal t).toReal <= delta
      rw [ENNReal.toReal_ofReal (le_of_lt ht_pos)]
      exact le_of_lt ht_hit
    · by_cases htop : bound = ⊤
      · simp [htop]
      · apply (ENNReal.ofReal_lt_iff_lt_toReal (le_of_lt ht_pos) htop).2
        simpa [radius, htop] using ht_small


/-- Exact lower-side classification at the *actual* positive-time right
limit of a simple frozen quarter realization.  This is stronger than the
uniform sufficient condition `delta < 1 / 8`: no information is discarded
when the realization initial distance is larger than that lower bound. -/
theorem canonicalFrozenQuarter_strictlySeparatedBeforeClosedHit_of_simple_of_lt_initial
    {N : Nat} [NeZero N] (hN : 3 <= N)
    (kappa beta g : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (omega : RandomEnsemble.SampleSpace)
    (hsimple : SimpleOrderedSpectrum
      (harmonicHermitian
        (canonicalIIDMassPhaseEnsemble.restrictPositiveMass (N := N) omega)))
    (mu delta : Real) (hmu0 : 0 <= mu) (hmu1 : mu < 1)
    (hbelow : delta < canonicalFrozenQuarterInitialL1Distance (N := N) omega) :
    StrictlySeparatedBeforeClosedHit
      (fun T => canonicalFrozenLateWindowL1Distance
        (N := N) kappa beta g hbeta (1 / 4) mu T omega) delta := by
  apply strictlySeparatedBeforeClosedHit_of_positiveTime_of_tendsto_right
    (rightLimit := canonicalFrozenQuarterInitialL1Distance (N := N) omega)
  · intro T hT
    exact continuousAt_canonicalFrozenQuarterLateWindowL1Distance_of_simple
      hN kappa beta g hbeta omega hsimple mu T hmu0 hmu1 hT
  · exact tendsto_canonicalFrozenQuarterLateWindowL1Distance_zero_right_of_simple
      hN kappa beta g hbeta omega hsimple mu hmu1
  · exact hbelow

/-- Below the actual right limit, the measurable rational representative is
the raw true closed first hit on each simple realization. -/
theorem canonicalFrozenQuarterOuterRationalClosedHittingTime_eq_closed_of_simple_of_lt_initial
    {N : Nat} [NeZero N] (hN : 3 <= N)
    (kappa beta g : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (omega : RandomEnsemble.SampleSpace)
    (hsimple : SimpleOrderedSpectrum
      (harmonicHermitian
        (canonicalIIDMassPhaseEnsemble.restrictPositiveMass (N := N) omega)))
    (mu delta : Real) (hmu0 : 0 <= mu) (hmu1 : mu < 1)
    (hbelow : delta < canonicalFrozenQuarterInitialL1Distance (N := N) omega) :
    canonicalFrozenQuarterOuterRationalClosedHittingTime
        (N := N) kappa beta g hbeta mu delta omega =
      canonicalFrozenQuarterClosedHittingTime
        (N := N) kappa beta g hbeta mu delta omega := by
  unfold canonicalFrozenQuarterOuterRationalClosedHittingTime
    canonicalFrozenQuarterClosedHittingTime
  exact outerRationalStrictApproximationHittingTime_eq_closed_of_separated
    (fun T => canonicalFrozenLateWindowL1Distance
      (N := N) kappa beta g hbeta (1 / 4) mu T omega) delta
    (fun T hT =>
      continuousAt_canonicalFrozenQuarterLateWindowL1Distance_of_simple
        hN kappa beta g hbeta omega hsimple mu T hmu0 hmu1 hT)
    (canonicalFrozenQuarter_strictlySeparatedBeforeClosedHit_of_simple_of_lt_initial
      hN kappa beta g hbeta omega hsimple mu delta hmu0 hmu1 hbelow)

/-- If the threshold is below the actual right limit almost surely, the
everywhere-measurable rational construction is an almost-sure version of the
raw true closed first hit. -/
theorem canonicalFrozenQuarterOuterRationalClosedHittingTime_eq_closed_ae_of_lt_initial
    {N : Nat} [NeZero N] (hN : 3 <= N)
    (kappa beta g : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (mu delta : Real) (hmu0 : 0 <= mu) (hmu1 : mu < 1)
    (hbelow : ∀ᵐ omega ∂canonicalIIDMassPhaseEnsemble.probability,
      delta < canonicalFrozenQuarterInitialL1Distance (N := N) omega) :
    ∀ᵐ omega ∂canonicalIIDMassPhaseEnsemble.probability,
      canonicalFrozenQuarterOuterRationalClosedHittingTime
          (N := N) kappa beta g hbeta mu delta omega =
        canonicalFrozenQuarterClosedHittingTime
          (N := N) kappa beta g hbeta mu delta omega := by
  have hsimpleAE :=
    RandomMassOrderedProjectorBridge.simpleOrderedSpectrum_ae
      (N := N) canonicalIIDMassPhaseEnsemble (show 2 <= N by omega)
  filter_upwards [hsimpleAE, hbelow] with omega hsimpleSample hbelowOmega
  have hsimple : SimpleOrderedSpectrum
      (harmonicHermitian
        (canonicalIIDMassPhaseEnsemble.restrictPositiveMass (N := N) omega)) := by
    simpa [harmonicHermitianSample, harmonicHermitian] using hsimpleSample
  exact
    canonicalFrozenQuarterOuterRationalClosedHittingTime_eq_closed_of_simple_of_lt_initial
      hN kappa beta g hbeta omega hsimple mu delta hmu0 hmu1 hbelowOmega

/-- Consequently, below its actual right limit almost surely, the raw true
closed hit is almost-everywhere measurable. -/
theorem aemeasurable_canonicalFrozenQuarterClosedHittingTime_of_lt_initial
    {N : Nat} [NeZero N] (hN : 3 <= N)
    (kappa beta g : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (mu delta : Real) (hmu0 : 0 <= mu) (hmu1 : mu < 1)
    (hbelow : ∀ᵐ omega ∂canonicalIIDMassPhaseEnsemble.probability,
      delta < canonicalFrozenQuarterInitialL1Distance (N := N) omega) :
    AEMeasurable
      (canonicalFrozenQuarterClosedHittingTime
        (N := N) kappa beta g hbeta mu delta)
      canonicalIIDMassPhaseEnsemble.probability := by
  exact (measurable_canonicalFrozenQuarterOuterRationalClosedHittingTime
    (N := N) kappa beta g hbeta mu delta).aemeasurable.congr
      (canonicalFrozenQuarterOuterRationalClosedHittingTime_eq_closed_ae_of_lt_initial
        hN kappa beta g hbeta mu delta hmu0 hmu1 hbelow)

/-- Exact upper-side classification at the actual right limit: if the right
limit is strictly inside the threshold, positive-time hits occur arbitrarily
near zero, so the raw closed hitting infimum is zero.  There is deliberately
no theorem here for the boundary equality. -/
theorem canonicalFrozenQuarterClosedHittingTime_eq_zero_of_simple_of_initial_lt
    {N : Nat} [NeZero N] (hN : 3 <= N)
    (kappa beta g : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (omega : RandomEnsemble.SampleSpace)
    (hsimple : SimpleOrderedSpectrum
      (harmonicHermitian
        (canonicalIIDMassPhaseEnsemble.restrictPositiveMass (N := N) omega)))
    (mu delta : Real) (hmu1 : mu < 1)
    (habove : canonicalFrozenQuarterInitialL1Distance (N := N) omega < delta) :
    canonicalFrozenQuarterClosedHittingTime
        (N := N) kappa beta g hbeta mu delta omega = 0 := by
  unfold canonicalFrozenQuarterClosedHittingTime
  exact distanceThresholdHittingTime_eq_zero_of_tendsto_right_of_lt
    (fun T => canonicalFrozenLateWindowL1Distance
      (N := N) kappa beta g hbeta (1 / 4) mu T omega)
    (canonicalFrozenQuarterInitialL1Distance (N := N) omega) delta
    (tendsto_canonicalFrozenQuarterLateWindowL1Distance_zero_right_of_simple
      hN kappa beta g hbeta omega hsimple mu hmu1)
    habove

/-- Above the actual right limit almost surely, the raw closed hitting time is
almost surely the measurable constant zero. -/
theorem canonicalFrozenQuarterClosedHittingTime_eq_zero_ae_of_initial_lt
    {N : Nat} [NeZero N] (hN : 3 <= N)
    (kappa beta g : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (mu delta : Real) (hmu1 : mu < 1)
    (habove : ∀ᵐ omega ∂canonicalIIDMassPhaseEnsemble.probability,
      canonicalFrozenQuarterInitialL1Distance (N := N) omega < delta) :
    ∀ᵐ omega ∂canonicalIIDMassPhaseEnsemble.probability,
      canonicalFrozenQuarterClosedHittingTime
          (N := N) kappa beta g hbeta mu delta omega = 0 := by
  have hsimpleAE :=
    RandomMassOrderedProjectorBridge.simpleOrderedSpectrum_ae
      (N := N) canonicalIIDMassPhaseEnsemble (show 2 <= N by omega)
  filter_upwards [hsimpleAE, habove] with omega hsimpleSample haboveOmega
  have hsimple : SimpleOrderedSpectrum
      (harmonicHermitian
        (canonicalIIDMassPhaseEnsemble.restrictPositiveMass (N := N) omega)) := by
    simpa [harmonicHermitianSample, harmonicHermitian] using hsimpleSample
  exact canonicalFrozenQuarterClosedHittingTime_eq_zero_of_simple_of_initial_lt
    hN kappa beta g hbeta omega hsimple mu delta hmu1 haboveOmega

/-- The upper-side classification also supplies almost-everywhere
measurability of the raw true closed hit. -/
theorem aemeasurable_canonicalFrozenQuarterClosedHittingTime_of_initial_lt
    {N : Nat} [NeZero N] (hN : 3 <= N)
    (kappa beta g : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (mu delta : Real) (hmu1 : mu < 1)
    (habove : ∀ᵐ omega ∂canonicalIIDMassPhaseEnsemble.probability,
      canonicalFrozenQuarterInitialL1Distance (N := N) omega < delta) :
    AEMeasurable
      (canonicalFrozenQuarterClosedHittingTime
        (N := N) kappa beta g hbeta mu delta)
      canonicalIIDMassPhaseEnsemble.probability := by
  have hzero := canonicalFrozenQuarterClosedHittingTime_eq_zero_ae_of_initial_lt
    hN kappa beta g hbeta mu delta hmu1 habove
  have hzeroSymm : ∀ᵐ omega ∂canonicalIIDMassPhaseEnsemble.probability,
      (0 : ENNReal) = canonicalFrozenQuarterClosedHittingTime
        (N := N) kappa beta g hbeta mu delta omega := by
    filter_upwards [hzero] with omega hzeroOmega
    exact hzeroOmega.symm
  exact (measurable_const : Measurable
    (fun _ : RandomEnsemble.SampleSpace => (0 : ENNReal))).aemeasurable.congr
      hzeroSymm


end

end ArchonPhysics.CanonicalFrozenClosedHittingAdapter
