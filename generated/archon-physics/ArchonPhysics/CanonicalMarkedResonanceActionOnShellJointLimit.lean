import ArchonPhysics.CanonicalMarkedResonanceActionJointDiagonalization
import ArchonPhysics.CanonicalScalarCollisionDensityPositiveCluster
import ArchonPhysics.ResonantThreeWaveKineticRadonNikodym

/-!
# Joint finite-volume to on-shell limit for the canonical marked action

The canonical marked-kernel endpoint already identifies the thermodynamic
marked measure at every fixed positive observation time. The parameterized
diagonalization then supplies a deterministic volume cutoff for the
parameter-dependent squared-sinc test at kinetic time `T(g) = g⁻²`.

This file performs the remaining approximate-identity composition whenever
the scalar mismatch pushforward has an explicitly supplied nonnegative
integrable density which is continuous at exact resonance. Under precisely
that hypothesis, the deterministic action converges to the density at zero,
and the finite-volume action converges to the same value in measure along every
admitted `(N,g)` path.

The density hypothesis is deliberately visible. A merely measurable bounded
Radon--Nikodym density does not determine its value at zero and is insufficient
for this conclusion.
-/

open scoped ENNReal Topology InnerProductSpace RealInnerProductSpace

namespace ArchonPhysics.CanonicalMarkedResonanceActionOnShellJointLimit

open ArchonPhysics
open ArchonPhysics.BroadenedResonanceMeasure
open ArchonPhysics.CanonicalCollisionMeasureWeakLimit
open ArchonPhysics.CanonicalMarkedResonanceActionJointDiagonalization
open ArchonPhysics.CanonicalOnShellMarkedClusterPositiveExistence
open ArchonPhysics.CanonicalRankFrequencyMarkedBroadenedLimit
open ArchonPhysics.CanonicalRankFrequencyMarkedBroadenedMassBounds
open ArchonPhysics.CanonicalRankFrequencyMarkedBroadenedMarginal
open ArchonPhysics.CanonicalRankFrequencyMarkedFiniteMeasureWeakLimit
open ArchonPhysics.CanonicalRankFrequencyMarkedMeasure
open ArchonPhysics.CanonicalRankFrequencyMarkedResonanceLimit
open ArchonPhysics.CanonicalScalarCollisionDensityPositiveCluster
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.RandomMassThreeWaveCollisionNetwork
open ArchonPhysics.ResonantThreeWaveKineticRadonNikodym
open ArchonPhysics.ThermalizationTransfer
open Filter MeasureTheory Set Topology

noncomputable section

/-- The deterministic marked resonance action is exactly the real total mass
of the corresponding broadened marked finite measure. -/
theorem canonicalMarkedResonanceActionLimit_eq_markedBroadenedMass
    (sign : Fin 3 -> InteractionSign)
    (kineticTime : Real -> Real) {g : Real}
    (hT : 0 < kineticTime g) :
    canonicalMarkedResonanceActionLimit sign kineticTime g =
      ((canonicalRankFrequencyMarkedBroadenedPerSiteMeasureLimit
        canonicalIIDMassPhaseEnsemble sign (kineticTime g) hT).mass : Real) := by
  unfold canonicalMarkedResonanceActionLimit
    canonicalRankFrequencyMarkedBroadenedPerSiteMeasureLimit
  exact (broadenedResonanceMeasure_mass_eq_integral
    (canonicalRankFrequencyMarkedPerSiteMeasureLimit
      canonicalIIDMassPhaseEnsemble)
    (measurable_markedFrequencyMismatch sign) hT).symm

/-- Positive weak coupling tending to zero sends inverse-square kinetic time
to infinity. The one-sided filter rules out zero, where inversion is
discontinuous. -/
theorem inverseSquareKineticTime_comp_tendsto_atTop
    {coupling : Nat -> Real}
    (hcoupling : Tendsto coupling atTop (nhdsWithin 0 (Ioi 0))) :
    Tendsto (fun j => inverseSquareKineticTime (coupling j)) atTop atTop := by
  have hinv : Tendsto (fun j => (coupling j)⁻¹) atTop atTop :=
    tendsto_inv_nhdsGT_zero.comp hcoupling
  have hsquare : Tendsto (fun x : Real => x ^ 2) atTop atTop :=
    tendsto_pow_atTop (by norm_num)
  apply (hsquare.comp hinv).congr'
  exact Eventually.of_forall fun j => by
    simp [inverseSquareKineticTime]

/-- The deterministic canonical marked action at `T(g) = g⁻²` converges to
the exact-resonance value of the supplied scalar mismatch density. -/
theorem canonicalInverseSquareMarkedResonanceActionLimit_tendsto_onShell_of_collisionDensity
    (sign : Fin 3 -> InteractionSign)
    (rho : Real -> Real)
    (hrho_meas : Measurable rho)
    (hrho_nonneg : forall x, 0 <= rho x)
    (hrho_int : Integrable rho)
    (hrho_zero : ContinuousAt rho 0)
    (hdensity :
      (canonicalCollisionPerSiteMeasureLimit
        canonicalIIDMassPhaseEnsemble sign : Measure Real) =
      volume.withDensity (fun x => ENNReal.ofReal (rho x)))
    {coupling : Nat -> Real}
    (hcoupling_pos : forall j, 0 < coupling j)
    (hcoupling : Tendsto coupling atTop (nhdsWithin 0 (Ioi 0))) :
    Tendsto
      (fun j => canonicalMarkedResonanceActionLimit sign
        inverseSquareKineticTime (coupling j))
      atTop (nhds (rho 0)) := by
  let time : Nat -> Real := fun j => inverseSquareKineticTime (coupling j)
  have htime_pos : forall j, 0 < time j := fun j =>
    inverseSquareKineticTime_pos (hcoupling_pos j)
  have htime : Tendsto time atTop atTop := by
    simpa only [time] using
      inverseSquareKineticTime_comp_tendsto_atTop hcoupling
  have hmass :=
    canonicalRankFrequencyMarkedBroadenedPerSiteMass_tendsto_of_collisionDensity
      sign rho hrho_meas hrho_nonneg hrho_int hrho_zero hdensity
      time htime_pos htime
  apply hmass.congr'
  exact Eventually.of_forall fun j => by
    exact (canonicalMarkedResonanceActionLimit_eq_markedBroadenedMass
      sign inverseSquareKineticTime
      (inverseSquareKineticTime_pos (hcoupling_pos j))).symm

/-- Above the deterministic fixed-coupling cutoff, the exact finite-volume
action converges in measure to the on-shell density value along every
admissible weak-coupling/large-volume path. -/
theorem canonicalInverseSquareMarkedResonanceAction_tendstoInMeasure_onShell_of_collisionDensity
    (sign : Fin 3 -> InteractionSign)
    (rho : Real -> Real)
    (hrho_meas : Measurable rho)
    (hrho_nonneg : forall x, 0 <= rho x)
    (hrho_int : Integrable rho)
    (hrho_zero : ContinuousAt rho 0)
    (hdensity :
      (canonicalCollisionPerSiteMeasureLimit
        canonicalIIDMassPhaseEnsemble sign : Measure Real) =
      volume.withDensity (fun x => ENNReal.ofReal (rho x)))
    (s : AdmissibleJointLimit
      (canonicalInverseSquareMarkedResonanceActionSizeCutoff sign)) :
    TendstoInMeasure RandomEnsemble.canonicalLaw
      (fun j omega => canonicalMarkedResonanceActionSample sign
        inverseSquareKineticTime (s.coupling j) (s.systemSize j) omega)
      atTop (fun _omega => rho 0) := by
  rw [tendstoInMeasure_iff_measureReal_dist]
  intro epsilon hepsilon
  have htarget :=
    canonicalInverseSquareMarkedResonanceActionLimit_tendsto_onShell_of_collisionDensity
      sign rho hrho_meas hrho_nonneg hrho_int hrho_zero hdensity
      s.coupling_pos s.coupling_tendsto_zero
  have htarget_close : ∀ᶠ j in atTop,
      dist
        (canonicalMarkedResonanceActionLimit sign inverseSquareKineticTime
          (s.coupling j))
        (rho 0) < epsilon / 2 :=
    (Metric.tendsto_nhds.mp htarget) (epsilon / 2) (half_pos hepsilon)
  have hcoupling : Tendsto s.coupling atTop (nhds 0) :=
    s.coupling_tendsto_zero.mono_right inf_le_left
  have hcoupling_small : ∀ᶠ j in atTop, s.coupling j < epsilon / 2 :=
    (tendsto_order.1 hcoupling).2 (epsilon / 2) (half_pos hepsilon)
  have hdomination : ∀ᶠ j in atTop,
      RandomEnsemble.canonicalLaw.real
          {omega |
            epsilon <= dist
              (canonicalMarkedResonanceActionSample sign
                inverseSquareKineticTime (s.coupling j)
                (s.systemSize j) omega)
              (rho 0)} <=
        RandomEnsemble.canonicalLaw.real
          {omega |
            s.coupling j <= dist
              (canonicalMarkedResonanceActionSample sign
                inverseSquareKineticTime (s.coupling j)
                (s.systemSize j) omega)
              (canonicalMarkedResonanceActionLimit sign
                inverseSquareKineticTime (s.coupling j))} := by
    filter_upwards [htarget_close, hcoupling_small] with j hjtarget hjcoupling
    apply measureReal_mono (h₂ := by finiteness)
    intro omega homega
    change epsilon <=
      dist
        (canonicalMarkedResonanceActionSample sign inverseSquareKineticTime
          (s.coupling j) (s.systemSize j) omega)
        (rho 0) at homega
    have htriangle := dist_triangle
      (canonicalMarkedResonanceActionSample sign inverseSquareKineticTime
        (s.coupling j) (s.systemSize j) omega)
      (canonicalMarkedResonanceActionLimit sign inverseSquareKineticTime
        (s.coupling j))
      (rho 0)
    have hhalf : epsilon / 2 <
        dist
          (canonicalMarkedResonanceActionSample sign inverseSquareKineticTime
            (s.coupling j) (s.systemSize j) omega)
          (canonicalMarkedResonanceActionLimit sign inverseSquareKineticTime
            (s.coupling j)) := by
      linarith
    exact hjcoupling.le.trans hhalf.le
  exact squeeze_zero'
    (Eventually.of_forall fun _j => measureReal_nonneg)
    hdomination
    (canonicalInverseSquareMarkedResonanceActionBadEvent_probability_jointLimit_tendsto_zero
      sign s)

/-- A positive on-shell density yields a nonzero marked resonant cluster along
inverse-square observation times, together with its exact signed
Radon--Nikodym collision representation. -/
theorem exists_positive_canonicalInverseSquareOnShellMarkedCluster_with_rn_of_collisionDensity
    (rho : Real -> Real)
    (hrho_meas : Measurable rho)
    (hrho_nonneg : forall x, 0 <= rho x)
    (hrho_int : Integrable rho)
    (hrho_zero : ContinuousAt rho 0)
    (hrho_pos : 0 < rho 0)
    (hdensity :
      (canonicalCollisionPerSiteMeasureLimit canonicalIIDMassPhaseEnsemble
        decayInteractionSign : Measure Real) =
      volume.withDensity (fun x => ENNReal.ofReal (rho x)))
    {coupling : Nat -> Real}
    (hcoupling_pos : forall j, 0 < coupling j)
    (hcoupling : Tendsto coupling atTop (nhdsWithin 0 (Ioi 0))) :
    exists target : FiniteMeasure (Fin 3 -> RankFrequencyMark),
      exists subsequence : Nat -> Nat,
        exists collision : ResonantThreeWaveMeasure RankFrequencyMark,
          StrictMono subsequence /\
          Tendsto
            (fun j =>
              canonicalRankFrequencyMarkedBroadenedPerSiteMeasureLimit
                canonicalIIDMassPhaseEnsemble decayInteractionSign
                (inverseSquareKineticTime (coupling (subsequence j)))
                (inverseSquareKineticTime_pos
                  (hcoupling_pos (subsequence j))))
            atTop (nhds target) /\
          collision.collisionMeasure = target /\
          collision.collisionMeasure.mass = Real.toNNReal (rho 0) /\
          collision.collisionMeasure ≠ 0 /\
          forall action : RankFrequencyMark -> Real,
            (collisionReferenceMeasure collision).withDensityᵥ
                (collisionVector collision action) =
              signedCollisionMeasure collision action := by
  let time : Nat -> Real := fun j => inverseSquareKineticTime (coupling j)
  have htime_pos : forall j, 0 < time j := fun j =>
    inverseSquareKineticTime_pos (hcoupling_pos j)
  have htime : Tendsto time atTop atTop := by
    simpa only [time] using
      inverseSquareKineticTime_comp_tendsto_atTop hcoupling
  obtain ⟨target, subsequence, collision, hmono, hweak, hcollision,
      hmass, hnonzero⟩ :=
    exists_positive_canonicalOnShellMarkedCluster_of_decayDensity
      canonicalIIDMassPhaseEnsemble rho hrho_meas hrho_nonneg hrho_int
      hrho_zero hrho_pos hdensity time htime_pos htime
  refine ⟨target, subsequence, collision, hmono, ?_, hcollision, hmass,
    hnonzero, ?_⟩
  · simpa only [time] using hweak
  · intro action
    exact withDensity_collisionVector_eq_signedCollisionMeasure collision action

end

end ArchonPhysics.CanonicalMarkedResonanceActionOnShellJointLimit
