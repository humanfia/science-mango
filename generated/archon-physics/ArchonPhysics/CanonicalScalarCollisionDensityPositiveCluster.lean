import ArchonPhysics.CanonicalBroadenedMassTwoScaleDiagonalization
import ArchonPhysics.CanonicalOnShellMarkedClusterPositiveExistence
import ArchonPhysics.CanonicalRankFrequencyMarkedBroadenedMassBounds

/-!
# Scalar collision densities produce positive canonical on-shell clusters

This module closes the normalization-sensitive bridge from a Lebesgue density
for the *unnormalized per-site* scalar collision measure to a nonzero resonant
marked cluster.  The density assumptions are explicit propositions: no density
existence or positivity input is hidden in a definition or an instance.

The same bridge also supplies the deterministic coefficient limit required by
the canonical two-scale probability diagonalization theorem.
-/

open scoped ENNReal Topology

namespace ArchonPhysics.CanonicalScalarCollisionDensityPositiveCluster

open ArchonPhysics
open ArchonPhysics.CanonicalBroadenedMassTwoScaleDiagonalization
open ArchonPhysics.CanonicalCollisionMeasureWeakLimit
open ArchonPhysics.CanonicalOnShellMarkedClusterPositiveExistence
open ArchonPhysics.CanonicalRankFrequencyMarkedBroadenedLimit
open ArchonPhysics.CanonicalRankFrequencyMarkedBroadenedMarginal
open ArchonPhysics.CanonicalRankFrequencyMarkedBroadenedMassBounds
open ArchonPhysics.CanonicalRankFrequencyMarkedMeasure
open ArchonPhysics.RandomMassThreeWaveCollisionNetwork
open Filter MeasureTheory Topology

noncomputable section

variable {Omega : Type*} [MeasurableSpace Omega]

/-- If the unnormalized canonical scalar collision per-site finite measure in
the decay channel has Lebesgue density `rho`, its scalar broadened masses
converge to the exact density value at zero.  The target is stated in
`NNReal`, the native type of `FiniteMeasure.mass`; no probability
normalization is inserted. -/
theorem canonicalBroadenedCollisionPerSiteMeasureLimit_mass_tendsto_of_decayDensity
    (ensemble : IIDMassPhaseEnsemble Omega)
    (rho : Real -> Real)
    (hrho_meas : Measurable rho)
    (hrho_nonneg : forall x, 0 <= rho x)
    (hrho_int : Integrable rho)
    (hrho_zero : ContinuousAt rho 0)
    (hrho_pos : 0 < rho 0)
    (hdensity :
      (canonicalCollisionPerSiteMeasureLimit
        ensemble decayInteractionSign : Measure Real) =
      volume.withDensity (fun x => ENNReal.ofReal (rho x)))
    (time : Nat -> Real)
    (htime_pos : forall n, 0 < time n)
    (htime : Tendsto time atTop atTop) :
    Tendsto
      (fun n =>
        (canonicalBroadenedCollisionPerSiteMeasureLimit
          ensemble decayInteractionSign (time n) (htime_pos n)).mass)
      atTop (nhds (Real.toNNReal (rho 0))) := by
  have hreal : Tendsto
      (fun n =>
        ((canonicalBroadenedCollisionPerSiteMeasureLimit
          ensemble decayInteractionSign (time n) (htime_pos n)).mass : Real))
      atTop (nhds (rho 0)) := by
    simpa only [canonicalBroadenedCollisionPerSiteMeasureLimit] using
      (broadenedResonanceMeasure_id_mass_tendsto_of_density
        (canonicalCollisionPerSiteMeasureLimit
          ensemble decayInteractionSign)
        rho hrho_meas hrho_nonneg hrho_int hrho_zero hdensity
        time htime_pos htime)
  apply NNReal.tendsto_coe.mp
  simpa [Real.coe_toNNReal (rho 0) hrho_pos.le] using hreal

/-- A strictly positive density at zero yields a subsequential canonical
on-shell marked limit whose associated resonant three-wave collision measure
has exactly the per-site mass `rho 0` and is nonzero. -/
theorem exists_positive_canonicalOnShellMarkedCluster_of_decayDensity
    (ensemble : IIDMassPhaseEnsemble Omega)
    (rho : Real -> Real)
    (hrho_meas : Measurable rho)
    (hrho_nonneg : forall x, 0 <= rho x)
    (hrho_int : Integrable rho)
    (hrho_zero : ContinuousAt rho 0)
    (hrho_pos : 0 < rho 0)
    (hdensity :
      (canonicalCollisionPerSiteMeasureLimit
        ensemble decayInteractionSign : Measure Real) =
      volume.withDensity (fun x => ENNReal.ofReal (rho x)))
    (time : Nat -> Real)
    (htime_pos : forall n, 0 < time n)
    (htime : Tendsto time atTop atTop) :
    exists target : FiniteMeasure (Fin 3 -> RankFrequencyMark),
      exists subsequence : Nat -> Nat,
        exists collision : ResonantThreeWaveMeasure RankFrequencyMark,
          StrictMono subsequence /\
          Tendsto
            (fun j =>
              canonicalRankFrequencyMarkedBroadenedPerSiteMeasureLimit
                ensemble decayInteractionSign (time (subsequence j))
                  (htime_pos (subsequence j)))
            atTop (nhds target) /\
          collision.collisionMeasure = target /\
          collision.collisionMeasure.mass = Real.toNNReal (rho 0) /\
          collision.collisionMeasure ≠ 0 := by
  exact
    exists_positive_canonicalOnShellMarkedCluster_of_scalarMass_tendsto
      ensemble time htime_pos htime (Real.toNNReal (rho 0))
      (Real.toNNReal_pos.mpr hrho_pos)
      (canonicalBroadenedCollisionPerSiteMeasureLimit_mass_tendsto_of_decayDensity
        ensemble rho hrho_meas hrho_nonneg hrho_int hrho_zero hrho_pos
        hdensity time htime_pos htime)

/-- Under the density hypothesis for the canonical iid ensemble, the
deterministic integer-time scalar coefficients converge to `rho 0`. -/
theorem canonicalBroadenedScalarCoefficient_decay_tendsto_of_density
    (rho : Real -> Real)
    (hrho_meas : Measurable rho)
    (hrho_nonneg : forall x, 0 <= rho x)
    (hrho_int : Integrable rho)
    (hrho_zero : ContinuousAt rho 0)
    (hrho_pos : 0 < rho 0)
    (hdensity :
      (canonicalCollisionPerSiteMeasureLimit
        canonicalIIDMassPhaseEnsemble decayInteractionSign : Measure Real) =
      volume.withDensity (fun x => ENNReal.ofReal (rho x))) :
    Tendsto
      (canonicalBroadenedScalarCoefficient decayInteractionSign)
      atTop (nhds (rho 0)) := by
  have htime : Tendsto
      (fun n : Nat => ((n + 1 : Nat) : Real)) atTop atTop :=
    (tendsto_natCast_atTop_atTop (R := Real)).comp
      (tendsto_add_atTop_nat 1)
  have hmass :=
    canonicalBroadenedCollisionPerSiteMeasureLimit_mass_tendsto_of_decayDensity
      canonicalIIDMassPhaseEnsemble rho hrho_meas hrho_nonneg hrho_int
      hrho_zero hrho_pos hdensity
      (fun n : Nat => ((n + 1 : Nat) : Real)) (fun _ => by positivity) htime
  have hreal := (NNReal.continuous_coe.tendsto _).comp hmass
  unfold canonicalBroadenedScalarCoefficient
  simpa [Function.comp_def,
    Real.coe_toNNReal (rho 0) hrho_pos.le] using hreal

/-- The density input discharges the sole analytic coefficient premise in the
canonical two-scale theorem.  Hence every integer-time/volume path above the
deterministic cutoff has broadened marked per-site mass converging in
probability to the same positive on-shell value `rho 0`. -/
theorem canonicalBroadenedMarkedPerSiteMass_tendstoInMeasure_along_cutoff_of_decayDensity
    (rho : Real -> Real)
    (hrho_meas : Measurable rho)
    (hrho_nonneg : forall x, 0 <= rho x)
    (hrho_int : Integrable rho)
    (hrho_zero : ContinuousAt rho 0)
    (hrho_pos : 0 < rho 0)
    (hdensity :
      (canonicalCollisionPerSiteMeasureLimit
        canonicalIIDMassPhaseEnsemble decayInteractionSign : Measure Real) =
      volume.withDensity (fun x => ENNReal.ofReal (rho x)))
    (timeIndex sizeIndex : Nat -> Nat)
    (htime : Tendsto timeIndex atTop atTop)
    (hcutoff : ∀ᶠ j in atTop,
      canonicalBroadenedMarkedPerSiteMassSizeCutoff decayInteractionSign
          (timeIndex j) <= sizeIndex j) :
    TendstoInMeasure RandomEnsemble.canonicalLaw
      (fun j omega => canonicalBroadenedMarkedPerSiteMassSample
        decayInteractionSign (timeIndex j) (sizeIndex j) omega)
      atTop (fun _omega => rho 0) := by
  exact
    canonicalBroadenedMarkedPerSiteMass_tendstoInMeasure_along_cutoff
      decayInteractionSign (rho 0)
      (canonicalBroadenedScalarCoefficient_decay_tendsto_of_density
        rho hrho_meas hrho_nonneg hrho_int hrho_zero hrho_pos hdensity)
      timeIndex sizeIndex htime hcutoff

end

end ArchonPhysics.CanonicalScalarCollisionDensityPositiveCluster
