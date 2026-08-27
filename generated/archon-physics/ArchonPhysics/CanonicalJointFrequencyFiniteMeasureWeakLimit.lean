import ArchonPhysics.CanonicalCollisionMeasureWeakLimit
import ArchonPhysics.CanonicalJointFrequencyMeasureWeakLimit
import ArchonPhysics.CanonicalJointFrequencyPerSiteMeasure

/-!
# Canonical joint-frequency finite-measure weak limit

The normalized joint-frequency measures already have a deterministic weak
limit.  Here we restore their total collision density.  Exact finite-volume
signed pushforward identities show that the joint mass has the same limit as
every scalar collision mass, independently of the sign pattern.  Combining
that mass convergence with normalized weak convergence gives convergence of
the genuine Euclidean per-site finite measures.

Every signed mismatch pushforward of the resulting finite-measure limit is
exactly the previously constructed scalar per-site collision-measure limit.
-/

open scoped Topology InnerProductSpace RealInnerProductSpace

namespace ArchonPhysics.CanonicalJointFrequencyFiniteMeasureWeakLimit

open ArchonPhysics
open ArchonPhysics.CanonicalCollisionMeasureWeakLimit
open ArchonPhysics.CanonicalCollisionPerSiteMeasureFourier
open ArchonPhysics.CanonicalJointFrequencyEuclideanBridge
open ArchonPhysics.CanonicalJointFrequencyMeasureWeakLimit
open ArchonPhysics.CanonicalJointFrequencyPerSiteMeasure
open ArchonPhysics.MeasurableOrderedModeCoupling.Harmonic
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.RandomMassPositiveCollisionData
open Filter MeasureTheory Topology

noncomputable section

variable {Omega : Type*} [MeasurableSpace Omega]

/-- The deterministic limiting collision density of the joint per-site
frequency measure.  The definition uses the all-plus scalar marginal; below
we prove that every sign pattern gives the same value. -/
def canonicalJointFrequencyPerSiteMassLimit
    (ensemble : IIDMassPhaseEnsemble Omega) : NNReal :=
  canonicalCollisionPerSiteMassLimit ensemble
    (fun _r => InteractionSign.plus)

/-- The masses of the joint per-site measures at `N = n + 3` converge almost
surely to the deterministic joint collision density. -/
theorem canonicalJointFrequencyPerSiteFiniteMeasure_mass_tendsto_ae
    (ensemble : IIDMassPhaseEnsemble Omega) :
    ∀ᵐ omega ∂ensemble.probability,
      Tendsto
        (fun n : Nat =>
          (canonicalJointFrequencyPerSiteFiniteMeasure
            ensemble (n + 1) omega).mass)
        atTop (nhds (canonicalJointFrequencyPerSiteMassLimit ensemble)) := by
  filter_upwards
    [canonicalCollisionPerSiteFiniteMeasure_mass_tendsto_ae ensemble
      (fun _r => InteractionSign.plus)] with omega hmass
  unfold canonicalJointFrequencyPerSiteMassLimit
  apply hmass.congr'
  exact Eventually.of_forall fun n =>
    (canonicalJointFrequencyPerSiteFiniteMeasure_mass_eq_collisionPerSite
      ensemble (fun _r => InteractionSign.plus) (n + 1) omega).symm

/-- The joint limiting density equals the limiting density of every signed
scalar collision marginal. -/
theorem canonicalJointFrequencyPerSiteMassLimit_eq_collision
    (ensemble : IIDMassPhaseEnsemble Omega)
    (sign : Fin 3 -> InteractionSign) :
    canonicalJointFrequencyPerSiteMassLimit ensemble =
      canonicalCollisionPerSiteMassLimit ensemble sign := by
  let _ : IsProbabilityMeasure ensemble.probability :=
    ⟨ensemble.probability_univ⟩
  have hevent : ∀ᵐ omega ∂ensemble.probability,
      Tendsto
          (fun n : Nat =>
            (canonicalJointFrequencyPerSiteFiniteMeasure
              ensemble (n + 1) omega).mass)
          atTop (nhds (canonicalJointFrequencyPerSiteMassLimit ensemble)) ∧
        Tendsto
          (fun n : Nat =>
            (canonicalCollisionPerSiteFiniteMeasure
              ensemble sign (n + 1) omega).mass)
          atTop
          (nhds (canonicalCollisionPerSiteMassLimit ensemble sign)) := by
    filter_upwards
      [canonicalJointFrequencyPerSiteFiniteMeasure_mass_tendsto_ae ensemble,
      canonicalCollisionPerSiteFiniteMeasure_mass_tendsto_ae ensemble sign] with
        omega hjoint hscalar
    exact ⟨hjoint, hscalar⟩
  obtain ⟨omega, hjoint, hscalar⟩ := hevent.exists
  have hscalarAsJoint : Tendsto
      (fun n : Nat =>
        (canonicalJointFrequencyPerSiteFiniteMeasure
          ensemble (n + 1) omega).mass)
      atTop (nhds (canonicalCollisionPerSiteMassLimit ensemble sign)) := by
    apply hscalar.congr'
    exact Eventually.of_forall fun n =>
      (canonicalJointFrequencyPerSiteFiniteMeasure_mass_eq_collisionPerSite
        ensemble sign (n + 1) omega).symm
  exact tendsto_nhds_unique hjoint hscalarAsJoint

/-- In particular, the deterministic scalar collision-mass limit is
independent of the chosen three-wave sign pattern. -/
theorem canonicalCollisionPerSiteMassLimit_sign_independent
    (ensemble : IIDMassPhaseEnsemble Omega)
    (sign₁ sign₂ : Fin 3 -> InteractionSign) :
    canonicalCollisionPerSiteMassLimit ensemble sign₁ =
      canonicalCollisionPerSiteMassLimit ensemble sign₂ := by
  rw [← canonicalJointFrequencyPerSiteMassLimit_eq_collision ensemble sign₁,
    ← canonicalJointFrequencyPerSiteMassLimit_eq_collision ensemble sign₂]

/-- The joint limiting collision density is strictly positive. -/
theorem canonicalJointFrequencyPerSiteMassLimit_pos
    (ensemble : IIDMassPhaseEnsemble Omega) :
    0 < canonicalJointFrequencyPerSiteMassLimit ensemble := by
  rw [canonicalJointFrequencyPerSiteMassLimit_eq_collision ensemble
    (fun _r => InteractionSign.plus)]
  exact canonicalCollisionPerSiteMassLimit_pos ensemble
    (fun _r => InteractionSign.plus)

/-- The deterministic Euclidean joint finite-measure limit: the common
collision-density limit times the deterministic joint probability shape. -/
def canonicalEuclideanJointFrequencyPerSiteMeasureLimit
    (ensemble : IIDMassPhaseEnsemble Omega) :
    FiniteMeasure (EuclideanSpace Real (Fin 3)) :=
  canonicalJointFrequencyPerSiteMassLimit ensemble •
    (canonicalJointFrequencyMeasureLimit ensemble).toFiniteMeasure

@[simp]
theorem canonicalEuclideanJointFrequencyPerSiteMeasureLimit_mass
    (ensemble : IIDMassPhaseEnsemble Omega) :
    (canonicalEuclideanJointFrequencyPerSiteMeasureLimit ensemble).mass =
      canonicalJointFrequencyPerSiteMassLimit ensemble := by
  unfold canonicalEuclideanJointFrequencyPerSiteMeasureLimit
    FiniteMeasure.mass
  rw [FiniteMeasure.smul_apply]
  simp

@[simp]
theorem canonicalEuclideanJointFrequencyPerSiteMeasureLimit_normalize
    (ensemble : IIDMassPhaseEnsemble Omega) :
    (canonicalEuclideanJointFrequencyPerSiteMeasureLimit ensemble).normalize =
      canonicalJointFrequencyMeasureLimit ensemble := by
  let target := canonicalEuclideanJointFrequencyPerSiteMeasureLimit ensemble
  have hmass : target.mass ≠ 0 := by
    rw [canonicalEuclideanJointFrequencyPerSiteMeasureLimit_mass]
    exact (canonicalJointFrequencyPerSiteMassLimit_pos ensemble).ne'
  have htarget : target ≠ 0 := target.mass_nonzero_iff.mp hmass
  apply ProbabilityMeasure.eq_of_forall_apply_eq
  intro s hs
  rw [target.normalize_eq_of_nonzero htarget]
  dsimp only [target]
  rw [canonicalEuclideanJointFrequencyPerSiteMeasureLimit_mass]
  unfold canonicalEuclideanJointFrequencyPerSiteMeasureLimit
  rw [FiniteMeasure.smul_apply]
  simp [(canonicalJointFrequencyPerSiteMassLimit_pos ensemble).ne']

/-- Euclidean transport preserves the almost-sure convergence of the joint
per-site masses. -/
theorem canonicalEuclideanJointFrequencyPerSiteFiniteMeasure_mass_tendsto_ae
    (ensemble : IIDMassPhaseEnsemble Omega) :
    ∀ᵐ omega ∂ensemble.probability,
      Tendsto
        (fun n : Nat =>
          (canonicalEuclideanJointFrequencyPerSiteFiniteMeasure
            ensemble (n + 1) omega).mass)
        atTop (nhds (canonicalJointFrequencyPerSiteMassLimit ensemble)) := by
  filter_upwards
    [canonicalJointFrequencyPerSiteFiniteMeasure_mass_tendsto_ae ensemble] with
      omega hmass
  apply hmass.congr'
  exact Eventually.of_forall fun n =>
    (canonicalEuclideanJointFrequencyPerSiteFiniteMeasure_mass_eq
      ensemble (n + 1) omega).symm

/-- The genuine Euclidean joint per-site finite measures at `N = n + 3`
converge almost surely to the deterministic unnormalized joint limit. -/
theorem canonicalEuclideanJointFrequencyPerSiteFiniteMeasure_tendsto_limit_ae
    (ensemble : IIDMassPhaseEnsemble Omega) :
    ∀ᵐ omega ∂ensemble.probability,
      Tendsto
        (fun n : Nat =>
          canonicalEuclideanJointFrequencyPerSiteFiniteMeasure
            ensemble (n + 1) omega)
        atTop
        (nhds
          (canonicalEuclideanJointFrequencyPerSiteMeasureLimit ensemble)) := by
  filter_upwards
    [canonicalJointFrequencyVolumes_simpleOrderedSpectrum_ae ensemble,
    canonicalEuclideanNormalizedJointFrequencyMeasure_tendsto_limit_ae
      ensemble,
    canonicalEuclideanJointFrequencyPerSiteFiniteMeasure_mass_tendsto_ae
      ensemble] with omega hsimple hnormalize hmass
  apply
    FiniteMeasure.tendsto_of_tendsto_normalize_testAgainstNN_of_tendsto_mass
  · rw [canonicalEuclideanJointFrequencyPerSiteMeasureLimit_normalize]
    apply hnormalize.congr'
    exact Eventually.of_forall fun n => by
      have hnonzero :
          (canonicalJointFrequencyPerSiteFiniteMeasure
            ensemble (n + 1) omega).mass ≠ 0 :=
        canonicalJointFrequencyPerSiteFiniteMeasure_mass_ne_zero
          ensemble (fun _r => InteractionSign.plus) (n + 1) omega
          (by omega) (by simpa [Nat.add_assoc] using hsimple n)
      exact canonicalEuclideanNormalizedJointFrequencyMeasure_eq_finite_normalize
        ensemble (n + 1) omega hnonzero
  · simpa using hmass

/-- Every signed mismatch pushforward of the deterministic Euclidean joint
finite-measure limit is exactly the corresponding deterministic scalar
per-site collision-measure limit. -/
theorem map_canonicalEuclideanJointFrequencyPerSiteMeasureLimit_eq_collision
    (ensemble : IIDMassPhaseEnsemble Omega)
    (sign : Fin 3 -> InteractionSign) :
    (canonicalEuclideanJointFrequencyPerSiteMeasureLimit ensemble).map
        (euclideanFrequencyTripleMismatch sign) =
      canonicalCollisionPerSiteMeasureLimit ensemble sign := by
  let _ : IsProbabilityMeasure ensemble.probability :=
    ⟨ensemble.probability_univ⟩
  have hevent : ∀ᵐ omega ∂ensemble.probability,
      Tendsto
          (fun n : Nat =>
            canonicalEuclideanJointFrequencyPerSiteFiniteMeasure
              ensemble (n + 1) omega)
          atTop
          (nhds
            (canonicalEuclideanJointFrequencyPerSiteMeasureLimit ensemble)) ∧
        Tendsto
          (fun n : Nat =>
            canonicalCollisionPerSiteFiniteMeasure
              ensemble sign (n + 1) omega)
          atTop
          (nhds (canonicalCollisionPerSiteMeasureLimit ensemble sign)) := by
    filter_upwards
      [canonicalEuclideanJointFrequencyPerSiteFiniteMeasure_tendsto_limit_ae
        ensemble,
      canonicalCollisionPerSiteFiniteMeasure_tendsto_limit_ae ensemble sign] with
        omega hjoint hscalar
    exact ⟨hjoint, hscalar⟩
  obtain ⟨omega, hjoint, hscalar⟩ := hevent.exists
  have hmapped :=
    FiniteMeasure.tendsto_map_of_tendsto_of_continuous
      (fun n : Nat =>
        canonicalEuclideanJointFrequencyPerSiteFiniteMeasure
          ensemble (n + 1) omega)
      (canonicalEuclideanJointFrequencyPerSiteMeasureLimit ensemble)
      hjoint (continuous_euclideanFrequencyTripleMismatch sign)
  have hmappedScalar : Tendsto
      (fun n : Nat =>
        (canonicalEuclideanJointFrequencyPerSiteFiniteMeasure
          ensemble (n + 1) omega).map
            (euclideanFrequencyTripleMismatch sign))
      atTop
      (nhds (canonicalCollisionPerSiteMeasureLimit ensemble sign)) := by
    apply hscalar.congr'
    exact Eventually.of_forall fun n =>
      (map_canonicalEuclideanJointFrequencyPerSiteFiniteMeasure_eq_collisionPerSite
        ensemble sign (n + 1) omega).symm
  exact tendsto_nhds_unique hmapped hmappedScalar

end

end ArchonPhysics.CanonicalJointFrequencyFiniteMeasureWeakLimit
