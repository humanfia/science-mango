import ArchonPhysics.CanonicalIIDCoerciveUniformBlockMomentBound
import ArchonPhysics.JointMassEnergyCompactness

/-!
# Explicit-energy uniform bounds for canonical iid block moments

This module avoids the noncomputable `cutoffRadius` when bounding the actual
canonical trajectory.  Energy conservation on the matching reduced
trajectory and `physicalEnergySublevel_norm_le` give a physical radius from
the explicit initial-energy ceiling.  A finite-dimensional sup-to-Euclidean
comparison then bounds the Hilbert position and momentum, hence every
nontranslation signed interaction amplitude and every fixed Bochner block
moment.

For couplings satisfying `|g| <= G`, all constants depend only on
`N`, `kappa`, `beta`, `G`, and a uniform mass-gauge Poincare constant.  Since
every convergent real sequence has bounded range, a coupling sequence tending
to zero automatically supplies the `hmoment` premise used by ordered-cluster
factorization convergence.  No bound on the chosen cutoff radius, RPA closure,
or kinetic decay is asserted.
-/

namespace ArchonPhysics.CanonicalIIDCoerciveExplicitEnergyBlockMomentBound

open scoped BigOperators Topology

open Filter
open ArchonPhysics
open ArchonPhysics.CanonicalIIDCoerciveActualExpectationAdapter
open ArchonPhysics.CanonicalIIDCoerciveActualExpectationClosure
open ArchonPhysics.CanonicalIIDCoerciveActualExpectationCompleted
open ArchonPhysics.CanonicalIIDCoerciveActualExpectationTheorem
open ArchonPhysics.CanonicalIIDCoerciveContinuousMomentFrontier
open ArchonPhysics.CanonicalIIDCoerciveSignedModalHierarchy
open ArchonPhysics.CanonicalIIDCoerciveSignedModalObservableBridge
open ArchonPhysics.CanonicalIIDCoerciveUniformBlockMomentBound
open ArchonPhysics.CanonicalRandomMassPhaseGlobalFlow
open ArchonPhysics.CoerciveHamiltonianContinuation
open ArchonPhysics.CoerciveHamiltonianPhyslib
open ArchonPhysics.FinitePhaseMonomials
open ArchonPhysics.GlobalReducedParametricFlowAdapter
open ArchonPhysics.MeasurableOrderedEigenframe
open ArchonPhysics.MeasurableOrderedModeCoupling.Harmonic
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.MassWeightedHamiltonianDynamics
open ArchonPhysics.OrderedSingleModeProjector
open ArchonPhysics.OrderedTranslationLastMode
open ArchonPhysics.PhaseRenormalization
open ArchonPhysics.RandomMassInitialEnergyBound
open ArchonPhysics.RandomMassMeasurableHarmonicEnergy
open ArchonPhysics.RandomMassMeasurableOrderedEigenframe
open ArchonPhysics.RandomMassOrderedProjectorBridge
open ArchonPhysics.RandomMassPositiveCollisionData
open ArchonPhysics.RandomMassReducedPhaseInitialData
open ArchonPhysics.ReducedModeTransform
open ArchonPhysics.UniformMassGaugeCoercivity
open MeasureTheory
open Set

noncomputable section

variable {N : Nat} [NeZero N]

/-- A coupling-independent upper bound for the initial energy whenever
`|g| <= G`. -/
def canonicalCouplingEnergyCeiling
    (kappa beta G : Real) : Real :=
  1 + 4 * (|kappa| * G / 3) + beta * G ^ 2

/-- The explicit radius supplied by the physical energy-sublevel theorem. -/
def canonicalExplicitPhysicalRadius
    (C kappa beta G : Real) : Real :=
  max
    (C * (canonicalCouplingEnergyCeiling kappa beta G /
      CoerciveCubicPotential.coercivityConstant kappa beta + 1))
    (2 * (6 / 5 : Real) * canonicalCouplingEnergyCeiling kappa beta G + 1)

/-- A coarse Euclidean radius obtained from the physical sup-norm radius. -/
def canonicalExplicitHilbertRadius
    (N : Nat) (C kappa beta G : Real) : Real :=
  (N : Real) * canonicalExplicitPhysicalRadius C kappa beta G ^ 2 + 1

/-- Explicit signed-amplitude envelope obtained from the Euclidean position
and momentum radius. -/
def canonicalExplicitSignedAmplitudeEnvelope
    (N : Nat) (C kappa beta G : Real) : Real :=
  let B := 2 * canonicalExplicitHilbertRadius N C kappa beta G
  (Real.sqrt 5 * B + B) * canonicalPositiveFrequencyNormalizationEnvelope N

theorem initialEnergyUpperBound_le_canonicalCouplingEnergyCeiling
    {kappa beta g G : Real} (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (_hG : 0 <= G) (hg : |g| <= G) :
    initialEnergyUpperBound kappa beta g <=
      canonicalCouplingEnergyCeiling kappa beta G := by
  have hcubic : |kappa * g / 3| <= |kappa| * G / 3 := by
    rw [abs_div, abs_mul]
    norm_num
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hg (abs_nonneg kappa)) (by norm_num)
  have hgLower : -G <= g := by
    exact (abs_le.mp hg).1
  have hgUpper : g <= G := by
    exact (abs_le.mp hg).2
  have hsq : g ^ 2 <= G ^ 2 := by
    nlinarith
  have hbetaNonneg : 0 <= beta :=
    (CoerciveCubicPotential.beta_pos hbeta).le
  have hquartic : beta * g ^ 2 <= beta * G ^ 2 :=
    mul_le_mul_of_nonneg_left hsq hbetaNonneg
  rw [initialEnergyUpperBound_spec]
  unfold canonicalCouplingEnergyCeiling
  linarith

theorem canonicalCouplingEnergyCeiling_nonneg
    {kappa beta G : Real} (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (hG : 0 <= G) :
    0 <= canonicalCouplingEnergyCeiling kappa beta G := by
  unfold canonicalCouplingEnergyCeiling
  have hbetaNonneg : 0 <= beta :=
    (CoerciveCubicPotential.beta_pos hbeta).le
  positivity

theorem canonicalExplicitPhysicalRadius_nonneg
    {C kappa beta G : Real} (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (hG : 0 <= G) :
    0 <= canonicalExplicitPhysicalRadius C kappa beta G := by
  have hH := canonicalCouplingEnergyCeiling_nonneg hbeta hG
  unfold canonicalExplicitPhysicalRadius
  exact (add_nonneg
    (mul_nonneg
      (mul_nonneg (by norm_num) (by norm_num : (0 : Real) <= 6 / 5)) hH)
    zero_le_one).trans (le_max_right _ _)

omit [NeZero N] in
theorem canonicalExplicitHilbertRadius_nonneg
    (C kappa beta G : Real) :
    0 <= canonicalExplicitHilbertRadius N C kappa beta G := by
  unfold canonicalExplicitHilbertRadius
  exact add_nonneg
    (mul_nonneg (Nat.cast_nonneg N)
      (sq_nonneg (canonicalExplicitPhysicalRadius C kappa beta G)))
    zero_le_one

theorem canonicalExplicitSignedAmplitudeEnvelope_nonneg
    (C kappa beta G : Real) :
    0 <= canonicalExplicitSignedAmplitudeEnvelope N C kappa beta G := by
  unfold canonicalExplicitSignedAmplitudeEnvelope
  have hR := canonicalExplicitHilbertRadius_nonneg (N := N) C kappa beta G
  exact mul_nonneg
    (add_nonneg
      (mul_nonneg (Real.sqrt_nonneg 5) (mul_nonneg (by norm_num) hR))
      (mul_nonneg (by norm_num) hR))
    canonicalPositiveFrequencyNormalizationEnvelope_nonneg

/-- A physical configuration sup-norm bound gives a coarse Euclidean bound
with no compactness choice. -/
theorem norm_hilbertConfiguration_le_card_mul_sq_add_one
    (x : HilbertConfiguration N) {R : Real}
    (hx : ‖asConfiguration x‖ <= R) :
    ‖x‖ <= (N : Real) * R ^ 2 + 1 := by
  have hcoordinate (i : Lattice.Site N) : |x i| <= R := by
    calc
      |x i| = ‖asConfiguration x i‖ := by
        simp [asConfiguration, Real.norm_eq_abs]
      _ <= ‖asConfiguration x‖ := norm_le_pi_norm _ i
      _ <= R := hx
  have hsquare (i : Lattice.Site N) : x i ^ 2 <= R ^ 2 := by
    simpa only [sq_abs] using
      pow_le_pow_left₀ (abs_nonneg (x i)) (hcoordinate i) 2
  have hsum : (∑ i : Lattice.Site N, x i ^ 2) <=
      (N : Real) * R ^ 2 := by
    calc
      (∑ i : Lattice.Site N, x i ^ 2) <=
          ∑ _i : Lattice.Site N, R ^ 2 :=
        Finset.sum_le_sum fun i _hi => hsquare i
      _ = (N : Real) * R ^ 2 := by simp
  have hnormSq : ‖x‖ ^ 2 <= (N : Real) * R ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    exact hsum
  calc
    ‖x‖ <= ‖x‖ ^ 2 + 1 := by
      nlinarith [sq_nonneg (‖x‖ - (1 / 2 : Real))]
    _ <= (N : Real) * R ^ 2 + 1 := by linarith

/-- Energy conservation and the explicit physical sublevel estimate bound the
actual canonical Hilbert position and momentum at every time on each simple
sample.  The bound is independent of the particular coupling `g` inside
`[-G,G]`. -/
theorem norm_canonicalFlowPosition_and_momentum_le_explicitEnergy_of_simple
    (hN : 3 <= N) {a : Real} (ha0 : 0 <= a) (ha1 : a <= 1 / 4)
    (C : Real) (hC : 0 <= C)
    (hPoincare : forall (m : Lattice.PositiveMassConfig N)
      (q : Lattice.Configuration N),
      (∑ i, m.mass i * q i = 0) ->
        ‖q‖ <= C * ‖Lattice.forwardDifference q‖)
    (kappa beta g G : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (hG : 0 <= G) (hg : |g| <= G)
    (omega : CanonicalSample)
    (hsimple : SimpleOrderedSpectrum
      (harmonicHermitian (canonicalMass (N := N) omega)))
    (time : Real) :
    ‖canonicalFlowPosition (N := N)
        kappa beta g hbeta a (omega, time)‖ <=
        canonicalExplicitHilbertRadius N C kappa beta G ∧
      ‖canonicalFlowMomentum (N := N)
        kappa beta g hbeta a (omega, time)‖ <=
        canonicalExplicitHilbertRadius N C kappa beta G := by
  rcases canonicalRandomMassPhaseTrajectory_matches_reduced_of_simple
      canonicalIIDMassPhaseEnsemble hN ha0 ha1 kappa beta g hbeta omega
        hsimple with ⟨z, _hz0, _hz, hmatch, henergy⟩
  have hinitial : reducedHamiltonian (canonicalMass (N := N) omega)
      kappa beta g
      (reducedInitialStateOfSimple canonicalIIDMassPhaseEnsemble a omega
        hsimple) <= initialEnergyUpperBound kappa beta g := by
    simpa [canonicalMass] using
      reducedHamiltonian_reducedInitialStateOfSimple_le
        canonicalIIDMassPhaseEnsemble hN ha0 ha1 hbeta g omega hsimple
  have henergyTime : reducedHamiltonian (canonicalMass (N := N) omega)
      kappa beta g (z time) <= canonicalCouplingEnergyCeiling kappa beta G := by
    exact (henergy time).le.trans
      (hinitial.trans
        (initialEnergyUpperBound_le_canonicalCouplingEnergyCeiling
          hbeta hG hg))
  let physical : PhysicalPhaseSpace N :=
    (asConfiguration ((z time).1 : HilbertConfiguration N),
      asConfiguration ((z time).2 : HilbertConfiguration N))
  have hphysical : physical ∈ physicalEnergySublevel
      (canonicalMass (N := N) omega) kappa beta g
        (canonicalCouplingEnergyCeiling kappa beta G) := by
    refine ⟨?_, ?_⟩
    · simpa [physical, asConfiguration] using
        (mem_reducedPositionSpace_iff
          (canonicalMass (N := N) omega)
          ((z time).1 : HilbertConfiguration N)).1 (z time).1.property
    · simpa [physical, reducedHamiltonian] using henergyTime
  have hphysicalNorm := physicalEnergySublevel_norm_le hC hPoincare hbeta
    (canonicalMass (N := N) omega) (canonicalMass_upper omega) hphysical
  have hphysicalNorm' : ‖physical‖ <=
      canonicalExplicitPhysicalRadius C kappa beta G := by
    simpa [canonicalExplicitPhysicalRadius] using hphysicalNorm
  have hqConfiguration :
      ‖asConfiguration ((z time).1 : HilbertConfiguration N)‖ <=
        canonicalExplicitPhysicalRadius C kappa beta G := by
    exact (le_max_left _ _).trans
      (by simpa [physical, Prod.norm_def] using hphysicalNorm')
  have hpConfiguration :
      ‖asConfiguration ((z time).2 : HilbertConfiguration N)‖ <=
        canonicalExplicitPhysicalRadius C kappa beta G := by
    exact (le_max_right _ _).trans
      (by simpa [physical, Prod.norm_def] using hphysicalNorm')
  have hqHilbert := norm_hilbertConfiguration_le_card_mul_sq_add_one
    ((z time).1 : HilbertConfiguration N) hqConfiguration
  have hpHilbert := norm_hilbertConfiguration_le_card_mul_sq_add_one
    ((z time).2 : HilbertConfiguration N) hpConfiguration
  have hq : canonicalFlowPosition (N := N) kappa beta g hbeta a
      (omega, time) = ((z time).1 : HilbertConfiguration N) := by
    simpa [canonicalFlowPosition, embedReducedPoint] using
      congrArg (fun x => x.2.1) (hmatch time)
  have hp : canonicalFlowMomentum (N := N) kappa beta g hbeta a
      (omega, time) = ((z time).2 : HilbertConfiguration N) := by
    simpa [canonicalFlowMomentum, embedReducedPoint] using
      congrArg (fun x => x.2.2) (hmatch time)
  simpa [canonicalExplicitHilbertRadius, hq, hp] using And.intro hqHilbert hpHilbert

/-- The explicit energy radius bounds one signed nontranslation interaction
amplitude, uniformly over `|g| <= G`. -/
theorem norm_canonicalSignedInteractionAmplitude_le_explicitEnergy_of_simple
    (hN : 3 <= N) {a : Real} (ha0 : 0 <= a) (ha1 : a <= 1 / 4)
    (C : Real) (hC : 0 <= C)
    (hPoincare : forall (m : Lattice.PositiveMassConfig N)
      (q : Lattice.Configuration N),
      (∑ i, m.mass i * q i = 0) ->
        ‖q‖ <= C * ‖Lattice.forwardDifference q‖)
    (kappa beta g G : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (hG : 0 <= G) (hg : |g| <= G)
    (omega : CanonicalSample)
    (hsimple : SimpleOrderedSpectrum
      (harmonicHermitian (canonicalMass (N := N) omega)))
    (entry : PhaseSign × OrderedModeIndex N)
    (hentry : entry.2 ≠ lastOrderedIndex (ι := Lattice.Site N))
    (time : Real) :
    ‖canonicalSignedInteractionAmplitude (N := N)
        kappa beta g hbeta a entry (omega, time)‖ <=
      canonicalExplicitSignedAmplitudeEnvelope N C kappa beta G := by
  let R := canonicalExplicitHilbertRadius N C kappa beta G
  let B := 2 * R
  have hflow :=
    norm_canonicalFlowPosition_and_momentum_le_explicitEnergy_of_simple
      hN ha0 ha1 C hC hPoincare kappa beta g G hbeta hG hg omega
        hsimple time
  have hQproject := abs_orderedSignedCoordinate_le_norm
    (canonicalMass (N := N) omega) hsimple entry.2
    (sqrtMassTransform (canonicalMass (N := N) omega)
      (canonicalFlowPosition (N := N)
        kappa beta g hbeta a (omega, time)))
  have hQweight := norm_sqrtMassTransform_le_two_mul
    (canonicalMass (N := N) omega) (canonicalMass_upper omega)
    (canonicalFlowPosition (N := N)
      kappa beta g hbeta a (omega, time))
  have hQ : |canonicalOrderedModalPosition (N := N)
      kappa beta g hbeta a entry.2 (omega, time)| <= B := by
    have hbound : ‖sqrtMassTransform (canonicalMass (N := N) omega)
        (canonicalFlowPosition (N := N)
          kappa beta g hbeta a (omega, time))‖ <= B := by
      exact hQweight.trans (by dsimp [B, R]; gcongr; exact hflow.1)
    simpa [canonicalOrderedModalPosition, orderedSignedCoordinate,
      orderedEigenvectorSample, harmonicHermitianSample, harmonicHermitian,
      canonicalMass, massWeightedPositionSample] using hQproject.trans hbound
  have hPproject := abs_orderedSignedCoordinate_le_norm
    (canonicalMass (N := N) omega) hsimple entry.2
    (inverseSqrtMassTransform (canonicalMass (N := N) omega)
      (canonicalFlowMomentum (N := N)
        kappa beta g hbeta a (omega, time)))
  have hPweight := norm_inverseSqrtMassTransform_le_two_mul
    (canonicalMass (N := N) omega) (canonicalMass_lower omega)
    (canonicalFlowMomentum (N := N)
      kappa beta g hbeta a (omega, time))
  have hP : |canonicalOrderedModalMomentum (N := N)
      kappa beta g hbeta a entry.2 (omega, time)| <= B := by
    have hbound : ‖inverseSqrtMassTransform (canonicalMass (N := N) omega)
        (canonicalFlowMomentum (N := N)
          kappa beta g hbeta a (omega, time))‖ <= B := by
      exact hPweight.trans (by dsimp [B, R]; gcongr; exact hflow.2)
    simpa [canonicalOrderedModalMomentum, orderedSignedCoordinate,
      orderedEigenvectorSample, harmonicHermitianSample, harmonicHermitian,
      canonicalMass, massWeightedMomentumSample] using hPproject.trans hbound
  have hB : 0 <= B := by
    dsimp [B, R]
    exact mul_nonneg (by norm_num)
      (canonicalExplicitHilbertRadius_nonneg (N := N) C kappa beta G)
  have hmode := norm_complexModeAmplitude_le
    (canonicalOrderedFrequency_pos entry.2 hentry omega)
    (canonicalOrderedFrequency_le_sqrt_five entry.2 omega)
    (Real.sqrt_nonneg 5) hQ hP hB
    (inv_sqrt_two_mul_canonicalOrderedFrequency_le_envelope
      entry.2 hentry omega)
    canonicalPositiveFrequencyNormalizationEnvelope_nonneg
  rw [canonicalSignedInteractionAmplitude, norm_phaseSignActComplex,
    canonicalInteractionAmplitude, norm_phaseRenormalize]
  simpa [canonicalExplicitSignedAmplitudeEnvelope, B, R] using hmode

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- Explicit-energy bound for a canonical continuous-law block moment,
uniform over every coupling in `[-G,G]`. -/
theorem norm_canonicalSignedBlockBochnerIntegral_le_explicitEnergyEnvelope
    (hN : 3 <= N) {a : Real} (ha0 : 0 <= a) (ha1 : a <= 1 / 4)
    (C : Real) (hC : 0 <= C)
    (hPoincare : forall (m : Lattice.PositiveMassConfig N)
      (q : Lattice.Configuration N),
      (∑ i, m.mass i * q i = 0) ->
        ‖q‖ <= C * ‖Lattice.forwardDifference q‖)
    (kappa beta g G : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (hG : 0 <= G) (hg : |g| <= G)
    (entry : I -> PhaseSign × OrderedModeIndex N)
    (hpositive : forall i, (entry i).2 ≠
      lastOrderedIndex (ι := Lattice.Site N))
    (block : Finset I) (time : Real) :
    ‖canonicalSignedBlockBochnerIntegral (N := N)
        kappa beta g hbeta a entry block time‖ <=
      canonicalSignedBlockEnvelope
        (canonicalExplicitSignedAmplitudeEnvelope N C kappa beta G) block := by
  let _ : IsFiniteMeasure canonicalIIDMassPhaseEnsemble.probability :=
    ⟨by rw [canonicalIIDMassPhaseEnsemble.probability_univ]; norm_num⟩
  have hsimpleAE := simpleOrderedSpectrum_ae
    (N := N) canonicalIIDMassPhaseEnsemble (show 2 <= N by omega)
  have h := norm_integral_le_of_norm_le_const
    (μ := canonicalIIDMassPhaseEnsemble.probability)
    (f := fun omega : CanonicalSample =>
      canonicalSignedBlockObservable (N := N)
        kappa beta g hbeta a entry block (omega, time))
    (C := canonicalSignedBlockEnvelope
      (canonicalExplicitSignedAmplitudeEnvelope N C kappa beta G) block)
    (by
      filter_upwards [hsimpleAE] with omega hsimple
      unfold canonicalSignedBlockObservable
      exact norm_finite_signed_block_le
        (fun i => canonicalSignedInteractionAmplitude (N := N)
          kappa beta g hbeta a (entry i) (omega, time)) block
        (canonicalExplicitSignedAmplitudeEnvelope_nonneg
          (N := N) C kappa beta G)
        (fun i hi =>
          norm_canonicalSignedInteractionAmplitude_le_explicitEnergy_of_simple
            hN ha0 ha1 C hC hPoincare kappa beta g G hbeta hG hg omega
              hsimple (entry i) (hpositive i) time))
  rw [Measure.real, canonicalIIDMassPhaseEnsemble.probability_univ] at h
  norm_num at h
  simpa [canonicalSignedBlockBochnerIntegral] using h

/-- A bounded coupling sequence has one explicit uniform witness for every
fixed block. -/
theorem exists_systemUniform_canonicalSignedBlockBochnerIntegral_bound_of_couplingBound
    (hN : 3 <= N) {a : Real} (ha0 : 0 <= a) (ha1 : a <= 1 / 4)
    (C : Real) (hC : 0 <= C)
    (hPoincare : forall (m : Lattice.PositiveMassConfig N)
      (q : Lattice.Configuration N),
      (∑ i, m.mass i * q i = 0) ->
        ‖q‖ <= C * ‖Lattice.forwardDifference q‖)
    (kappa beta : Real) (g : Nat -> Real)
    (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (G : Real) (hG : 0 <= G) (hg : forall scale, |g scale| <= G)
    (entry : I -> PhaseSign × OrderedModeIndex N)
    (hpositive : forall i, (entry i).2 ≠
      lastOrderedIndex (ι := Lattice.Site N))
    (block : Finset I) (time : Nat -> Real) :
    exists bound : Real, 0 <= bound ∧ forall scale,
      ‖canonicalSignedBlockBochnerIntegral (N := N)
          kappa beta (g scale) hbeta a entry block (time scale)‖ <= bound := by
  refine ⟨canonicalSignedBlockEnvelope
    (canonicalExplicitSignedAmplitudeEnvelope N C kappa beta G) block, ?_, ?_⟩
  · unfold canonicalSignedBlockEnvelope
    exact pow_nonneg (by
      linarith [canonicalExplicitSignedAmplitudeEnvelope_nonneg
        (N := N) C kappa beta G]) block.card
  · intro scale
    exact norm_canonicalSignedBlockBochnerIntegral_le_explicitEnergyEnvelope
      hN ha0 ha1 C hC hPoincare kappa beta (g scale) G hbeta hG
        (hg scale) entry hpositive block (time scale)

/-- Every convergent real coupling sequence admits a global absolute bound. -/
theorem exists_abs_coupling_bound_of_tendsto_zero
    (g : Nat -> Real) (hg : Tendsto g atTop (nhds 0)) :
    exists G : Real, 0 <= G ∧ forall scale, |g scale| <= G := by
  have hbounded := Metric.isBounded_range_of_tendsto g hg
  rcases (isBounded_iff_forall_norm_le.1 hbounded) with ⟨G, hG⟩
  refine ⟨max G 0, le_max_right _ _, ?_⟩
  intro scale
  have hnorm := hG (g scale) ⟨scale, rfl⟩
  simpa only [Real.norm_eq_abs] using hnorm.trans (le_max_left G 0)

/-- Coupling convergence to zero automatically supplies the exact `hmoment`
premise for every ordered family of fixed finite clusters. -/
theorem canonicalSignedBlockBochnerIntegral_hmoment_of_tendsto_coupling_zero
    (hN : 3 <= N) {a : Real} (ha0 : 0 <= a) (ha1 : a <= 1 / 4)
    (kappa beta : Real) (g : Nat -> Real)
    (hg : Tendsto g atTop (nhds 0))
    (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (entry : I -> PhaseSign × OrderedModeIndex N)
    (hpositive : forall i, (entry i).2 ≠
      lastOrderedIndex (ι := Lattice.Site N))
    (cluster : Nat -> Finset I) (time : Nat -> Real) :
    forall level, exists bound : Real, forall scale,
      ‖canonicalSignedBlockBochnerIntegral (N := N)
          kappa beta (g scale) hbeta a entry (cluster level) (time scale)‖ <=
        bound := by
  rcases exists_abs_coupling_bound_of_tendsto_zero g hg with ⟨G, hG, hgG⟩
  rcases exists_uniform_massWeighted_poincareConstant (N := N) with
    ⟨C, hC, hPoincare⟩
  intro level
  rcases
      exists_systemUniform_canonicalSignedBlockBochnerIntegral_bound_of_couplingBound
        hN ha0 ha1 C hC.le hPoincare kappa beta g hbeta G hG hgG entry
          hpositive (cluster level) time with ⟨bound, _hbound, hbound⟩
  exact ⟨bound, hbound⟩

end

end ArchonPhysics.CanonicalIIDCoerciveExplicitEnergyBlockMomentBound
