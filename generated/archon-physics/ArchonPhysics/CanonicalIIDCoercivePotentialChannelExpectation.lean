import ArchonPhysics.CanonicalIIDCoerciveClusterExpectationClosure
import ArchonPhysics.PhyslibFPUTActualSourceSlotPotentialSplit

/-!
# Canonical iid quadratic/quartic potential channels

The finite-ensemble source split from
`PhyslibFPUTActualSourceSlotPotentialSplit` is rebuilt in the globally
measurable ordered eigenframe used by the canonical iid Bochner hierarchy.
The actual full alpha--beta source is exactly the sum of its quadratic-force
and quartic-force channels.  Each channel is jointly measurable and has its
own explicit shell/infrared envelope.
-/

namespace ArchonPhysics.CanonicalIIDCoercivePotentialChannelExpectation

open scoped BigOperators Matrix Topology

open ArchonPhysics
open ArchonPhysics.CanonicalIIDCoerciveActualExpectationAdapter
open ArchonPhysics.CanonicalIIDCoerciveActualExpectationClosure
open ArchonPhysics.CanonicalIIDCoerciveActualExpectationTheorem
open ArchonPhysics.CanonicalIIDCoerciveActualExpectationCompleted
open ArchonPhysics.CanonicalIIDCoerciveClusterExpectationClosure
open ArchonPhysics.CanonicalIIDCoerciveContinuousMomentFrontier
open ArchonPhysics.CanonicalIIDCoerciveExpectationHierarchy
open ArchonPhysics.CanonicalIIDCoerciveSignedModalBlockHierarchy
open ArchonPhysics.CanonicalIIDCoerciveSignedModalHierarchy
open ArchonPhysics.CanonicalIIDCoerciveSignedModalObservableBridge
open ArchonPhysics.CanonicalRandomMassPhaseGlobalFlow
open ArchonPhysics.CoerciveHamiltonianPhyslib
open ArchonPhysics.FinitePhaseMonomials
open ArchonPhysics.ForcedComplexModeDuhamel
open ArchonPhysics.MassWeightedHamiltonianDynamics
open ArchonPhysics.MeasurableOrderedEigenframe
open ArchonPhysics.MeasurableOrderedModeCoupling.Harmonic
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.OrderedSingleModeProjector
open ArchonPhysics.OrderedTranslationLastMode
open ArchonPhysics.PhaseRenormalization
open ArchonPhysics.PhyslibFPUTActualSourceSlotPotentialSplit
open ArchonPhysics.PhyslibFPUTBinaryInteractionTreeCouples
open ArchonPhysics.RandomMassMeasurableHarmonicEnergy
open ArchonPhysics.RandomMassMeasurableOrderedEigenframe
open ArchonPhysics.RandomMassOrderedProjectorBridge
open ArchonPhysics.RandomMassPositiveCollisionData
open ArchonPhysics.ReducedModeTransform
open MeasureTheory

noncomputable section

variable {N : Nat} [NeZero N]

/-- Ordered rotated source with source-potential coefficients separated from
the coefficients selecting the actual canonical flow. -/
def canonicalOrderedPotentialChannelRotatedSource
    (flowKappa flowBeta flowG : Real)
    (hflowBeta : 2 * flowKappa ^ 2 / 9 < flowBeta)
    (a sourceKappa sourceBeta sourceG : Real)
    (k : OrderedModeIndex N) (st : CanonicalSample × Real) : Complex :=
  orderedSignedRotatedSource (canonicalMass (N := N) st.1)
    sourceKappa sourceBeta sourceG k
    (fun time => canonicalFlowPosition (N := N)
      flowKappa flowBeta flowG hflowBeta a (st.1, time)) st.2

/-- Signed phase/conjugate branch of a separated potential channel. -/
def canonicalSignedPotentialChannelRotatedSource
    (flowKappa flowBeta flowG : Real)
    (hflowBeta : 2 * flowKappa ^ 2 / 9 < flowBeta)
    (a sourceKappa sourceBeta sourceG : Real)
    (entry : PhaseSign × OrderedModeIndex N)
    (st : CanonicalSample × Real) : Complex :=
  phaseSignActComplex entry.1
    (canonicalOrderedPotentialChannelRotatedSource (N := N)
      flowKappa flowBeta flowG hflowBeta a
      sourceKappa sourceBeta sourceG entry.2 st)

/-- The alpha quadratic-force channel on the actual alpha--beta flow. -/
def canonicalSignedQuadraticRotatedSource
    (kappa beta g : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (a : Real) (entry : PhaseSign × OrderedModeIndex N) :=
  canonicalSignedPotentialChannelRotatedSource (N := N)
    kappa beta g hbeta a kappa 0 g entry

/-- The beta quartic-force channel on the actual alpha--beta flow. -/
def canonicalSignedQuarticRotatedSource
    (kappa beta g : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (a : Real) (entry : PhaseSign × OrderedModeIndex N) :=
  canonicalSignedPotentialChannelRotatedSource (N := N)
    kappa beta g hbeta a 0 beta g entry

/-- Explicit envelope for one separated signed potential channel. -/
def canonicalSignedPotentialChannelSourceEnvelope
    (N : Nat) (sourceKappa sourceBeta sourceG B : Real) : Real :=
  canonicalTransformedNonlinearForceEnvelope N
      sourceKappa sourceBeta sourceG B *
    canonicalPositiveFrequencyNormalizationEnvelope N

theorem canonicalSignedPotentialChannelSourceEnvelope_nonneg
    (sourceKappa sourceBeta sourceG B : Real) (hB : 0 ≤ B) :
    0 ≤ canonicalSignedPotentialChannelSourceEnvelope N
      sourceKappa sourceBeta sourceG B := by
  unfold canonicalSignedPotentialChannelSourceEnvelope
  exact mul_nonneg
    (canonicalTransformedNonlinearForceEnvelope_nonneg
      sourceKappa sourceBeta sourceG B hB)
    canonicalPositiveFrequencyNormalizationEnvelope_nonneg

theorem nonlinearPotentialDerivative_eq_quadratic_add_quartic
    (kappa beta g x : Real) :
    nonlinearPotentialDerivative kappa beta g x =
      nonlinearPotentialDerivative kappa 0 g x +
        nonlinearPotentialDerivative 0 beta g x := by
  unfold nonlinearPotentialDerivative
  ring

theorem nonlinearPotentialGradient_eq_quadratic_add_quartic
    (kappa beta g : Real) (q : HilbertConfiguration N) :
    nonlinearPotentialGradient kappa beta g q =
      nonlinearPotentialGradient kappa 0 g q +
        nonlinearPotentialGradient 0 beta g q := by
  classical
  unfold nonlinearPotentialGradient
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [← add_smul, nonlinearPotentialDerivative_eq_quadratic_add_quartic]

theorem transformedNonlinearForce_eq_quadratic_add_quartic
    (m : Lattice.PositiveMassConfig N)
    (kappa beta g : Real) (q : HilbertConfiguration N) :
    transformedNonlinearForce m kappa beta g q =
      transformedNonlinearForce m kappa 0 g q +
        transformedNonlinearForce m 0 beta g q := by
  unfold transformedNonlinearForce
  rw [nonlinearPotentialGradient_eq_quadratic_add_quartic, map_add]
  simp only [neg_add_rev]
  abel

theorem orderedSignedNonlinearForce_eq_quadratic_add_quartic
    (m : Lattice.PositiveMassConfig N) (kappa beta g : Real)
    (k : OrderedModeIndex N) (q : HilbertConfiguration N) :
    orderedSignedNonlinearForce m kappa beta g k q =
      orderedSignedNonlinearForce m kappa 0 g k q +
        orderedSignedNonlinearForce m 0 beta g k q := by
  unfold orderedSignedNonlinearForce orderedSignedCoordinate
  rw [transformedNonlinearForce_eq_quadratic_add_quartic]
  simp only [WithLp.ofLp_add, dotProduct_add]

theorem canonicalSignedRotatedSource_eq_quadratic_add_quartic
    (kappa beta g : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (a : Real) (entry : PhaseSign × OrderedModeIndex N)
    (st : CanonicalSample × Real) :
    canonicalSignedRotatedSource (N := N)
        kappa beta g hbeta a entry st =
      canonicalSignedQuadraticRotatedSource (N := N)
          kappa beta g hbeta a entry st +
        canonicalSignedQuarticRotatedSource (N := N)
          kappa beta g hbeta a entry st := by
  rcases entry with ⟨sign, k⟩
  unfold canonicalSignedRotatedSource canonicalOrderedRotatedSource
    canonicalSignedQuadraticRotatedSource
    canonicalSignedQuarticRotatedSource
    canonicalSignedPotentialChannelRotatedSource
    canonicalOrderedPotentialChannelRotatedSource
    orderedSignedRotatedSource forcedModeSource
  rw [orderedSignedNonlinearForce_eq_quadratic_add_quartic]
  cases sign <;> simp [phaseSignActComplex]
  <;> ring

theorem measurable_canonicalOrderedPotentialChannelNonlinearForce
    (flowKappa flowBeta flowG : Real)
    (hflowBeta : 2 * flowKappa ^ 2 / 9 < flowBeta)
    (a sourceKappa sourceBeta sourceG : Real)
    (k : OrderedModeIndex N) :
    Measurable fun st : CanonicalSample × Real =>
      orderedSignedNonlinearForce (canonicalMass (N := N) st.1)
        sourceKappa sourceBeta sourceG k
        (canonicalFlowPosition (N := N)
          flowKappa flowBeta flowG hflowBeta a st) := by
  have hq := measurable_canonicalFlowPosition
    (N := N) flowKappa flowBeta flowG hflowBeta a
  have hv (i : Lattice.Site N) : Measurable fun st : CanonicalSample × Real =>
      orderedEigenvectorSample canonicalIIDMassPhaseEnsemble k st.1 i :=
    (measurable_pi_apply i).comp
      ((measurable_orderedEigenvectorSample
        canonicalIIDMassPhaseEnsemble k).comp measurable_fst)
  have hm (i : Lattice.Site N) : Measurable fun st : CanonicalSample × Real =>
      (canonicalMass (N := N) st.1).mass i :=
    (measurable_canonicalMass_coordinate (N := N) i).comp measurable_fst
  have hqcoord (i : Lattice.Site N) : Measurable fun st : CanonicalSample × Real =>
      canonicalFlowPosition (N := N)
        flowKappa flowBeta flowG hflowBeta a st i :=
    (measurable_pi_apply i).comp
      ((WithLp.measurable_ofLp 2 _).comp hq)
  have hgradient (i : Lattice.Site N) : Measurable fun st : CanonicalSample × Real =>
      nonlinearPotentialGradient sourceKappa sourceBeta sourceG
        (canonicalFlowPosition (N := N)
          flowKappa flowBeta flowG hflowBeta a st) i := by
    unfold nonlinearPotentialGradient
    simp only [WithLp.ofLp_sum, WithLp.ofLp_smul, Finset.sum_apply,
      Pi.smul_apply, smul_eq_mul]
    apply Finset.measurable_sum
    intro j _hj
    have hforward : Measurable fun st : CanonicalSample × Real =>
        Lattice.forwardDifference
          (asConfiguration
            (canonicalFlowPosition (N := N)
              flowKappa flowBeta flowG hflowBeta a st)) j := by
      unfold Lattice.forwardDifference asConfiguration
      exact (hqcoord (j + 1)).sub (hqcoord j)
    have hnonlinear : Measurable fun st : CanonicalSample × Real =>
        nonlinearPotentialDerivative sourceKappa sourceBeta sourceG
          (Lattice.forwardDifference
            (asConfiguration
              (canonicalFlowPosition (N := N)
                flowKappa flowBeta flowG hflowBeta a st)) j) := by
      unfold nonlinearPotentialDerivative
      fun_prop
    exact hnonlinear.mul measurable_const
  unfold orderedSignedNonlinearForce orderedSignedCoordinate
    transformedNonlinearForce dotProduct
  apply Finset.measurable_sum
  intro i _hi
  have hforce : Measurable fun st : CanonicalSample × Real =>
      (-inverseSqrtMassTransform (canonicalMass (N := N) st.1)
        (nonlinearPotentialGradient sourceKappa sourceBeta sourceG
          (canonicalFlowPosition (N := N)
            flowKappa flowBeta flowG hflowBeta a st))) i := by
    simp only [PiLp.neg_apply, inverseSqrtMassTransform_apply]
    exact ((hm i).sqrt.inv.mul (hgradient i)).neg
  exact (hv i).mul hforce

theorem measurable_canonicalSignedPotentialChannelRotatedSource
    (flowKappa flowBeta flowG : Real)
    (hflowBeta : 2 * flowKappa ^ 2 / 9 < flowBeta)
    (a sourceKappa sourceBeta sourceG : Real)
    (entry : PhaseSign × OrderedModeIndex N) :
    Measurable (canonicalSignedPotentialChannelRotatedSource (N := N)
      flowKappa flowBeta flowG hflowBeta a
      sourceKappa sourceBeta sourceG entry) := by
  rcases entry with ⟨sign, k⟩
  have hfrequency : Measurable fun st : CanonicalSample × Real =>
      canonicalOrderedFrequency (N := N) k st.1 :=
    (measurable_canonicalOrderedFrequency (N := N) k).comp measurable_fst
  have hforce := measurable_canonicalOrderedPotentialChannelNonlinearForce
    (N := N) flowKappa flowBeta flowG hflowBeta a
      sourceKappa sourceBeta sourceG k
  have hordered : Measurable
      (canonicalOrderedPotentialChannelRotatedSource (N := N)
        flowKappa flowBeta flowG hflowBeta a
        sourceKappa sourceBeta sourceG k) := by
    change Measurable fun st : CanonicalSample × Real =>
      phaseFactor (canonicalOrderedFrequency (N := N) k st.1 * st.2) *
        forcedModeSource (canonicalOrderedFrequency (N := N) k st.1)
          (orderedSignedNonlinearForce (canonicalMass (N := N) st.1)
            sourceKappa sourceBeta sourceG k
            (canonicalFlowPosition (N := N)
              flowKappa flowBeta flowG hflowBeta a st))
    apply Measurable.mul
    · unfold phaseFactor
      fun_prop
    · unfold forcedModeSource
      fun_prop
  cases sign with
  | phase =>
      change Measurable
        (canonicalOrderedPotentialChannelRotatedSource (N := N)
          flowKappa flowBeta flowG hflowBeta a
          sourceKappa sourceBeta sourceG k)
      exact hordered
  | conjugate =>
      change Measurable fun st => star
        (canonicalOrderedPotentialChannelRotatedSource (N := N)
          flowKappa flowBeta flowG hflowBeta a
          sourceKappa sourceBeta sourceG k st)
      exact Complex.continuous_conj.measurable.comp hordered

theorem norm_canonicalSignedPotentialChannelRotatedSource_le_envelope_of_simple
    (flowKappa flowBeta flowG : Real)
    (hflowBeta : 2 * flowKappa ^ 2 / 9 < flowBeta)
    (a sourceKappa sourceBeta sourceG : Real)
    (omega : CanonicalSample)
    (hsimple : SimpleOrderedSpectrum
      (harmonicHermitian (canonicalMass (N := N) omega)))
    (entry : PhaseSign × OrderedModeIndex N)
    (hentry : entry.2 ≠ lastOrderedIndex (ι := Lattice.Site N))
    (time : Real)
    (hq : ‖canonicalFlowPosition (N := N)
        flowKappa flowBeta flowG hflowBeta a (omega, time)‖ ≤
      (canonicalRandomMassPhaseEnergyShell N
        flowKappa flowBeta flowG hflowBeta).cutoffRadius) :
    ‖canonicalSignedPotentialChannelRotatedSource (N := N)
        flowKappa flowBeta flowG hflowBeta a
          sourceKappa sourceBeta sourceG entry (omega, time)‖ ≤
      canonicalSignedPotentialChannelSourceEnvelope N
        sourceKappa sourceBeta sourceG
        (canonicalWeightedCoordinateEnvelope N
          flowKappa flowBeta flowG hflowBeta) := by
  let B := canonicalWeightedCoordinateEnvelope N
    flowKappa flowBeta flowG hflowBeta
  let q := canonicalFlowPosition (N := N)
    flowKappa flowBeta flowG hflowBeta a (omega, time)
  have hB0 : 0 ≤ B := canonicalWeightedCoordinateEnvelope_nonneg
    flowKappa flowBeta flowG hflowBeta
  have hbond : ∀ i : Lattice.Site N,
      |Lattice.forwardDifference (asConfiguration q) i| ≤ B := by
    intro i
    calc
      |Lattice.forwardDifference (asConfiguration q) i| ≤ 2 * ‖q‖ :=
        abs_forwardDifference_le_two_mul_norm q i
      _ ≤ 2 * canonicalNonnegativeShellRadius N
          flowKappa flowBeta flowG hflowBeta := by
        gcongr
        exact hq.trans (le_max_left _ _)
      _ = B := rfl
  have hforceNorm := norm_transformedNonlinearForce_le_envelope
    (canonicalMass (N := N) omega) (canonicalMass_lower omega)
    sourceKappa sourceBeta sourceG B hB0 q hbond
  have hproject :
      |orderedSignedNonlinearForce (canonicalMass (N := N) omega)
          sourceKappa sourceBeta sourceG entry.2 q| ≤
        canonicalTransformedNonlinearForceEnvelope N
          sourceKappa sourceBeta sourceG B :=
    (abs_orderedSignedCoordinate_le_norm
      (canonicalMass (N := N) omega) hsimple entry.2
      (transformedNonlinearForce (canonicalMass (N := N) omega)
        sourceKappa sourceBeta sourceG q)).trans hforceNorm
  have hsource := norm_forcedModeSource_le
    (canonicalOrderedFrequency_pos entry.2 hentry omega)
    (inv_sqrt_two_mul_canonicalOrderedFrequency_le_envelope
      entry.2 hentry omega)
    canonicalPositiveFrequencyNormalizationEnvelope_nonneg
    (force := orderedSignedNonlinearForce
      (canonicalMass (N := N) omega)
        sourceKappa sourceBeta sourceG entry.2 q)
  rw [canonicalSignedPotentialChannelRotatedSource,
    norm_phaseSignActComplex]
  calc
    ‖canonicalOrderedPotentialChannelRotatedSource (N := N)
        flowKappa flowBeta flowG hflowBeta a sourceKappa sourceBeta sourceG
          entry.2 (omega, time)‖ =
        ‖forcedModeSource
          (canonicalOrderedFrequency (N := N) entry.2 omega)
          (orderedSignedNonlinearForce (canonicalMass (N := N) omega)
            sourceKappa sourceBeta sourceG entry.2 q)‖ := by
      simp [canonicalOrderedPotentialChannelRotatedSource,
        orderedSignedRotatedSource, canonicalOrderedFrequency, q]
    _ ≤ |orderedSignedNonlinearForce (canonicalMass (N := N) omega)
          sourceKappa sourceBeta sourceG entry.2 q| *
        canonicalPositiveFrequencyNormalizationEnvelope N := hsource
    _ ≤ canonicalTransformedNonlinearForceEnvelope N
          sourceKappa sourceBeta sourceG B *
        canonicalPositiveFrequencyNormalizationEnvelope N := by
      exact mul_le_mul_of_nonneg_right hproject
        canonicalPositiveFrequencyNormalizationEnvelope_nonneg
    _ = canonicalSignedPotentialChannelSourceEnvelope N
        sourceKappa sourceBeta sourceG B := rfl

theorem canonicalSignedPotentialChannelSourceBounds_ae_allTime
    (hN : 3 ≤ N) {a : Real} (ha0 : 0 ≤ a) (ha1 : a ≤ 1 / 4)
    (flowKappa flowBeta flowG : Real)
    (hflowBeta : 2 * flowKappa ^ 2 / 9 < flowBeta)
    (sourceKappa sourceBeta sourceG : Real)
    (entry : PhaseSign × OrderedModeIndex N)
    (hentry : entry.2 ≠ lastOrderedIndex (ι := Lattice.Site N)) :
    ∀ᵐ omega ∂canonicalIIDMassPhaseEnsemble.probability,
      ∀ time : Real,
        ‖canonicalSignedPotentialChannelRotatedSource (N := N)
            flowKappa flowBeta flowG hflowBeta a
              sourceKappa sourceBeta sourceG entry (omega, time)‖ ≤
          canonicalSignedPotentialChannelSourceEnvelope N
            sourceKappa sourceBeta sourceG
            (canonicalWeightedCoordinateEnvelope N
              flowKappa flowBeta flowG hflowBeta) := by
  filter_upwards [RandomMassOrderedProjectorBridge.simpleOrderedSpectrum_ae
      (N := N) canonicalIIDMassPhaseEnsemble (show 2 ≤ N by omega),
    norm_canonicalFlowPosition_le_cutoffRadius_ae_allTime
      hN ha0 ha1 flowKappa flowBeta flowG hflowBeta]
      with omega hsimpleSample hq
  have hsimple : SimpleOrderedSpectrum
      (harmonicHermitian (canonicalMass (N := N) omega)) := by
    simpa [canonicalMass, harmonicHermitianSample, harmonicHermitian] using
      hsimpleSample
  intro time
  exact norm_canonicalSignedPotentialChannelRotatedSource_le_envelope_of_simple
    flowKappa flowBeta flowG hflowBeta a
      sourceKappa sourceBeta sourceG omega hsimple entry hentry time (hq time)

end

end ArchonPhysics.CanonicalIIDCoercivePotentialChannelExpectation
