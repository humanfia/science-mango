import ArchonPhysics.CanonicalIIDCoerciveExplicitEnergyBlockMomentBound
import ArchonPhysics.CanonicalIIDCoerciveActualClusterSourceSlotCouplingScaling

/-!
# Explicit-energy uniform costs for normalized source slots

The older source-slot domination constants are expressed through a chosen
compact-shell `cutoffRadius`.  Here the actual canonical trajectory is bounded
instead by `canonicalExplicitHilbertRadius`, obtained from conserved energy and
the physical coercivity theorem.  This gives explicit envelopes for the
normalized quadratic source `(1,0,1)` and normalized quartic source `(0,1,1)`.

For every `|g| <= G` and every real time, all four left/right normalized slot
factorization defects and their finite norm sums are bounded by constants
depending only on the fixed finite system data, the two blocks, and
`N,C,kappa,beta,G`.  In particular the bounds contain neither `g`, `time`, nor
the noncomputable shell cutoff.  They are uniform `O(1)` frontiers only: no
small-o decay, RPA, nonresonance, or kinetic convergence is asserted.
-/

namespace ArchonPhysics.CanonicalIIDCoerciveExplicitEnergyUnitSlotCost

open scoped BigOperators Matrix

open ArchonPhysics
open ArchonPhysics.CanonicalIIDCoerciveActualClusterSourceSlotCouplingScaling
open ArchonPhysics.CanonicalIIDCoerciveActualExpectationAdapter
open ArchonPhysics.CanonicalIIDCoerciveActualExpectationClosure
open ArchonPhysics.CanonicalIIDCoerciveActualExpectationCompleted
open ArchonPhysics.CanonicalIIDCoerciveActualExpectationTheorem
open ArchonPhysics.CanonicalIIDCoerciveActualSourceSlotExpectation
open ArchonPhysics.CanonicalIIDCoerciveContinuousMomentFrontier
open ArchonPhysics.CanonicalIIDCoerciveExplicitEnergyBlockMomentBound
open ArchonPhysics.CanonicalIIDCoercivePotentialChannelExpectation
open ArchonPhysics.CanonicalIIDCoerciveSignedModalHierarchy
open ArchonPhysics.CanonicalIIDCoerciveSignedModalObservableBridge
open ArchonPhysics.CanonicalIIDCoerciveSourceSlotCouplingScalingExpectation
open ArchonPhysics.CanonicalIIDCoerciveSourceSlotExpectationClosure
open ArchonPhysics.CoerciveHamiltonianPhyslib
open ArchonPhysics.FinitePhaseMonomials
open ArchonPhysics.ForcedComplexModeDuhamel
open ArchonPhysics.MassWeightedHamiltonianDynamics
open ArchonPhysics.MeasurableOrderedModeCoupling.Harmonic
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.OrderedSingleModeProjector
open ArchonPhysics.OrderedTranslationLastMode
open ArchonPhysics.PhyslibFPUTBinaryInteractionTreeCouples
open ArchonPhysics.RandomMassOrderedProjectorBridge
open ArchonPhysics.RandomMassPositiveCollisionData
open ArchonPhysics.ReducedModeTransform
open MeasureTheory

noncomputable section

variable {N : Nat} [NeZero N]

/-- Explicit bond-coordinate envelope obtained from the conserved-energy
Hilbert radius. -/
def canonicalExplicitWeightedCoordinateEnvelope
    (N : Nat) (C kappa beta G : Real) : Real :=
  2 * canonicalExplicitHilbertRadius N C kappa beta G

/-- Explicit source envelope for a separated potential channel evaluated on
the actual flow. -/
def canonicalExplicitPotentialChannelSourceEnvelope
    (N : Nat) (C kappa beta G sourceKappa sourceBeta sourceG : Real) : Real :=
  canonicalSignedPotentialChannelSourceEnvelope N
    sourceKappa sourceBeta sourceG
    (canonicalExplicitWeightedCoordinateEnvelope N C kappa beta G)

/-- Coupling-normalized quadratic source envelope. -/
def canonicalExplicitUnitQuadraticSourceEnvelope
    (N : Nat) (C kappa beta G : Real) : Real :=
  canonicalExplicitPotentialChannelSourceEnvelope N C kappa beta G 1 0 1

/-- Coupling-normalized quartic source envelope. -/
def canonicalExplicitUnitQuarticSourceEnvelope
    (N : Nat) (C kappa beta G : Real) : Real :=
  canonicalExplicitPotentialChannelSourceEnvelope N C kappa beta G 0 1 1

omit [NeZero N] in
theorem canonicalExplicitWeightedCoordinateEnvelope_nonneg
    (C kappa beta G : Real) :
    0 <= canonicalExplicitWeightedCoordinateEnvelope N C kappa beta G := by
  unfold canonicalExplicitWeightedCoordinateEnvelope
  exact mul_nonneg (by norm_num)
    (canonicalExplicitHilbertRadius_nonneg (N := N) C kappa beta G)

theorem canonicalExplicitPotentialChannelSourceEnvelope_nonneg
    (C kappa beta G sourceKappa sourceBeta sourceG : Real) :
    0 <= canonicalExplicitPotentialChannelSourceEnvelope N C kappa beta G
      sourceKappa sourceBeta sourceG := by
  unfold canonicalExplicitPotentialChannelSourceEnvelope
  exact canonicalSignedPotentialChannelSourceEnvelope_nonneg
    sourceKappa sourceBeta sourceG
    (canonicalExplicitWeightedCoordinateEnvelope N C kappa beta G)
    (canonicalExplicitWeightedCoordinateEnvelope_nonneg
      (N := N) C kappa beta G)

theorem canonicalExplicitUnitQuadraticSourceEnvelope_nonneg
    (C kappa beta G : Real) :
    0 <= canonicalExplicitUnitQuadraticSourceEnvelope N C kappa beta G := by
  exact canonicalExplicitPotentialChannelSourceEnvelope_nonneg
    (N := N) C kappa beta G 1 0 1

theorem canonicalExplicitUnitQuarticSourceEnvelope_nonneg
    (C kappa beta G : Real) :
    0 <= canonicalExplicitUnitQuarticSourceEnvelope N C kappa beta G := by
  exact canonicalExplicitPotentialChannelSourceEnvelope_nonneg
    (N := N) C kappa beta G 0 1 1

/-- One separated signed source is bounded by the explicit conserved-energy
radius, uniformly over the actual flow coupling in `[-G,G]`. -/
theorem norm_canonicalSignedPotentialChannelRotatedSource_le_explicitEnergy_of_simple
    (hN : 3 <= N) {a : Real} (ha0 : 0 <= a) (ha1 : a <= 1 / 4)
    (C : Real) (hC : 0 <= C)
    (hPoincare : forall (m : Lattice.PositiveMassConfig N)
      (q : Lattice.Configuration N),
      (∑ i, m.mass i * q i = 0) ->
        ‖q‖ <= C * ‖Lattice.forwardDifference q‖)
    (flowKappa flowBeta flowG G : Real)
    (hflowBeta : 2 * flowKappa ^ 2 / 9 < flowBeta)
    (hG : 0 <= G) (hg : |flowG| <= G)
    (sourceKappa sourceBeta sourceG : Real)
    (omega : CanonicalSample)
    (hsimple : SimpleOrderedSpectrum
      (harmonicHermitian (canonicalMass (N := N) omega)))
    (entry : PhaseSign × OrderedModeIndex N)
    (hentry : entry.2 ≠ lastOrderedIndex (ι := Lattice.Site N))
    (time : Real) :
    ‖canonicalSignedPotentialChannelRotatedSource (N := N)
        flowKappa flowBeta flowG hflowBeta a
          sourceKappa sourceBeta sourceG entry (omega, time)‖ <=
      canonicalExplicitPotentialChannelSourceEnvelope N C
        flowKappa flowBeta G sourceKappa sourceBeta sourceG := by
  let R := canonicalExplicitHilbertRadius N C flowKappa flowBeta G
  let B := canonicalExplicitWeightedCoordinateEnvelope N C
    flowKappa flowBeta G
  let q := canonicalFlowPosition (N := N)
    flowKappa flowBeta flowG hflowBeta a (omega, time)
  have hflow :=
    norm_canonicalFlowPosition_and_momentum_le_explicitEnergy_of_simple
      hN ha0 ha1 C hC hPoincare flowKappa flowBeta flowG G
        hflowBeta hG hg omega hsimple time
  have hB0 : 0 <= B := by
    exact canonicalExplicitWeightedCoordinateEnvelope_nonneg
      (N := N) C flowKappa flowBeta G
  have hbond : forall i : Lattice.Site N,
      |Lattice.forwardDifference (asConfiguration q) i| <= B := by
    intro i
    calc
      |Lattice.forwardDifference (asConfiguration q) i| <= 2 * ‖q‖ :=
        abs_forwardDifference_le_two_mul_norm q i
      _ <= 2 * R := by
        gcongr
        exact hflow.1
      _ = B := rfl
  have hforceNorm := norm_transformedNonlinearForce_le_envelope
    (canonicalMass (N := N) omega) (canonicalMass_lower omega)
    sourceKappa sourceBeta sourceG B hB0 q hbond
  have hproject :
      |orderedSignedNonlinearForce (canonicalMass (N := N) omega)
          sourceKappa sourceBeta sourceG entry.2 q| <=
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
    _ <= |orderedSignedNonlinearForce (canonicalMass (N := N) omega)
          sourceKappa sourceBeta sourceG entry.2 q| *
        canonicalPositiveFrequencyNormalizationEnvelope N := hsource
    _ <= canonicalTransformedNonlinearForceEnvelope N
          sourceKappa sourceBeta sourceG B *
        canonicalPositiveFrequencyNormalizationEnvelope N := by
      exact mul_le_mul_of_nonneg_right hproject
        canonicalPositiveFrequencyNormalizationEnvelope_nonneg
    _ = canonicalExplicitPotentialChannelSourceEnvelope N C
        flowKappa flowBeta G sourceKappa sourceBeta sourceG := rfl

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- Pointwise explicit-energy bound for one source-replaced block. -/
theorem norm_canonicalPotentialSourceSlotObservable_le_explicitEnergy_of_simple
    (hN : 3 <= N) {a : Real} (ha0 : 0 <= a) (ha1 : a <= 1 / 4)
    (C : Real) (hC : 0 <= C)
    (hPoincare : forall (m : Lattice.PositiveMassConfig N)
      (q : Lattice.Configuration N),
      (∑ i, m.mass i * q i = 0) ->
        ‖q‖ <= C * ‖Lattice.forwardDifference q‖)
    (flowKappa flowBeta flowG G : Real)
    (hflowBeta : 2 * flowKappa ^ 2 / 9 < flowBeta)
    (hG : 0 <= G) (hg : |flowG| <= G)
    (sourceKappa sourceBeta sourceG : Real)
    (entry : I -> PhaseSign × OrderedModeIndex N)
    (hpositive : forall i, (entry i).2 ≠
      lastOrderedIndex (ι := Lattice.Site N))
    (block : Finset I) (slot : I)
    (omega : CanonicalSample)
    (hsimple : SimpleOrderedSpectrum
      (harmonicHermitian (canonicalMass (N := N) omega)))
    (time : Real) :
    ‖canonicalPotentialSourceSlotObservable (N := N)
        flowKappa flowBeta flowG hflowBeta a
        sourceKappa sourceBeta sourceG entry block slot (omega, time)‖ <=
      canonicalPotentialSourceSlotEnvelope
        (canonicalExplicitSignedAmplitudeEnvelope N C flowKappa flowBeta G)
        (canonicalExplicitPotentialChannelSourceEnvelope N C
          flowKappa flowBeta G sourceKappa sourceBeta sourceG)
        block slot := by
  unfold canonicalPotentialSourceSlotObservable
    canonicalPotentialSourceSlotEnvelope
  rw [norm_mul]
  exact mul_le_mul
    (norm_finite_signed_block_le
      (fun j => canonicalSignedInteractionAmplitude (N := N)
        flowKappa flowBeta flowG hflowBeta a (entry j) (omega, time))
      (block.erase slot)
      (canonicalExplicitSignedAmplitudeEnvelope_nonneg
        (N := N) C flowKappa flowBeta G)
      (fun j _hj =>
        norm_canonicalSignedInteractionAmplitude_le_explicitEnergy_of_simple
          hN ha0 ha1 C hC hPoincare flowKappa flowBeta flowG G
            hflowBeta hG hg omega hsimple (entry j) (hpositive j) time))
    (norm_canonicalSignedPotentialChannelRotatedSource_le_explicitEnergy_of_simple
      hN ha0 ha1 C hC hPoincare flowKappa flowBeta flowG G
        hflowBeta hG hg sourceKappa sourceBeta sourceG omega hsimple
          (entry slot) (hpositive slot) time)
    (norm_nonneg _)
    (by
      unfold canonicalSignedBlockEnvelope
      exact pow_nonneg (by
        linarith [canonicalExplicitSignedAmplitudeEnvelope_nonneg
          (N := N) C flowKappa flowBeta G]) _)

/-- Explicit-energy bound for the expectation of one source-replaced block. -/
theorem norm_canonicalPotentialSourceSlotBochnerIntegral_le_explicitEnergy
    (hN : 3 <= N) {a : Real} (ha0 : 0 <= a) (ha1 : a <= 1 / 4)
    (C : Real) (hC : 0 <= C)
    (hPoincare : forall (m : Lattice.PositiveMassConfig N)
      (q : Lattice.Configuration N),
      (∑ i, m.mass i * q i = 0) ->
        ‖q‖ <= C * ‖Lattice.forwardDifference q‖)
    (flowKappa flowBeta flowG G : Real)
    (hflowBeta : 2 * flowKappa ^ 2 / 9 < flowBeta)
    (hG : 0 <= G) (hg : |flowG| <= G)
    (sourceKappa sourceBeta sourceG : Real)
    (entry : I -> PhaseSign × OrderedModeIndex N)
    (hpositive : forall i, (entry i).2 ≠
      lastOrderedIndex (ι := Lattice.Site N))
    (block : Finset I) (slot : I) (time : Real) :
    ‖canonicalPotentialSourceSlotBochnerIntegral (N := N)
        flowKappa flowBeta flowG hflowBeta a
        sourceKappa sourceBeta sourceG entry block slot time‖ <=
      canonicalPotentialSourceSlotEnvelope
        (canonicalExplicitSignedAmplitudeEnvelope N C flowKappa flowBeta G)
        (canonicalExplicitPotentialChannelSourceEnvelope N C
          flowKappa flowBeta G sourceKappa sourceBeta sourceG)
        block slot := by
  let _ : IsFiniteMeasure canonicalIIDMassPhaseEnsemble.probability :=
    ⟨by rw [canonicalIIDMassPhaseEnsemble.probability_univ]; norm_num⟩
  have hsimpleAE := simpleOrderedSpectrum_ae
    (N := N) canonicalIIDMassPhaseEnsemble (show 2 <= N by omega)
  have h := norm_integral_le_of_norm_le_const
    (μ := canonicalIIDMassPhaseEnsemble.probability)
    (f := fun omega : CanonicalSample =>
      canonicalPotentialSourceSlotObservable (N := N)
        flowKappa flowBeta flowG hflowBeta a
        sourceKappa sourceBeta sourceG entry block slot (omega, time))
    (C := canonicalPotentialSourceSlotEnvelope
      (canonicalExplicitSignedAmplitudeEnvelope N C flowKappa flowBeta G)
      (canonicalExplicitPotentialChannelSourceEnvelope N C
        flowKappa flowBeta G sourceKappa sourceBeta sourceG)
      block slot)
    (by
      filter_upwards [hsimpleAE] with omega hsimple
      exact norm_canonicalPotentialSourceSlotObservable_le_explicitEnergy_of_simple
        hN ha0 ha1 C hC hPoincare flowKappa flowBeta flowG G
          hflowBeta hG hg sourceKappa sourceBeta sourceG entry hpositive
            block slot omega hsimple time)
  rw [Measure.real, canonicalIIDMassPhaseEnsemble.probability_univ] at h
  norm_num at h
  simpa [canonicalPotentialSourceSlotBochnerIntegral] using h

/-- Explicit-energy left source-slot defect cost for any separated channel. -/
theorem norm_canonicalLeftPotentialSourceSlotFactorizationDefect_le_explicitEnergyCost
    (hN : 3 <= N) {a : Real} (ha0 : 0 <= a) (ha1 : a <= 1 / 4)
    (C : Real) (hC : 0 <= C)
    (hPoincare : forall (m : Lattice.PositiveMassConfig N)
      (q : Lattice.Configuration N),
      (∑ i, m.mass i * q i = 0) ->
        ‖q‖ <= C * ‖Lattice.forwardDifference q‖)
    (flowKappa flowBeta flowG G : Real)
    (hflowBeta : 2 * flowKappa ^ 2 / 9 < flowBeta)
    (hG : 0 <= G) (hg : |flowG| <= G)
    (sourceKappa sourceBeta sourceG : Real)
    (entry : I -> PhaseSign × OrderedModeIndex N)
    (hpositive : forall i, (entry i).2 ≠
      lastOrderedIndex (ι := Lattice.Site N))
    (left right : Finset I) (slot : I) (time : Real) :
    ‖canonicalLeftPotentialSourceSlotFactorizationDefect (N := N)
        flowKappa flowBeta flowG hflowBeta a
        sourceKappa sourceBeta sourceG entry left right slot time‖ <=
      canonicalLeftSourceSlotDefectCost
        (canonicalExplicitSignedAmplitudeEnvelope N C flowKappa flowBeta G)
        (canonicalExplicitPotentialChannelSourceEnvelope N C
          flowKappa flowBeta G sourceKappa sourceBeta sourceG)
        left right slot := by
  let A := canonicalExplicitSignedAmplitudeEnvelope N C flowKappa flowBeta G
  let S := canonicalExplicitPotentialChannelSourceEnvelope N C
    flowKappa flowBeta G sourceKappa sourceBeta sourceG
  let _ : IsFiniteMeasure canonicalIIDMassPhaseEnsemble.probability :=
    ⟨by rw [canonicalIIDMassPhaseEnsemble.probability_univ]; norm_num⟩
  have hsimpleAE := simpleOrderedSpectrum_ae
    (N := N) canonicalIIDMassPhaseEnsemble (show 2 <= N by omega)
  have hmixed := norm_integral_le_of_norm_le_const
    (μ := canonicalIIDMassPhaseEnsemble.probability)
    (f := fun omega : CanonicalSample =>
      canonicalPotentialSourceSlotObservable (N := N)
          flowKappa flowBeta flowG hflowBeta a
          sourceKappa sourceBeta sourceG entry left slot (omega, time) *
        canonicalSignedBlockObservable (N := N)
          flowKappa flowBeta flowG hflowBeta a entry right (omega, time))
    (C := canonicalPotentialSourceSlotEnvelope A S left slot *
      canonicalSignedBlockEnvelope A right)
    (by
      filter_upwards [hsimpleAE] with omega hsimple
      rw [norm_mul]
      exact mul_le_mul
        (norm_canonicalPotentialSourceSlotObservable_le_explicitEnergy_of_simple
          hN ha0 ha1 C hC hPoincare flowKappa flowBeta flowG G
            hflowBeta hG hg sourceKappa sourceBeta sourceG entry hpositive
              left slot omega hsimple time)
        (by
          unfold canonicalSignedBlockObservable
          exact norm_finite_signed_block_le
            (fun j => canonicalSignedInteractionAmplitude (N := N)
              flowKappa flowBeta flowG hflowBeta a (entry j) (omega, time))
            right
            (canonicalExplicitSignedAmplitudeEnvelope_nonneg
              (N := N) C flowKappa flowBeta G)
            (fun j _hj =>
              norm_canonicalSignedInteractionAmplitude_le_explicitEnergy_of_simple
                hN ha0 ha1 C hC hPoincare flowKappa flowBeta flowG G
                  hflowBeta hG hg omega hsimple (entry j) (hpositive j) time))
        (norm_nonneg _)
        (canonicalPotentialSourceSlotEnvelope_nonneg
          (canonicalExplicitSignedAmplitudeEnvelope_nonneg
            (N := N) C flowKappa flowBeta G)
          (canonicalExplicitPotentialChannelSourceEnvelope_nonneg
            (N := N) C flowKappa flowBeta G
              sourceKappa sourceBeta sourceG)
          left slot))
  rw [Measure.real, canonicalIIDMassPhaseEnsemble.probability_univ] at hmixed
  norm_num at hmixed
  have hslot :=
    norm_canonicalPotentialSourceSlotBochnerIntegral_le_explicitEnergy
      hN ha0 ha1 C hC hPoincare flowKappa flowBeta flowG G
        hflowBeta hG hg sourceKappa sourceBeta sourceG entry hpositive
          left slot time
  have hblock :=
    norm_canonicalSignedBlockBochnerIntegral_le_explicitEnergyEnvelope
      hN ha0 ha1 C hC hPoincare flowKappa flowBeta flowG G
        hflowBeta hG hg entry hpositive right time
  unfold canonicalLeftPotentialSourceSlotFactorizationDefect
    canonicalLeftSourceSlotDefectCost
  apply (norm_sub_le _ _).trans
  calc
    ‖integral canonicalIIDMassPhaseEnsemble.probability
        (fun omega =>
          canonicalPotentialSourceSlotObservable (N := N)
              flowKappa flowBeta flowG hflowBeta a
              sourceKappa sourceBeta sourceG entry left slot (omega, time) *
            canonicalSignedBlockObservable (N := N)
              flowKappa flowBeta flowG hflowBeta a entry right (omega, time))‖ +
        ‖canonicalPotentialSourceSlotBochnerIntegral (N := N)
            flowKappa flowBeta flowG hflowBeta a
            sourceKappa sourceBeta sourceG entry left slot time *
          canonicalSignedBlockBochnerIntegral (N := N)
            flowKappa flowBeta flowG hflowBeta a entry right time‖ <=
      canonicalPotentialSourceSlotEnvelope A S left slot *
          canonicalSignedBlockEnvelope A right +
        canonicalPotentialSourceSlotEnvelope A S left slot *
          canonicalSignedBlockEnvelope A right := by
      apply add_le_add hmixed
      rw [norm_mul]
      exact mul_le_mul hslot hblock (norm_nonneg _)
        (canonicalPotentialSourceSlotEnvelope_nonneg
          (canonicalExplicitSignedAmplitudeEnvelope_nonneg
            (N := N) C flowKappa flowBeta G)
          (canonicalExplicitPotentialChannelSourceEnvelope_nonneg
            (N := N) C flowKappa flowBeta G
              sourceKappa sourceBeta sourceG)
          left slot)
    _ = 2 * canonicalPotentialSourceSlotEnvelope A S left slot *
        canonicalSignedBlockEnvelope A right := by ring

/-- Explicit-energy right source-slot defect cost for any separated channel. -/
theorem norm_canonicalRightPotentialSourceSlotFactorizationDefect_le_explicitEnergyCost
    (hN : 3 <= N) {a : Real} (ha0 : 0 <= a) (ha1 : a <= 1 / 4)
    (C : Real) (hC : 0 <= C)
    (hPoincare : forall (m : Lattice.PositiveMassConfig N)
      (q : Lattice.Configuration N),
      (∑ i, m.mass i * q i = 0) ->
        ‖q‖ <= C * ‖Lattice.forwardDifference q‖)
    (flowKappa flowBeta flowG G : Real)
    (hflowBeta : 2 * flowKappa ^ 2 / 9 < flowBeta)
    (hG : 0 <= G) (hg : |flowG| <= G)
    (sourceKappa sourceBeta sourceG : Real)
    (entry : I -> PhaseSign × OrderedModeIndex N)
    (hpositive : forall i, (entry i).2 ≠
      lastOrderedIndex (ι := Lattice.Site N))
    (left right : Finset I) (slot : I) (time : Real) :
    ‖canonicalRightPotentialSourceSlotFactorizationDefect (N := N)
        flowKappa flowBeta flowG hflowBeta a
        sourceKappa sourceBeta sourceG entry left right slot time‖ <=
      canonicalRightSourceSlotDefectCost
        (canonicalExplicitSignedAmplitudeEnvelope N C flowKappa flowBeta G)
        (canonicalExplicitPotentialChannelSourceEnvelope N C
          flowKappa flowBeta G sourceKappa sourceBeta sourceG)
        left right slot := by
  let A := canonicalExplicitSignedAmplitudeEnvelope N C flowKappa flowBeta G
  let S := canonicalExplicitPotentialChannelSourceEnvelope N C
    flowKappa flowBeta G sourceKappa sourceBeta sourceG
  let _ : IsFiniteMeasure canonicalIIDMassPhaseEnsemble.probability :=
    ⟨by rw [canonicalIIDMassPhaseEnsemble.probability_univ]; norm_num⟩
  have hsimpleAE := simpleOrderedSpectrum_ae
    (N := N) canonicalIIDMassPhaseEnsemble (show 2 <= N by omega)
  have hmixed := norm_integral_le_of_norm_le_const
    (μ := canonicalIIDMassPhaseEnsemble.probability)
    (f := fun omega : CanonicalSample =>
      canonicalSignedBlockObservable (N := N)
          flowKappa flowBeta flowG hflowBeta a entry left (omega, time) *
        canonicalPotentialSourceSlotObservable (N := N)
          flowKappa flowBeta flowG hflowBeta a
          sourceKappa sourceBeta sourceG entry right slot (omega, time))
    (C := canonicalSignedBlockEnvelope A left *
      canonicalPotentialSourceSlotEnvelope A S right slot)
    (by
      filter_upwards [hsimpleAE] with omega hsimple
      rw [norm_mul]
      exact mul_le_mul
        (by
          unfold canonicalSignedBlockObservable
          exact norm_finite_signed_block_le
            (fun j => canonicalSignedInteractionAmplitude (N := N)
              flowKappa flowBeta flowG hflowBeta a (entry j) (omega, time))
            left
            (canonicalExplicitSignedAmplitudeEnvelope_nonneg
              (N := N) C flowKappa flowBeta G)
            (fun j _hj =>
              norm_canonicalSignedInteractionAmplitude_le_explicitEnergy_of_simple
                hN ha0 ha1 C hC hPoincare flowKappa flowBeta flowG G
                  hflowBeta hG hg omega hsimple (entry j) (hpositive j) time))
        (norm_canonicalPotentialSourceSlotObservable_le_explicitEnergy_of_simple
          hN ha0 ha1 C hC hPoincare flowKappa flowBeta flowG G
            hflowBeta hG hg sourceKappa sourceBeta sourceG entry hpositive
              right slot omega hsimple time)
        (norm_nonneg _)
        (by
          unfold canonicalSignedBlockEnvelope
          exact pow_nonneg (by
            linarith [canonicalExplicitSignedAmplitudeEnvelope_nonneg
              (N := N) C flowKappa flowBeta G]) _))
  rw [Measure.real, canonicalIIDMassPhaseEnsemble.probability_univ] at hmixed
  norm_num at hmixed
  have hblock :=
    norm_canonicalSignedBlockBochnerIntegral_le_explicitEnergyEnvelope
      hN ha0 ha1 C hC hPoincare flowKappa flowBeta flowG G
        hflowBeta hG hg entry hpositive left time
  have hslot :=
    norm_canonicalPotentialSourceSlotBochnerIntegral_le_explicitEnergy
      hN ha0 ha1 C hC hPoincare flowKappa flowBeta flowG G
        hflowBeta hG hg sourceKappa sourceBeta sourceG entry hpositive
          right slot time
  unfold canonicalRightPotentialSourceSlotFactorizationDefect
    canonicalRightSourceSlotDefectCost
  apply (norm_sub_le _ _).trans
  calc
    ‖integral canonicalIIDMassPhaseEnsemble.probability
        (fun omega =>
          canonicalSignedBlockObservable (N := N)
              flowKappa flowBeta flowG hflowBeta a entry left (omega, time) *
            canonicalPotentialSourceSlotObservable (N := N)
              flowKappa flowBeta flowG hflowBeta a
              sourceKappa sourceBeta sourceG entry right slot (omega, time))‖ +
        ‖canonicalSignedBlockBochnerIntegral (N := N)
            flowKappa flowBeta flowG hflowBeta a entry left time *
          canonicalPotentialSourceSlotBochnerIntegral (N := N)
            flowKappa flowBeta flowG hflowBeta a
            sourceKappa sourceBeta sourceG entry right slot time‖ <=
      canonicalSignedBlockEnvelope A left *
          canonicalPotentialSourceSlotEnvelope A S right slot +
        canonicalSignedBlockEnvelope A left *
          canonicalPotentialSourceSlotEnvelope A S right slot := by
      apply add_le_add hmixed
      rw [norm_mul]
      exact mul_le_mul hblock hslot (norm_nonneg _) (by
        unfold canonicalSignedBlockEnvelope
        exact pow_nonneg (by
          linarith [canonicalExplicitSignedAmplitudeEnvelope_nonneg
            (N := N) C flowKappa flowBeta G]) _)
    _ = 2 * canonicalSignedBlockEnvelope A left *
        canonicalPotentialSourceSlotEnvelope A S right slot := by ring

/-! ## The four normalized unit-slot bounds -/

theorem norm_canonicalLeftUnitQuadraticSourceSlotFactorizationDefect_le_explicitEnergyCost
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
    (left right : Finset I) (slot : I) (time : Real) :
    ‖canonicalLeftUnitQuadraticSourceSlotFactorizationDefect (N := N)
        kappa beta g hbeta a entry left right slot time‖ <=
      canonicalLeftSourceSlotDefectCost
        (canonicalExplicitSignedAmplitudeEnvelope N C kappa beta G)
        (canonicalExplicitUnitQuadraticSourceEnvelope N C kappa beta G)
        left right slot := by
  unfold canonicalLeftUnitQuadraticSourceSlotFactorizationDefect
    canonicalExplicitUnitQuadraticSourceEnvelope
  exact norm_canonicalLeftPotentialSourceSlotFactorizationDefect_le_explicitEnergyCost
    hN ha0 ha1 C hC hPoincare kappa beta g G hbeta hG hg 1 0 1
      entry hpositive left right slot time

theorem norm_canonicalLeftUnitQuarticSourceSlotFactorizationDefect_le_explicitEnergyCost
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
    (left right : Finset I) (slot : I) (time : Real) :
    ‖canonicalLeftUnitQuarticSourceSlotFactorizationDefect (N := N)
        kappa beta g hbeta a entry left right slot time‖ <=
      canonicalLeftSourceSlotDefectCost
        (canonicalExplicitSignedAmplitudeEnvelope N C kappa beta G)
        (canonicalExplicitUnitQuarticSourceEnvelope N C kappa beta G)
        left right slot := by
  unfold canonicalLeftUnitQuarticSourceSlotFactorizationDefect
    canonicalExplicitUnitQuarticSourceEnvelope
  exact norm_canonicalLeftPotentialSourceSlotFactorizationDefect_le_explicitEnergyCost
    hN ha0 ha1 C hC hPoincare kappa beta g G hbeta hG hg 0 1 1
      entry hpositive left right slot time

theorem norm_canonicalRightUnitQuadraticSourceSlotFactorizationDefect_le_explicitEnergyCost
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
    (left right : Finset I) (slot : I) (time : Real) :
    ‖canonicalRightUnitQuadraticSourceSlotFactorizationDefect (N := N)
        kappa beta g hbeta a entry left right slot time‖ <=
      canonicalRightSourceSlotDefectCost
        (canonicalExplicitSignedAmplitudeEnvelope N C kappa beta G)
        (canonicalExplicitUnitQuadraticSourceEnvelope N C kappa beta G)
        left right slot := by
  unfold canonicalRightUnitQuadraticSourceSlotFactorizationDefect
    canonicalExplicitUnitQuadraticSourceEnvelope
  exact norm_canonicalRightPotentialSourceSlotFactorizationDefect_le_explicitEnergyCost
    hN ha0 ha1 C hC hPoincare kappa beta g G hbeta hG hg 1 0 1
      entry hpositive left right slot time

theorem norm_canonicalRightUnitQuarticSourceSlotFactorizationDefect_le_explicitEnergyCost
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
    (left right : Finset I) (slot : I) (time : Real) :
    ‖canonicalRightUnitQuarticSourceSlotFactorizationDefect (N := N)
        kappa beta g hbeta a entry left right slot time‖ <=
      canonicalRightSourceSlotDefectCost
        (canonicalExplicitSignedAmplitudeEnvelope N C kappa beta G)
        (canonicalExplicitUnitQuarticSourceEnvelope N C kappa beta G)
        left right slot := by
  unfold canonicalRightUnitQuarticSourceSlotFactorizationDefect
    canonicalExplicitUnitQuarticSourceEnvelope
  exact norm_canonicalRightPotentialSourceSlotFactorizationDefect_le_explicitEnergyCost
    hN ha0 ha1 C hC hPoincare kappa beta g G hbeta hG hg 0 1 1
      entry hpositive left right slot time

/-- Explicit finite cost for the sum of all normalized quadratic slot norms. -/
def canonicalExplicitClusterUnitQuadraticSourceSlotCost
    (N : Nat) (C kappa beta G : Real)
    (left right : Finset I) : Real :=
  (∑ slot ∈ left,
    canonicalLeftSourceSlotDefectCost
      (canonicalExplicitSignedAmplitudeEnvelope N C kappa beta G)
      (canonicalExplicitUnitQuadraticSourceEnvelope N C kappa beta G)
      left right slot) +
  ∑ slot ∈ right,
    canonicalRightSourceSlotDefectCost
      (canonicalExplicitSignedAmplitudeEnvelope N C kappa beta G)
      (canonicalExplicitUnitQuadraticSourceEnvelope N C kappa beta G)
      left right slot

/-- Explicit finite cost for the sum of all normalized quartic slot norms. -/
def canonicalExplicitClusterUnitQuarticSourceSlotCost
    (N : Nat) (C kappa beta G : Real)
    (left right : Finset I) : Real :=
  (∑ slot ∈ left,
    canonicalLeftSourceSlotDefectCost
      (canonicalExplicitSignedAmplitudeEnvelope N C kappa beta G)
      (canonicalExplicitUnitQuarticSourceEnvelope N C kappa beta G)
      left right slot) +
  ∑ slot ∈ right,
    canonicalRightSourceSlotDefectCost
      (canonicalExplicitSignedAmplitudeEnvelope N C kappa beta G)
      (canonicalExplicitUnitQuarticSourceEnvelope N C kappa beta G)
      left right slot

/-- The full normalized quadratic slot-norm sum has one coupling- and
time-independent explicit cost. -/
theorem canonicalClusterUnitQuadraticSourceSlotNormSum_le_explicitEnergyCost
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
    (left right : Finset I) (time : Real) :
    canonicalClusterUnitQuadraticSourceSlotNormSum (N := N)
        kappa beta g hbeta a entry left right time <=
      canonicalExplicitClusterUnitQuadraticSourceSlotCost N C
        kappa beta G left right := by
  unfold canonicalClusterUnitQuadraticSourceSlotNormSum
    canonicalExplicitClusterUnitQuadraticSourceSlotCost
  apply add_le_add <;> apply Finset.sum_le_sum
  · intro slot _hslot
    exact norm_canonicalLeftUnitQuadraticSourceSlotFactorizationDefect_le_explicitEnergyCost
      hN ha0 ha1 C hC hPoincare kappa beta g G hbeta hG hg
        entry hpositive left right slot time
  · intro slot _hslot
    exact norm_canonicalRightUnitQuadraticSourceSlotFactorizationDefect_le_explicitEnergyCost
      hN ha0 ha1 C hC hPoincare kappa beta g G hbeta hG hg
        entry hpositive left right slot time

/-- The full normalized quartic slot-norm sum has one coupling- and
time-independent explicit cost. -/
theorem canonicalClusterUnitQuarticSourceSlotNormSum_le_explicitEnergyCost
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
    (left right : Finset I) (time : Real) :
    canonicalClusterUnitQuarticSourceSlotNormSum (N := N)
        kappa beta g hbeta a entry left right time <=
      canonicalExplicitClusterUnitQuarticSourceSlotCost N C
        kappa beta G left right := by
  unfold canonicalClusterUnitQuarticSourceSlotNormSum
    canonicalExplicitClusterUnitQuarticSourceSlotCost
  apply add_le_add <;> apply Finset.sum_le_sum
  · intro slot _hslot
    exact norm_canonicalLeftUnitQuarticSourceSlotFactorizationDefect_le_explicitEnergyCost
      hN ha0 ha1 C hC hPoincare kappa beta g G hbeta hG hg
        entry hpositive left right slot time
  · intro slot _hslot
    exact norm_canonicalRightUnitQuarticSourceSlotFactorizationDefect_le_explicitEnergyCost
      hN ha0 ha1 C hC hPoincare kappa beta g G hbeta hG hg
        entry hpositive left right slot time

end

end ArchonPhysics.CanonicalIIDCoerciveExplicitEnergyUnitSlotCost
