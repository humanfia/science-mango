import ArchonPhysics.CanonicalRankFrequencyMarkedMeasureWeakLimit
import ArchonPhysics.CanonicalScalarIDSUpperBandSaturation
import Mathlib.MeasureTheory.Measure.Portmanteau

/-!
# Compact support of the canonical marked thermodynamic limit

The deterministic Euclidean joint-frequency limit inherits the common
finite-volume spectral box by Portmanteau.  The canonical scalar IDS takes
values in `[0,1]` on that box, so its rank-frequency graph lift lies in the
common marked box.  Hence the deterministic marked limit has the same
compact support as every finite-volume marked measure.
-/

open scoped Topology InnerProductSpace RealInnerProductSpace

namespace ArchonPhysics.CanonicalRankFrequencyMarkedLimitCompactSupport

open ArchonPhysics
open ArchonPhysics.CanonicalJointFrequencyEuclideanBridge
open ArchonPhysics.CanonicalJointFrequencyMeasureWeakLimit
open ArchonPhysics.CanonicalJointFrequencyPerSiteMeasure
open ArchonPhysics.CanonicalRankFrequencyMarkedGraphLimit
open ArchonPhysics.CanonicalRankFrequencyMarkedMeasure
open ArchonPhysics.CanonicalRankFrequencyMarkedMeasureWeakLimit
open ArchonPhysics.CanonicalScalarIDSBlockApproximation
open ArchonPhysics.CanonicalScalarIDSContinuity
open ArchonPhysics.CanonicalScalarIDSUpperBandSaturation
open ArchonPhysics.FrozenUniformCollisionCompactSupport
open ArchonPhysics.MeasurableOrderedModeCoupling.Harmonic
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.OrderedSingleModeProjector
open Filter MeasureTheory Set Topology

noncomputable section

variable {Omega : Type*} [MeasurableSpace Omega]

/-- The deterministic Euclidean joint-frequency probability limit is
carried by the common box `[0,sqrt 5]^3`. -/
theorem canonicalJointFrequencyMeasureLimit_compl_support_eq_zero
    (ensemble : IIDMassPhaseEnsemble Omega) :
    (canonicalJointFrequencyMeasureLimit ensemble :
      Measure (EuclideanSpace Real (Fin 3)))
        (euclideanCollisionFrequencyTripleSupportᶜ) = 0 := by
  let _ : IsProbabilityMeasure ensemble.probability :=
    ⟨ensemble.probability_univ⟩
  have hevent : ∀ᵐ omega ∂ensemble.probability,
      (forall n : Nat, SimpleOrderedSpectrum
        (harmonicHermitian
          (ensemble.restrictPositiveMass (N := n + 3) omega))) /\
      Tendsto
        (fun n : Nat => canonicalEuclideanNormalizedJointFrequencyMeasure
          ensemble (n + 1) omega)
        atTop (nhds (canonicalJointFrequencyMeasureLimit ensemble)) := by
    filter_upwards
      [canonicalJointFrequencyVolumes_simpleOrderedSpectrum_ae ensemble,
      canonicalEuclideanNormalizedJointFrequencyMeasure_tendsto_limit_ae
        ensemble] with omega hsimple hweak
    exact ⟨hsimple, hweak⟩
  obtain ⟨omega, hsimple, hweak⟩ := hevent.exists
  have hzero : forall n : Nat,
      (canonicalEuclideanNormalizedJointFrequencyMeasure
        ensemble (n + 1) omega : Measure (EuclideanSpace Real (Fin 3)))
          (euclideanCollisionFrequencyTripleSupportᶜ) = 0 := by
    intro n
    apply
      canonicalEuclideanNormalizedJointFrequencyMeasure_compl_support_eq_zero
    exact canonicalJointFrequencyPerSiteFiniteMeasure_mass_ne_zero
      ensemble (fun _ => InteractionSign.plus) (n + 1) omega
      (by omega) (by simpa [Nat.add_assoc] using hsimple n)
  have hopen : IsOpen (euclideanCollisionFrequencyTripleSupportᶜ) :=
    euclideanCollisionFrequencyTripleSupport_isCompact.isClosed.isOpen_compl
  have hle := ProbabilityMeasure.le_liminf_measure_open_of_tendsto
    hweak hopen
  have hzeroFun :
      (fun n : Nat =>
        (canonicalEuclideanNormalizedJointFrequencyMeasure
          ensemble (n + 1) omega : Measure (EuclideanSpace Real (Fin 3)))
            (euclideanCollisionFrequencyTripleSupportᶜ)) =
      fun _n => 0 := by
    funext n
    exact hzero n
  rw [hzeroFun, liminf_const] at hle
  exact nonpos_iff_eq_zero.mp hle

/-- Every Euclidean frequency in the common spectral box is lifted by the
canonical IDS to a mark in the common rank-frequency box. -/
theorem liftEuclideanRankFrequencyTriple_mem_uniformSupport
    {frequency : EuclideanSpace Real (Fin 3)}
    (hfrequency : frequency ∈ euclideanCollisionFrequencyTripleSupport) :
    liftEuclideanRankFrequencyTriple canonicalScalarIDSValue frequency ∈
      collisionRankFrequencyTripleSupport := by
  rcases hfrequency with ⟨plain, hplain, rfl⟩
  unfold liftEuclideanRankFrequencyTriple liftRankFrequencyTriple
  rw [euclideanFrequencyTripleToPlain_plainFrequencyTripleToEuclidean]
  constructor
  · intro r
    have hnonneg : 0 <= plain r := hplain.1 r
    have hFnonneg : 0 <= canonicalScalarIDSValue (plain r ^ 2) := by
      calc
        0 = canonicalScalarIDSValue 0 := canonicalScalarIDSValue_zero.symm
        _ <= canonicalScalarIDSValue (plain r ^ 2) :=
          monotone_canonicalScalarIDSValue (sq_nonneg (plain r))
    constructor
    · change 0 <= 1 - canonicalScalarIDSValue (plain r ^ 2)
      have hupper0 : plain r <= Real.sqrt 5 := by
        simpa [collisionFrequencyCeiling] using hplain.2 r
      have hsq0 : plain r ^ 2 <= 5 := by
        nlinarith [Real.sq_sqrt (by norm_num : (0 : Real) <= 5)]
      have hFupper0 : canonicalScalarIDSValue (plain r ^ 2) <= 1 := by
        calc
          canonicalScalarIDSValue (plain r ^ 2) <= canonicalScalarIDSValue 5 :=
            monotone_canonicalScalarIDSValue hsq0
          _ = 1 := canonicalScalarIDSValue_eq_one_of_five_le le_rfl
      linarith
    · exact hnonneg
  · intro r
    have hupper : plain r <= Real.sqrt 5 := by
      simpa [collisionFrequencyCeiling] using hplain.2 r
    have hnonneg : 0 <= plain r := hplain.1 r
    have hsq : plain r ^ 2 <= 5 := by
      nlinarith [Real.sq_sqrt (by norm_num : (0 : Real) <= 5)]
    have hFupper : canonicalScalarIDSValue (plain r ^ 2) <= 1 := by
      calc
        canonicalScalarIDSValue (plain r ^ 2) <=
            canonicalScalarIDSValue 5 :=
          monotone_canonicalScalarIDSValue hsq
        _ = 1 := canonicalScalarIDSValue_eq_one_of_five_le le_rfl
    constructor
    · change 1 - canonicalScalarIDSValue (plain r ^ 2) <= 1
      have hFnonneg1 : 0 <= canonicalScalarIDSValue (plain r ^ 2) := by
        calc
          0 = canonicalScalarIDSValue 0 := canonicalScalarIDSValue_zero.symm
          _ <= canonicalScalarIDSValue (plain r ^ 2) :=
            monotone_canonicalScalarIDSValue (sq_nonneg (plain r))
      linarith
    · exact hplain.2 r

/-- The deterministic normalized marked thermodynamic limit retains the
same common compact box as every finite-volume marked measure. -/
theorem canonicalRankFrequencyMarkedMeasureLimit_compl_uniformSupport_eq_zero
    (ensemble : IIDMassPhaseEnsemble Omega) :
    (canonicalRankFrequencyMarkedMeasureLimit ensemble :
      Measure (Fin 3 -> RankFrequencyMark))
        (collisionRankFrequencyTripleSupportᶜ) = 0 := by
  unfold canonicalRankFrequencyMarkedMeasureLimit
  rw [ProbabilityMeasure.toMeasure_map]
  rw [Measure.map_apply
    (measurable_liftEuclideanRankFrequencyTriple
      continuous_canonicalScalarIDSValue)
    collisionRankFrequencyTripleSupport_isCompact.isClosed.measurableSet.compl]
  apply measure_mono_null _
    (canonicalJointFrequencyMeasureLimit_compl_support_eq_zero ensemble)
  intro frequency hfrequency
  simp only [Set.mem_preimage, Set.mem_compl_iff] at hfrequency ⊢
  intro hsupport
  exact hfrequency
    (liftEuclideanRankFrequencyTriple_mem_uniformSupport hsupport)

end

end ArchonPhysics.CanonicalRankFrequencyMarkedLimitCompactSupport
