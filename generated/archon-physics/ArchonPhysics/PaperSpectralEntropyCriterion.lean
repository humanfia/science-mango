import ArchonPhysics.ClosedHittingTimeRescaling
import ArchonPhysics.EnergyDensityThermalization
import ArchonPhysics.LateWindowRescaling

/-!
# Paper spectral-entropy thermalization criterion

Wang--Fu--Zhang--Zhao use a late-window diagnostic which is the product of
two distinct factors: the effective fraction of modes occupied inside the
monitored upper spectral band, and twice the fraction of total energy in that
band.  This file keeps the second factor visible.  In particular, entropy
equipartition inside the monitored band alone is not silently identified with
the full paper observable.

The threshold-hitting API is independent of the repository's primary `l1`
criterion.  The two diagnostics are compared only by later corollaries.
-/

namespace ArchonPhysics.PaperSpectralEntropyCriterion

open Filter MeasureTheory Set Topology
open scoped BigOperators ENNReal
open ArchonPhysics.EquipartitionEntropy
open ArchonPhysics.HamiltonianScaling
open ArchonPhysics.ThermalizationTransfer

noncomputable section

/-- Entropy-derived effective number of modes, divided by the number of
monitored modes. -/
def normalizedEffectiveModeFraction {mode : Type} [Fintype mode]
    (weight : mode -> Real) : Real :=
  participationNumber weight / (Fintype.card mode : Real)

/-- The paper's upper-band energy multiplier.  The factor two is part of the
published upper-half convention. -/
def monitoredBandEnergyFactor {mode : Type} [Fintype mode]
    (energy : mode -> Real) (monitored : Finset mode) : Real :=
  2 * (∑ i ∈ monitored, energy i) / totalWeight energy

/-- Restriction of a full modal-energy profile to the monitored band. -/
def monitoredBandWeights {mode : Type} [Fintype mode]
    (energy : mode -> Real) (monitored : Finset mode) : monitored -> Real :=
  fun i => energy i.1

/-- The complete paper-compatible spectral-entropy observable:

`(2 * monitored energy / total energy) * (exp entropy / monitored card)`.
-/
def paperXi {mode : Type} [Fintype mode]
    (energy : mode -> Real) (monitored : Finset mode) : Real :=
  monitoredBandEnergyFactor energy monitored *
    normalizedEffectiveModeFraction
      (normalizedWeights (monitoredBandWeights energy monitored))

/-- The complete diagnostic on late-window averaged modal energies. -/
def lateWindowPaperXi {mode : Type} [Fintype mode]
    (energy : Real -> mode -> Real) (monitored : Finset mode)
    (mu T : Real) : Real :=
  paperXi (lateWindowAverage energy mu T) monitored

/-- Formula-level lock for the two independent factors of the paper
observable. -/
theorem paperXi_eq_bandFactor_mul_expEntropy_div_card
    {mode : Type} [Fintype mode]
    (energy : mode -> Real) (monitored : Finset mode) :
    paperXi energy monitored =
      (2 * (∑ i ∈ monitored, energy i) / totalWeight energy) *
        (Real.exp (spectralEntropy
          (normalizedWeights (monitoredBandWeights energy monitored))) /
          (Fintype.card monitored : Real)) := by
  rfl

/-- Exact late-window invariance of the complete paper diagnostic under
`tau = g^2 t`. -/
theorem lateWindowPaperXi_rescaling_of_continuous
    {mode : Type} [Fintype mode]
    (energyG energyOne : Real -> mode -> Real)
    (monitored : Finset mode) (mu T g : Real)
    (hg : g ≠ 0) (hmu_lt_one : mu < 1) (hT : 0 < T)
    (hrescale : forall t i, energyG t i = energyOne (g ^ 2 * t) i)
    (hcontinuous : forall i, Continuous (fun tau => energyOne tau i)) :
    lateWindowPaperXi energyG monitored mu T =
      lateWindowPaperXi energyOne monitored mu (g ^ 2 * T) := by
  unfold lateWindowPaperXi
  rw [ArchonPhysics.LateWindowRescaling.lateWindowAverage_rescaling_of_continuous
    energyG energyOne mu T g hg hmu_lt_one hT hrescale hcontinuous]

/-- The same rescaling identity on every nonnegative endpoint, including the
zero endpoint used by `ENNReal.toReal top`. -/
theorem lateWindowPaperXi_rescaling_nonnegative_of_continuous
    {mode : Type} [Fintype mode]
    (energyG energyOne : Real -> mode -> Real)
    (monitored : Finset mode) (mu g : Real)
    (hg : g ≠ 0) (hmu_lt_one : mu < 1)
    (hrescale : forall t i, energyG t i = energyOne (g ^ 2 * t) i)
    (hcontinuous : forall i, Continuous (fun tau => energyOne tau i)) :
    forall T, 0 <= T ->
      lateWindowPaperXi energyG monitored mu T =
        lateWindowPaperXi energyOne monitored mu (g ^ 2 * T) := by
  intro T hT
  rcases hT.eq_or_lt with rfl | hTpos
  · have hzero (energy : Real -> mode -> Real) :
        lateWindowAverage energy mu 0 = 0 := by
      funext i
      simp [lateWindowAverage]
    simp only [mul_zero, lateWindowPaperXi]
    rw [hzero energyG, hzero energyOne]
  · exact lateWindowPaperXi_rescaling_of_continuous
      energyG energyOne monitored mu T g hg hmu_lt_one hTpos
        hrescale hcontinuous

/-- First strictly positive time at which a real diagnostic reaches an upward
closed threshold.  It is expressed through the existing closed-distance hit,
so the empty-event value remains `top`. -/
def paperXiThresholdHittingTime (xi : Real -> Real)
    (threshold : Real) : ENNReal :=
  distanceThresholdHittingTime (fun t => -xi t) (-threshold)

/-- The experimental threshold `xi >= 1/2`. -/
def paperXiHalfHittingTime (xi : Real -> Real) : ENNReal :=
  paperXiThresholdHittingTime xi (1 / 2)

/-- The upward-threshold definition unfolds to the expected infimum. -/
theorem paperXiThresholdHittingTime_eq_sInf
    (xi : Real -> Real) (threshold : Real) :
    paperXiThresholdHittingTime xi threshold =
      sInf {time : ENNReal | 0 < time /\ threshold <= xi time.toReal} := by
  unfold paperXiThresholdHittingTime
  rw [distanceThresholdHittingTime_eq_sInf]
  congr 1
  ext time
  change (0 < time ∧ -xi time.toReal ≤ -threshold) ↔
    (0 < time ∧ threshold ≤ xi time.toReal)
  constructor
  · rintro ⟨htime, hthreshold⟩
    exact ⟨htime, (neg_le_neg_iff.mp hthreshold)⟩
  · rintro ⟨htime, hthreshold⟩
    exact ⟨htime, (neg_le_neg_iff.mpr hthreshold)⟩

/-- Diagnostics agreeing at all nonnegative real times have the same upward
threshold hitting time. -/
theorem paperXiThresholdHittingTime_congr_nonnegative
    (xi zeta : Real -> Real) (threshold : Real)
    (hxi : forall t, 0 <= t -> xi t = zeta t) :
    paperXiThresholdHittingTime xi threshold =
      paperXiThresholdHittingTime zeta threshold := by
  rw [paperXiThresholdHittingTime_eq_sInf,
    paperXiThresholdHittingTime_eq_sInf]
  congr 1
  ext time
  change (0 < time ∧ threshold ≤ xi time.toReal) ↔
    (0 < time ∧ threshold ≤ zeta time.toReal)
  rw [hxi time.toReal ENNReal.toReal_nonneg]

/-- Exact kinetic rescaling of an upward-threshold hitting time. -/
theorem paperXiThresholdHittingTime_kineticScale
    (xi : Real -> Real) (threshold g : Real) (hg : g ≠ 0) :
    ENNReal.ofReal (g ^ 2) * paperXiThresholdHittingTime xi threshold =
      paperXiThresholdHittingTime (fun tau => xi (tau / g ^ 2)) threshold := by
  simpa only [paperXiThresholdHittingTime] using
    distanceThresholdHittingTime_kineticScale
      (fun t => -xi t) (-threshold) g hg

/-- If the physical diagnostic is exactly the kinetic diagnostic observed at
`g^2 t`, its hitting time is exactly `g^-2` times the kinetic hit. -/
theorem paperXiThresholdHittingTime_eq_of_kinetic_rescaling
    (xiPhysical xiKinetic : Real -> Real) (threshold g : Real)
    (hg : g ≠ 0)
    (hrescale : forall t, 0 <= t ->
      xiPhysical t = xiKinetic (g ^ 2 * t)) :
    ENNReal.ofReal (g ^ 2) *
        paperXiThresholdHittingTime xiPhysical threshold =
      paperXiThresholdHittingTime xiKinetic threshold := by
  rw [paperXiThresholdHittingTime_kineticScale xiPhysical threshold g hg]
  apply paperXiThresholdHittingTime_congr_nonnegative
  intro tau htau
  rw [hrescale (tau / g ^ 2) (div_nonneg htau (sq_nonneg g))]
  congr 1
  field_simp [pow_ne_zero 2 hg]

/-- Standalone experimental-criterion theorem: the full late-window paper
observable, with threshold `1/2`, has the exact `g^-2` hitting-time law. -/
theorem lateWindowPaperXiHalfHittingTime_kineticScale_of_continuous
    {mode : Type} [Fintype mode]
    (energyG energyOne : Real -> mode -> Real)
    (monitored : Finset mode) (mu g : Real)
    (hg : g ≠ 0) (hmu_lt_one : mu < 1)
    (hrescale : forall t i, energyG t i = energyOne (g ^ 2 * t) i)
    (hcontinuous : forall i, Continuous (fun tau => energyOne tau i)) :
    ENNReal.ofReal (g ^ 2) *
        paperXiHalfHittingTime
          (fun T => lateWindowPaperXi energyG monitored mu T) =
      paperXiHalfHittingTime
        (fun tau => lateWindowPaperXi energyOne monitored mu tau) := by
  unfold paperXiHalfHittingTime
  apply paperXiThresholdHittingTime_eq_of_kinetic_rescaling
  · exact hg
  · exact lateWindowPaperXi_rescaling_nonnegative_of_continuous
      energyG energyOne monitored mu g hg hmu_lt_one hrescale hcontinuous

/-- Random finite-volume paper-criterion hitting times. -/
def paperXiHalfEquilibrationTime {Omega : Type}
    (xi : Nat -> Real -> Omega -> Real -> Real) :
    Nat -> Real -> Omega -> ENNReal :=
  fun N g omega => paperXiHalfHittingTime (xi N g omega)

/-- The existing high-probability `g^-2` interface specializes directly to
the independent paper criterion, and then to the energy-density law
`lambda^-2 epsilon^-(n-2)`. -/
theorem paperXi_energyDensity_corollary_of_highProbabilityG2Bounds
    {Omega : Type} [MeasurableSpace Omega] (P : Measure Omega)
    [IsProbabilityMeasure P]
    (xi : Nat -> Real -> Omega -> Real -> Real)
    (sizeCutoff : Real -> Nat) (lower upper : Real)
    (h : HighProbabilityG2Bounds P
      (paperXiHalfEquilibrationTime xi) sizeCutoff lower upper)
    (lambda : Real) (n : Nat) (hn : 3 <= n) (hlambda : lambda ≠ 0)
    (s : AdmissibleJointLimit sizeCutoff) (epsilon : Nat -> Real)
    (hepsilon : forall j, 0 < epsilon j)
    (hcoupling : forall j,
      s.coupling j = effectiveCoupling lambda (epsilon j) n) :
    Tendsto
      (fun j => P (EnergyDensityThermalization.energyDensityWindowEvent
        (paperXiHalfEquilibrationTime xi) lower upper
        (s.systemSize j) lambda (epsilon j) n))
      atTop (nhds 1) := by
  exact EnergyDensityThermalization.HighProbabilityG2Bounds.energyDensity_corollary
    P (paperXiHalfEquilibrationTime xi) sizeCutoff lower upper h
      lambda n hn hlambda s epsilon hepsilon hcoupling

/-- In degree three the energy-density scale is exactly
`lambda^-2 * epsilon^-1`. -/
theorem inverseSquareEnergyScale_cubic (lambda epsilon : Real) :
    EnergyDensityThermalization.inverseSquareEnergyScale lambda epsilon 3 =
      ENNReal.ofReal (lambda⁻¹ ^ 2 * epsilon⁻¹) := by
  simp [EnergyDensityThermalization.inverseSquareEnergyScale]

/-- Explicit cubic (`epsilon^-1`) paper-criterion window. -/
def paperXiCubicEnergyDensityWindowEvent {Omega : Type}
    (xi : Nat -> Real -> Omega -> Real -> Real)
    (lower upper : Real) (N : Nat) (lambda epsilon : Real) : Set Omega :=
  paperXiHalfEquilibrationTime xi N
      (effectiveCoupling lambda epsilon 3) ⁻¹'
    Icc
      (ENNReal.ofReal (lambda⁻¹ ^ 2 * epsilon⁻¹) * ENNReal.ofReal lower)
      (ENNReal.ofReal (lambda⁻¹ ^ 2 * epsilon⁻¹) * ENNReal.ofReal upper)

/-- High-probability cubic specialization of the independent paper
criterion. -/
theorem paperXi_cubic_energyDensity_corollary_of_highProbabilityG2Bounds
    {Omega : Type} [MeasurableSpace Omega] (P : Measure Omega)
    [IsProbabilityMeasure P]
    (xi : Nat -> Real -> Omega -> Real -> Real)
    (sizeCutoff : Real -> Nat) (lower upper : Real)
    (h : HighProbabilityG2Bounds P
      (paperXiHalfEquilibrationTime xi) sizeCutoff lower upper)
    (lambda : Real) (hlambda : lambda ≠ 0)
    (s : AdmissibleJointLimit sizeCutoff) (epsilon : Nat -> Real)
    (hepsilon : forall j, 0 < epsilon j)
    (hcoupling : forall j,
      s.coupling j = effectiveCoupling lambda (epsilon j) 3) :
    Tendsto
      (fun j => P (paperXiCubicEnergyDensityWindowEvent xi lower upper
        (s.systemSize j) lambda (epsilon j)))
      atTop (nhds 1) := by
  have hgeneral := paperXi_energyDensity_corollary_of_highProbabilityG2Bounds P xi sizeCutoff
    lower upper h lambda 3 (by norm_num) hlambda s epsilon hepsilon hcoupling
  simpa only [paperXiCubicEnergyDensityWindowEvent,
    EnergyDensityThermalization.energyDensityWindowEvent,
    inverseSquareEnergyScale_cubic] using hgeneral

end

end ArchonPhysics.PaperSpectralEntropyCriterion
