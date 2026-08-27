import ArchonPhysics.GlobalRandomMassModalObservable
import ArchonPhysics.EquipartitionEntropy
import ArchonPhysics.LateWindowL1Stability
import ArchonPhysics.MeasurableHittingTime
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Measurable positive-mode late-window observables

Starting from a jointly measurable nonnegative physical ordered-mode energy
profile, this module constructs the actual late-window integral and average,
their total and normalized weights, and the finite `l1` distance from the
realization-dependent positive-mode uniform profile.  The latter is written
on the complete ordered index set, with zero outside the positive sector and
with the physical denominator `N - 1`.

The constructions are total: if the late-window total energy vanishes, Lean's
real division convention makes every normalized weight zero.  Positivity of
that denominator is deliberately kept as a separate downstream hypothesis.

We also expose two measurable countable-time diagnostics.  The first is the
positive-rational strict-threshold hitting time.  The second requires the
closed threshold to persist at every rational evaluation in a fixed real
duration.  These facts use only measurability.  Identifying either countable
diagnostic with an uncountable continuous-time notion requires the additional
path regularity/entry hypotheses already isolated in `MeasurableHittingTime`.

No random initial datum is asserted to lie in a common coercive shell, and no
microscopic-to-kinetic or thermalization limit is asserted.
-/

namespace ArchonPhysics.RandomMassPositiveLateWindowObservable

open ArchonPhysics
open ArchonPhysics.EquipartitionEntropy
open ArchonPhysics.GlobalRandomMassModalObservable
open ArchonPhysics.MeasurableHittingTime
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.OrderedSpectrumContinuity
open ArchonPhysics.ParametricLocalHamiltonianFlow
open MeasureTheory Set

noncomputable section

variable {S : Type*} [MeasurableSpace S]

/-- Ordered spectral index for an `N`-site chain. -/
abbrev OrderedModeIndex (N : Nat) [NeZero N] :=
  Fin (Fintype.card (Lattice.Site N))

/-- A fixed-endpoint interval integral of a jointly measurable real function
is measurable in the remaining parameter.  No integrability hypothesis is
needed because the Bochner integral is total (and is zero when undefined). -/
theorem measurable_intervalIntegral_prod_right
    (f : S × Real → Real) (hf : Measurable f) (a b : Real) :
    Measurable fun s ↦ ∫ t in a..b, f (s, t) := by
  unfold intervalIntegral
  have hab : StronglyMeasurable fun st : S × Real ↦ f st :=
    hf.stronglyMeasurable
  have hba : StronglyMeasurable fun st : S × Real ↦ f st := hab
  exact
    (hab.integral_prod_right'
      (ν := volume.restrict (Ioc a b))).measurable.sub
    (hba.integral_prod_right'
      (ν := volume.restrict (Ioc b a))).measurable

/-- Per-mode physical energy integrated over the late window
`[mu * T, T]`. -/
def sampledPositiveLateWindowIntegral
    {N : Nat} [NeZero N]
    (massSample : S → Lattice.PositiveMassConfig N)
    (initial : S → ParametricPhaseSpace N)
    (flow : ParametricPhaseSpace N × Real → ParametricPhaseSpace N)
    (mu T : Real) (s : S) (k : OrderedModeIndex N) : Real :=
  ∫ t in mu * T..T,
    sampledPositivePhysicalOrderedEnergyProfileAlongFlow
      massSample initial flow (s, t) k

/-- Per-mode late-window average, reusing the repository's exact convention. -/
def sampledPositiveLateWindowAverage
    {N : Nat} [NeZero N]
    (massSample : S → Lattice.PositiveMassConfig N)
    (initial : S → ParametricPhaseSpace N)
    (flow : ParametricPhaseSpace N × Real → ParametricPhaseSpace N)
    (mu T : Real) (s : S) (k : OrderedModeIndex N) : Real :=
  lateWindowAverage
    (fun t k ↦ sampledPositivePhysicalOrderedEnergyProfileAlongFlow
      massSample initial flow (s, t) k) mu T k

omit [MeasurableSpace S] in
theorem sampledPositiveLateWindowAverage_eq
    {N : Nat} [NeZero N]
    (massSample : S → Lattice.PositiveMassConfig N)
    (initial : S → ParametricPhaseSpace N)
    (flow : ParametricPhaseSpace N × Real → ParametricPhaseSpace N)
    (mu T : Real) (s : S) (k : OrderedModeIndex N) :
    sampledPositiveLateWindowAverage massSample initial flow mu T s k =
      ((1 - mu) * T)⁻¹ *
        sampledPositiveLateWindowIntegral massSample initial flow mu T s k :=
  rfl

/-- Total late-window weight in all strictly positive ordered modes. -/
def sampledPositiveLateWindowTotalWeight
    {N : Nat} [NeZero N]
    (massSample : S → Lattice.PositiveMassConfig N)
    (initial : S → ParametricPhaseSpace N)
    (flow : ParametricPhaseSpace N × Real → ParametricPhaseSpace N)
    (mu T : Real) (s : S) : Real :=
  totalWeight (sampledPositiveLateWindowAverage
    massSample initial flow mu T s)

/-- Late-window positive-mode weights normalized by their total. -/
def sampledPositiveLateWindowNormalizedWeights
    {N : Nat} [NeZero N]
    (massSample : S → Lattice.PositiveMassConfig N)
    (initial : S → ParametricPhaseSpace N)
    (flow : ParametricPhaseSpace N × Real → ParametricPhaseSpace N)
    (mu T : Real) (s : S) : OrderedModeIndex N → Real :=
  normalizedWeights (sampledPositiveLateWindowAverage
    massSample initial flow mu T s)

/-- Uniform positive-sector profile on the complete ordered index set.  The
mask is realization dependent, while the physical denominator is `N - 1`. -/
def sampledPositiveUniformWeights
    {N : Nat} [NeZero N]
    (massSample : S → Lattice.PositiveMassConfig N)
    (s : S) (k : OrderedModeIndex N) : Real :=
  if k ∈ positiveModeIndices (harmonicHermitianSample massSample s) then
    ((N - 1 : Nat) : Real)⁻¹
  else 0

/-- The complete ordered-coordinate `l1` distance from positive-mode
equipartition.  Both the observed and target profiles vanish at masked modes. -/
def sampledPositiveLateWindowL1Distance
    {N : Nat} [NeZero N]
    (massSample : S → Lattice.PositiveMassConfig N)
    (initial : S → ParametricPhaseSpace N)
    (flow : ParametricPhaseSpace N × Real → ParametricPhaseSpace N)
    (mu T : Real) (s : S) : Real :=
  l1Distance
    (sampledPositiveLateWindowNormalizedWeights
      massSample initial flow mu T s)
    (sampledPositiveUniformWeights massSample s)

theorem measurable_sampledPositiveLateWindowIntegral_apply
    {N : Nat} [NeZero N]
    (massSample : S → Lattice.PositiveMassConfig N)
    (initial : S → ParametricPhaseSpace N)
    (flow : ParametricPhaseSpace N × Real → ParametricPhaseSpace N)
    (hmass : ∀ i, Measurable fun s ↦ (massSample s).mass i)
    (hinitial : Measurable initial) (hflow : Measurable flow)
    (mu T : Real) (k : OrderedModeIndex N) :
    Measurable fun s ↦ sampledPositiveLateWindowIntegral
      massSample initial flow mu T s k := by
  unfold sampledPositiveLateWindowIntegral
  exact measurable_intervalIntegral_prod_right
    (fun st ↦ sampledPositivePhysicalOrderedEnergyProfileAlongFlow
      massSample initial flow st k)
    (measurable_sampledPositivePhysicalOrderedEnergyProfileAlongFlow_apply
      massSample initial flow hmass hinitial hflow k) (mu * T) T

theorem measurable_sampledPositiveLateWindowAverage_apply
    {N : Nat} [NeZero N]
    (massSample : S → Lattice.PositiveMassConfig N)
    (initial : S → ParametricPhaseSpace N)
    (flow : ParametricPhaseSpace N × Real → ParametricPhaseSpace N)
    (hmass : ∀ i, Measurable fun s ↦ (massSample s).mass i)
    (hinitial : Measurable initial) (hflow : Measurable flow)
    (mu T : Real) (k : OrderedModeIndex N) :
    Measurable fun s ↦ sampledPositiveLateWindowAverage
      massSample initial flow mu T s k := by
  rw [show (fun s ↦ sampledPositiveLateWindowAverage
      massSample initial flow mu T s k) =
      fun s ↦ ((1 - mu) * T)⁻¹ * sampledPositiveLateWindowIntegral
        massSample initial flow mu T s k by
    funext s
    exact sampledPositiveLateWindowAverage_eq
      massSample initial flow mu T s k]
  exact measurable_const.mul
    (measurable_sampledPositiveLateWindowIntegral_apply
      massSample initial flow hmass hinitial hflow mu T k)

theorem measurable_sampledPositiveLateWindowAverage
    {N : Nat} [NeZero N]
    (massSample : S → Lattice.PositiveMassConfig N)
    (initial : S → ParametricPhaseSpace N)
    (flow : ParametricPhaseSpace N × Real → ParametricPhaseSpace N)
    (hmass : ∀ i, Measurable fun s ↦ (massSample s).mass i)
    (hinitial : Measurable initial) (hflow : Measurable flow)
    (mu T : Real) :
    Measurable (sampledPositiveLateWindowAverage
      massSample initial flow mu T) := by
  apply measurable_pi_lambda
  intro k
  exact measurable_sampledPositiveLateWindowAverage_apply
    massSample initial flow hmass hinitial hflow mu T k

theorem measurable_sampledPositiveLateWindowTotalWeight
    {N : Nat} [NeZero N]
    (massSample : S → Lattice.PositiveMassConfig N)
    (initial : S → ParametricPhaseSpace N)
    (flow : ParametricPhaseSpace N × Real → ParametricPhaseSpace N)
    (hmass : ∀ i, Measurable fun s ↦ (massSample s).mass i)
    (hinitial : Measurable initial) (hflow : Measurable flow)
    (mu T : Real) :
    Measurable (sampledPositiveLateWindowTotalWeight
      massSample initial flow mu T) := by
  unfold sampledPositiveLateWindowTotalWeight totalWeight
  apply Finset.measurable_sum
  intro k _hk
  exact measurable_sampledPositiveLateWindowAverage_apply
    massSample initial flow hmass hinitial hflow mu T k

theorem measurable_sampledPositiveLateWindowNormalizedWeights_apply
    {N : Nat} [NeZero N]
    (massSample : S → Lattice.PositiveMassConfig N)
    (initial : S → ParametricPhaseSpace N)
    (flow : ParametricPhaseSpace N × Real → ParametricPhaseSpace N)
    (hmass : ∀ i, Measurable fun s ↦ (massSample s).mass i)
    (hinitial : Measurable initial) (hflow : Measurable flow)
    (mu T : Real) (k : OrderedModeIndex N) :
    Measurable fun s ↦ sampledPositiveLateWindowNormalizedWeights
      massSample initial flow mu T s k := by
  exact
    (measurable_sampledPositiveLateWindowAverage_apply
      massSample initial flow hmass hinitial hflow mu T k).div
    (measurable_sampledPositiveLateWindowTotalWeight
      massSample initial flow hmass hinitial hflow mu T)

theorem measurable_sampledPositiveLateWindowNormalizedWeights
    {N : Nat} [NeZero N]
    (massSample : S → Lattice.PositiveMassConfig N)
    (initial : S → ParametricPhaseSpace N)
    (flow : ParametricPhaseSpace N × Real → ParametricPhaseSpace N)
    (hmass : ∀ i, Measurable fun s ↦ (massSample s).mass i)
    (hinitial : Measurable initial) (hflow : Measurable flow)
    (mu T : Real) :
    Measurable (sampledPositiveLateWindowNormalizedWeights
      massSample initial flow mu T) := by
  apply measurable_pi_lambda
  intro k
  exact measurable_sampledPositiveLateWindowNormalizedWeights_apply
    massSample initial flow hmass hinitial hflow mu T k

theorem measurable_sampledPositiveUniformWeights_apply
    {N : Nat} [NeZero N]
    (massSample : S → Lattice.PositiveMassConfig N)
    (hmass : ∀ i, Measurable fun s ↦ (massSample s).mass i)
    (k : OrderedModeIndex N) :
    Measurable fun s ↦ sampledPositiveUniformWeights massSample s k := by
  apply Measurable.ite
  · exact measurableSet_mem_positiveModeIndices_unconditional
      (harmonicHermitianSample massSample)
      (measurable_harmonicHermitianSample massSample hmass) k
  · exact measurable_const
  · exact measurable_const

theorem measurable_sampledPositiveUniformWeights
    {N : Nat} [NeZero N]
    (massSample : S → Lattice.PositiveMassConfig N)
    (hmass : ∀ i, Measurable fun s ↦ (massSample s).mass i) :
    Measurable (sampledPositiveUniformWeights massSample) := by
  apply measurable_pi_lambda
  intro k
  exact measurable_sampledPositiveUniformWeights_apply massSample hmass k

theorem measurable_sampledPositiveLateWindowL1Distance
    {N : Nat} [NeZero N]
    (massSample : S → Lattice.PositiveMassConfig N)
    (initial : S → ParametricPhaseSpace N)
    (flow : ParametricPhaseSpace N × Real → ParametricPhaseSpace N)
    (hmass : ∀ i, Measurable fun s ↦ (massSample s).mass i)
    (hinitial : Measurable initial) (hflow : Measurable flow)
    (mu T : Real) :
    Measurable (sampledPositiveLateWindowL1Distance
      massSample initial flow mu T) := by
  unfold sampledPositiveLateWindowL1Distance l1Distance
  apply Finset.measurable_sum
  intro k _hk
  exact ((measurable_sampledPositiveLateWindowNormalizedWeights_apply
    massSample initial flow hmass hinitial hflow mu T k).sub
      (measurable_sampledPositiveUniformWeights_apply
        massSample hmass k)).abs

omit [MeasurableSpace S] in
theorem sampledPositiveLateWindowIntegral_nonneg
    {N : Nat} [NeZero N]
    (massSample : S → Lattice.PositiveMassConfig N)
    (initial : S → ParametricPhaseSpace N)
    (flow : ParametricPhaseSpace N × Real → ParametricPhaseSpace N)
    (mu T : Real) (_hmu : 0 ≤ mu) (hmuOne : mu ≤ 1) (hT : 0 ≤ T)
    (s : S) (k : OrderedModeIndex N) :
    0 ≤ sampledPositiveLateWindowIntegral
      massSample initial flow mu T s k := by
  have hinterval : mu * T ≤ T := by
    calc
      mu * T ≤ 1 * T := mul_le_mul_of_nonneg_right hmuOne hT
      _ = T := one_mul T
  exact intervalIntegral.integral_nonneg hinterval fun t _ht ↦
    sampledPositivePhysicalOrderedEnergyProfileAlongFlow_nonneg
      massSample initial flow (s, t) k

omit [MeasurableSpace S] in
theorem sampledPositiveLateWindowAverage_nonneg
    {N : Nat} [NeZero N]
    (massSample : S → Lattice.PositiveMassConfig N)
    (initial : S → ParametricPhaseSpace N)
    (flow : ParametricPhaseSpace N × Real → ParametricPhaseSpace N)
    (mu T : Real) (hmu : 0 ≤ mu) (hmuOne : mu < 1) (hT : 0 < T)
    (s : S) (k : OrderedModeIndex N) :
    0 ≤ sampledPositiveLateWindowAverage
      massSample initial flow mu T s k := by
  exact lateWindowAverage_nonneg
    (fun t k ↦ sampledPositivePhysicalOrderedEnergyProfileAlongFlow
      massSample initial flow (s, t) k)
    mu T hmu hmuOne hT
    (fun t k ↦ sampledPositivePhysicalOrderedEnergyProfileAlongFlow_nonneg
      massSample initial flow (s, t) k) k

omit [MeasurableSpace S] in
theorem sampledPositiveLateWindowTotalWeight_nonneg
    {N : Nat} [NeZero N]
    (massSample : S → Lattice.PositiveMassConfig N)
    (initial : S → ParametricPhaseSpace N)
    (flow : ParametricPhaseSpace N × Real → ParametricPhaseSpace N)
    (mu T : Real) (hmu : 0 ≤ mu) (hmuOne : mu < 1) (hT : 0 < T)
    (s : S) :
    0 ≤ sampledPositiveLateWindowTotalWeight
      massSample initial flow mu T s := by
  unfold sampledPositiveLateWindowTotalWeight totalWeight
  exact Finset.sum_nonneg fun k _hk ↦
    sampledPositiveLateWindowAverage_nonneg
      massSample initial flow mu T hmu hmuOne hT s k

/-- Positive-rational strict-threshold hitting time of the late-window
equipartition distance. -/
def sampledPositiveLateWindowRationalStrictHittingTime
    {N : Nat} [NeZero N]
    (massSample : S → Lattice.PositiveMassConfig N)
    (initial : S → ParametricPhaseSpace N)
    (flow : ParametricPhaseSpace N × Real → ParametricPhaseSpace N)
    (mu delta : Real) (s : S) : ENNReal :=
  rationalStrictDistanceThresholdHittingTime
    (fun T ↦ sampledPositiveLateWindowL1Distance
      massSample initial flow mu T s) delta

theorem measurable_sampledPositiveLateWindowRationalStrictHittingTime
    {N : Nat} [NeZero N]
    (massSample : S → Lattice.PositiveMassConfig N)
    (initial : S → ParametricPhaseSpace N)
    (flow : ParametricPhaseSpace N × Real → ParametricPhaseSpace N)
    (hmass : ∀ i, Measurable fun s ↦ (massSample s).mass i)
    (hinitial : Measurable initial) (hflow : Measurable flow)
    (mu delta : Real) :
    Measurable (sampledPositiveLateWindowRationalStrictHittingTime
      massSample initial flow mu delta) := by
  exact measurable_rationalStrictDistanceThresholdHittingTime
    (fun s T ↦ sampledPositiveLateWindowL1Distance
      massSample initial flow mu T s) delta
    (fun q ↦ measurable_sampledPositiveLateWindowL1Distance
      massSample initial flow hmass hinitial hflow mu (q : Real))

/-- Closed threshold at every rational evaluation in the real interval
`[start, start + duration]`. -/
def RationalClosedPersistsFor
    (distance : Real → Real) (delta start duration : Real) : Prop :=
  ∀ q : Rat,
    start ≤ (q : Real) → (q : Real) ≤ start + duration →
      distance (q : Real) ≤ delta

theorem measurableSet_rationalClosedPersistsFor
    (distance : S → Real → Real) (delta start duration : Real)
    (heval : ∀ q : Rat, Measurable fun s ↦ distance s (q : Real)) :
    MeasurableSet {s | RationalClosedPersistsFor
      (distance s) delta start duration} := by
  rw [show {s | RationalClosedPersistsFor
      (distance s) delta start duration} = ⋂ q : Rat,
      {s | start ≤ (q : Real) → (q : Real) ≤ start + duration →
        distance s (q : Real) ≤ delta} by
    ext s
    simp only [mem_ofPred_eq, mem_iInter]
    rfl]
  apply MeasurableSet.iInter
  intro q
  by_cases hleft : start ≤ (q : Real)
  · by_cases hright : (q : Real) ≤ start + duration
    · simpa [hleft, hright] using
        measurableSet_le (heval q) measurable_const
    · simp [hleft, hright]
  · simp [hleft]

/-- First positive rational start time whose following fixed-duration window
stays below the closed threshold at every rational evaluation. -/
def sampledPositiveLateWindowRationalPersistentHittingTime
    {N : Nat} [NeZero N]
    (massSample : S → Lattice.PositiveMassConfig N)
    (initial : S → ParametricPhaseSpace N)
    (flow : ParametricPhaseSpace N × Real → ParametricPhaseSpace N)
    (mu delta duration : Real) (s : S) : ENNReal :=
  countableFirstHittingTime
    (fun q : Rat ↦ ENNReal.ofReal (q : Real))
    (fun q s ↦ RationalClosedPersistsFor
      (fun T ↦ sampledPositiveLateWindowL1Distance
        massSample initial flow mu T s)
      delta (q : Real) duration) s

theorem measurable_sampledPositiveLateWindowRationalPersistentHittingTime
    {N : Nat} [NeZero N]
    (massSample : S → Lattice.PositiveMassConfig N)
    (initial : S → ParametricPhaseSpace N)
    (flow : ParametricPhaseSpace N × Real → ParametricPhaseSpace N)
    (hmass : ∀ i, Measurable fun s ↦ (massSample s).mass i)
    (hinitial : Measurable initial) (hflow : Measurable flow)
    (mu delta duration : Real) :
    Measurable (sampledPositiveLateWindowRationalPersistentHittingTime
      massSample initial flow mu delta duration) := by
  apply measurable_countableFirstHittingTime
  intro q
  exact measurableSet_rationalClosedPersistsFor
    (fun s T ↦ sampledPositiveLateWindowL1Distance
      massSample initial flow mu T s)
    delta (q : Real) duration
    (fun r ↦ measurable_sampledPositiveLateWindowL1Distance
      massSample initial flow hmass hinitial hflow mu (r : Real))


/-- Closed threshold at every real time in the interval
start to start + duration. -/
def RealClosedPersistsFor
    (distance : Real → Real) (delta start duration : Real) : Prop :=
  ∀ time : Real,
    start ≤ time → time ≤ start + duration → distance time ≤ delta

/-- A real-time window immediately implies its rationally sampled version. -/
theorem rationalClosedPersistsFor_of_realClosedPersistsFor
    (distance : Real → Real) (delta start duration : Real)
    (hreal : RealClosedPersistsFor distance delta start duration) :
    RationalClosedPersistsFor distance delta start duration := by
  intro q hleft hright
  exact hreal (q : Real) hleft hright

/-- For a continuous diagnostic and a positive-duration window, checking every
rational time is exactly as strong as checking every real time.  Positivity of
the duration is essential: a zero-length interval at an irrational endpoint
contains no rational sample. -/
theorem realClosedPersistsFor_of_rationalClosedPersistsFor
    (distance : Real → Real) (delta start duration : Real)
    (hduration : 0 < duration) (hcontinuous : Continuous distance)
    (hrational : RationalClosedPersistsFor distance delta start duration) :
    RealClosedPersistsFor distance delta start duration := by
  intro time hleft hright
  by_contra hnot
  have hbad : delta < distance time := lt_of_not_ge hnot
  have hopen : IsOpen {x : Real | delta < distance x} :=
    isOpen_lt continuous_const hcontinuous
  obtain ⟨epsilon, hepsilon, hball⟩ :
      ∃ epsilon > 0, Metric.ball time epsilon ⊆
        {x : Real | delta < distance x} :=
    Metric.isOpen_iff.1 hopen time hbad
  have hstartEnd : start < start + duration :=
    lt_add_of_pos_right start hduration
  have hinterior :
      max start (time - epsilon) <
        min (start + duration) (time + epsilon) := by
    apply max_lt
    · apply lt_min
      · exact hstartEnd
      · exact hleft.trans_lt (lt_add_of_pos_right time hepsilon)
    · apply lt_min
      · exact (sub_lt_self time hepsilon).trans_le hright
      · linarith
  obtain ⟨q, hqLower, hqUpper⟩ := exists_rat_btwn hinterior
  have hqStart : start ≤ (q : Real) :=
    (le_max_left start (time - epsilon)).trans hqLower.le
  have hqEnd : (q : Real) ≤ start + duration :=
    hqUpper.le.trans (min_le_left (start + duration) (time + epsilon))
  have hqLeft : time - epsilon < (q : Real) :=
    (le_max_right start (time - epsilon)).trans_lt hqLower
  have hqRight : (q : Real) < time + epsilon :=
    hqUpper.trans_le (min_le_right (start + duration) (time + epsilon))
  have hqBall : (q : Real) ∈ Metric.ball time epsilon := by
    rw [Metric.mem_ball, Real.dist_eq]
    exact (abs_lt.2 ⟨by linarith, by linarith⟩)
  have hbadQ : delta < distance (q : Real) := hball hqBall
  exact (not_lt_of_ge (hrational q hqStart hqEnd)) hbadQ

/-- Continuous diagnostics identify the measurable rational-window predicate
with the literal all-real-times predicate. -/
theorem rationalClosedPersistsFor_iff_realClosedPersistsFor
    (distance : Real → Real) (delta start duration : Real)
    (hduration : 0 < duration) (hcontinuous : Continuous distance) :
    RationalClosedPersistsFor distance delta start duration ↔
      RealClosedPersistsFor distance delta start duration := by
  constructor
  · exact realClosedPersistsFor_of_rationalClosedPersistsFor
      distance delta start duration hduration hcontinuous
  · exact rationalClosedPersistsFor_of_realClosedPersistsFor
      distance delta start duration

/-- Canonical iid random masses: the complete positive-mode late-window
distance is measurable for every fixed terminal time. -/
theorem canonical_measurable_sampledPositiveLateWindowL1Distance
    {N : Nat} [NeZero N]
    (initial : RandomEnsemble.SampleSpace → ParametricPhaseSpace N)
    (flow : ParametricPhaseSpace N × Real → ParametricPhaseSpace N)
    (hinitial : Measurable initial) (hflow : Measurable flow)
    (mu T : Real) :
    Measurable (sampledPositiveLateWindowL1Distance
      (canonicalIIDMassPhaseEnsemble.restrictPositiveMass (N := N))
      initial flow mu T) :=
  measurable_sampledPositiveLateWindowL1Distance
    (canonicalIIDMassPhaseEnsemble.restrictPositiveMass (N := N))
    initial flow
    (RandomMassOrderedProjectorBridge.measurable_restrictPositiveMass_coordinate
      canonicalIIDMassPhaseEnsemble)
    hinitial hflow mu T

end

end ArchonPhysics.RandomMassPositiveLateWindowObservable
