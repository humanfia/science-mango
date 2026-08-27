import ArchonPhysics.LennardJonesModalRemainderKineticMeanSquareBound
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-!
# Stopped-flow probability bound for the higher Lennard--Jones remainder

This module turns the volume-uniform all-mode mean-square estimate for the
force remainder beyond the local FPUT `alpha-beta` jet into an accumulated
kinetic-window estimate.  On the physical interval `0 <= t <= L / g^2`, the
per-mode root-mean-square norm of the integrated higher remainder is
`O(L * g)` with a coefficient independent of the number of sites.

For a random trajectory we then isolate an explicitly supplied measurable
good-tube event.  The stopped observable agrees with the actual accumulated
remainder on that event and is zero outside it.  Consequently every tail of
the actual remainder above its deterministic good-event bound is paid for
entirely by the probability of the event complement.  A final abstract
interface shows convergence in probability when `g -> 0` and those
complement probabilities vanish.

The result controls only the Taylor remainder beyond the cubic and quartic
FPUT force terms.  It neither controls the leading cubic interaction, proves
that the good tube has high probability, nor supplies the microscopic-to-
kinetic limit or stability of the leading flow.
-/

namespace ArchonPhysics.LennardJonesStoppedHigherRemainderProbability

open Filter MeasureTheory Set Topology
open ArchonPhysics
open ArchonPhysics.CoerciveHamiltonianPhyslib
open ArchonPhysics.LennardJonesKineticTimeForceRemainder
open ArchonPhysics.LennardJonesForceTaylorTube
open ArchonPhysics.LennardJonesModalRemainderKineticBound
open ArchonPhysics.LennardJonesModalRemainderMeanSquareBound

noncomputable section

/-! ## Deterministic all-mode accumulated remainder -/

/-- The complete vector of modal force remainders beyond the local
FPUT `alpha-beta` force. -/
def modalHigherResidualVector {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (depth r₀ g : Real)
    (q : HilbertConfiguration N) : HilbertConfiguration N :=
  WithLp.toLp 2 fun k =>
    normalizedHigherResidualModalForce m depth r₀ g q k

/-- Its Euclidean norm squared is the sum of the modal squares used by the
existing volume-uniform mean-square estimate. -/
theorem norm_sq_modalHigherResidualVector
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (depth r₀ g : Real)
    (q : HilbertConfiguration N) :
    ‖modalHigherResidualVector m depth r₀ g q‖ ^ 2 =
      ∑ k, normalizedHigherResidualModalForce m depth r₀ g q k ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  rfl

/-- Per-mode root-mean-square norm of the instantaneous all-mode higher
remainder. -/
def modalHigherResidualRMS {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (depth r₀ g : Real)
    (q : HilbertConfiguration N) : Real :=
  ‖modalHigherResidualVector m depth r₀ g q‖ / Real.sqrt N

/-- Volume-independent coefficient in the instantaneous RMS bound. -/
def higherRemainderRMSCoefficient
    (mLower r₀ rho amplitudeBound : Real) : Real :=
  Real.sqrt
    (4 * mLower⁻¹ *
      kineticForceRemainderCoefficient r₀ rho amplitudeBound ^ 2)

theorem higherRemainderRMSCoefficient_nonneg
    (mLower r₀ rho amplitudeBound : Real) :
    0 ≤ higherRemainderRMSCoefficient mLower r₀ rho amplitudeBound := by
  exact Real.sqrt_nonneg _

/-- The existing all-mode mean-square theorem is equivalently a pointwise
`O(g^3)` bound for the per-mode RMS norm. -/
theorem modalHigherResidualRMS_le_g_cubed
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N)
    (mLower : Real) (hmLower : 0 < mLower)
    (hmass : ∀ i, mLower ≤ m.mass i)
    {depth r₀ g rho amplitudeBound : Real}
    (hdepth : 0 < depth) (hr₀ : 0 < r₀) (hg : 0 < g)
    (hrho0 : 0 ≤ rho) (hrho1 : rho < 1)
    (hAmplitude : 0 ≤ amplitudeBound)
    (q : HilbertConfiguration N)
    (htube : ∀ i : Lattice.Site N,
      |g * Lattice.forwardDifference (asConfiguration q) i| ≤ rho * r₀)
    (hamplitude : ∀ i : Lattice.Site N,
      |Lattice.forwardDifference (asConfiguration q) i| ≤ amplitudeBound) :
    modalHigherResidualRMS m depth r₀ g q ≤
      higherRemainderRMSCoefficient mLower r₀ rho amplitudeBound * g ^ 3 := by
  let coefficient := kineticForceRemainderCoefficient r₀ rho amplitudeBound
  let squareCoefficient := 4 * mLower⁻¹ * coefficient ^ 2
  have hcoefficient : 0 ≤ coefficient := by
    unfold coefficient kineticForceRemainderCoefficient
    exact mul_nonneg
      (mul_nonneg (div_nonneg hr₀.le (by norm_num))
        (forceRemainderTubeConstant_pos hrho0 hrho1).le)
      (pow_nonneg (div_nonneg hAmplitude hr₀.le) 4)
  have hsquareCoefficient : 0 ≤ squareCoefficient := by
    unfold squareCoefficient
    exact mul_nonneg
      (mul_nonneg (by norm_num) (inv_nonneg.mpr hmLower.le))
      (sq_nonneg coefficient)
  have hN : 0 < (N : Real) := by
    exact_mod_cast NeZero.pos N
  have hsqrtN : 0 < Real.sqrt (N : Real) := Real.sqrt_pos.2 hN
  have hrmsNonneg :
      0 ≤ modalHigherResidualRMS m depth r₀ g q := by
    exact div_nonneg (norm_nonneg _) hsqrtN.le
  have hrightNonneg :
      0 ≤ higherRemainderRMSCoefficient
          mLower r₀ rho amplitudeBound * g ^ 3 :=
    mul_nonneg (higherRemainderRMSCoefficient_nonneg _ _ _ _)
      (pow_nonneg hg.le 3)
  apply (sq_le_sq₀ hrmsNonneg hrightNonneg).mp
  calc
    modalHigherResidualRMS m depth r₀ g q ^ 2 =
        modalHigherResidualMeanSquare m depth r₀ g q := by
      unfold modalHigherResidualRMS modalHigherResidualMeanSquare
      rw [div_pow, norm_sq_modalHigherResidualVector,
        Real.sq_sqrt hN.le]
    _ ≤ squareCoefficient * g ^ 6 := by
      simpa [squareCoefficient, coefficient] using
        modalHigherResidualMeanSquare_le_g_six
          m mLower hmLower hmass hdepth hr₀ hg hrho0 hrho1 hAmplitude
            q htube hamplitude
    _ = (higherRemainderRMSCoefficient
          mLower r₀ rho amplitudeBound * g ^ 3) ^ 2 := by
      change squareCoefficient * g ^ 6 =
        (Real.sqrt squareCoefficient * g ^ 3) ^ 2
      rw [mul_pow, Real.sq_sqrt hsquareCoefficient]
      ring

/-- The vector accumulated on the physical kinetic window. -/
def kineticWindowAccumulatedHigherResidualVector
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (depth r₀ g L : Real)
    (q : Real → HilbertConfiguration N) : HilbertConfiguration N :=
  ∫ t in 0..kineticWindowTime g L,
    modalHigherResidualVector m depth r₀ g (q t)

/-- Per-mode RMS size of the accumulated higher remainder. -/
def kineticWindowAccumulatedHigherResidualRMS
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (depth r₀ g L : Real)
    (q : Real → HilbertConfiguration N) : Real :=
  ‖kineticWindowAccumulatedHigherResidualVector m depth r₀ g L q‖ /
    Real.sqrt N

/-- On a uniform kinetic-window tube, the accumulated all-mode higher
remainder has volume-independent per-mode RMS size `O(L * g)`. -/
theorem kineticWindowAccumulatedHigherResidualRMS_le
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N)
    (mLower : Real) (hmLower : 0 < mLower)
    (hmass : ∀ i, mLower ≤ m.mass i)
    {depth r₀ g rho L amplitudeBound : Real}
    (hdepth : 0 < depth) (hr₀ : 0 < r₀) (hg : 0 < g)
    (hrho0 : 0 ≤ rho) (hrho1 : rho < 1)
    (hL : 0 ≤ L) (hAmplitude : 0 ≤ amplitudeBound)
    (q : Real → HilbertConfiguration N)
    (_hIntegrable : IntervalIntegrable
      (fun t => modalHigherResidualVector m depth r₀ g (q t))
      MeasureTheory.volume 0 (kineticWindowTime g L))
    (htube : ∀ t ∈ Icc 0 (kineticWindowTime g L),
      ∀ i : Lattice.Site N,
        |g * Lattice.forwardDifference (asConfiguration (q t)) i| ≤ rho * r₀)
    (hamplitude : ∀ t ∈ Icc 0 (kineticWindowTime g L),
      ∀ i : Lattice.Site N,
        |Lattice.forwardDifference (asConfiguration (q t)) i| ≤ amplitudeBound) :
    kineticWindowAccumulatedHigherResidualRMS m depth r₀ g L q ≤
      higherRemainderRMSCoefficient mLower r₀ rho amplitudeBound * L * g := by
  have htime : 0 ≤ kineticWindowTime g L := by
    unfold kineticWindowTime
    exact div_nonneg hL (sq_nonneg g)
  have hN : 0 < (N : Real) := by
    exact_mod_cast NeZero.pos N
  have hsqrtN : 0 < Real.sqrt (N : Real) := Real.sqrt_pos.2 hN
  let bound := higherRemainderRMSCoefficient
    mLower r₀ rho amplitudeBound * g ^ 3
  have hboundNonneg : 0 ≤ bound := by
    exact mul_nonneg (higherRemainderRMSCoefficient_nonneg _ _ _ _)
      (pow_nonneg hg.le 3)
  have hpoint : ∀ t ∈ Set.uIoc 0 (kineticWindowTime g L),
      ‖modalHigherResidualVector m depth r₀ g (q t)‖ ≤
        bound * Real.sqrt N := by
    intro t ht
    have htIcc : t ∈ Icc 0 (kineticWindowTime g L) := by
      simpa only [uIcc_of_le htime] using Set.uIoc_subset_uIcc ht
    have hrms := modalHigherResidualRMS_le_g_cubed
      m mLower hmLower hmass hdepth hr₀ hg hrho0 hrho1 hAmplitude
        (q t) (htube t htIcc) (hamplitude t htIcc)
    change ‖modalHigherResidualVector m depth r₀ g (q t)‖ /
      Real.sqrt N ≤ bound at hrms
    exact (div_le_iff₀ hsqrtN).mp hrms
  have hintegral :
      ‖∫ t in 0..kineticWindowTime g L,
          modalHigherResidualVector m depth r₀ g (q t)‖ ≤
        (bound * Real.sqrt N) * |kineticWindowTime g L - 0| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    exact hpoint
  unfold kineticWindowAccumulatedHigherResidualRMS
    kineticWindowAccumulatedHigherResidualVector
  calc
    ‖∫ t in 0..kineticWindowTime g L,
        modalHigherResidualVector m depth r₀ g (q t)‖ / Real.sqrt N ≤
      ((bound * Real.sqrt N) * |kineticWindowTime g L - 0|) /
        Real.sqrt N := (div_le_div_iff_of_pos_right hsqrtN).2 hintegral
    _ = higherRemainderRMSCoefficient
          mLower r₀ rho amplitudeBound * L * g := by
      rw [sub_zero, abs_of_nonneg htime]
      unfold bound kineticWindowTime
      field_simp [ne_of_gt hg, ne_of_gt hsqrtN]

/-! ## Measurable good tube and stopped observable -/

variable {Omega : Type*} [MeasurableSpace Omega]

/-- The exact finite-window tube and amplitude event used by the deterministic
estimate.  Its measurability is deliberately a separate hypothesis below:
an uncountable time intersection does not follow from pointwise measurability
alone. -/
def kineticWindowGoodTubeEvent
    {N : Nat} [NeZero N]
    (r₀ g rho L amplitudeBound : Real)
    (q : Omega → Real → HilbertConfiguration N) : Set Omega :=
  {omega |
    (∀ t ∈ Icc 0 (kineticWindowTime g L), ∀ i : Lattice.Site N,
      |g * Lattice.forwardDifference (asConfiguration (q omega t)) i| ≤ rho * r₀) ∧
    (∀ t ∈ Icc 0 (kineticWindowTime g L), ∀ i : Lattice.Site N,
      |Lattice.forwardDifference (asConfiguration (q omega t)) i| ≤ amplitudeBound)}

/-- The actual accumulated higher-remainder observable. -/
def randomAccumulatedHigherResidualRMS
    {N : Nat} [NeZero N]
    (m : Omega → Lattice.PositiveMassConfig N)
    (depth r₀ g L : Real)
    (q : Omega → Real → HilbertConfiguration N) : Omega → Real :=
  fun omega => kineticWindowAccumulatedHigherResidualRMS
    (m omega) depth r₀ g L (q omega)

omit [MeasurableSpace Omega] in
/-- The accumulated RMS observable is nonnegative for every sample. -/
theorem randomAccumulatedHigherResidualRMS_nonneg
    {N : Nat} [NeZero N]
    (m : Omega → Lattice.PositiveMassConfig N)
    (depth r₀ g L : Real)
    (q : Omega → Real → HilbertConfiguration N)
    (omega : Omega) :
    0 ≤ randomAccumulatedHigherResidualRMS m depth r₀ g L q omega := by
  unfold randomAccumulatedHigherResidualRMS
    kineticWindowAccumulatedHigherResidualRMS
  exact div_nonneg (norm_nonneg _) (Real.sqrt_nonneg _)

/-- Stop the observable at the boundary of the supplied good event. -/
def stoppedAccumulatedHigherResidualRMS
    {N : Nat} [NeZero N]
    (m : Omega → Lattice.PositiveMassConfig N)
    (depth r₀ g rho L amplitudeBound : Real)
    (q : Omega → Real → HilbertConfiguration N) : Omega → Real := by
  classical
  exact fun omega =>
    if omega ∈ kineticWindowGoodTubeEvent r₀ g rho L amplitudeBound q then
      randomAccumulatedHigherResidualRMS m depth r₀ g L q omega
    else 0

/-- Data needed to apply the deterministic estimate on a measurable random
good-tube event.  No probability estimate for that event is hidden here. -/
structure MeasurableGoodTubeData
    {N : Nat} [NeZero N]
    (m : Omega → Lattice.PositiveMassConfig N)
    (mLower depth r₀ g rho L amplitudeBound : Real)
    (q : Omega → Real → HilbertConfiguration N) : Prop where
  goodEvent_measurable : MeasurableSet
    (kineticWindowGoodTubeEvent r₀ g rho L amplitudeBound q)
  mass_lower : ∀ omega i, mLower ≤ (m omega).mass i
  vector_intervalIntegrable :
    ∀ omega ∈ kineticWindowGoodTubeEvent r₀ g rho L amplitudeBound q,
      IntervalIntegrable
        (fun t => modalHigherResidualVector
          (m omega) depth r₀ g (q omega t))
        MeasureTheory.volume 0 (kineticWindowTime g L)


/-- Measurability of the actual accumulated observable and of the good event
gives measurability of its stopped version. -/
theorem measurable_stoppedAccumulatedHigherResidualRMS
    {N : Nat} [NeZero N]
    (m : Omega → Lattice.PositiveMassConfig N)
    (mLower depth r₀ g rho L amplitudeBound : Real)
    (q : Omega → Real → HilbertConfiguration N)
    (data : MeasurableGoodTubeData
      m mLower depth r₀ g rho L amplitudeBound q)
    (hactual : Measurable
      (randomAccumulatedHigherResidualRMS m depth r₀ g L q)) :
    Measurable (stoppedAccumulatedHigherResidualRMS
      m depth r₀ g rho L amplitudeBound q) := by
  classical
  unfold stoppedAccumulatedHigherResidualRMS
  exact Measurable.ite data.goodEvent_measurable hactual measurable_const
/-- On the good event the random observable satisfies the same deterministic
volume-uniform bound. -/
theorem randomAccumulatedHigherResidualRMS_le_on_good
    {N : Nat} [NeZero N]
    (m : Omega → Lattice.PositiveMassConfig N)
    (mLower : Real) (hmLower : 0 < mLower)
    {depth r₀ g rho L amplitudeBound : Real}
    (hdepth : 0 < depth) (hr₀ : 0 < r₀) (hg : 0 < g)
    (hrho0 : 0 ≤ rho) (hrho1 : rho < 1)
    (hL : 0 ≤ L) (hAmplitude : 0 ≤ amplitudeBound)
    (q : Omega → Real → HilbertConfiguration N)
    (data : MeasurableGoodTubeData
      m mLower depth r₀ g rho L amplitudeBound q)
    {omega : Omega}
    (homega : omega ∈
      kineticWindowGoodTubeEvent r₀ g rho L amplitudeBound q) :
    randomAccumulatedHigherResidualRMS m depth r₀ g L q omega ≤
      higherRemainderRMSCoefficient mLower r₀ rho amplitudeBound * L * g := by
  rcases homega with ⟨htube, hamplitude⟩
  exact kineticWindowAccumulatedHigherResidualRMS_le
    (m omega) mLower hmLower (data.mass_lower omega)
      hdepth hr₀ hg hrho0 hrho1 hL hAmplitude (q omega)
      (data.vector_intervalIntegrable omega ⟨htube, hamplitude⟩)
      htube hamplitude

omit [MeasurableSpace Omega] in
/-- The stopped observable agrees with the actual one on the good event. -/
theorem stoppedAccumulatedHigherResidualRMS_eq_on_good
    {N : Nat} [NeZero N]
    (m : Omega → Lattice.PositiveMassConfig N)
    (depth r₀ g rho L amplitudeBound : Real)
    (q : Omega → Real → HilbertConfiguration N)
    {omega : Omega}
    (homega : omega ∈
      kineticWindowGoodTubeEvent r₀ g rho L amplitudeBound q) :
    stoppedAccumulatedHigherResidualRMS
        m depth r₀ g rho L amplitudeBound q omega =
      randomAccumulatedHigherResidualRMS m depth r₀ g L q omega := by
  simp [stoppedAccumulatedHigherResidualRMS, homega]


/-- The stopped observable satisfies the deterministic bound on every sample;
outside the good event it is exactly zero. -/
theorem stoppedAccumulatedHigherResidualRMS_le
    {N : Nat} [NeZero N]
    (m : Omega → Lattice.PositiveMassConfig N)
    (mLower : Real) (hmLower : 0 < mLower)
    {depth r₀ g rho L amplitudeBound : Real}
    (hdepth : 0 < depth) (hr₀ : 0 < r₀) (hg : 0 < g)
    (hrho0 : 0 ≤ rho) (hrho1 : rho < 1)
    (hL : 0 ≤ L) (hAmplitude : 0 ≤ amplitudeBound)
    (q : Omega → Real → HilbertConfiguration N)
    (data : MeasurableGoodTubeData
      m mLower depth r₀ g rho L amplitudeBound q)
    (omega : Omega) :
    stoppedAccumulatedHigherResidualRMS
        m depth r₀ g rho L amplitudeBound q omega ≤
      higherRemainderRMSCoefficient mLower r₀ rho amplitudeBound * L * g := by
  classical
  by_cases hgood : omega ∈
      kineticWindowGoodTubeEvent r₀ g rho L amplitudeBound q
  · rw [stoppedAccumulatedHigherResidualRMS_eq_on_good
      m depth r₀ g rho L amplitudeBound q hgood]
    exact randomAccumulatedHigherResidualRMS_le_on_good
      m mLower hmLower hdepth hr₀ hg hrho0 hrho1 hL hAmplitude q data hgood
  · simp only [stoppedAccumulatedHigherResidualRMS, hgood, if_false]
    exact mul_nonneg
      (mul_nonneg (higherRemainderRMSCoefficient_nonneg _ _ _ _) hL)
      hg.le
/-- A threshold strictly above the deterministic good-event bound can fail
only on the complement of the good-tube event. -/
theorem accumulatedHigherResidual_tail_subset_good_compl
    {N : Nat} [NeZero N]
    (m : Omega → Lattice.PositiveMassConfig N)
    (mLower : Real) (hmLower : 0 < mLower)
    {depth r₀ g rho L amplitudeBound threshold : Real}
    (hdepth : 0 < depth) (hr₀ : 0 < r₀) (hg : 0 < g)
    (hrho0 : 0 ≤ rho) (hrho1 : rho < 1)
    (hL : 0 ≤ L) (hAmplitude : 0 ≤ amplitudeBound)
    (q : Omega → Real → HilbertConfiguration N)
    (data : MeasurableGoodTubeData
      m mLower depth r₀ g rho L amplitudeBound q)
    (hthreshold :
      higherRemainderRMSCoefficient mLower r₀ rho amplitudeBound * L * g <
        threshold) :
    {omega | threshold ≤
      randomAccumulatedHigherResidualRMS m depth r₀ g L q omega} ⊆
      (kineticWindowGoodTubeEvent r₀ g rho L amplitudeBound q)ᶜ := by
  intro omega htail hgood
  have hbound := randomAccumulatedHigherResidualRMS_le_on_good
    m mLower hmLower hdepth hr₀ hg hrho0 hrho1 hL hAmplitude q data hgood
  change threshold ≤
    randomAccumulatedHigherResidualRMS m depth r₀ g L q omega at htail
  linarith

/-- Probability-budget form of the stopped-flow estimate. -/
theorem measureReal_accumulatedHigherResidual_tail_le_good_compl
    (probability : Measure Omega) [IsProbabilityMeasure probability]
    {N : Nat} [NeZero N]
    (m : Omega → Lattice.PositiveMassConfig N)
    (mLower : Real) (hmLower : 0 < mLower)
    {depth r₀ g rho L amplitudeBound threshold : Real}
    (hdepth : 0 < depth) (hr₀ : 0 < r₀) (hg : 0 < g)
    (hrho0 : 0 ≤ rho) (hrho1 : rho < 1)
    (hL : 0 ≤ L) (hAmplitude : 0 ≤ amplitudeBound)
    (q : Omega → Real → HilbertConfiguration N)
    (data : MeasurableGoodTubeData
      m mLower depth r₀ g rho L amplitudeBound q)
    (hthreshold :
      higherRemainderRMSCoefficient mLower r₀ rho amplitudeBound * L * g <
        threshold) :
    probability.real {omega | threshold ≤
        randomAccumulatedHigherResidualRMS m depth r₀ g L q omega} ≤
      probability.real
        (kineticWindowGoodTubeEvent r₀ g rho L amplitudeBound q)ᶜ := by
  apply measureReal_mono (h₂ := by finiteness)
  exact accumulatedHigherResidual_tail_subset_good_compl
    m mLower hmLower hdepth hr₀ hg hrho0 hrho1 hL hAmplitude q data hthreshold

/-! ## Abstract joint-limit interface -/

/-- A transparent family-level certificate for applying the good/bad estimate
when the finite volume may vary with the family index.  The construction
above supplies `error_le_on_good` separately at every volume; the remaining
field `good_compl_probability_zero` is precisely the unproved tube-persistence
probability input. -/
structure VanishingGoodEventRemainderCertificate
    (probability : Measure Omega)
    (coupling : Nat → Real) (coefficient : Real)
    (error : Nat → Omega → Real) where
  goodEvent : Nat → Set Omega
  goodEvent_measurable : ∀ j, MeasurableSet (goodEvent j)
  coupling_nonneg : ∀ j, 0 ≤ coupling j
  coefficient_nonneg : 0 ≤ coefficient
  error_nonneg : ∀ j omega, 0 ≤ error j omega
  error_measurable : ∀ j, Measurable (error j)
  error_le_on_good : ∀ j omega, omega ∈ goodEvent j →
    error j omega ≤ coefficient * coupling j
  good_compl_probability_zero : Tendsto
    (fun j => probability.real (goodEvent j)ᶜ) atTop (nhds 0)

/-- Tail probability is bounded by the explicit good-event complement once
the deterministic remainder scale lies below the requested threshold. -/
theorem VanishingGoodEventRemainderCertificate.measureReal_tail_le_compl
    (probability : Measure Omega) [IsProbabilityMeasure probability]
    (coupling : Nat → Real) (coefficient : Real)
    (error : Nat → Omega → Real)
    (certificate : VanishingGoodEventRemainderCertificate
      probability coupling coefficient error)
    {j : Nat} {threshold : Real}
    (hthreshold : coefficient * coupling j < threshold) :
    probability.real {omega | threshold ≤ error j omega} ≤
      probability.real (certificate.goodEvent j)ᶜ := by
  apply measureReal_mono (h₂ := by finiteness)
  intro omega htail hgood
  have hbound := certificate.error_le_on_good j omega hgood
  change threshold ≤ error j omega at htail
  linarith

/-- If the coupling and the explicit bad-event budget both vanish, the
higher-remainder error converges to zero in probability.  This theorem does
not identify the limit of the retained leading FPUT dynamics. -/
theorem VanishingGoodEventRemainderCertificate.tendstoInMeasure_zero
    (probability : Measure Omega) [IsProbabilityMeasure probability]
    (coupling : Nat → Real) (coefficient : Real)
    (error : Nat → Omega → Real)
    (certificate : VanishingGoodEventRemainderCertificate
      probability coupling coefficient error)
    (hcoupling : Tendsto coupling atTop (nhds 0)) :
    TendstoInMeasure probability error atTop (fun _omega => 0) := by
  rw [tendstoInMeasure_iff_measureReal_dist]
  intro epsilon hepsilon
  have hscale : Tendsto (fun j => coefficient * coupling j)
      atTop (nhds 0) := by
    simpa using (tendsto_const_nhds.mul hcoupling)
  have hsmall : ∀ᶠ j in atTop, coefficient * coupling j < epsilon :=
    hscale.eventually (Iio_mem_nhds hepsilon)
  have htail : ∀ᶠ j in atTop,
      probability.real {omega | epsilon ≤ error j omega} ≤
        probability.real (certificate.goodEvent j)ᶜ := by
    filter_upwards [hsmall] with j hj
    exact certificate.measureReal_tail_le_compl
      probability coupling coefficient error hj
  have hdist : (fun j => probability.real
      {omega | epsilon ≤ dist (error j omega) 0}) =
      fun j => probability.real {omega | epsilon ≤ error j omega} := by
    funext j
    congr 2
    ext omega
    simp [abs_of_nonneg (certificate.error_nonneg j omega)]
  rw [hdist]
  exact squeeze_zero'
    (Eventually.of_forall fun _j => measureReal_nonneg)
    htail certificate.good_compl_probability_zero

end

end ArchonPhysics.LennardJonesStoppedHigherRemainderProbability
