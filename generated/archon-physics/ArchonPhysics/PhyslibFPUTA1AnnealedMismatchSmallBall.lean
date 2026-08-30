import ArchonPhysics.PhyslibFPUTA1A2NonresonantHistorySplit
import ArchonPhysics.CubicVertexInfraredBound
import ArchonPhysics.PhyslibFPUTAfterSecondPicardEnergyEnvelope
import ArchonPhysics.UniformRandomMassHarmonicSpectrumBound
import ArchonPhysics.FrozenAndersonOneSiteSpectralAveraging
import ArchonPhysics.QuantitativeJacobianPushforward
import ArchonPhysics.ActualTwoMassChildRepeatedAnnealedReconstruction
import ArchonPhysics.RandomMassOrderedProjectorBridge
import ArchonPhysics.MeasurableOrderedModeCoupling

/-!
# Annealed actual A1 near-mismatch reduction and its one-denominator gap

This module connects the static near sector in
`PhyslibFPUTA1A2NonresonantHistorySplit` to the frozen iid random-mass law.
It does three unconditional finite-volume jobs:

* the actual ordered-frequency A1 mismatch is a measurable random variable;
* every static A1 coefficient is at most `2 * |kappa| * R^2` when the modal
  radii are bounded by `R`;
* the annealed near coefficient mass is bounded by that ceiling times the
  finite sum of the actual one-denominator small-ball probabilities.

The scalar averaging endpoint then freezes every mass except a selected iid
pair.  On the second coordinate it applies the sharp one-site density bound
`5 / 2`.  A good-set version retains the complement mass explicitly.  On the
full mass support, a derivative determinant lower bound `jacLower` and
injectivity give the concrete bound

`(5 / 2) * (ENNReal.ofReal jacLower)⁻¹ * ENNReal.ofReal (2 * delta)`.

The pair/complement reconstruction is exact, so a transversality estimate
uniform in the frozen environment lifts to the original ensemble.  This
pinpoints the remaining model-specific gap: for every relevant signed A1
mismatch one must prove a one-coordinate derivative lower bound and
injectivity (or control the displayed bad-Jacobian mass).  Existing simple
spectrum and projector measurability make the random variable legitimate,
but do not supply that non-cancellation.  A zero interaction coefficient is
harmless for the upper bound; a zero mismatch derivative is the genuine
degeneracy.

No phase variable occurs below.  In particular, initial-only Haar or Gaussian
phases, block independence, and re-Haar are irrelevant to this static mass
average.  The file fixes finite `N`, takes no `g,N` joint limit, introduces no
kinetic window `tau ∈ [0,delta]`, and proves no equidistribution statement.
It also controls no nonlinear memory or recollision remainder.  Consequently
these finite-volume one-denominator estimates are inputs to a finite union
bound for ordered/branching IBP histories; by themselves they are not a
Markov closure or a kinetic-scale theorem.
-/

namespace ArchonPhysics.PhyslibFPUTA1AnnealedMismatchSmallBall

open ArchonPhysics
open ArchonPhysics.ActualTwoMassChildRepeatedAnnealedReconstruction
open ArchonPhysics.ActualTwoMassSpectralChart
open ArchonPhysics.CubicVertexInfraredBound
open ArchonPhysics.ForcedComplexModeDuhamel
open ArchonPhysics.FreeFPUTDuhamelResonanceBridge
open ArchonPhysics.FreeFPUTMismatchPhaseExpansion
open ArchonPhysics.FreeFPUTTensorPhaseExpansion
open ArchonPhysics.FrozenAndersonOneSiteSpectralAveraging
open ArchonPhysics.HarmonicModes
open ArchonPhysics.IIDMassPairFiniteVolumeReconstruction
open ArchonPhysics.IIDMassTripleFiniteEnvironment
open ArchonPhysics.MeasurableOrderedModeCoupling.Harmonic
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.ModeCoupling
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.OrderedSingleModeProjector
open ArchonPhysics.OrderedSpectrumContinuity
open ArchonPhysics.PhyslibFPUTA1A2NonresonantHistorySplit
open ArchonPhysics.PhyslibFPUTAfterSecondPicardEnergyEnvelope
open ArchonPhysics.PhyslibFPUTFirstPicardDecomposition
open ArchonPhysics.QuantitativeJacobianPushforward
open ArchonPhysics.RandomEnsemble
open ArchonPhysics.RandomMassOrderedProjectorBridge
open ArchonPhysics.TwoParameterSpectralAveragingAtlas
open ArchonPhysics.UniformRandomMassHarmonicSpectrumBound
open MeasureTheory Set
open scoped BigOperators ENNReal

noncomputable section

/-- Measurability of an actual signed quadratic mismatch follows solely from
coordinatewise measurability of the positive mass configuration.  Ordered
frequencies make this statement global, including the nonsimple locus. -/
theorem measurable_quadraticPhaseMismatch_of_mass_coordinates
    {X : Type*} [MeasurableSpace X]
    {N : Nat} [NeZero N]
    (massSample : X → Lattice.PositiveMassConfig N)
    (hmass : ∀ site, Measurable fun sample => (massSample sample).mass site)
    (observed : Lattice.Site N) (term : QuadraticPhaseTerm N) :
    Measurable fun sample =>
      quadraticPhaseMismatch (modeFrequency (massSample sample)) observed term := by
  have hmatrix : Measurable fun sample =>
      harmonicHermitian (massSample sample) := by
    apply Measurable.subtype_mk
    exact MeasurableHarmonicData.measurable_massWeightedHarmonicMatrix_of_coordinate
      massSample hmass
  have hordered : Measurable fun sample mode =>
      orderedModeFrequency (harmonicHermitian (massSample sample)) mode :=
    measurable_orderedModeFrequencies_unconditional
      (fun sample => harmonicHermitian (massSample sample)) hmatrix
  have hfrequency : ∀ mode : Lattice.Site N,
      Measurable fun sample => modeFrequency (massSample sample) mode := by
    intro mode
    let ordered := orderedIndexEquiv.symm mode
    have h : Measurable fun sample =>
        orderedModeFrequency (harmonicHermitian (massSample sample)) ordered :=
      hordered.eval
    simpa [ordered, orderedModeFrequency_harmonicHermitian_eq] using h
  unfold quadraticPhaseMismatch outputChargeMismatch chargeFrequency
  apply (hfrequency observed).sub
  apply Finset.measurable_sum
  intro mode hmode
  exact measurable_const.mul (hfrequency mode)

variable {Omega : Type*} [MeasurableSpace Omega]

/-- The actual signed A1 mismatch under the initial frozen iid mass sample. -/
def physlibA1MismatchSample
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N]
    (observed : Lattice.Site N) (term : QuadraticPhaseTerm N)
    (sample : Omega) : Real :=
  quadraticPhaseMismatch
    (modeFrequency (ensemble.restrictPositiveMass (N := N) sample))
    observed term

theorem measurable_physlibA1MismatchSample
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N]
    (observed : Lattice.Site N) (term : QuadraticPhaseTerm N) :
    Measurable (physlibA1MismatchSample ensemble observed term) := by
  exact measurable_quadraticPhaseMismatch_of_mass_coordinates
    (ensemble.restrictPositiveMass (N := N))
    (measurable_restrictPositiveMass_coordinate ensemble) observed term

/-- The pushforward law of one actual signed A1 mismatch. -/
def physlibA1MismatchLaw
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N]
    (observed : Lattice.Site N) (term : QuadraticPhaseTerm N) : Measure Real :=
  Measure.map (physlibA1MismatchSample ensemble observed term)
    ensemble.probability

/-- The centered interval mass of the mismatch law is exactly the actual
initial-mass small-ball probability. -/
theorem physlibA1MismatchLaw_Ioo
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N]
    (observed : Lattice.Site N) (term : QuadraticPhaseTerm N)
    (delta : Real) :
    physlibA1MismatchLaw ensemble observed term (Ioo (-delta) delta) =
      ensemble.probability
        {sample |
          |physlibA1MismatchSample ensemble observed term sample| < delta} := by
  unfold physlibA1MismatchLaw
  rw [Measure.map_apply
    (measurable_physlibA1MismatchSample ensemble observed term)
    measurableSet_Ioo]
  congr 1
  ext sample
  simp only [Set.mem_preimage, Set.mem_Ioo, Set.mem_ofPred_eq, abs_lt]

/-- The exact number of signed A1 monomials at volume `N`: two input modes
and two binary phase signs. -/
theorem card_quadraticPhaseTerm (N : Nat) [NeZero N] :
    Fintype.card (QuadraticPhaseTerm N) = 4 * N ^ 2 := by
  simp [QuadraticPhaseTerm]
  ring

/-- A deterministic finite-family reduction: a uniform coefficient ceiling
turns annealed near coefficient mass into the sum of the corresponding
measurable mismatch-event probabilities.  Coefficient measurability is not
needed. -/
theorem annealed_nearCoefficientAbsMass_le_sum_mismatchProbability
    {X J : Type*} [MeasurableSpace X] [Fintype J]
    (mu : Measure X) (delta C : Real)
    (mismatch : X → J → Real)
    (coefficient : X → J → Complex)
    (hmeas : ∀ j, Measurable fun sample => mismatch sample j)
    (hcoefficient : ∀ sample j, ‖coefficient sample j‖ <= C) :
    (∫⁻ sample,
        ENNReal.ofReal
          (coefficientAbsMassOn
            (nearMismatchIndices delta (mismatch sample))
            (coefficient sample)) ∂mu) <=
      ENNReal.ofReal C *
        ∑ j : J, mu {sample | |mismatch sample j| < delta} := by
  calc
    (∫⁻ sample,
        ENNReal.ofReal
          (coefficientAbsMassOn
            (nearMismatchIndices delta (mismatch sample))
            (coefficient sample)) ∂mu) <=
      ∫⁻ sample,
        ∑ j : J,
          if |mismatch sample j| < delta then ENNReal.ofReal C else 0 ∂mu := by
      apply lintegral_mono
      intro sample
      unfold coefficientAbsMassOn nearMismatchIndices
      change ENNReal.ofReal
        (∑ j ∈ Finset.univ.filter (fun j => |mismatch sample j| < delta),
          ‖coefficient sample j‖) <= _
      rw [ENNReal.ofReal_sum_of_nonneg]
      · simp only [Finset.sum_filter]
        apply Finset.sum_le_sum
        intro j hj
        split_ifs with hnear
        · exact ENNReal.ofReal_le_ofReal (hcoefficient sample j)
        · exact le_rfl
      · intro j hj
        exact norm_nonneg _
    _ = ∑ j : J,
        ∫⁻ sample,
          if |mismatch sample j| < delta then ENNReal.ofReal C else 0 ∂mu := by
      rw [lintegral_finsetSum Finset.univ]
      intro j hj
      exact Measurable.ite
        (measurableSet_lt (hmeas j).abs measurable_const)
        measurable_const measurable_const
    _ = ∑ j : J,
        ENNReal.ofReal C * mu {sample | |mismatch sample j| < delta} := by
      apply Finset.sum_congr rfl
      intro j hj
      let event : Set X := {sample | |mismatch sample j| < delta}
      have hevent : MeasurableSet event :=
        measurableSet_lt (hmeas j).abs measurable_const
      change (∫⁻ sample,
          if sample ∈ event then ENNReal.ofReal C else 0 ∂mu) = _
      rw [show (fun sample =>
          if sample ∈ event then ENNReal.ofReal C else 0) =
          event.indicator (fun _ => ENNReal.ofReal C) by
        funext sample
        simp [Set.indicator_apply]]
      exact lintegral_indicator_const hevent (ENNReal.ofReal C)
    _ = ENNReal.ofReal C *
        ∑ j : J, mu {sample | |mismatch sample j| < delta} := by
      rw [Finset.mul_sum]

/-- Uniform actual FPUT A1 coefficient ceiling on the random-mass spectral
band.  The physical output normalization is canceled by the acoustic factor
in the cubic interaction tensor; an exactly zero output frequency gives a
zero coefficient. -/
theorem physlibA1StaticCoefficient_le_two_absKappa_radiusSq
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa R : Real)
    (hR : 0 <= R)
    (hfrequency : ∀ mode, modeFrequencySq m mode <= 5)
    (radius : Lattice.Site N → Real)
    (hradius : ∀ mode, |radius mode| <= R)
    (observed : Lattice.Site N) (term : QuadraticPhaseTerm N) :
    ‖freeQuadraticDuhamelCoefficient
        (physlibQuadraticCoupling m kappa 1 observed)
        m observed radius term‖ <=
      2 * |kappa| * R ^ 2 := by
  let w0 := modeFrequency m observed
  let w1 := modeFrequency m (term.1 0)
  let w2 := modeFrequency m (term.1 1)
  let d := interactionTensor m 3 (Fin.cons observed term.1)
  have hw0 : 0 <= w0 := modeFrequency_nonneg m observed
  have hw1 : 0 <= w1 := modeFrequency_nonneg m (term.1 0)
  have hw2 : 0 <= w2 := modeFrequency_nonneg m (term.1 1)
  have hw0sq : w0 ^ 2 <= 5 := by
    simpa [w0, modeFrequency_sq] using hfrequency observed
  have hw1sq : w1 ^ 2 <= 5 := by
    simpa [w1, modeFrequency_sq] using hfrequency (term.1 0)
  have hw2sq : w2 ^ 2 <= 5 := by
    simpa [w2, modeFrequency_sq] using hfrequency (term.1 1)
  by_cases hw0zero : w0 = 0
  · have hzero : freeQuadraticDuhamelCoefficient
        (physlibQuadraticCoupling m kappa 1 observed)
        m observed radius term = 0 := by
      simp [freeQuadraticDuhamelCoefficient, physlibQuadraticCoupling,
        forcedModeSource, w0, hw0zero]
    rw [hzero, norm_zero]
    positivity
  have hw0pos : 0 < w0 := lt_of_le_of_ne hw0 (Ne.symm hw0zero)
  have hsqrtPos : 0 < Real.sqrt (2 * w0) := Real.sqrt_pos.2 (by positivity)
  have hdsq0 := interactionTensor_three_sq_le m (Fin.cons observed term.1)
  have hcons0 :
      (Fin.cons observed term.1 : Fin 3 → Lattice.Site N) (0 : Fin 3) =
        observed := by rfl
  have hcons1 :
      (Fin.cons observed term.1 : Fin 3 → Lattice.Site N) (1 : Fin 3) =
        term.1 0 := by rfl
  have hcons2 :
      (Fin.cons observed term.1 : Fin 3 → Lattice.Site N) (2 : Fin 3) =
        term.1 1 := by rfl
  have hdsq : d ^ 2 <= w0 ^ 2 * w1 ^ 2 * w2 ^ 2 := by
    rw [hcons0, hcons1, hcons2, ← modeFrequency_sq,
      ← modeFrequency_sq, ← modeFrequency_sq] at hdsq0
    simpa [d, w0, w1, w2] using hdsq0
  have hdsq' : d ^ 2 <= 25 * w0 ^ 2 := by
    calc
      d ^ 2 <= w0 ^ 2 * w1 ^ 2 * w2 ^ 2 := hdsq
      _ <= w0 ^ 2 * 5 * 5 := by gcongr
      _ = 25 * w0 ^ 2 := by ring
  have hw0three : w0 <= 3 := by nlinarith
  have hdtarget : |d| ^ 2 <= (7 * Real.sqrt (2 * w0)) ^ 2 := by
    rw [sq_abs, mul_pow, Real.sq_sqrt (by positivity : 0 <= 2 * w0)]
    nlinarith
  have hd : |d| <= 7 * Real.sqrt (2 * w0) :=
    (sq_le_sq₀ (abs_nonneg d) (by positivity)).mp hdtarget
  have hcoupling :
      ‖physlibQuadraticCoupling m kappa 1 observed‖ =
        |kappa| / Real.sqrt (2 * w0) := by
    simpa [physlibQuadraticCoupling, w0] using
      (norm_forcedModeSource hw0pos (-(kappa * 1)))
  unfold freeQuadraticDuhamelCoefficient quadraticPhaseCoefficient
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  rw [hcoupling]
  have hr0 := hradius (term.1 0)
  have hr1 := hradius (term.1 1)
  change |kappa| / Real.sqrt (2 * w0) *
      (|d| * |radius (term.1 0) / 2| * |radius (term.1 1) / 2|) <= _
  have hpref : 0 <= |kappa| / Real.sqrt (2 * w0) := by positivity
  have hr0half : |radius (term.1 0) / 2| <= R / 2 := by
    rw [abs_div, abs_of_pos (by norm_num : (0 : Real) < 2)]
    exact div_le_div_of_nonneg_right hr0 (by norm_num)
  have hr1half : |radius (term.1 1) / 2| <= R / 2 := by
    rw [abs_div, abs_of_pos (by norm_num : (0 : Real) < 2)]
    exact div_le_div_of_nonneg_right hr1 (by norm_num)
  calc
    |kappa| / Real.sqrt (2 * w0) *
          (|d| * |radius (term.1 0) / 2| * |radius (term.1 1) / 2|) <=
        |kappa| / Real.sqrt (2 * w0) *
          ((7 * Real.sqrt (2 * w0)) *
            |radius (term.1 0) / 2| * |radius (term.1 1) / 2|) := by
      gcongr
    _ <= |kappa| / Real.sqrt (2 * w0) *
          ((7 * Real.sqrt (2 * w0)) *
            (R / 2) * |radius (term.1 1) / 2|) := by
      gcongr
    _ <= |kappa| / Real.sqrt (2 * w0) *
          ((7 * Real.sqrt (2 * w0)) * (R / 2) * (R / 2)) := by
      gcongr
    _ = (7 / 4) * |kappa| * R ^ 2 := by
      field_simp [ne_of_gt hsqrtPos]
      ring
    _ <= 2 * |kappa| * R ^ 2 := by
      have hnonneg : 0 <= |kappa| * R ^ 2 := by positivity
      nlinarith

/-- Annealed static coefficient mass of the actual A1 near-mismatch sector. -/
def physlibA1AnnealedNearStaticAbsMass
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N]
    (kappa delta : Real) (radius : Lattice.Site N → Real)
    (observed : Lattice.Site N) : ENNReal :=
  ∫⁻ sample,
    ENNReal.ofReal
      (physlibA1NearStaticAbsMass
        (ensemble.restrictPositiveMass (N := N) sample)
        kappa delta radius observed) ∂ensemble.probability

/-- Unconditional finite-volume reduction of the A1 near sector to actual
ordered-frequency mismatch laws.  No smallness premise is used here. -/
theorem physlibA1AnnealedNearStaticAbsMass_le_sum_mismatchLaw
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N]
    (kappa delta R : Real) (hR : 0 <= R)
    (radius : Lattice.Site N → Real)
    (hradius : ∀ mode, |radius mode| <= R)
    (observed : Lattice.Site N) :
    physlibA1AnnealedNearStaticAbsMass
        ensemble kappa delta radius observed <=
      ENNReal.ofReal (2 * |kappa| * R ^ 2) *
        ∑ term : QuadraticPhaseTerm N,
          physlibA1MismatchLaw ensemble observed term
            (Ioo (-delta) delta) := by
  let mismatch := fun sample term =>
    physlibA1MismatchSample ensemble observed term sample
  let coefficient := fun sample term =>
    freeQuadraticDuhamelCoefficient
      (physlibQuadraticCoupling
        (ensemble.restrictPositiveMass (N := N) sample) kappa 1 observed)
      (ensemble.restrictPositiveMass (N := N) sample) observed radius term
  have hmain := annealed_nearCoefficientAbsMass_le_sum_mismatchProbability
    ensemble.probability delta (2 * |kappa| * R ^ 2)
    mismatch coefficient
    (fun term => measurable_physlibA1MismatchSample ensemble observed term)
    (fun sample term => physlibA1StaticCoefficient_le_two_absKappa_radiusSq
      (ensemble.restrictPositiveMass (N := N) sample) kappa R hR
      (iid_modeFrequencySq_le_five ensemble sample) radius hradius observed term)
  rw [show (∑ term : QuadraticPhaseTerm N,
      ensemble.probability
        {sample | |mismatch sample term| < delta}) =
      ∑ term : QuadraticPhaseTerm N,
        physlibA1MismatchLaw ensemble observed term
          (Ioo (-delta) delta) by
    apply Finset.sum_congr rfl
    intro term hterm
    exact (physlibA1MismatchLaw_Ioo ensemble observed term delta).symm] at hmain
  simpa [physlibA1AnnealedNearStaticAbsMass,
    physlibA1NearStaticAbsMass, mismatch, coefficient,
    physlibA1MismatchSample] using hmain

/-- Sharp scalar one-site small-ball bound on a regular set, with the entire
bad-set mass retained.  This is the reusable endpoint for any one cumulative
denominator in a finite ordered/branching history. -/
theorem oneSiteMismatchSmallBall_le_sharp_add_badMass
    (chart : Real → Real) (hchart : Measurable chart)
    (good : Set Real) (hgood : MeasurableSet good)
    (derivative : Real → (Real →L[Real] Real))
    (hderivative : ∀ point, point ∈ good →
      HasFDerivWithinAt chart (derivative point) good point)
    (hinjective : InjOn chart good)
    {jacLower : Real} (hjacLower : 0 < jacLower)
    (hjac : ∀ point, point ∈ good →
      jacLower <= |(derivative point).det|)
    (delta : Real) :
    Measure.map chart massCoordinateLaw (Ioo (-delta) delta) <=
      ((5 / 2 : ENNReal) * (ENNReal.ofReal jacLower)⁻¹) *
          ENNReal.ofReal (2 * delta) +
        massCoordinateLaw goodᶜ := by
  have hsourceVolume : massCoordinateLaw.restrict good <=
      (5 / 2 : ENNReal) • (volume : Measure Real).restrict good := by
    calc
      massCoordinateLaw.restrict good <=
          ((5 / 2 : ENNReal) • (volume : Measure Real)).restrict good :=
        Measure.restrict_mono_measure
          massCoordinateLaw_le_fiveHalves_smul_volume good
      _ = (5 / 2 : ENNReal) • (volume : Measure Real).restrict good := by
        rw [Measure.restrict_smul]
  have hgoodMap : Measure.map chart (massCoordinateLaw.restrict good) <=
      ((5 / 2 : ENNReal) * (ENNReal.ofReal jacLower)⁻¹) •
        (volume : Measure Real) :=
    map_le_smul_volume_of_le_volume_restrict_of_det_lower
      (volume : Measure Real) hgood chart hchart derivative hderivative
      hinjective hjacLower hjac (massCoordinateLaw.restrict good)
      (5 / 2 : ENNReal) hsourceVolume
  have hmapSplit : Measure.map chart massCoordinateLaw =
      Measure.map chart (massCoordinateLaw.restrict good) +
        Measure.map chart (massCoordinateLaw.restrict goodᶜ) := by
    rw [← Measure.map_add _ _ hchart,
      massCoordinateLaw.restrict_add_restrict_compl hgood]
  rw [hmapSplit]
  simp only [Measure.add_apply]
  calc
    Measure.map chart (massCoordinateLaw.restrict good) (Ioo (-delta) delta) +
        Measure.map chart (massCoordinateLaw.restrict goodᶜ)
          (Ioo (-delta) delta) <=
      ((5 / 2 : ENNReal) * (ENNReal.ofReal jacLower)⁻¹) *
          (volume : Measure Real) (Ioo (-delta) delta) +
        Measure.map chart (massCoordinateLaw.restrict goodᶜ)
          (Ioo (-delta) delta) := by
      gcongr
      simpa only [Measure.smul_apply, smul_eq_mul] using
        hgoodMap (Ioo (-delta) delta)
    _ <= ((5 / 2 : ENNReal) * (ENNReal.ofReal jacLower)⁻¹) *
          (volume : Measure Real) (Ioo (-delta) delta) +
        massCoordinateLaw goodᶜ := by
      have hbad :
          Measure.map chart (massCoordinateLaw.restrict goodᶜ)
              (Ioo (-delta) delta) <=
            massCoordinateLaw goodᶜ := by
        rw [Measure.map_apply hchart measurableSet_Ioo,
          Measure.restrict_apply (measurableSet_Ioo.preimage hchart)]
        exact measure_mono inter_subset_right
      exact add_le_add_right hbad _
    _ = ((5 / 2 : ENNReal) * (ENNReal.ofReal jacLower)⁻¹) *
          ENNReal.ofReal (2 * delta) + massCoordinateLaw goodᶜ := by
      rw [Real.volume_Ioo]
      congr 2
      ring_nf

/-- Actual A1 mismatch chart for two selected masses with every other mass
frozen. -/
def physlibA1PairMismatchChart
    {N : Nat} [NeZero N]
    (fixed : Lattice.PositiveMassConfig N)
    (site1 site2 observed : Lattice.Site N)
    (term : QuadraticPhaseTerm N) (pair : Real × Real) : Real :=
  quadraticPhaseMismatch
    (modeFrequency (twoSiteMassConfig fixed site1 site2 pair))
    observed term

theorem measurable_physlibA1PairMismatchChart
    {N : Nat} [NeZero N]
    (fixed : Lattice.PositiveMassConfig N)
    (site1 site2 observed : Lattice.Site N)
    (term : QuadraticPhaseTerm N) :
    Measurable
      (physlibA1PairMismatchChart fixed site1 site2 observed term) := by
  exact measurable_quadraticPhaseMismatch_of_mass_coordinates
    (twoSiteMassConfig fixed site1 site2)
    (fun site =>
      (continuous_twoSiteMassConfig_mass fixed site1 site2 site).measurable)
    observed term

/-- Actual pair-law endpoint with a possibly first-coordinate-dependent good
set for the second coordinate.  The right side displays the averaged
Jacobian-degeneracy mass rather than assuming it is small. -/
theorem physlibA1PairMismatchSmallBall_le_integrated_badMass
    {N : Nat} [NeZero N]
    (fixed : Lattice.PositiveMassConfig N)
    (site1 site2 observed : Lattice.Site N)
    (term : QuadraticPhaseTerm N)
    (good : Real → Set Real)
    (hgood : ∀ first, MeasurableSet (good first))
    (derivative : Real → Real → (Real →L[Real] Real))
    (hderivative : ∀ first second, second ∈ good first →
      HasFDerivWithinAt
        (fun x => physlibA1PairMismatchChart fixed site1 site2 observed term
          (first, x))
        (derivative first second) (good first) second)
    (hinjective : ∀ first, InjOn
      (fun x => physlibA1PairMismatchChart fixed site1 site2 observed term
        (first, x)) (good first))
    {jacLower : Real} (hjacLower : 0 < jacLower)
    (hjac : ∀ first second, second ∈ good first →
      jacLower <= |(derivative first second).det|)
    (delta : Real) :
    Measure.map
        (physlibA1PairMismatchChart fixed site1 site2 observed term)
        iidMassPairLaw (Ioo (-delta) delta) <=
      ∫⁻ first,
        (((5 / 2 : ENNReal) * (ENNReal.ofReal jacLower)⁻¹) *
            ENNReal.ofReal (2 * delta) +
          massCoordinateLaw (good first)ᶜ) ∂massCoordinateLaw := by
  let chart := physlibA1PairMismatchChart fixed site1 site2 observed term
  have hchart : Measurable chart :=
    measurable_physlibA1PairMismatchChart fixed site1 site2 observed term
  let target : Set Real := Ioo (-delta) delta
  have htarget : MeasurableSet target := measurableSet_Ioo
  let event : Set (Real × Real) := chart ⁻¹' target
  have hevent : MeasurableSet event := htarget.preimage hchart
  rw [Measure.map_apply hchart htarget]
  change iidMassPairLaw event <= _
  rw [iidMassPairLaw, MeasureTheory.Measure.prod_apply hevent]
  apply lintegral_mono
  intro first
  let fiber : Real → Real := fun x => chart (first, x)
  have hfiber : Measurable fiber := by
    exact hchart.comp (measurable_const.prodMk measurable_id)
  have hpreimage :
      massCoordinateLaw (Prod.mk first ⁻¹' event) =
        Measure.map fiber massCoordinateLaw target := by
    rw [Measure.map_apply hfiber htarget]
    rfl
  change massCoordinateLaw (Prod.mk first ⁻¹' event) <= _
  rw [hpreimage]
  simpa [target] using
    oneSiteMismatchSmallBall_le_sharp_add_badMass
      fiber hfiber (good first) (hgood first) (derivative first)
      (hderivative first) (hinjective first) hjacLower (hjac first) delta

/-- Reusable one-denominator endpoint on the full iid mass support.  Its only
model-facing assumptions are the displayed derivative, injectivity, and
Jacobian lower bound for the actual mismatch chart. -/
theorem physlibA1PairMismatchSmallBall_of_fullTransversality
    {N : Nat} [NeZero N]
    (fixed : Lattice.PositiveMassConfig N)
    (site1 site2 observed : Lattice.Site N)
    (term : QuadraticPhaseTerm N)
    (derivative : Real → Real → (Real →L[Real] Real))
    (hderivative : ∀ first second, second ∈ massSupport →
      HasFDerivWithinAt
        (fun x => physlibA1PairMismatchChart fixed site1 site2 observed term
          (first, x))
        (derivative first second) massSupport second)
    (hinjective : ∀ first, InjOn
      (fun x => physlibA1PairMismatchChart fixed site1 site2 observed term
        (first, x)) massSupport)
    {jacLower : Real} (hjacLower : 0 < jacLower)
    (hjac : ∀ first second, second ∈ massSupport →
      jacLower <= |(derivative first second).det|)
    (delta : Real) :
    Measure.map
        (physlibA1PairMismatchChart fixed site1 site2 observed term)
        iidMassPairLaw (Ioo (-delta) delta) <=
      ((5 / 2 : ENNReal) * (ENNReal.ofReal jacLower)⁻¹) *
        ENNReal.ofReal (2 * delta) := by
  have hbound := physlibA1PairMismatchSmallBall_le_integrated_badMass
    fixed site1 site2 observed term (fun _first => massSupport)
    (fun _first => by
      unfold massSupport
      exact measurableSet_Icc)
    derivative hderivative hinjective hjacLower hjac delta
  have hoff : massCoordinateLaw massSupportᶜ = 0 := by
    simpa [Set.compl_def] using
      (MeasureTheory.ae_iff.mp massCoordinate_mem_support_ae)
  simpa [hoff] using hbound

/-- The full pair/complement mismatch chart used by the exact finite-volume
resampling identity. -/
def physlibA1ReconstructedMismatchChart
    {N : Nat} [NeZero N]
    (site1 site2 observed : Lattice.Site N)
    (term : QuadraticPhaseTerm N)
    (state : (Real × Real) ×
      FiniteMassVector (finiteVolumeMassPairComplement site1 site2)) : Real :=
  quadraticPhaseMismatch
    (modeFrequency
      (finiteVolumePositiveMassPairReconstruction site1 site2 state))
    observed term

theorem measurable_physlibA1ReconstructedMismatchChart
    {N : Nat} [NeZero N]
    (site1 site2 observed : Lattice.Site N)
    (term : QuadraticPhaseTerm N) :
    Measurable
      (physlibA1ReconstructedMismatchChart site1 site2 observed term) := by
  exact measurable_quadraticPhaseMismatch_of_mass_coordinates
    (finiteVolumePositiveMassPairReconstruction site1 site2)
    (measurable_finiteVolumePositiveMassPairReconstruction_mass site1 site2)
    observed term

/-- Exact identification of a frozen-rest fiber with the actual two-mass
mismatch chart. -/
theorem physlibA1ReconstructedMismatchChart_eq_pairMismatchChart
    {N : Nat} [NeZero N]
    (site1 site2 observed : Lattice.Site N)
    (term : QuadraticPhaseTerm N)
    (state : (Real × Real) ×
      FiniteMassVector (finiteVolumeMassPairComplement site1 site2)) :
    physlibA1ReconstructedMismatchChart site1 site2 observed term state =
      physlibA1PairMismatchChart
        (finitePairEnvironmentPositiveMassConfig site1 site2 state.2)
        site1 site2 observed term state.1 := by
  rfl

/-- Exact pointwise random-variable reduction from the iid ensemble to the
selected mass pair and its complementary frozen environment. -/
theorem physlibA1ReconstructedMismatchChart_ensemble_eq
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N]
    (site1 site2 : Lattice.Site N) (hsite : site1 ≠ site2)
    (observed : Lattice.Site N) (term : QuadraticPhaseTerm N)
    (sample : Omega) :
    physlibA1ReconstructedMismatchChart site1 site2 observed term
        (ensembleMassPair ensemble site1.val site2.val sample,
          ensembleFiniteMassVector ensemble
            (finiteVolumeMassPairComplement site1 site2) sample) =
      physlibA1MismatchSample ensemble observed term sample := by
  unfold physlibA1ReconstructedMismatchChart physlibA1MismatchSample
  rw [finiteVolumePositiveMassPairReconstruction_ensemble_eq
    ensemble site1 site2 hsite sample]

private theorem physlibA1MismatchProbability_le_of_frozenPairBound
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N]
    (site1 site2 : Lattice.Site N) (hsite : site1 ≠ site2)
    (observed : Lattice.Site N) (term : QuadraticPhaseTerm N)
    (delta : Real) (bound : ENNReal)
    (hpair : ∀ rest : FiniteMassVector
        (finiteVolumeMassPairComplement site1 site2),
      Measure.map
          (physlibA1PairMismatchChart
            (finitePairEnvironmentPositiveMassConfig site1 site2 rest)
            site1 site2 observed term)
          iidMassPairLaw (Ioo (-delta) delta) <= bound) :
    ensemble.probability
        {sample |
          |physlibA1MismatchSample ensemble observed term sample| < delta} <=
      bound := by
  let restIndices := finiteVolumeMassPairComplement site1 site2
  let _ : IsProbabilityMeasure iidMassPairLaw := by
    unfold iidMassPairLaw
    infer_instance
  let _ : IsProbabilityMeasure (iidFiniteMassVectorLaw restIndices) := by
    unfold iidFiniteMassVectorLaw
    infer_instance
  let randomState := fun sample =>
    (ensembleMassPair ensemble site1.val site2.val sample,
      ensembleFiniteMassVector ensemble restIndices sample)
  let chart :=
    physlibA1ReconstructedMismatchChart site1 site2 observed term
  let target : Set Real := Ioo (-delta) delta
  let event : Set ((Real × Real) × FiniteMassVector restIndices) :=
    chart ⁻¹' target
  have hchart : Measurable chart :=
    measurable_physlibA1ReconstructedMismatchChart
      site1 site2 observed term
  have hevent : MeasurableSet event := measurableSet_Ioo.preimage hchart
  have hval : site1.val ≠ site2.val := by
    intro heq
    exact hsite (ZMod.val_injective N heq)
  have hsite1Rest : site1.val ∉ restIndices := by
    simp [restIndices, finiteVolumeMassPairComplement,
      selectedMassPairIndices]
  have hsite2Rest : site2.val ∉ restIndices := by
    simp [restIndices, finiteVolumeMassPairComplement,
      selectedMassPairIndices]
  have hlaw := ensembleMassPair_prod_finiteEnvironment_hasLaw
    ensemble hval restIndices hsite1Rest hsite2Rest
  have heventProbability :
      ensemble.probability (randomState ⁻¹' event) =
        (iidMassPairLaw.prod (iidFiniteMassVectorLaw restIndices)) event :=
    hlaw.measure_eq hevent
  have hsourceEvent :
      {sample |
        |physlibA1MismatchSample ensemble observed term sample| < delta} =
        randomState ⁻¹' event := by
    ext sample
    have heq := physlibA1ReconstructedMismatchChart_ensemble_eq
      ensemble site1 site2 hsite observed term sample
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, event, target, chart,
      Set.mem_Ioo, randomState]
    rw [heq]
    simp only [abs_lt]
  rw [hsourceEvent, heventProbability,
    MeasureTheory.Measure.prod_apply_symm hevent]
  calc
    (∫⁻ rest,
        iidMassPairLaw ((fun pair => (pair, rest)) ⁻¹' event)
        ∂iidFiniteMassVectorLaw restIndices) <=
      ∫⁻ _rest, bound ∂iidFiniteMassVectorLaw restIndices := by
      apply lintegral_mono
      intro rest
      have hpairMeas : Measurable
          (physlibA1PairMismatchChart
            (finitePairEnvironmentPositiveMassConfig site1 site2 rest)
            site1 site2 observed term) := by
        have hcomp : Measurable
            (fun pair : Real × Real => chart (pair, rest)) :=
          hchart.comp (measurable_id.prodMk measurable_const)
        simpa [chart,
          physlibA1ReconstructedMismatchChart_eq_pairMismatchChart] using hcomp
      have hfiber :
          iidMassPairLaw ((fun pair => (pair, rest)) ⁻¹' event) =
            Measure.map
              (physlibA1PairMismatchChart
                (finitePairEnvironmentPositiveMassConfig site1 site2 rest)
                site1 site2 observed term)
              iidMassPairLaw target := by
        rw [Measure.map_apply hpairMeas measurableSet_Ioo]
        rfl
      change iidMassPairLaw ((fun pair => (pair, rest)) ⁻¹' event) <= bound
      rw [hfiber]
      exact hpair rest
    _ = bound := by simp

/-- Exact finite-volume ensemble small-ball bound for one actual A1
denominator, conditional only on uniform scalar transversality of that
denominator in one selected mass coordinate. -/
theorem physlibA1MismatchLaw_smallBall_of_uniform_pairFiberTransversality
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N]
    (site1 site2 : Lattice.Site N) (hsite : site1 ≠ site2)
    (observed : Lattice.Site N) (term : QuadraticPhaseTerm N)
    (derivative :
      FiniteMassVector (finiteVolumeMassPairComplement site1 site2) →
        Real → Real → (Real →L[Real] Real))
    (hderivative : ∀ rest first second, second ∈ massSupport →
      HasFDerivWithinAt
        (fun x => physlibA1PairMismatchChart
          (finitePairEnvironmentPositiveMassConfig site1 site2 rest)
          site1 site2 observed term (first, x))
        (derivative rest first second) massSupport second)
    (hinjective : ∀ rest first, InjOn
      (fun x => physlibA1PairMismatchChart
        (finitePairEnvironmentPositiveMassConfig site1 site2 rest)
        site1 site2 observed term (first, x)) massSupport)
    {jacLower : Real} (hjacLower : 0 < jacLower)
    (hjac : ∀ rest first second, second ∈ massSupport →
      jacLower <= |(derivative rest first second).det|)
    (delta : Real) :
    physlibA1MismatchLaw ensemble observed term (Ioo (-delta) delta) <=
      ((5 / 2 : ENNReal) * (ENNReal.ofReal jacLower)⁻¹) *
        ENNReal.ofReal (2 * delta) := by
  rw [physlibA1MismatchLaw_Ioo]
  apply physlibA1MismatchProbability_le_of_frozenPairBound
    ensemble site1 site2 hsite observed term delta
  intro rest
  exact physlibA1PairMismatchSmallBall_of_fullTransversality
    (finitePairEnvironmentPositiveMassConfig site1 site2 rest)
    site1 site2 observed term (derivative rest)
    (hderivative rest) (hinjective rest) hjacLower (hjac rest) delta

/-- Explicit finite-`N` annealed A1 near-mass bound when the same selected
pair supplies a uniform scalar transversality estimate for every signed A1
term.  The factor `4 * N^2` is the exact term count, so this endpoint can be
inserted directly into a finite denominator union bound. -/
theorem physlibA1AnnealedNearStaticAbsMass_le_explicit_smallBall_of_uniform_pairFiberTransversality
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N]
    (site1 site2 : Lattice.Site N) (hsite : site1 ≠ site2)
    (kappa delta R : Real) (hR : 0 <= R)
    (radius : Lattice.Site N → Real)
    (hradius : ∀ mode, |radius mode| <= R)
    (observed : Lattice.Site N)
    (derivative : QuadraticPhaseTerm N →
      FiniteMassVector (finiteVolumeMassPairComplement site1 site2) →
        Real → Real → (Real →L[Real] Real))
    (hderivative : ∀ term rest first second, second ∈ massSupport →
      HasFDerivWithinAt
        (fun x => physlibA1PairMismatchChart
          (finitePairEnvironmentPositiveMassConfig site1 site2 rest)
          site1 site2 observed term (first, x))
        (derivative term rest first second) massSupport second)
    (hinjective : ∀ term rest first, InjOn
      (fun x => physlibA1PairMismatchChart
        (finitePairEnvironmentPositiveMassConfig site1 site2 rest)
        site1 site2 observed term (first, x)) massSupport)
    {jacLower : Real} (hjacLower : 0 < jacLower)
    (hjac : ∀ term rest first second, second ∈ massSupport →
      jacLower <= |(derivative term rest first second).det|) :
    physlibA1AnnealedNearStaticAbsMass
        ensemble kappa delta radius observed <=
      ENNReal.ofReal (2 * |kappa| * R ^ 2) *
        ((4 * N ^ 2 : Nat) : ENNReal) *
          (((5 / 2 : ENNReal) * (ENNReal.ofReal jacLower)⁻¹) *
            ENNReal.ofReal (2 * delta)) := by
  let bound : ENNReal :=
    ((5 / 2 : ENNReal) * (ENNReal.ofReal jacLower)⁻¹) *
      ENNReal.ofReal (2 * delta)
  calc
    physlibA1AnnealedNearStaticAbsMass
        ensemble kappa delta radius observed <=
      ENNReal.ofReal (2 * |kappa| * R ^ 2) *
        ∑ term : QuadraticPhaseTerm N,
          physlibA1MismatchLaw ensemble observed term
            (Ioo (-delta) delta) :=
      physlibA1AnnealedNearStaticAbsMass_le_sum_mismatchLaw
        ensemble kappa delta R hR radius hradius observed
    _ <= ENNReal.ofReal (2 * |kappa| * R ^ 2) *
        ∑ _term : QuadraticPhaseTerm N, bound := by
      gcongr
      exact physlibA1MismatchLaw_smallBall_of_uniform_pairFiberTransversality
        ensemble site1 site2 hsite observed term (derivative term)
        (hderivative term) (hinjective term) hjacLower (hjac term) delta
    _ = ENNReal.ofReal (2 * |kappa| * R ^ 2) *
        ((4 * N ^ 2 : Nat) : ENNReal) *
          (((5 / 2 : ENNReal) * (ENNReal.ofReal jacLower)⁻¹) *
            ENNReal.ofReal (2 * delta)) := by
      simp [bound]
      ring

end

end ArchonPhysics.PhyslibFPUTA1AnnealedMismatchSmallBall
