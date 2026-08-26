import ArchonPhysics.RandomMassMeasurableModeCoupling
import Mathlib.MeasureTheory.Measure.GiryMonad
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Measurable positive-mode three-wave collision data

For a finite random-mass chain, this module filters the complete ordered
harmonic spectrum to strictly positive frequencies and records every ordered
three-mode tuple by its signed frequency mismatch and its normalized squared
interaction weight.  The filter is implemented by an indicator in a finite
sum, so the resulting random finite measures are defined on the whole sample
space without choosing a random zero-mode index.

On the almost-sure simple-spectrum event, the projector formula for the
squared interaction weight agrees exactly with the physical normal-mode
eigenvector formula.  A second deterministic identification covers every
real eigenframe whose rank-one outer products are the ordered spectral
projectors, and is therefore insensitive to arbitrary eigenvector signs.

No empirical convergence, resonance-density asymptotic, nondegeneracy, or
kinetic limit is asserted.
-/

open scoped Matrix ENNReal

namespace ArchonPhysics.RandomMassPositiveCollisionData

open ArchonPhysics
open ArchonPhysics.MeasurableOrderedModeCoupling
open ArchonPhysics.MeasurableOrderedModeCoupling.Harmonic
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.HarmonicModes
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.OrderedSingleModeProjector
open ArchonPhysics.OrderedSpectrumContinuity
open ArchonPhysics.RandomMassMeasurableModeCoupling
open ArchonPhysics.RandomMassOrderedProjectorBridge
open MeasureTheory

noncomputable section

/-- Ordered spectral index for an `N`-site chain. -/
abbrev OrderedModeIndex (N : Nat) [NeZero N] :=
  Fin (Fintype.card (Lattice.Site N))

/-- An ordered three-wave mode tuple. -/
abbrev OrderedModeTriple (N : Nat) [NeZero N] := Fin 3 → OrderedModeIndex N

/-- The finite set of strictly positive ordered modes of one realization. -/
def orderedPositiveModeIndices {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) : Finset (OrderedModeIndex N) :=
  positiveModeIndices (harmonicHermitian m)

@[simp] theorem mem_orderedPositiveModeIndices_iff
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (k : OrderedModeIndex N) :
    k ∈ orderedPositiveModeIndices m ↔
      0 < orderedModeFrequency (harmonicHermitian m) k := by
  exact mem_positiveModeIndices_iff _ _

/-- Every entry of an ordered triple belongs to the strictly positive sector. -/
def IsPositiveOrderedTriple {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (modes : OrderedModeTriple N) : Prop :=
  ∀ r, modes r ∈ orderedPositiveModeIndices m

/-- The sample-dependent finite filter of all ordered positive triples. -/
def orderedPositiveModeTriples {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) : Finset (OrderedModeTriple N) := by
  classical
  exact Finset.univ.filter (IsPositiveOrderedTriple m)

@[simp] theorem mem_orderedPositiveModeTriples_iff
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (modes : OrderedModeTriple N) :
    modes ∈ orderedPositiveModeTriples m ↔ IsPositiveOrderedTriple m modes := by
  classical
  simp [orderedPositiveModeTriples]

/-- On simple spectrum, the positive-mode filter is exactly the complete
ordered index set with its unique translation zero mode erased. -/
theorem exists_zeroMode_and_orderedPositiveModeIndices_eq_erase_of_simple
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (hsimple : SimpleOrderedSpectrum (harmonicHermitian m)) :
    ∃ z : OrderedModeIndex N,
      orderedEigenvalue (harmonicHermitian m) z = 0 ∧
      orderedPositiveModeIndices m = Finset.univ.erase z := by
  obtain ⟨z, hz, hpositive⟩ :=
    exists_orderedZeroMode_and_positive_iff_ne_of_simple m hsimple
  refine ⟨z, hz, ?_⟩
  ext k
  rw [mem_orderedPositiveModeIndices_iff]
  simp only [Finset.mem_erase, Finset.mem_univ, and_true]
  have hk : 0 < orderedEigenvalue (harmonicHermitian m) k ↔ k ≠ z := by
    simpa [harmonicHermitian] using hpositive k
  simpa [orderedModeFrequency] using hk

/-- Signed mismatch formed from the canonical ordered frequencies. -/
def orderedThreeWaveMismatch {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N)
    (sign : Fin 3 → InteractionSign) (modes : OrderedModeTriple N) : Real :=
  ∑ r, (sign r).coefficient *
    orderedModeFrequency (harmonicHermitian m) (modes r)

/-- A three-wave collision mark consists of mismatch and normalized squared
coupling. -/
abbrev PositiveCollisionMark := Real × Real

namespace PositiveCollisionMark

def mismatch (mark : PositiveCollisionMark) : Real := mark.1

def interactionWeight (mark : PositiveCollisionMark) : Real := mark.2

end PositiveCollisionMark

/-- Canonical basis-free collision mark for one ordered triple. -/
def orderedPositiveCollisionMark {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N)
    (sign : Fin 3 → InteractionSign) (modes : OrderedModeTriple N) :
    PositiveCollisionMark :=
  (orderedThreeWaveMismatch m sign modes,
    harmonicOrderedNormalizedInteractionWeight m modes)

/-- One Dirac mass for each ordered triple whose three frequencies are
strictly positive.  This is an unnormalized finite counting measure. -/
def positiveMarkedEmpiricalMeasure {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N)
    (sign : Fin 3 → InteractionSign) : Measure PositiveCollisionMark := by
  classical
  exact ∑ modes : OrderedModeTriple N,
    if IsPositiveOrderedTriple m modes then
      Measure.dirac (orderedPositiveCollisionMark m sign modes)
    else 0

/-- Coupling-weighted phase-mismatch measure on the real line.  It is the
direct finite-size input expected by resonance-kernel testing. -/
def positiveWeightedMismatchMeasure {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N)
    (sign : Fin 3 → InteractionSign) : Measure Real := by
  classical
  exact ∑ modes : OrderedModeTriple N,
    if IsPositiveOrderedTriple m modes then
      ENNReal.ofReal (harmonicOrderedNormalizedInteractionWeight m modes) •
        Measure.dirac (orderedThreeWaveMismatch m sign modes)
    else 0

/-- Canonical finite collision functional, written without measure theory. -/
def positiveCollisionFiniteSum {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N)
    (sign : Fin 3 → InteractionSign)
    (test : PositiveCollisionMark → Real) : Real := by
  classical
  exact ∑ modes : OrderedModeTriple N,
    if IsPositiveOrderedTriple m modes then
      test (orderedPositiveCollisionMark m sign modes)
    else 0

@[simp] theorem orderedPositiveCollisionMark_mismatch
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (sign : Fin 3 → InteractionSign) (modes : OrderedModeTriple N) :
    PositiveCollisionMark.mismatch (orderedPositiveCollisionMark m sign modes) =
      orderedThreeWaveMismatch m sign modes := rfl

@[simp] theorem orderedPositiveCollisionMark_interactionWeight
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (sign : Fin 3 → InteractionSign) (modes : OrderedModeTriple N) :
    PositiveCollisionMark.interactionWeight
        (orderedPositiveCollisionMark m sign modes) =
      harmonicOrderedNormalizedInteractionWeight m modes := rfl

/-- Ordered frequencies reproduce the physical Mathlib eigenbasis mismatch
after transport through `orderedIndexEquiv`. -/
theorem orderedThreeWaveMismatch_eq_phaseMismatch
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (sign : Fin 3 → InteractionSign) (modes : OrderedModeTriple N) :
    orderedThreeWaveMismatch m sign modes =
      phaseMismatch m sign (fun r ↦ orderedIndexEquiv (modes r)) := by
  unfold orderedThreeWaveMismatch phaseMismatch
  apply Finset.sum_congr rfl
  intro r _hr
  rw [orderedModeFrequency_harmonicHermitian_eq]

/-- On simple spectrum, every physical tuple is positive exactly when its
ordered representative passes the canonical positive-mode filter. -/
theorem isPositiveOrderedTriple_iff_physical
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (modes : OrderedModeTriple N) :
    IsPositiveOrderedTriple m modes ↔
      NormalizedModeCoupling.PositiveModeTuple m
        (fun r ↦ orderedIndexEquiv (modes r)) := by
  constructor <;> intro h r
  · have hr := h r
    rw [mem_orderedPositiveModeIndices_iff,
      orderedModeFrequency_harmonicHermitian_eq] at hr
    exact hr
  · rw [mem_orderedPositiveModeIndices_iff,
      orderedModeFrequency_harmonicHermitian_eq]
    exact h r

/-- Under simple spectrum, the canonical mark equals the existing physical
normal-mode mark exactly. -/
theorem orderedPositiveCollisionMark_eq_physical
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (hsimple : SimpleOrderedSpectrum (harmonicHermitian m))
    (sign : Fin 3 → InteractionSign) (modes : OrderedModeTriple N) :
    orderedPositiveCollisionMark m sign modes =
      (phaseMismatch m sign (fun r ↦ orderedIndexEquiv (modes r)),
        NormalizedModeCoupling.normalizedInteractionWeight m
          (fun r ↦ orderedIndexEquiv (modes r))) := by
  apply Prod.ext
  · exact orderedThreeWaveMismatch_eq_phaseMismatch m sign modes
  · exact harmonicOrderedNormalizedInteractionWeight_eq m hsimple modes

/-- A real ordered eigenframe is physically admissible for the collision
weight when each vector has the ordered rank-one spectral projector as its
outer product.  This formulation identifies all sign choices. -/
def IsPhysicalOrderedEigenframe {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N)
    (frame : OrderedModeIndex N → Lattice.Configuration N) : Prop :=
  ∀ k, orderedModeProjector (harmonicHermitian m) k =
    Matrix.vecMulVec (frame k) (frame k)

/-- Interaction tensor computed from an arbitrary supplied ordered frame. -/
def frameInteractionTensor {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N)
    (frame : OrderedModeIndex N → Lattice.Configuration N)
    (modes : OrderedModeTriple N) : Real :=
  ∑ j, ∏ r, (massWeightedDifferenceMatrix m *ᵥ frame (modes r)) j

/-- Frequency-normalized squared coupling represented in an arbitrary
physical ordered eigenframe. -/
def frameNormalizedInteractionWeight {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N)
    (frame : OrderedModeIndex N → Lattice.Configuration N)
    (modes : OrderedModeTriple N) : Real :=
  (frameInteractionTensor m frame modes) ^ 2 *
    ∏ r, (2 * orderedModeFrequency (harmonicHermitian m) (modes r))⁻¹

theorem projectedBondKernel_apply_eq_frame_mul
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (frame : OrderedModeIndex N → Lattice.Configuration N)
    (hframe : IsPhysicalOrderedEigenframe m frame)
    (k : OrderedModeIndex N) (j l : Lattice.Site N) :
    projectedBondKernel (massWeightedDifferenceMatrix m)
        (harmonicHermitian m) k j l =
      (massWeightedDifferenceMatrix m *ᵥ frame k) j *
        (massWeightedDifferenceMatrix m *ᵥ frame k) l := by
  unfold projectedBondKernel
  rw [hframe k, Matrix.mul_vecMulVec, Matrix.vecMulVec_mul,
    Matrix.vecMul_transpose]
  rfl

/-- The projector formula equals the square computed in every physical
ordered eigenframe, independently of eigenvector signs. -/
theorem harmonicOrderedInteractionWeightSq_eq_frame
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (frame : OrderedModeIndex N → Lattice.Configuration N)
    (hframe : IsPhysicalOrderedEigenframe m frame)
    (modes : OrderedModeTriple N) :
    harmonicOrderedInteractionWeightSq m modes =
      (frameInteractionTensor m frame modes) ^ 2 := by
  unfold harmonicOrderedInteractionWeightSq orderedInteractionWeightSq
    frameInteractionTensor
  simp_rw [projectedBondKernel_apply_eq_frame_mul m frame hframe]
  rw [pow_two, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _hj
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l _hl
  rw [← Finset.prod_mul_distrib]

/-- Exact equality with every physical eigenframe representation. -/
theorem harmonicOrderedNormalizedInteractionWeight_eq_frame
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (frame : OrderedModeIndex N → Lattice.Configuration N)
    (hframe : IsPhysicalOrderedEigenframe m frame)
    (modes : OrderedModeTriple N) :
    harmonicOrderedNormalizedInteractionWeight m modes =
      frameNormalizedInteractionWeight m frame modes := by
  unfold harmonicOrderedNormalizedInteractionWeight
    frameNormalizedInteractionWeight
  rw [harmonicOrderedInteractionWeightSq_eq_frame m frame hframe modes]

/-- Collision mark computed in an arbitrary physical ordered eigenframe. -/
def framePositiveCollisionMark {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N)
    (sign : Fin 3 → InteractionSign)
    (frame : OrderedModeIndex N → Lattice.Configuration N)
    (modes : OrderedModeTriple N) : PositiveCollisionMark :=
  (orderedThreeWaveMismatch m sign modes,
    frameNormalizedInteractionWeight m frame modes)

/-- The canonical mark is exactly the mark computed in every compatible real
physical eigenframe. -/
theorem orderedPositiveCollisionMark_eq_frame
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (sign : Fin 3 → InteractionSign)
    (frame : OrderedModeIndex N → Lattice.Configuration N)
    (hframe : IsPhysicalOrderedEigenframe m frame)
    (modes : OrderedModeTriple N) :
    orderedPositiveCollisionMark m sign modes =
      framePositiveCollisionMark m sign frame modes := by
  apply Prod.ext
  · rfl
  · exact harmonicOrderedNormalizedInteractionWeight_eq_frame
      m frame hframe modes

/-- Positive marked empirical measure computed in an arbitrary physical
ordered eigenframe. -/
def framePositiveMarkedEmpiricalMeasure {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N)
    (sign : Fin 3 → InteractionSign)
    (frame : OrderedModeIndex N → Lattice.Configuration N) :
    Measure PositiveCollisionMark := by
  classical
  exact ∑ modes : OrderedModeTriple N,
    if IsPositiveOrderedTriple m modes then
      Measure.dirac (framePositiveCollisionMark m sign frame modes)
    else 0

/-- The complete finite marked measure is independent of the chosen physical
real eigenframe, including every independent eigenvector sign choice. -/
theorem positiveMarkedEmpiricalMeasure_eq_frame
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (sign : Fin 3 → InteractionSign)
    (frame : OrderedModeIndex N → Lattice.Configuration N)
    (hframe : IsPhysicalOrderedEigenframe m frame) :
    positiveMarkedEmpiricalMeasure m sign =
      framePositiveMarkedEmpiricalMeasure m sign frame := by
  classical
  unfold positiveMarkedEmpiricalMeasure framePositiveMarkedEmpiricalMeasure
  apply Finset.sum_congr rfl
  intro modes _hmodes
  by_cases hpositive : IsPositiveOrderedTriple m modes
  · rw [if_pos hpositive, if_pos hpositive,
      orderedPositiveCollisionMark_eq_frame m sign frame hframe modes]
  · rw [if_neg hpositive, if_neg hpositive]

/-- The Mathlib eigenvector basis, transported to ordered indices, is a
physical ordered eigenframe whenever the spectrum is simple. -/
theorem isPhysicalOrderedEigenframe_eigenvectorBasis
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (hsimple : SimpleOrderedSpectrum (harmonicHermitian m)) :
    IsPhysicalOrderedEigenframe m
      (fun k ↦ ⇑((harmonicHermitian m).2.eigenvectorBasis
        (orderedIndexEquiv k))) := by
  intro k
  exact orderedModeProjector_eq_vecMulVec (harmonicHermitian m) hsimple k

variable {Omega : Type*} [MeasurableSpace Omega]

/-- Membership of a fixed ordered mode in the random positive sector is a
globally measurable event. -/
theorem measurableSet_mem_orderedPositiveModeIndicesSample
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N] (k : OrderedModeIndex N) :
    MeasurableSet {omega |
      k ∈ orderedPositiveModeIndices
        (ensemble.restrictPositiveMass (N := N) omega)} := by
  exact measurableSet_mem_positiveModeIndices_unconditional
    (fun omega ↦ harmonicHermitian
      (ensemble.restrictPositiveMass (N := N) omega))
    (by
      apply Measurable.subtype_mk
      exact MeasurableHarmonicData.measurable_massWeightedHarmonicMatrix_of_coordinate
        _ (measurable_restrictPositiveMass_coordinate ensemble)) k

/-- Positivity of all three fixed ordered modes is a globally measurable
event. -/
theorem measurableSet_isPositiveOrderedTripleSample
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N] (modes : OrderedModeTriple N) :
    MeasurableSet {omega |
      IsPositiveOrderedTriple
        (ensemble.restrictPositiveMass (N := N) omega) modes} := by
  have heq :
      {omega | IsPositiveOrderedTriple
        (ensemble.restrictPositiveMass (N := N) omega) modes} =
        ⋂ r, {omega | modes r ∈ orderedPositiveModeIndices
          (ensemble.restrictPositiveMass (N := N) omega)} := by
    ext omega
    simp [IsPositiveOrderedTriple]
  rw [heq]
  exact MeasurableSet.iInter fun r ↦
    measurableSet_mem_orderedPositiveModeIndicesSample ensemble (modes r)

/-- A fixed ordered three-wave mismatch is globally measurable. -/
theorem measurable_orderedThreeWaveMismatchSample
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N]
    (sign : Fin 3 → InteractionSign) (modes : OrderedModeTriple N) :
    Measurable fun omega ↦ orderedThreeWaveMismatch
      (ensemble.restrictPositiveMass (N := N) omega) sign modes := by
  unfold orderedThreeWaveMismatch
  apply Finset.measurable_sum
  intro r _hr
  exact measurable_const.mul
    ((measurable_orderedModeFrequencies_unconditional
      (fun omega ↦ harmonicHermitian
        (ensemble.restrictPositiveMass (N := N) omega))
      (by
        apply Measurable.subtype_mk
        exact MeasurableHarmonicData.measurable_massWeightedHarmonicMatrix_of_coordinate
          _ (measurable_restrictPositiveMass_coordinate ensemble))).eval)

/-- Every fixed canonical collision mark is globally measurable. -/
theorem measurable_orderedPositiveCollisionMarkSample
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N]
    (sign : Fin 3 → InteractionSign) (modes : OrderedModeTriple N) :
    Measurable fun omega ↦ orderedPositiveCollisionMark
      (ensemble.restrictPositiveMass (N := N) omega) sign modes := by
  exact (measurable_orderedThreeWaveMismatchSample ensemble sign modes).prodMk
    (measurable_orderedNormalizedInteractionWeightSample ensemble modes)

/-- The random positive marked empirical measure is measurable as a
measure-valued map on the whole sample space. -/
theorem measurable_positiveMarkedEmpiricalMeasure
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N] (sign : Fin 3 → InteractionSign) :
    Measurable fun omega ↦ positiveMarkedEmpiricalMeasure
      (ensemble.restrictPositiveMass (N := N) omega) sign := by
  classical
  unfold positiveMarkedEmpiricalMeasure
  apply Finset.measurable_sum
  intro modes _hmodes
  apply Measurable.ite
    (measurableSet_isPositiveOrderedTripleSample ensemble modes)
  · exact Measure.measurable_dirac.comp
      (measurable_orderedPositiveCollisionMarkSample ensemble sign modes)
  · exact measurable_const

/-- The coupling-weighted random phase-mismatch measure is globally
measurable as a measure-valued map. -/
theorem measurable_positiveWeightedMismatchMeasure
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N] (sign : Fin 3 → InteractionSign) :
    Measurable fun omega ↦ positiveWeightedMismatchMeasure
      (ensemble.restrictPositiveMass (N := N) omega) sign := by
  classical
  unfold positiveWeightedMismatchMeasure
  apply Finset.measurable_sum
  intro modes _hmodes
  apply Measurable.ite
    (measurableSet_isPositiveOrderedTripleSample ensemble modes)
  · have hcoefficient : Measurable fun omega ↦
        ENNReal.ofReal (harmonicOrderedNormalizedInteractionWeight
          (ensemble.restrictPositiveMass (N := N) omega) modes) :=
      (measurable_orderedNormalizedInteractionWeightSample ensemble modes).ennreal_ofReal
    have hdirac : Measurable fun omega ↦
        Measure.dirac (orderedThreeWaveMismatch
          (ensemble.restrictPositiveMass (N := N) omega) sign modes) :=
      Measure.measurable_dirac.comp
        (measurable_orderedThreeWaveMismatchSample ensemble sign modes)
    refine Measure.measurable_of_measurable_coe _ fun s hs ↦ ?_
    simp only [Measure.smul_apply, smul_eq_mul]
    exact hcoefficient.mul ((Measure.measurable_coe hs).comp hdirac)
  · exact measurable_const

/-- Integration of any real test against the marked finite measure is the
canonical filtered finite sum. -/
theorem integral_positiveMarkedEmpiricalMeasure_eq_finiteSum
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (sign : Fin 3 → InteractionSign)
    (test : PositiveCollisionMark → Real) :
    ∫ mark, test mark ∂positiveMarkedEmpiricalMeasure m sign =
      positiveCollisionFiniteSum m sign test := by
  classical
  unfold positiveMarkedEmpiricalMeasure positiveCollisionFiniteSum
  rw [integral_finsetSum_measure]
  · apply Finset.sum_congr rfl
    intro modes _hmodes
    by_cases hpositive : IsPositiveOrderedTriple m modes
    · simp only [if_pos hpositive, integral_dirac]
    · simp only [if_neg hpositive, integral_zero_measure]
  · intro modes _hmodes
    by_cases hpositive : IsPositiveOrderedTriple m modes
    · rw [if_pos hpositive]
      exact integrable_dirac (by simp)
    · rw [if_neg hpositive]
      exact integrable_zero_measure

/-- On the almost-sure simple-spectrum event, every fixed canonical mark is
exactly the existing physical eigenbasis mark. -/
theorem orderedPositiveCollisionMark_eq_physical_ae
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N] (hN : 2 ≤ N)
    (sign : Fin 3 → InteractionSign) (modes : OrderedModeTriple N) :
    ∀ᵐ omega ∂ensemble.probability,
      orderedPositiveCollisionMark
          (ensemble.restrictPositiveMass (N := N) omega) sign modes =
        (phaseMismatch
            (ensemble.restrictPositiveMass (N := N) omega) sign
            (fun r ↦ orderedIndexEquiv (modes r)),
          NormalizedModeCoupling.normalizedInteractionWeight
            (ensemble.restrictPositiveMass (N := N) omega)
            (fun r ↦ orderedIndexEquiv (modes r))) := by
  filter_upwards [simpleOrderedSpectrum_ae ensemble hN] with omega hsimple
  exact orderedPositiveCollisionMark_eq_physical _ hsimple sign modes

/-- The canonical iid `[4/5,6/5]` marked empirical measure is globally
measurable. -/
theorem measurable_canonicalPositiveMarkedEmpiricalMeasure
    {N : Nat} [NeZero N] (sign : Fin 3 → InteractionSign) :
    Measurable fun omega ↦ positiveMarkedEmpiricalMeasure
      (canonicalIIDMassPhaseEnsemble.restrictPositiveMass (N := N) omega)
      sign :=
  measurable_positiveMarkedEmpiricalMeasure
    canonicalIIDMassPhaseEnsemble sign

/-- The canonical iid `[4/5,6/5]` coupling-weighted mismatch measure is
globally measurable. -/
theorem measurable_canonicalPositiveWeightedMismatchMeasure
    {N : Nat} [NeZero N] (sign : Fin 3 → InteractionSign) :
    Measurable fun omega ↦ positiveWeightedMismatchMeasure
      (canonicalIIDMassPhaseEnsemble.restrictPositiveMass (N := N) omega)
      sign :=
  measurable_positiveWeightedMismatchMeasure
    canonicalIIDMassPhaseEnsemble sign

end

end ArchonPhysics.RandomMassPositiveCollisionData
