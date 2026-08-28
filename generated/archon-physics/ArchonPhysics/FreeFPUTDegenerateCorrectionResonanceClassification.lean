import ArchonPhysics.FreeFPUTAllDistinctCounterrotatingSignedFluxDecay
import ArchonPhysics.FreeFPUTAllEqualGlobalSelectorMultiplicity
import ArchonPhysics.FreeFPUTObservedChildGlobalFeedbackClosure
import ArchonPhysics.FreeFPUTRepeatedAwayGlobalFeedbackReindex

/-!
# Resonance classification of the resolved degenerate FPUT corrections

The three global feedback closures leave explicit quadratic collision-kernel
corrections.  This file separates the sign sectors which have an algebraic
frequency gap from the sectors which can still meet a three-wave resonance.

All inverse-time constants below are literal finite sums at fixed volume.
No lower frequency bound uniform in the lattice size is assumed or concluded.
In particular, the potentially resonant sectors are named and retained; they
are not hidden behind an off-resonance hypothesis.
-/

namespace ArchonPhysics.FreeFPUTDegenerateCorrectionResonanceClassification

open ArchonPhysics
open ArchonPhysics.FreeFPUTAllDistinctCounterrotatingSignedFluxDecay
open ArchonPhysics.FreeFPUTAllEqualGlobalSelectorMultiplicity
open ArchonPhysics.FreeFPUTCollisionMismatchBridge
open ArchonPhysics.FreeFPUTCanonicalConnectedReturnTree
open ArchonPhysics.FreeFPUTCounterrotatingFiniteTimeDecay
open ArchonPhysics.FreeFPUTEnergyCollisionWeightBridge
open ArchonPhysics.FreeFPUTObservedChildGlobalFeedbackClosure
open ArchonPhysics.FreeFPUTPositiveDegenerateRepresentativeA1Partition
open ArchonPhysics.FreeFPUTRepeatedAwayGlobalFeedbackReindex
open ArchonPhysics.FreeFPUTRepeatedChildSameSignCorrection
open ArchonPhysics.FreeFPUTTensorPhaseExpansion
open ArchonPhysics.MicroscopicFiniteTimeCollisionPolynomial
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.NormalizedModeCoupling
open ArchonPhysics.PhyslibFPUTIteratedQuadraticSecondPicardCharacterFamily
open ArchonPhysics.PhyslibFPUTSecondOrderA1CollisionGainDecomposition
open ArchonPhysics.SignedThreeWaveCollisionFlux
open ArchonPhysics.ThreeSignedChargeCancellationClassification
open ArchonPhysics.UniformOffResonanceDecay

noncomputable section

/-! ## Generic fixed-volume estimate -/

/-- A quadratic collision kernel with a displayed positive mismatch gap has
the corresponding inverse-time bound. -/
theorem finiteTimeCollisionKernel_quadratic_le_inverseTime_of_gap
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (kappa : Real) (observed : Lattice.Site N)
    (q : QuadraticPhaseTerm N) {time delta : Real}
    (htime : 0 < time) (hdelta : 0 < delta)
    (hgap : delta ≤
      |phaseMismatch m (quadraticCollisionSign q)
        (quadraticCollisionModes observed q)|) :
    finiteTimeCollisionKernel m kappa (quadraticCollisionSign q) time
        (quadraticCollisionModes observed q) ≤
      (kappa ^ 2 * normalizedInteractionWeight m
          (quadraticCollisionModes observed q)) *
        ((2 / delta) ^ 2 / time) := by
  unfold finiteTimeCollisionKernel hamiltonianInteractionVertex
  rw [mul_pow, normalizedInteractionVertex_sq]
  exact mul_le_mul_of_nonneg_left
    (finiteTimeResonanceWeight_le_inverseThreshold
      htime hdelta hgap)
    (mul_nonneg (sq_nonneg kappa)
      (normalizedInteractionWeight_nonneg m
        (quadraticCollisionModes observed q)))

/-- Finite weighted quadratic sums inherit `O(1 / T)` from termwise explicit
gaps.  The static constant is deliberately a literal finite sum. -/
theorem abs_weightedQuadraticKernelSum_le_inverseTime
    {N : Nat} [NeZero N] {ι : Type*}
    (m : Lattice.PositiveMassConfig N) (kappa : Real)
    (observed : Lattice.Site N) (indices : Finset ι)
    (q : ι → QuadraticPhaseTerm N) (weight gap : ι → Real)
    {time : Real} (htime : 0 < time)
    (hgapPos : ∀ i ∈ indices, 0 < gap i)
    (hgap : ∀ i ∈ indices, gap i ≤
      |phaseMismatch m (quadraticCollisionSign (q i))
        (quadraticCollisionModes observed (q i))|) :
    |∑ i ∈ indices,
        weight i * finiteTimeCollisionKernel m kappa
          (quadraticCollisionSign (q i)) time
          (quadraticCollisionModes observed (q i))| ≤
      (∑ i ∈ indices,
        |weight i| *
          (kappa ^ 2 * normalizedInteractionWeight m
            (quadraticCollisionModes observed (q i))) *
          (2 / gap i) ^ 2) / time := by
  classical
  calc
    |∑ i ∈ indices,
        weight i * finiteTimeCollisionKernel m kappa
          (quadraticCollisionSign (q i)) time
          (quadraticCollisionModes observed (q i))| ≤
        ∑ i ∈ indices,
          |weight i * finiteTimeCollisionKernel m kappa
            (quadraticCollisionSign (q i)) time
            (quadraticCollisionModes observed (q i))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ indices,
        (|weight i| *
          (kappa ^ 2 * normalizedInteractionWeight m
            (quadraticCollisionModes observed (q i))) *
          (2 / gap i) ^ 2) / time := by
      apply Finset.sum_le_sum
      intro i hi
      have hkernel := finiteTimeCollisionKernel_quadratic_le_inverseTime_of_gap
        m kappa observed (q i) htime (hgapPos i hi) (hgap i hi)
      rw [abs_mul, abs_of_nonneg
        (finiteTimeCollisionKernel_nonneg m kappa
          (quadraticCollisionSign (q i)) time
          (quadraticCollisionModes observed (q i)))]
      calc
        |weight i| * finiteTimeCollisionKernel m kappa
            (quadraticCollisionSign (q i)) time
            (quadraticCollisionModes observed (q i)) ≤
          |weight i| *
            ((kappa ^ 2 * normalizedInteractionWeight m
                (quadraticCollisionModes observed (q i))) *
              ((2 / gap i) ^ 2 / time)) :=
          mul_le_mul_of_nonneg_left hkernel (abs_nonneg _)
        _ = (|weight i| *
              (kappa ^ 2 * normalizedInteractionWeight m
                (quadraticCollisionModes observed (q i))) *
              (2 / gap i) ^ 2) / time := by ring
    _ = (∑ i ∈ indices,
        |weight i| *
          (kappa ^ 2 * normalizedInteractionWeight m
            (quadraticCollisionModes observed (q i))) *
          (2 / gap i) ^ 2) / time := by
      rw [Finset.sum_div]

/-! ## Elementary quadratic mismatch identities -/

/-- Two phase inputs have mismatch `omega_out - omega_0 - omega_1`. -/
theorem phaseMismatch_quadratic_bothPhase
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N) (q : QuadraticPhaseTerm N)
    (hzero : q.2.1 = 0) (hone : q.2.2 = 0) :
    phaseMismatch m (quadraticCollisionSign q)
        (quadraticCollisionModes observed q) =
      modeFrequency m observed - modeFrequency m (q.1 0) -
        modeFrequency m (q.1 1) := by
  rw [← quadraticPhaseMismatch_modeFrequency_eq_phaseMismatch,
    quadraticPhaseMismatch_eq_signedCollisionSum]
  simp [hzero, hone, binaryPhaseSign,
    phaseSignToInputInteractionSign, Fin.sum_univ_three]
  ring

/-- If the selected observed input is a phase character, it cancels the
output frequency.  The remaining absolute mismatch is the free frequency,
independently of the free character sign. -/
theorem abs_phaseMismatch_selectedPhase_observed_eq_freeFrequency
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N) (q : QuadraticPhaseTerm N)
    (selected : Fin 2)
    (hObserved : observed = q.1 selected)
    (hSelected : quadraticPhaseTermBinarySign q selected = 0) :
    |phaseMismatch m (quadraticCollisionSign q)
        (quadraticCollisionModes observed q)| =
      modeFrequency m (q.1 (otherQuadraticSlot selected)) := by
  rcases q with ⟨modes, signZero, signOne⟩
  fin_cases selected <;> fin_cases signZero <;> fin_cases signOne <;>
    simp_all [quadraticPhaseTermBinarySign, otherQuadraticSlot,
      binaryPhaseSign,
      phaseSignToInputInteractionSign, phaseMismatch, Fin.sum_univ_three,
      abs_neg, modeFrequency_nonneg]

/-- The carrier-observed `conjugate/phase` sector has the potentially
resonant mismatch `2 omega_observed - omega_free`. -/
theorem phaseMismatch_selectedConjugate_otherPhase_observed
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N) (q : QuadraticPhaseTerm N)
    (selected : Fin 2)
    (hObserved : observed = q.1 selected)
    (hSelected : quadraticPhaseTermBinarySign q selected = 1)
    (hOther : quadraticPhaseTermBinarySign q
      (otherQuadraticSlot selected) = 0) :
    phaseMismatch m (quadraticCollisionSign q)
        (quadraticCollisionModes observed q) =
      2 * modeFrequency m observed -
        modeFrequency m (q.1 (otherQuadraticSlot selected)) := by
  rcases q with ⟨modes, signZero, signOne⟩
  fin_cases selected <;> fin_cases signZero <;> fin_cases signOne <;>
    simp_all [quadraticPhaseTermBinarySign, otherQuadraticSlot,
      binaryPhaseSign,
      phaseSignToInputInteractionSign, phaseMismatch, Fin.sum_univ_three] <;>
    ring

/-- The free-observed `phase/conjugate` sector has the potentially resonant
mismatch `2 omega_observed - omega_selected`. -/
theorem phaseMismatch_selectedPhase_otherConjugate_observed
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N) (q : QuadraticPhaseTerm N)
    (selected : Fin 2)
    (hObserved : observed = q.1 (otherQuadraticSlot selected))
    (hSelected : quadraticPhaseTermBinarySign q selected = 0)
    (hOther : quadraticPhaseTermBinarySign q
      (otherQuadraticSlot selected) = 1) :
    phaseMismatch m (quadraticCollisionSign q)
        (quadraticCollisionModes observed q) =
      2 * modeFrequency m observed - modeFrequency m (q.1 selected) := by
  rcases q with ⟨modes, signZero, signOne⟩
  fin_cases selected <;> fin_cases signZero <;> fin_cases signOne <;>
    simp_all [quadraticPhaseTermBinarySign, otherQuadraticSlot,
      binaryPhaseSign,
      phaseSignToInputInteractionSign, phaseMismatch, Fin.sum_univ_three] <;>
    ring

/-- Two conjugate inputs are exactly the all-plus collision sign. -/
theorem quadraticCollisionSign_eq_counterrotating_of_bothConjugate
    {N : Nat} [NeZero N] (q : QuadraticPhaseTerm N)
    (hzero : q.2.1 = 1) (hone : q.2.2 = 1) :
    quadraticCollisionSign q = counterrotatingThreeWaveSign := by
  funext r
  fin_cases r <;>
    simp [hzero, hone, binaryPhaseSign, phaseSignToInputInteractionSign,
      counterrotatingThreeWaveSign]

/-! ## Repeated-away same-sign correction -/

/-- The phase/phase repeated-away representatives.  Their mismatch can be
`omega_observed - 2 omega_child`, so this sector is retained as potentially
resonant. -/
def repeatedAwayPotentiallyResonantSameSignRepresentatives
    (N : Nat) [NeZero N] (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N) : Finset (QuadraticPhaseTerm N) := by
  classical
  exact (positiveRepeatedChildSameSignRepresentatives N m observed).filter
    fun q ↦ q.2.1 = 0

/-- The complementary same-sign repeated-away sector.  Since the binary sign
is nonzero, both repeated inputs are conjugate and the sector is all plus. -/
def repeatedAwayCounterrotatingSameSignRepresentatives
    (N : Nat) [NeZero N] (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N) : Finset (QuadraticPhaseTerm N) := by
  classical
  exact (positiveRepeatedChildSameSignRepresentatives N m observed).filter
    fun q ↦ q.2.1 ≠ 0

/-- Literal two-copy correction weight, with the finite-time kernel factored
out. -/
def repeatedAwaySameSignTwoCopyWeight
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (energy : Lattice.Site N → Real) (observed : Lattice.Site N)
    (q : QuadraticPhaseTerm N) : Real :=
  2 * (quadraticInputInteractionSign q 0).coefficient *
    modeAction energy (modeFrequency m) observed *
    modeAction energy (modeFrequency m) (q.1 0)

/-- Full repeated-away same-sign two-copy correction. -/
def repeatedAwaySameSignTwoCopyCorrectionSum
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa time : Real)
    (energy : Lattice.Site N → Real) (observed : Lattice.Site N) : Real :=
  ∑ q ∈ positiveRepeatedChildSameSignRepresentatives N m observed,
    repeatedAwaySameSignTwoCopyWeight m energy observed q *
      finiteTimeCollisionKernel m kappa (quadraticCollisionSign q) time
        (quadraticCollisionModes observed q)

/-- Potentially resonant phase/phase part of the same correction. -/
def repeatedAwayPotentiallyResonantCorrectionSum
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa time : Real)
    (energy : Lattice.Site N → Real) (observed : Lattice.Site N) : Real :=
  ∑ q ∈ repeatedAwayPotentiallyResonantSameSignRepresentatives
      N m observed,
    repeatedAwaySameSignTwoCopyWeight m energy observed q *
      finiteTimeCollisionKernel m kappa (quadraticCollisionSign q) time
        (quadraticCollisionModes observed q)

/-- Algebraically off-resonant all-plus part of the same correction. -/
def repeatedAwayCounterrotatingCorrectionSum
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa time : Real)
    (energy : Lattice.Site N → Real) (observed : Lattice.Site N) : Real :=
  ∑ q ∈ repeatedAwayCounterrotatingSameSignRepresentatives N m observed,
    repeatedAwaySameSignTwoCopyWeight m energy observed q *
      finiteTimeCollisionKernel m kappa (quadraticCollisionSign q) time
        (quadraticCollisionModes observed q)

/-- The named two-copy term is exactly the correction displayed by the
repeated-away global closure. -/
theorem repeatedChildSameSignSignedFluxWithCorrection_eq_flux_add_twoCopy
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa time : Real)
    (energy : Lattice.Site N → Real) (observed : Lattice.Site N)
    (q : QuadraticPhaseTerm N) :
    repeatedChildSameSignSignedFluxWithCorrection
        m kappa time energy observed q =
      finiteTimeCollisionKernel m kappa (quadraticCollisionSign q) time
          (quadraticCollisionModes observed q) *
        quadraticSignedCollisionFlux q
          (modeAction energy (modeFrequency m)) observed +
      repeatedAwaySameSignTwoCopyWeight m energy observed q *
        finiteTimeCollisionKernel m kappa (quadraticCollisionSign q) time
          (quadraticCollisionModes observed q) := by
  unfold repeatedChildSameSignSignedFluxWithCorrection
    repeatedAwaySameSignTwoCopyWeight
  ring

/-- Sum-level identification of the named correction with the second term in
the global repeated-away formula. -/
theorem sum_repeatedChildSameSignSignedFluxWithCorrection_eq_flux_add_correction
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa time : Real)
    (energy : Lattice.Site N → Real) (observed : Lattice.Site N) :
    (∑ q ∈ positiveRepeatedChildSameSignRepresentatives N m observed,
      repeatedChildSameSignSignedFluxWithCorrection
        m kappa time energy observed q) =
      (∑ q ∈ positiveRepeatedChildSameSignRepresentatives N m observed,
        finiteTimeCollisionKernel m kappa (quadraticCollisionSign q) time
            (quadraticCollisionModes observed q) *
          quadraticSignedCollisionFlux q
            (modeAction energy (modeFrequency m)) observed) +
        repeatedAwaySameSignTwoCopyCorrectionSum
          m kappa time energy observed := by
  classical
  unfold repeatedAwaySameSignTwoCopyCorrectionSum
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro q _hq
  exact repeatedChildSameSignSignedFluxWithCorrection_eq_flux_add_twoCopy
    m kappa time energy observed q

/-- Exact sign partition of the two-copy correction. -/
theorem repeatedAwaySameSignTwoCopyCorrectionSum_eq_potential_add_counterrotating
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa time : Real)
    (energy : Lattice.Site N → Real) (observed : Lattice.Site N) :
    repeatedAwaySameSignTwoCopyCorrectionSum
        m kappa time energy observed =
      repeatedAwayPotentiallyResonantCorrectionSum
          m kappa time energy observed +
        repeatedAwayCounterrotatingCorrectionSum
          m kappa time energy observed := by
  classical
  unfold repeatedAwaySameSignTwoCopyCorrectionSum
    repeatedAwayPotentiallyResonantCorrectionSum
    repeatedAwayCounterrotatingCorrectionSum
    repeatedAwayPotentiallyResonantSameSignRepresentatives
    repeatedAwayCounterrotatingSameSignRepresentatives
  exact (Finset.sum_filter_add_sum_filter_not
    (positiveRepeatedChildSameSignRepresentatives N m observed)
    (fun q ↦ q.2.1 = 0)
    (fun q ↦ repeatedAwaySameSignTwoCopyWeight m energy observed q *
      finiteTimeCollisionKernel m kappa (quadraticCollisionSign q) time
        (quadraticCollisionModes observed q))).symm

/-- The named potentially resonant repeated-away sector has the exact
`omega_observed - 2 omega_child` mismatch. -/
theorem phaseMismatch_repeatedAwayPotentiallyResonant
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N) (q : QuadraticPhaseTerm N)
    (hq : q ∈ repeatedAwayPotentiallyResonantSameSignRepresentatives
      N m observed) :
    phaseMismatch m (quadraticCollisionSign q)
        (quadraticCollisionModes observed q) =
      modeFrequency m observed - 2 * modeFrequency m (q.1 0) := by
  have hfilter := Finset.mem_filter.mp hq
  have hbase :=
    (mem_positiveRepeatedChildSameSignRepresentatives_iff
      m observed q).1 hfilter.1
  have hRepeated := hbase.2.1
  have hzero : q.2.1 = 0 := hfilter.2
  have hone : q.2.2 = 0 := hRepeated.2.symm.trans hzero
  rw [phaseMismatch_quadratic_bothPhase m observed q hzero hone,
    hRepeated.1]
  ring

/-- Exact resonance in the repeated-away dangerous sector is precisely the
frequency relation `omega_observed = 2 omega_child`. -/
theorem isResonant_repeatedAwayPotentiallyResonant_iff
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N) (q : QuadraticPhaseTerm N)
    (hq : q ∈ repeatedAwayPotentiallyResonantSameSignRepresentatives
      N m observed) :
    IsResonant m (quadraticCollisionSign q)
        (quadraticCollisionModes observed q) ↔
      modeFrequency m observed = 2 * modeFrequency m (q.1 0) := by
  unfold IsResonant
  rw [phaseMismatch_repeatedAwayPotentiallyResonant m observed q hq]
  constructor <;> intro h <;> linarith

/-- Every representative in the complementary repeated-away sector is
exactly all plus. -/
theorem quadraticCollisionSign_repeatedAwayCounterrotating
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N) (q : QuadraticPhaseTerm N)
    (hq : q ∈ repeatedAwayCounterrotatingSameSignRepresentatives
      N m observed) :
    quadraticCollisionSign q = counterrotatingThreeWaveSign := by
  have hfilter := Finset.mem_filter.mp hq
  have hbase :=
    (mem_positiveRepeatedChildSameSignRepresentatives_iff
      m observed q).1 hfilter.1
  have hleft : q.2.1 = 1 := by
    omega
  have hright : q.2.2 = 1 := hbase.2.1.2.symm.trans hleft
  exact quadraticCollisionSign_eq_counterrotating_of_bothConjugate
    q hleft hright

/-- The all-plus repeated-away correction uses the observed frequency as an
explicit gap. -/
theorem modeFrequency_le_abs_phaseMismatch_repeatedAwayCounterrotating
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N) (q : QuadraticPhaseTerm N)
    (hq : q ∈ repeatedAwayCounterrotatingSameSignRepresentatives
      N m observed) :
    modeFrequency m observed ≤
      |phaseMismatch m (quadraticCollisionSign q)
        (quadraticCollisionModes observed q)| := by
  rw [quadraticCollisionSign_repeatedAwayCounterrotating
    m observed q hq]
  exact modeFrequency_le_abs_phaseMismatch_counterrotating
    m (quadraticCollisionModes observed q)

/-- Literal fixed-volume constant for the repeated-away all-plus correction. -/
def repeatedAwayCounterrotatingStaticMass
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa : Real)
    (energy : Lattice.Site N → Real) (observed : Lattice.Site N) : Real :=
  ∑ q ∈ repeatedAwayCounterrotatingSameSignRepresentatives N m observed,
    |repeatedAwaySameSignTwoCopyWeight m energy observed q| *
      (kappa ^ 2 * normalizedInteractionWeight m
        (quadraticCollisionModes observed q)) *
      (2 / modeFrequency m observed) ^ 2

/-- Fixed-volume inverse-time bound for the complete repeated-away all-plus
two-copy correction.  The displayed constant is not `N`-uniform. -/
theorem abs_repeatedAwayCounterrotatingCorrectionSum_le_inverseTime
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa : Real)
    (energy : Lattice.Site N → Real) (observed : Lattice.Site N)
    {time : Real} (htime : 0 < time)
    (hObserved : 0 < modeFrequency m observed) :
    |repeatedAwayCounterrotatingCorrectionSum
        m kappa time energy observed| ≤
      repeatedAwayCounterrotatingStaticMass
        m kappa energy observed / time := by
  unfold repeatedAwayCounterrotatingCorrectionSum
    repeatedAwayCounterrotatingStaticMass
  exact abs_weightedQuadraticKernelSum_le_inverseTime
    m kappa observed
    (repeatedAwayCounterrotatingSameSignRepresentatives N m observed)
    (fun q ↦ q)
    (repeatedAwaySameSignTwoCopyWeight m energy observed)
    (fun _q ↦ modeFrequency m observed) htime
    (fun _q _hq ↦ hObserved)
    (fun q hq ↦
      modeFrequency_le_abs_phaseMismatch_repeatedAwayCounterrotating
        m observed q hq)

/-! ## Observed-carrier and observed-free corrections -/

/-- Conjugate signs in a selected slot and its opposite give the all-plus
collision sign, independently of which slot was selected. -/
theorem quadraticCollisionSign_eq_counterrotating_of_selected_bothConjugate
    {N : Nat} [NeZero N] (q : QuadraticPhaseTerm N) (selected : Fin 2)
    (hSelected : quadraticPhaseTermBinarySign q selected = 1)
    (hOther : quadraticPhaseTermBinarySign q
      (otherQuadraticSlot selected) = 1) :
    quadraticCollisionSign q = counterrotatingThreeWaveSign := by
  fin_cases selected
  · exact quadraticCollisionSign_eq_counterrotating_of_bothConjugate
      q hSelected hOther
  · exact quadraticCollisionSign_eq_counterrotating_of_bothConjugate
      q hOther hSelected

/-- Carrier-observed parameters with conjugate observed carrier and phase
free input.  Their mismatch can be `2 omega_observed - omega_free`. -/
def observedCarrierPotentiallyResonantParameters
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N) :
    Finset (PositiveObservedCarrierParameter N m observed) := by
  classical
  exact Finset.univ.filter fun parameter ↦
    quadraticPhaseTermBinarySign parameter.q parameter.selected = 1 ∧
      quadraticPhaseTermBinarySign parameter.q
        (otherQuadraticSlot parameter.selected) = 0

/-- Complement of the named carrier-observed dangerous sector. -/
def observedCarrierOffResonantParameters
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N) :
    Finset (PositiveObservedCarrierParameter N m observed) := by
  classical
  exact Finset.univ.filter fun parameter ↦ ¬
    (quadraticPhaseTermBinarySign parameter.q parameter.selected = 1 ∧
      quadraticPhaseTermBinarySign parameter.q
        (otherQuadraticSlot parameter.selected) = 0)

/-- One carrier-observed signed-kernel summand. -/
def observedCarrierCorrectionTerm
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa time : Real)
    (energy : Lattice.Site N → Real) (observed : Lattice.Site N)
    (parameter : PositiveObservedCarrierParameter N m observed) : Real :=
  (quadraticInputInteractionSign parameter.q
      parameter.selected).coefficient *
    (finiteTimeCollisionKernel m kappa
        (quadraticCollisionSign parameter.q) time
        (quadraticCollisionModes observed parameter.q) *
      modeAction energy (modeFrequency m) observed *
      modeAction energy (modeFrequency m)
        (parameter.q.1 (otherQuadraticSlot parameter.selected)))

/-- Explicit possibly resonant part of the carrier-observed correction. -/
def observedCarrierPotentiallyResonantSum
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa time : Real)
    (energy : Lattice.Site N → Real) (observed : Lattice.Site N) : Real :=
  ∑ parameter ∈ observedCarrierPotentiallyResonantParameters m observed,
    observedCarrierCorrectionTerm m kappa time energy observed parameter

/-- Explicit algebraically off-resonant part of the carrier-observed
correction. -/
def observedCarrierOffResonantSum
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa time : Real)
    (energy : Lattice.Site N → Real) (observed : Lattice.Site N) : Real :=
  ∑ parameter ∈ observedCarrierOffResonantParameters m observed,
    observedCarrierCorrectionTerm m kappa time energy observed parameter

/-- Exact partition of the resolved carrier-observed sum. -/
theorem observedCarrierSignedKernelSum_eq_potential_add_offResonant
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa time : Real)
    (energy : Lattice.Site N → Real) (observed : Lattice.Site N) :
    observedCarrierSignedKernelSum m kappa time energy observed =
      observedCarrierPotentiallyResonantSum
          m kappa time energy observed +
        observedCarrierOffResonantSum
          m kappa time energy observed := by
  classical
  unfold observedCarrierSignedKernelSum
    observedCarrierPotentiallyResonantSum
    observedCarrierOffResonantSum
    observedCarrierPotentiallyResonantParameters
    observedCarrierOffResonantParameters
    observedCarrierCorrectionTerm
  exact (Finset.sum_filter_add_sum_filter_not Finset.univ
    (fun parameter : PositiveObservedCarrierParameter N m observed ↦
      quadraticPhaseTermBinarySign parameter.q parameter.selected = 1 ∧
        quadraticPhaseTermBinarySign parameter.q
          (otherQuadraticSlot parameter.selected) = 0)
    (fun parameter ↦
      (quadraticInputInteractionSign parameter.q
          parameter.selected).coefficient *
        (finiteTimeCollisionKernel m kappa
            (quadraticCollisionSign parameter.q) time
            (quadraticCollisionModes observed parameter.q) *
          modeAction energy (modeFrequency m) observed *
          modeAction energy (modeFrequency m)
            (parameter.q.1
              (otherQuadraticSlot parameter.selected))))).symm

/-- Exact mismatch of the named carrier-observed dangerous sector. -/
theorem phaseMismatch_observedCarrierPotentiallyResonant
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N)
    (parameter : PositiveObservedCarrierParameter N m observed)
    (hParameter : parameter ∈
      observedCarrierPotentiallyResonantParameters m observed) :
    phaseMismatch m (quadraticCollisionSign parameter.q)
        (quadraticCollisionModes observed parameter.q) =
      2 * modeFrequency m observed -
        modeFrequency m
          (parameter.q.1 (otherQuadraticSlot parameter.selected)) := by
  have hsign := (Finset.mem_filter.mp hParameter).2
  exact phaseMismatch_selectedConjugate_otherPhase_observed
    m observed parameter.q parameter.selected parameter.observed_selected.1
      hsign.1 hsign.2

/-- The carrier-observed dangerous sector is resonant exactly at
`omega_free = 2 omega_observed`. -/
theorem isResonant_observedCarrierPotentiallyResonant_iff
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N)
    (parameter : PositiveObservedCarrierParameter N m observed)
    (hParameter : parameter ∈
      observedCarrierPotentiallyResonantParameters m observed) :
    IsResonant m (quadraticCollisionSign parameter.q)
        (quadraticCollisionModes observed parameter.q) ↔
      modeFrequency m
          (parameter.q.1 (otherQuadraticSlot parameter.selected)) =
        2 * modeFrequency m observed := by
  unfold IsResonant
  rw [phaseMismatch_observedCarrierPotentiallyResonant
    m observed parameter hParameter]
  constructor <;> intro h <;> linarith

/-- Transparent pointwise gap used on the carrier-observed complement.  A
phase carrier leaves the positive free frequency; an all-plus carrier uses
the observed frequency. -/
def observedCarrierOffResonantGap
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N)
    (parameter : PositiveObservedCarrierParameter N m observed) : Real :=
  if quadraticPhaseTermBinarySign parameter.q parameter.selected = 0 then
    modeFrequency m
      (parameter.q.1 (otherQuadraticSlot parameter.selected))
  else modeFrequency m observed

theorem observedCarrierOffResonantGap_pos
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N)
    (parameter : PositiveObservedCarrierParameter N m observed)
    (_hParameter : parameter ∈ observedCarrierOffResonantParameters m observed)
    (hObserved : 0 < modeFrequency m observed) :
    0 < observedCarrierOffResonantGap m observed parameter := by
  classical
  by_cases hSelected :
      quadraticPhaseTermBinarySign parameter.q parameter.selected = 0
  · rw [observedCarrierOffResonantGap, if_pos hSelected]
    have hPositive : PositiveModeTuple m
        (quadraticCollisionModes observed parameter.q) := by
      simpa [positiveQuadraticSwapOrbitRepresentatives] using
        (Finset.mem_filter.mp parameter.q_mem).2
    simpa [quadraticCollisionModes] using
      hPositive (Fin.succ (otherQuadraticSlot parameter.selected))
  · rw [observedCarrierOffResonantGap, if_neg hSelected]
    exact hObserved

theorem observedCarrierOffResonantGap_le_abs_phaseMismatch
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N)
    (parameter : PositiveObservedCarrierParameter N m observed)
    (hParameter : parameter ∈
      observedCarrierOffResonantParameters m observed) :
    observedCarrierOffResonantGap m observed parameter ≤
      |phaseMismatch m (quadraticCollisionSign parameter.q)
        (quadraticCollisionModes observed parameter.q)| := by
  have hnot := (Finset.mem_filter.mp hParameter).2
  by_cases hSelected :
      quadraticPhaseTermBinarySign parameter.q parameter.selected = 0
  · rw [observedCarrierOffResonantGap, if_pos hSelected,
      abs_phaseMismatch_selectedPhase_observed_eq_freeFrequency
        m observed parameter.q parameter.selected
          parameter.observed_selected.1 hSelected]
  · have hSelectedOne :
        quadraticPhaseTermBinarySign parameter.q parameter.selected = 1 := by
      omega
    have hOtherOne : quadraticPhaseTermBinarySign parameter.q
        (otherQuadraticSlot parameter.selected) = 1 := by
      omega
    rw [observedCarrierOffResonantGap, if_neg hSelected,
      quadraticCollisionSign_eq_counterrotating_of_selected_bothConjugate
        parameter.q parameter.selected hSelectedOne hOtherOne]
    exact modeFrequency_le_abs_phaseMismatch_counterrotating
      m (quadraticCollisionModes observed parameter.q)

/-- Literal fixed-volume mass for the algebraically off-resonant part of the
carrier-observed correction. -/
def observedCarrierOffResonantStaticMass
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa : Real)
    (energy : Lattice.Site N → Real) (observed : Lattice.Site N) : Real :=
  ∑ parameter ∈ observedCarrierOffResonantParameters m observed,
    |(quadraticInputInteractionSign parameter.q
        parameter.selected).coefficient *
      (modeAction energy (modeFrequency m) observed *
        modeAction energy (modeFrequency m)
          (parameter.q.1 (otherQuadraticSlot parameter.selected)))| *
      (kappa ^ 2 * normalizedInteractionWeight m
        (quadraticCollisionModes observed parameter.q)) *
      (2 / observedCarrierOffResonantGap m observed parameter) ^ 2

/-- Fixed-volume `O(1 / T)` bound for every carrier-observed correction
outside the explicitly named `2 omega_observed = omega_free` sector. -/
theorem abs_observedCarrierOffResonantSum_le_inverseTime
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa : Real)
    (energy : Lattice.Site N → Real) (observed : Lattice.Site N)
    {time : Real} (htime : 0 < time)
    (hObserved : 0 < modeFrequency m observed) :
    |observedCarrierOffResonantSum
        m kappa time energy observed| ≤
      observedCarrierOffResonantStaticMass
        m kappa energy observed / time := by
  classical
  unfold observedCarrierOffResonantSum observedCarrierCorrectionTerm
    observedCarrierOffResonantStaticMass
  simpa only [mul_assoc, mul_left_comm, mul_comm] using
    (abs_weightedQuadraticKernelSum_le_inverseTime
      m kappa observed (observedCarrierOffResonantParameters m observed)
      (fun parameter ↦ parameter.q)
      (fun parameter ↦
        (quadraticInputInteractionSign parameter.q
            parameter.selected).coefficient *
          (modeAction energy (modeFrequency m) observed *
            modeAction energy (modeFrequency m)
              (parameter.q.1 (otherQuadraticSlot parameter.selected))))
      (observedCarrierOffResonantGap m observed) htime
      (fun parameter hParameter ↦
        observedCarrierOffResonantGap_pos
          m observed parameter hParameter hObserved)
      (fun parameter hParameter ↦
        observedCarrierOffResonantGap_le_abs_phaseMismatch
          m observed parameter hParameter))

/-- Free-observed parameters with a phase selected carrier.  The fixed free
input is conjugate at the observed mode, leaving the possible mismatch
`2 omega_observed - omega_selected`. -/
def observedFreePotentiallyResonantParameters
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N) :
    Finset (PositiveObservedFreeConnectedParameter N m observed) := by
  classical
  exact Finset.univ.filter fun parameter ↦
    quadraticPhaseTermBinarySign parameter.q parameter.selected = 0

/-- Complementary free-observed parameters; their selected input is also
conjugate, so all three collision signs are plus. -/
def observedFreeCounterrotatingParameters
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N) :
    Finset (PositiveObservedFreeConnectedParameter N m observed) := by
  classical
  exact Finset.univ.filter fun parameter ↦
    quadraticPhaseTermBinarySign parameter.q parameter.selected ≠ 0

/-- One free-observed collapsed signed-kernel summand. -/
def observedFreeCorrectionTerm
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa time : Real)
    (energy : Lattice.Site N → Real) (observed : Lattice.Site N)
    (parameter : PositiveObservedFreeConnectedParameter N m observed) : Real :=
  (quadraticInputInteractionSign parameter.q
      parameter.selected).coefficient *
    (finiteTimeCollisionKernel m kappa
        (quadraticCollisionSign parameter.q) time
        (quadraticCollisionModes observed parameter.q) *
      modeAction energy (modeFrequency m) observed *
      modeAction energy (modeFrequency m) observed)

def observedFreePotentiallyResonantSum
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa time : Real)
    (energy : Lattice.Site N → Real) (observed : Lattice.Site N) : Real :=
  ∑ parameter ∈ observedFreePotentiallyResonantParameters m observed,
    observedFreeCorrectionTerm m kappa time energy observed parameter

def observedFreeCounterrotatingSum
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa time : Real)
    (energy : Lattice.Site N → Real) (observed : Lattice.Site N) : Real :=
  ∑ parameter ∈ observedFreeCounterrotatingParameters m observed,
    observedFreeCorrectionTerm m kappa time energy observed parameter

/-- Exact sign split of the collapsed free-observed correction. -/
theorem observedFreeCollapsedKernelSum_eq_potential_add_counterrotating
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa time : Real)
    (energy : Lattice.Site N → Real) (observed : Lattice.Site N) :
    observedFreeCollapsedKernelSum m kappa time energy observed =
      observedFreePotentiallyResonantSum m kappa time energy observed +
        observedFreeCounterrotatingSum m kappa time energy observed := by
  classical
  unfold observedFreeCollapsedKernelSum
    observedFreePotentiallyResonantSum observedFreeCounterrotatingSum
    observedFreePotentiallyResonantParameters
    observedFreeCounterrotatingParameters observedFreeCorrectionTerm
  exact (Finset.sum_filter_add_sum_filter_not Finset.univ
    (fun parameter : PositiveObservedFreeConnectedParameter N m observed ↦
      quadraticPhaseTermBinarySign parameter.q parameter.selected = 0)
    (fun parameter ↦
      (quadraticInputInteractionSign parameter.q
          parameter.selected).coefficient *
        (finiteTimeCollisionKernel m kappa
            (quadraticCollisionSign parameter.q) time
            (quadraticCollisionModes observed parameter.q) *
          modeAction energy (modeFrequency m) observed *
          modeAction energy (modeFrequency m) observed))).symm

/-- Exact mismatch on the named free-observed dangerous sector. -/
theorem phaseMismatch_observedFreePotentiallyResonant
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N)
    (parameter : PositiveObservedFreeConnectedParameter N m observed)
    (hParameter : parameter ∈
      observedFreePotentiallyResonantParameters m observed) :
    phaseMismatch m (quadraticCollisionSign parameter.q)
        (quadraticCollisionModes observed parameter.q) =
      2 * modeFrequency m observed -
        modeFrequency m (parameter.q.1 parameter.selected) := by
  have hSelected := (Finset.mem_filter.mp hParameter).2
  exact phaseMismatch_selectedPhase_otherConjugate_observed
    m observed parameter.q parameter.selected parameter.observed_free.1
      hSelected parameter.free_sign

/-- Exact resonance criterion for the named free-observed dangerous sector. -/
theorem isResonant_observedFreePotentiallyResonant_iff
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N)
    (parameter : PositiveObservedFreeConnectedParameter N m observed)
    (hParameter : parameter ∈
      observedFreePotentiallyResonantParameters m observed) :
    IsResonant m (quadraticCollisionSign parameter.q)
        (quadraticCollisionModes observed parameter.q) ↔
      modeFrequency m (parameter.q.1 parameter.selected) =
        2 * modeFrequency m observed := by
  unfold IsResonant
  rw [phaseMismatch_observedFreePotentiallyResonant
    m observed parameter hParameter]
  constructor <;> intro h <;> linarith

theorem quadraticCollisionSign_observedFreeCounterrotating
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N)
    (parameter : PositiveObservedFreeConnectedParameter N m observed)
    (hParameter : parameter ∈
      observedFreeCounterrotatingParameters m observed) :
    quadraticCollisionSign parameter.q = counterrotatingThreeWaveSign := by
  have hne := (Finset.mem_filter.mp hParameter).2
  have hSelected :
      quadraticPhaseTermBinarySign parameter.q parameter.selected = 1 := by
    omega
  exact quadraticCollisionSign_eq_counterrotating_of_selected_bothConjugate
    parameter.q parameter.selected hSelected parameter.free_sign

/-- Literal fixed-volume mass of the free-observed all-plus correction. -/
def observedFreeCounterrotatingStaticMass
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa : Real)
    (energy : Lattice.Site N → Real) (observed : Lattice.Site N) : Real :=
  ∑ parameter ∈ observedFreeCounterrotatingParameters m observed,
    |(quadraticInputInteractionSign parameter.q
        parameter.selected).coefficient *
      (modeAction energy (modeFrequency m) observed *
        modeAction energy (modeFrequency m) observed)| *
      (kappa ^ 2 * normalizedInteractionWeight m
        (quadraticCollisionModes observed parameter.q)) *
      (2 / modeFrequency m observed) ^ 2

/-- Fixed-volume `O(1 / T)` estimate for the complete free-observed all-plus
correction. -/
theorem abs_observedFreeCounterrotatingSum_le_inverseTime
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa : Real)
    (energy : Lattice.Site N → Real) (observed : Lattice.Site N)
    {time : Real} (htime : 0 < time)
    (hObserved : 0 < modeFrequency m observed) :
    |observedFreeCounterrotatingSum m kappa time energy observed| ≤
      observedFreeCounterrotatingStaticMass
        m kappa energy observed / time := by
  classical
  unfold observedFreeCounterrotatingSum observedFreeCorrectionTerm
    observedFreeCounterrotatingStaticMass
  simpa only [mul_assoc, mul_left_comm, mul_comm] using
    (abs_weightedQuadraticKernelSum_le_inverseTime
      m kappa observed (observedFreeCounterrotatingParameters m observed)
      (fun parameter ↦ parameter.q)
      (fun parameter ↦
        (quadraticInputInteractionSign parameter.q
            parameter.selected).coefficient *
          (modeAction energy (modeFrequency m) observed *
            modeAction energy (modeFrequency m) observed))
      (fun _parameter ↦ modeFrequency m observed) htime
      (fun _parameter _hParameter ↦ hObserved)
      (fun parameter hParameter ↦ by
        rw [quadraticCollisionSign_observedFreeCounterrotating
          m observed parameter hParameter]
        exact modeFrequency_le_abs_phaseMismatch_counterrotating
          m (quadraticCollisionModes observed parameter.q)))

/-! ## All-equal channel-five correction -/

/-- One surviving all-equal channel-five correction term. -/
def allEqualChannelFiveCorrectionTerm
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa time : Real)
    (energy : Lattice.Site N → Real) (observed : Lattice.Site N)
    (parameter : QuadraticPhaseTerm N × (Fin 2 × Fin 2)) : Real :=
  (quadraticInputInteractionSign parameter.1
      parameter.2.1).coefficient *
    finiteTimeCollisionKernel m kappa
      (quadraticCollisionSign parameter.1) time
      (quadraticCollisionModes observed parameter.1) *
    modeAction energy (modeFrequency m) observed ^ 2

/-- Complete explicit channel-five correction left by the global all-equal
selector closure. -/
def allEqualChannelFiveCorrectionSum
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa time : Real)
    (energy : Lattice.Site N → Real) (observed : Lattice.Site N) : Real :=
  ∑ parameter ∈ positiveAllEqualChannelFiveParameters N m observed,
    allEqualChannelFiveCorrectionTerm
      m kappa time energy observed parameter

/-- The all-equal channel-five mismatch is completely classified: a phase
selected input gives `omega_observed`, while a conjugate selected input gives
`3 omega_observed`. -/
theorem phaseMismatch_allEqualChannelFive
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N)
    (parameter : QuadraticPhaseTerm N × (Fin 2 × Fin 2))
    (hParameter : parameter ∈
      positiveAllEqualChannelFiveParameters N m observed) :
    phaseMismatch m (quadraticCollisionSign parameter.1)
        (quadraticCollisionModes observed parameter.1) =
      if quadraticPhaseTermBinarySign parameter.1 parameter.2.1 = 0 then
        modeFrequency m observed
      else 3 * modeFrequency m observed := by
  have hParts :=
    (mem_positiveAllEqualChannelFiveParameters_iff
      m observed parameter).1 hParameter
  have hqParts :=
    (mem_positiveObservedAtBothChildrenRepresentatives_iff
      m observed parameter.1).1 hParts.1
  have hAll := hqParts.2.2
  have hOtherSign := (Finset.mem_filter.mp hParts.2).2
  have hAllAny (input : Fin 2) : observed = parameter.1.1 input := by
    fin_cases input
    · exact hAll.1
    · exact hAll.2
  by_cases hSelected :
      quadraticPhaseTermBinarySign parameter.1 parameter.2.1 = 0
  · rw [if_pos hSelected,
      phaseMismatch_selectedPhase_otherConjugate_observed
        m observed parameter.1 parameter.2.1
          (hAllAny (otherQuadraticSlot parameter.2.1))
          hSelected hOtherSign,
      ← hAllAny parameter.2.1]
    ring
  · have hSelectedOne :
        quadraticPhaseTermBinarySign parameter.1 parameter.2.1 = 1 := by
      omega
    rw [if_neg hSelected,
      quadraticCollisionSign_eq_counterrotating_of_selected_bothConjugate
        parameter.1 parameter.2.1 hSelectedOne hOtherSign,
      phaseMismatch_counterrotatingThreeWaveSign]
    simp only [quadraticCollisionModes_zero,
      quadraticCollisionModes_one, quadraticCollisionModes_two,
      ← hAll.1, ← hAll.2]
    ring

/-- Every channel-five parameter is separated from resonance by the observed
frequency. -/
theorem modeFrequency_le_abs_phaseMismatch_allEqualChannelFive
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N)
    (parameter : QuadraticPhaseTerm N × (Fin 2 × Fin 2))
    (hParameter : parameter ∈
      positiveAllEqualChannelFiveParameters N m observed) :
    modeFrequency m observed ≤
      |phaseMismatch m (quadraticCollisionSign parameter.1)
        (quadraticCollisionModes observed parameter.1)| := by
  rw [phaseMismatch_allEqualChannelFive m observed parameter hParameter]
  split_ifs
  · rw [abs_of_nonneg (modeFrequency_nonneg m observed)]
  · rw [abs_of_nonneg (mul_nonneg (by norm_num)
      (modeFrequency_nonneg m observed))]
    nlinarith [modeFrequency_nonneg m observed]

/-- Literal fixed-volume static mass for the complete all-equal channel-five
correction. -/
def allEqualChannelFiveStaticMass
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa : Real)
    (energy : Lattice.Site N → Real) (observed : Lattice.Site N) : Real :=
  ∑ parameter ∈ positiveAllEqualChannelFiveParameters N m observed,
    |(quadraticInputInteractionSign parameter.1
        parameter.2.1).coefficient *
      modeAction energy (modeFrequency m) observed ^ 2| *
      (kappa ^ 2 * normalizedInteractionWeight m
        (quadraticCollisionModes observed parameter.1)) *
      (2 / modeFrequency m observed) ^ 2

/-- Fixed-volume inverse-time bound for the entire all-equal channel-five
correction.  Its constant is literal and is not asserted to be `N`-uniform. -/
theorem abs_allEqualChannelFiveCorrectionSum_le_inverseTime
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa : Real)
    (energy : Lattice.Site N → Real) (observed : Lattice.Site N)
    {time : Real} (htime : 0 < time)
    (hObserved : 0 < modeFrequency m observed) :
    |allEqualChannelFiveCorrectionSum
        m kappa time energy observed| ≤
      allEqualChannelFiveStaticMass m kappa energy observed / time := by
  classical
  unfold allEqualChannelFiveCorrectionSum allEqualChannelFiveCorrectionTerm
    allEqualChannelFiveStaticMass
  simpa only [mul_assoc, mul_left_comm, mul_comm] using
    (abs_weightedQuadraticKernelSum_le_inverseTime
      m kappa observed
      (positiveAllEqualChannelFiveParameters N m observed)
      (fun parameter ↦ parameter.1)
      (fun parameter ↦
        modeAction energy (modeFrequency m) observed ^ 2 *
          (quadraticInputInteractionSign parameter.1
            parameter.2.1).coefficient)
      (fun _parameter ↦ modeFrequency m observed) htime
      (fun _parameter _hParameter ↦ hObserved)
      (fun parameter hParameter ↦
        modeFrequency_le_abs_phaseMismatch_allEqualChannelFive
          m observed parameter hParameter))

/-- The correction term does not depend on the retained outer placement.
Thus the two outer parameters add with equal sign; they do not form a
cancellation pair. -/
theorem allEqualChannelFiveCorrectionTerm_outer_independent
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa time : Real)
    (energy : Lattice.Site N → Real) (observed : Lattice.Site N)
    (q : QuadraticPhaseTerm N) (selected leftOuter rightOuter : Fin 2) :
    allEqualChannelFiveCorrectionTerm m kappa time energy observed
        (q, (selected, leftOuter)) =
      allEqualChannelFiveCorrectionTerm m kappa time energy observed
        (q, (selected, rightOuter)) := rfl

end

end ArchonPhysics.FreeFPUTDegenerateCorrectionResonanceClassification
