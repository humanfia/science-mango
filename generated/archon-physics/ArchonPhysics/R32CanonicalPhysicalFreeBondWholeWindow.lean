import ArchonPhysics.R32CanonicalFreeBondConcentrationAnnealedV2NegativeTimeDraft
import ArchonPhysics.R32PhysicalSignedFreeBondEventsV3Final
import ArchonPhysics.R32CanonicalHaarAngleRepresentativeV3Final
import ArchonPhysics.RandomMassOrderedProjectorBridge
import ArchonPhysics.UniformRandomMassHarmonicSpectrumBound

/-!
# Canonical physical signed free-bond whole-window event

This isolated compositor combines the negative-time signed Haar tail with the
Borel physical finite-grid event.  The finite grid itself is the measurable
witness for the whole-window assertion; deterministic Lipschitz interpolation
is performed only after a sample belongs to that event.
-/

namespace ArchonPhysics.R32CanonicalPhysicalFreeBondWholeWindow

open ArchonPhysics
open ArchonPhysics.HarmonicNormalizedEdgeFrame
open ArchonPhysics.MeasurableOrderedModeCoupling.Harmonic
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.OrderedSingleModeProjector
open ArchonPhysics.R32CanonicalFreeBondConcentrationV3Final
open ArchonPhysics.R32CanonicalFreeBondConcentrationAnnealedV2NegativeTimeDraft
open ArchonPhysics.R32FrozenBondCoefficientBoundV2
open ArchonPhysics.R32HaarScalarTailCleanV4
open ArchonPhysics.R32PhysicalSignedFreeBondEventsV3Final
open ArchonPhysics.R32SignedFreeBondMeasurabilityV3Final
open ArchonPhysics.UniformRandomMassHarmonicSpectrumBound
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal ProbabilityTheory

noncomputable section

local instance canonicalProbabilityMeasure :
    IsProbabilityMeasure canonicalIIDMassPhaseEnsemble.probability :=
  ⟨canonicalIIDMassPhaseEnsemble.probability_univ⟩

/-! ## The physical grid is exactly the negative-time signed grid -/

theorem canonicalPhysicalSignedSimpleFreeGridBad_eq_negative
    {N : Nat} [NeZero N] (T g : Real) :
    canonicalPhysicalSignedSimpleFreeGridBad (N := N) T g =
      canonicalSignedSimpleNegativeFreeGridBad (N := N) T g := by
  rfl

theorem canonicalPhysicalSignedSimpleFreeGridBad_measureReal_le
    {N : Nat} [NeZero N] (hN : 3 ≤ N) (T g : Real) :
    canonicalIIDMassPhaseEnsemble.probability.real
        (canonicalPhysicalSignedSimpleFreeGridBad (N := N) T g) ≤
      freeGridBadBudget T g N := by
  rw [canonicalPhysicalSignedSimpleFreeGridBad_eq_negative]
  exact canonicalSignedSimpleNegativeFreeGridBad_measureReal_le hN T g

/-! ## The simple-spectrum guard is null only on a null set -/

theorem rawCanonicalFrozenMass_eq_restrictPositiveMass
    {N : Nat} [NeZero N] (sample : RandomEnsemble.SampleSpace) :
    rawCanonicalFrozenMass (N := N) sample.1 =
      canonicalIIDMassPhaseEnsemble.restrictPositiveMass sample := by
  rw [Lattice.PositiveMassConfig.mk.injEq]
  rfl

theorem rawCanonicalFrozenMass_simpleOrderedSpectrum_ae
    {N : Nat} [NeZero N] (hN : 3 ≤ N) :
    ∀ᵐ sample ∂canonicalIIDMassPhaseEnsemble.probability,
      SimpleOrderedSpectrum
        (harmonicHermitian (rawCanonicalFrozenMass (N := N) sample.1)) := by
  filter_upwards
    [RandomMassOrderedProjectorBridge.simpleOrderedSpectrum_ae
      canonicalIIDMassPhaseEnsemble (show 2 ≤ N by omega)] with sample hsimple
  rwa [rawCanonicalFrozenMass_eq_restrictPositiveMass]

/-- The Borel finite-grid witness has complement bounded by the explicit
negative-time union budget. -/
theorem canonicalPhysicalSignedFreeGridGood_compl_measureReal_le
    {N : Nat} [NeZero N] (hN : 3 ≤ N) (T g : Real) :
    canonicalIIDMassPhaseEnsemble.probability.real
        ((canonicalPhysicalSignedFreeGridGood (N := N) T g)ᶜ) ≤
      freeGridBadBudget T g N := by
  have hae : ∀ᵐ sample ∂canonicalIIDMassPhaseEnsemble.probability,
      sample ∈ (canonicalPhysicalSignedFreeGridGood (N := N) T g)ᶜ →
        sample ∈ canonicalPhysicalSignedSimpleFreeGridBad (N := N) T g := by
    filter_upwards [rawCanonicalFrozenMass_simpleOrderedSpectrum_ae hN]
      with sample hsimple
    intro hnotGood
    by_contra hnotBad
    exact hnotGood ⟨hsimple, hnotBad⟩
  have hmeasure :
      canonicalIIDMassPhaseEnsemble.probability
          ((canonicalPhysicalSignedFreeGridGood (N := N) T g)ᶜ) ≤
        canonicalIIDMassPhaseEnsemble.probability
          (canonicalPhysicalSignedSimpleFreeGridBad (N := N) T g) :=
    measure_mono_ae hae
  calc
    canonicalIIDMassPhaseEnsemble.probability.real
        ((canonicalPhysicalSignedFreeGridGood (N := N) T g)ᶜ) ≤
        canonicalIIDMassPhaseEnsemble.probability.real
          (canonicalPhysicalSignedSimpleFreeGridBad (N := N) T g) := by
      rw [measureReal_def, measureReal_def]
      exact ENNReal.toReal_mono
        (measure_ne_top canonicalIIDMassPhaseEnsemble.probability _) hmeasure
    _ ≤ freeGridBadBudget T g N :=
      canonicalPhysicalSignedSimpleFreeGridBad_measureReal_le hN T g

/-! ## A deterministic uniform time-Lipschitz estimate -/

/-- A signed coefficient vector differs modewise from the original normalized
edge-frame vector only by signs.  Those signs can be absorbed by adding `pi`
to the corresponding real phases. -/
theorem signedHaarBondField_eq_original_realPhase
    {N : Nat} [NeZero N]
    (angle : UnitAddCircle → Real)
    (hangle : IsHaarAngleRepresentative angle)
    (m : Lattice.PositiveMassConfig N)
    (hsimple : SimpleOrderedSpectrum (harmonicHermitian m))
    (bond : Lattice.Site N)
    (phase : HarmonicOrderedModeIndex N → UnitAddCircle)
    (time : Real) :
    signedHaarBondField m bond phase time =
      r32FrozenFreePhysicalBondField m bond
        (fun mode ↦
          if signedFrozenBondCoefficient m bond mode =
              r32FrozenBondCoefficient m bond mode then
            angle (phase mode)
          else angle (phase mode) + Real.pi)
        time := by
  unfold signedHaarBondField fixedTimeHaarScalarSum
    r32FrozenFreePhysicalBondField
  apply Finset.sum_congr rfl
  intro mode _hmode
  rw [hangle]
  by_cases heq : signedFrozenBondCoefficient m bond mode =
      r32FrozenBondCoefficient m bond mode
  · simp [heq]
  · have hneg : signedFrozenBondCoefficient m bond mode =
        -r32FrozenBondCoefficient m bond mode :=
      (eq_or_eq_neg_of_sq_eq_sq _ _
        (signedFrozenBondCoefficient_sq_eq_original
          m hsimple bond mode)).resolve_left heq
    simp only [heq, if_false]
    rw [hneg]
    rw [show
      orderedModeFrequency (harmonicHermitian m) mode * time +
          (angle (phase mode) + Real.pi) =
        (orderedModeFrequency (harmonicHermitian m) mode * time +
          angle (phase mode)) + Real.pi by ring,
      Real.cos_add_pi]
    ring

/-- On the frozen mass box, the measurable signed Haar bond field is
uniformly `128`-Lipschitz in time. -/
theorem signedHaarBondField_timeLipschitz_128
    {N : Nat} [NeZero N] (hN : 3 ≤ N)
    (angle : UnitAddCircle → Real)
    (hangle : IsHaarAngleRepresentative angle)
    (m : Lattice.PositiveMassConfig N)
    (hmassLower : ∀ site, (4 / 5 : Real) ≤ m.mass site)
    (hsimple : SimpleOrderedSpectrum (harmonicHermitian m))
    (bond : Lattice.Site N)
    (phase : HarmonicOrderedModeIndex N → UnitAddCircle)
    (s t : Real) :
    |signedHaarBondField m bond phase t -
        signedHaarBondField m bond phase s| ≤ 128 * |t - s| := by
  rw [signedHaarBondField_eq_original_realPhase
      angle hangle m hsimple bond phase t,
    signedHaarBondField_eq_original_realPhase
      angle hangle m hsimple bond phase s]
  have hfrequency : ∀ mode : HarmonicOrderedModeIndex N,
      orderedModeFrequency (harmonicHermitian m) mode ≤ Real.sqrt 5 := by
    intro mode
    simpa using orderedModeFrequency_harmonic_le_sqrt_four_div_massLower
      m (4 / 5 : Real) (by norm_num) hmassLower mode
  have hlip := r32FrozenFreePhysicalBondField_timeLipschitz_uniform
    hN m hsimple (Real.sqrt 5) (Real.sqrt_nonneg _) hfrequency
    bond
    (fun mode ↦
      if signedFrozenBondCoefficient m bond mode =
          r32FrozenBondCoefficient m bond mode then
        angle (phase mode)
      else angle (phase mode) + Real.pi)
    s t
  have hpredNat : 0 < N - 1 := by omega
  have hpred : 0 < (((N - 1 : Nat) : Real)) := by
    exact_mod_cast hpredNat
  have hNpredNat : N ≤ 2 * (N - 1) := by omega
  have hNpred : (N : Real) ≤ 2 * (((N - 1 : Nat) : Real)) := by
    exact_mod_cast hNpredNat
  have hratio :
      6 * (N : Real) / (((N - 1 : Nat) : Real)) ≤ 12 := by
    apply (div_le_iff₀ hpred).2
    nlinarith
  have hsqrtRatio :
      Real.sqrt (6 * (N : Real) / (((N - 1 : Nat) : Real))) ≤ 12 := by
    have hsqrt := Real.sqrt_le_sqrt hratio
    have hsqrtTwelve : Real.sqrt 12 ≤ 12 := by
      nlinarith [Real.sq_sqrt (by norm_num : (0 : Real) ≤ 12),
        Real.sqrt_nonneg 12]
    exact hsqrt.trans hsqrtTwelve
  have hsqrtFive : Real.sqrt 5 ≤ 5 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : Real) ≤ 5),
      Real.sqrt_nonneg 5]
  have hconstant :
      Real.sqrt 5 *
          Real.sqrt (6 * (N : Real) / (((N - 1 : Nat) : Real))) ≤
        128 := by
    have hmul := mul_le_mul hsqrtFive hsqrtRatio
      (Real.sqrt_nonneg _) (by norm_num : (0 : Real) ≤ 5)
    nlinarith
  exact hlip.trans
    (mul_le_mul_of_nonneg_right hconstant (abs_nonneg _))

theorem rawCanonicalFrozenMass_lower
    {N : Nat} [NeZero N]
    (mass : RandomEnsemble.RawMassSequence) (site : Lattice.Site N) :
    (4 / 5 : Real) ≤ (rawCanonicalFrozenMass (N := N) mass).mass site := by
  simpa [rawCanonicalFrozenMass, RandomEnsemble.massLower] using
    (canonicalIIDMassPhaseEnsemble.mass_mem_support site.val
      (mass, fun _ ↦ 0)).1

/-- The physical-sign wrapper has the same uniform constant; the reversal
`time ↦ -time` is an isometry. -/
theorem canonicalPhysicalSignedHaarBondField_timeLipschitz_128
    {N : Nat} [NeZero N] (hN : 3 ≤ N)
    (sample : RandomEnsemble.SampleSpace)
    (hsimple : SimpleOrderedSpectrum
      (harmonicHermitian (rawCanonicalFrozenMass (N := N) sample.1)))
    (bond : Lattice.Site N) (s t : Real) :
    |physicalSignedHaarBondField
          (rawCanonicalFrozenMass (N := N) sample.1) bond
          (orderedPhaseBlockFromSequence (N := N) sample.2) t -
        physicalSignedHaarBondField
          (rawCanonicalFrozenMass (N := N) sample.1) bond
          (orderedPhaseBlockFromSequence (N := N) sample.2) s| ≤
      128 * |t - s| := by
  have hlip := signedHaarBondField_timeLipschitz_128
    hN canonicalHaarAngle canonicalHaarAngle_isHaarAngleRepresentative
    (rawCanonicalFrozenMass (N := N) sample.1)
    (rawCanonicalFrozenMass_lower sample.1) hsimple bond
    (orderedPhaseBlockFromSequence (N := N) sample.2) (-s) (-t)
  change
    |signedHaarBondField (rawCanonicalFrozenMass sample.1) bond
          (orderedPhaseBlockFromSequence sample.2) (-t) -
        signedHaarBondField (rawCanonicalFrozenMass sample.1) bond
          (orderedPhaseBlockFromSequence sample.2) (-s)| ≤
      128 * |t - s|
  calc
    _ ≤ 128 * |(-t) - (-s)| := hlip
    _ = 128 * |t - s| := by
      rw [show (-t) - (-s) = -(t - s) by ring, abs_neg]

/-! ## The same Borel witness controls the entire kinetic window -/

/-- Membership in the high-probability finite-grid event implies the desired
uniform physical signed free-bond bound at every time in `[0, T / g^2]`. -/
theorem canonicalPhysicalSignedFreeGridGood_implies_wholeWindow_bound
    {N : Nat} [NeZero N] (hN : 3 ≤ N)
    (T g : Real) (hT : 0 ≤ T) (hg : 0 < g)
    {sample : RandomEnsemble.SampleSpace}
    (hgood : sample ∈
      canonicalPhysicalSignedFreeGridGood (N := N) T g)
    (bond : Lattice.Site N) (time : Real)
    (htime : time ∈ Icc (0 : Real) (T / g ^ 2)) :
    |physicalSignedHaarBondField
      (rawCanonicalFrozenMass (N := N) sample.1) bond
      (orderedPhaseBlockFromSequence (N := N) sample.2) time| ≤
      g ^ 4 := by
  apply canonicalPhysicalSignedFreeGridGood_implies_kineticWindow_bound
    T g 128 hT hg (by norm_num) ?_ hgood
      (canonicalPhysicalSignedHaarBondField_timeLipschitz_128
        hN sample hgood.1) bond time htime
  have hg4 : 0 ≤ g ^ 4 := by positivity
  norm_num [freeTimeGridScale]
  nlinarith

#print axioms canonicalPhysicalSignedFreeGridGood_compl_measureReal_le
#print axioms signedHaarBondField_timeLipschitz_128
#print axioms canonicalPhysicalSignedFreeGridGood_implies_wholeWindow_bound

end

end ArchonPhysics.R32CanonicalPhysicalFreeBondWholeWindow
