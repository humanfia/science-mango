import ArchonPhysics.CanonicalScalarIDSContinuity
import ArchonPhysics.CleanCycleAcousticCountEnvelope

/-!
# Acoustic bounds for the canonical scalar IDS

The clean-cycle acoustic count envelope and the deterministic comparison between
clean and random masses give square-root bounds on the canonical scalar IDS near
zero.  We use deliberately coarse radii so that the proof only needs
`Real.pi_le_four`.
-/

namespace ArchonPhysics.CanonicalScalarIDSAcousticBounds

open ArchonPhysics
open ArchonPhysics.CanonicalScalarIDSBlockApproximation
open ArchonPhysics.CanonicalScalarIDSContinuity
open ArchonPhysics.CanonicalScalarIDSUniformBlockLimit
open ArchonPhysics.CanonicalThresholdCountConcentrationInterface
open ArchonPhysics.CleanCycleAcousticCountEnvelope
open ArchonPhysics.MeasurableOrderedModeCoupling.Harmonic
open ArchonPhysics.RandomMassAcousticCountingComparison
open Filter MeasureTheory Set

noncomputable section

/-- A conservative clean-cycle radius used for the lower acoustic bound. -/
def acousticLowerRadius (E : Real) (N : Nat) : Nat :=
  ⌊(Real.sqrt E / 16) * (N : Real)⌋₊

/-- A conservative clean-cycle radius used for the upper acoustic bound. -/
def acousticUpperRadius (E : Real) (N : Nat) : Nat :=
  ⌊(Real.sqrt E / 2) * (N : Real)⌋₊

theorem acousticLowerRadius_cast_le (E : Real) (N : Nat) :
    (acousticLowerRadius E N : Real) ≤
      (Real.sqrt E / 16) * (N : Real) := by
  exact Nat.floor_le
    (mul_nonneg (div_nonneg (Real.sqrt_nonneg E) (by norm_num))
      (Nat.cast_nonneg N))

theorem acousticUpperRadius_lt_add_one (E : Real) (N : Nat) :
    (Real.sqrt E / 2) * (N : Real) <
      (acousticUpperRadius E N : Real) + 1 := by
  exact Nat.lt_floor_add_one _

theorem acousticLowerRadius_lt_volume
    (N : Nat) [NeZero N] {E : Real} (hE1 : E ≤ 1) :
    acousticLowerRadius E N < N := by
  have hsqrt : Real.sqrt E ≤ 1 := Real.sqrt_le_one.mpr hE1
  have ha : Real.sqrt E / 16 < 1 := by
    nlinarith [Real.sqrt_nonneg E]
  have hN : 0 < (N : Real) := by exact_mod_cast NeZero.pos N
  have hscaled : (Real.sqrt E / 16) * (N : Real) < (N : Real) := by
    simpa only [one_mul] using mul_lt_mul_of_pos_right ha hN
  exact_mod_cast
    (acousticLowerRadius_cast_le E N).trans_lt hscaled

theorem acousticUpperRadius_lt_volume
    (N : Nat) [NeZero N] {E : Real} (hE1 : E ≤ 1) :
    acousticUpperRadius E N < N := by
  have hsqrt : Real.sqrt E ≤ 1 := Real.sqrt_le_one.mpr hE1
  have ha : Real.sqrt E / 2 < 1 := by
    nlinarith [Real.sqrt_nonneg E]
  have hN : 0 < (N : Real) := by exact_mod_cast NeZero.pos N
  have hfloor : (acousticUpperRadius E N : Real) ≤
      (Real.sqrt E / 2) * (N : Real) := by
    exact Nat.floor_le
      (mul_nonneg (div_nonneg (Real.sqrt_nonneg E) (by norm_num))
        (Nat.cast_nonneg N))
  have hscaled : (Real.sqrt E / 2) * (N : Real) < (N : Real) := by
    simpa only [one_mul] using mul_lt_mul_of_pos_right ha hN
  exact_mod_cast hfloor.trans_lt hscaled

theorem clean_lower_energy_condition
    (N : Nat) [NeZero N] {E : Real} (hE0 : 0 ≤ E) :
    4 * Real.pi ^ 2 * (acousticLowerRadius E N : Real) ^ 2 /
        (N : Real) ^ 2 ≤ (4 / 5 : Real) * E := by
  have hN : 0 < (N : Real) := by exact_mod_cast NeZero.pos N
  have hfloor := acousticLowerRadius_cast_le E N
  have hfloor0 : 0 ≤ (acousticLowerRadius E N : Real) := by positivity
  have hscaled0 : 0 ≤ (Real.sqrt E / 16) * (N : Real) := by positivity
  have hsq : (acousticLowerRadius E N : Real) ^ 2 ≤
      ((Real.sqrt E / 16) * (N : Real)) ^ 2 := by
    nlinarith
  calc
    4 * Real.pi ^ 2 * (acousticLowerRadius E N : Real) ^ 2 /
          (N : Real) ^ 2 ≤
        4 * Real.pi ^ 2 * ((Real.sqrt E / 16) * (N : Real)) ^ 2 /
          (N : Real) ^ 2 := by gcongr
    _ = Real.pi ^ 2 / 64 * E := by
      field_simp [ne_of_gt hN]
      nlinarith [Real.sq_sqrt hE0]
    _ ≤ (4 / 5 : Real) * E := by
      have hpi : Real.pi ^ 2 ≤ 16 := by
        nlinarith [Real.pi_pos, Real.pi_le_four]
      nlinarith

theorem clean_upper_energy_condition
    (N : Nat) [NeZero N] {E : Real} (hE : 0 < E) :
    (6 / 5 : Real) * E <
      16 * ((acousticUpperRadius E N + 1 : Nat) : Real) ^ 2 /
        (N : Real) ^ 2 := by
  have hN : 0 < (N : Real) := by exact_mod_cast NeZero.pos N
  have hnext := acousticUpperRadius_lt_add_one E N
  have hleft0 : 0 ≤ (Real.sqrt E / 2) * (N : Real) := by positivity
  have hright0 : 0 ≤ ((acousticUpperRadius E N + 1 : Nat) : Real) := by
    positivity
  have hsq : ((Real.sqrt E / 2) * (N : Real)) ^ 2 <
      ((acousticUpperRadius E N + 1 : Nat) : Real) ^ 2 := by
    norm_num only [Nat.cast_add, Nat.cast_one]
    nlinarith
  calc
    (6 / 5 : Real) * E < 4 * E := by nlinarith
    _ = 16 * ((Real.sqrt E / 2) * (N : Real)) ^ 2 /
          (N : Real) ^ 2 := by
      field_simp [ne_of_gt hN]
      nlinarith [Real.sq_sqrt hE.le]
    _ < 16 * ((acousticUpperRadius E N + 1 : Nat) : Real) ^ 2 /
          (N : Real) ^ 2 := by gcongr

/-- The random normalized count dominates the conservative acoustic lower radius. -/
theorem lowerRadius_div_le_canonicalNormalizedHarmonicThresholdCount
    (N : Nat) [NeZero N] (omega : RandomEnsemble.SampleSpace)
    {E : Real} (hE0 : 0 ≤ E) (hE1 : E ≤ 1) :
    (acousticLowerRadius E N : Real) / (N : Real) ≤
      canonicalNormalizedHarmonicThresholdCount N E omega := by
  have hclean := orderedEigenvalueThresholdCount_clean_lower_of_quadratic
    N (acousticLowerRadius E N)
    (acousticLowerRadius_lt_volume N hE1)
    ((4 / 5 : Real) * E)
    (clean_lower_energy_condition N hE0)
  have hsandwich :=
    (iid_orderedEigenvalueThresholdCount_sandwich
      canonicalIIDMassPhaseEnsemble (N := N) omega E).1
  have hcount : acousticLowerRadius E N ≤
      orderedEigenvalueThresholdCount
        (harmonicHermitian
          (canonicalIIDMassPhaseEnsemble.restrictPositiveMass
            (N := N) omega)) E := by
    omega
  rw [canonicalNormalizedHarmonicThresholdCount_eq]
  exact div_le_div_of_nonneg_right (by exact_mod_cast hcount) (by positivity)

/-- The random normalized count is bounded by a conservative acoustic upper radius. -/
theorem canonicalNormalizedHarmonicThresholdCount_le_upperRadius_div
    (N : Nat) [NeZero N] (omega : RandomEnsemble.SampleSpace)
    {E : Real} (hE : 0 < E) (hE1 : E ≤ 1)
    (hrpos : 0 < acousticUpperRadius E N) :
    canonicalNormalizedHarmonicThresholdCount N E omega ≤
      ((2 * acousticUpperRadius E N + 1 : Nat) : Real) /
        (N : Real) := by
  have hclean := orderedEigenvalueThresholdCount_clean_upper_of_chordGap
    N (acousticUpperRadius E N) hrpos
    (acousticUpperRadius_lt_volume N hE1)
    ((6 / 5 : Real) * E)
    (clean_upper_energy_condition N hE)
  have hsandwich :=
    (iid_orderedEigenvalueThresholdCount_sandwich
      canonicalIIDMassPhaseEnsemble (N := N) omega E).2
  have hcount :
      orderedEigenvalueThresholdCount
        (harmonicHermitian
          (canonicalIIDMassPhaseEnsemble.restrictPositiveMass
            (N := N) omega)) E ≤
        2 * acousticUpperRadius E N + 1 := hsandwich.trans hclean
  rw [canonicalNormalizedHarmonicThresholdCount_eq]
  exact div_le_div_of_nonneg_right (by exact_mod_cast hcount) (by positivity)

/-- Expected normalized counts inherit the samplewise acoustic lower bound. -/
theorem lowerRadius_div_le_expectedCanonicalNormalizedHarmonicThresholdCount
    (N : Nat) [NeZero N] {E : Real} (hE0 : 0 ≤ E) (hE1 : E ≤ 1) :
    (acousticLowerRadius E N : Real) / (N : Real) ≤
      ∫ omega, canonicalNormalizedHarmonicThresholdCount N E omega
        ∂(RandomEnsemble.canonicalLaw) := by
  calc
    (acousticLowerRadius E N : Real) / (N : Real) =
        ∫ _omega, (acousticLowerRadius E N : Real) / (N : Real)
          ∂(RandomEnsemble.canonicalLaw) := by simp
    _ ≤ ∫ omega, canonicalNormalizedHarmonicThresholdCount N E omega
          ∂(RandomEnsemble.canonicalLaw) :=
      integral_mono (integrable_const _)
        (integrable_canonicalNormalizedHarmonicThresholdCount N E)
        (fun omega =>
          lowerRadius_div_le_canonicalNormalizedHarmonicThresholdCount
            N omega hE0 hE1)

/-- Expected normalized counts inherit the samplewise acoustic upper bound. -/
theorem expectedCanonicalNormalizedHarmonicThresholdCount_le_upperRadius_div
    (N : Nat) [NeZero N] {E : Real} (hE : 0 < E) (hE1 : E ≤ 1)
    (hrpos : 0 < acousticUpperRadius E N) :
    (∫ omega, canonicalNormalizedHarmonicThresholdCount N E omega
      ∂(RandomEnsemble.canonicalLaw)) ≤
      ((2 * acousticUpperRadius E N + 1 : Nat) : Real) /
        (N : Real) := by
  calc
    (∫ omega, canonicalNormalizedHarmonicThresholdCount N E omega
        ∂(RandomEnsemble.canonicalLaw)) ≤
        ∫ _omega,
          ((2 * acousticUpperRadius E N + 1 : Nat) : Real) /
            (N : Real) ∂(RandomEnsemble.canonicalLaw) :=
      integral_mono
        (integrable_canonicalNormalizedHarmonicThresholdCount N E)
        (integrable_const _)
        (fun omega =>
          canonicalNormalizedHarmonicThresholdCount_le_upperRadius_div
            N omega hE hE1 hrpos)
    _ = ((2 * acousticUpperRadius E N + 1 : Nat) : Real) /
        (N : Real) := by simp

theorem acousticLowerRadius_div_tendsto (E : Real) :
    Tendsto
      (fun N : Nat =>
        (acousticLowerRadius E N : Real) / (N : Real))
      atTop (nhds (Real.sqrt E / 16)) := by
  have hreal : Tendsto
      (fun x : Real => (⌊(Real.sqrt E / 16) * x⌋₊ : Real) / x)
      atTop (nhds (Real.sqrt E / 16)) :=
    tendsto_nat_floor_mul_div_atTop
      (show 0 ≤ Real.sqrt E / (16 : Real) by positivity)
  convert hreal.comp tendsto_natCast_atTop_atTop using 1
  funext N
  simp only [acousticLowerRadius, Function.comp_apply]

theorem acousticUpperRadius_tendsto_atTop
    {E : Real} (hE : 0 < E) :
    Tendsto (acousticUpperRadius E) atTop atTop := by
  change Tendsto (fun N : Nat => ⌊(Real.sqrt E / 2) * (N : Real)⌋₊)
    atTop atTop
  exact tendsto_nat_floor_mul_atTop (Real.sqrt E / 2)
    (show 0 < Real.sqrt E / (2 : Real) by positivity)

theorem acousticUpperEnvelope_div_tendsto (E : Real) :
    Tendsto
      (fun N : Nat =>
        ((2 * acousticUpperRadius E N + 1 : Nat) : Real) /
          (N : Real))
      atTop (nhds (Real.sqrt E)) := by
  have hradius : Tendsto
      (fun N : Nat =>
        (acousticUpperRadius E N : Real) / (N : Real))
      atTop (nhds (Real.sqrt E / 2)) := by
    have hreal : Tendsto
        (fun x : Real => (⌊(Real.sqrt E / 2) * x⌋₊ : Real) / x)
        atTop (nhds (Real.sqrt E / 2)) :=
      tendsto_nat_floor_mul_div_atTop
        (show 0 ≤ Real.sqrt E / (2 : Real) by positivity)
    convert hreal.comp tendsto_natCast_atTop_atTop using 1
    funext N
    simp only [acousticUpperRadius, Function.comp_apply]
  have hinv : Tendsto (fun N : Nat => (1 : Real) / (N : Real))
      atTop (nhds 0) := by
    simpa using
      (tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop :
        Tendsto (fun N : Nat => (1 : Real) / (N : Real))
          atTop (nhds 0))
  have htwice : Tendsto
      (fun N : Nat => 2 *
        ((acousticUpperRadius E N : Real) / (N : Real)))
      atTop (nhds (2 * (Real.sqrt E / 2))) :=
    (tendsto_const_nhds : Tendsto (fun _ : Nat => (2 : Real))
      atTop (nhds 2)).mul hradius
  convert htwice.add hinv using 1
  · funext N
    push_cast
    ring
  · ring

/-- The canonical scalar IDS has a square-root lower bound on `(0, 1]`. -/
theorem canonicalScalarIDSValue_acoustic_lower
    {E : Real} (hE : 0 < E) (hE1 : E ≤ 1) :
    Real.sqrt E / 16 ≤ canonicalScalarIDSValue E := by
  exact le_of_tendsto_of_tendsto'
    ((acousticLowerRadius_div_tendsto E).comp
      (tendsto_add_atTop_nat 1))
    (canonicalExpectedBlocks_tendstoUniformly_scalarIDS.tendsto_at E)
    (fun n =>
      lowerRadius_div_le_expectedCanonicalNormalizedHarmonicThresholdCount
        (n + 1) hE.le hE1)

/-- The canonical scalar IDS has a square-root upper bound on `(0, 1]`. -/
theorem canonicalScalarIDSValue_acoustic_upper
    {E : Real} (hE : 0 < E) (hE1 : E ≤ 1) :
    canonicalScalarIDSValue E ≤ Real.sqrt E := by
  have hrTop : Tendsto
      (fun n : Nat => acousticUpperRadius E (n + 1)) atTop atTop :=
    (acousticUpperRadius_tendsto_atTop hE).comp
      (tendsto_add_atTop_nat 1)
  have hrpos : ∀ᶠ n in atTop,
      0 < acousticUpperRadius E (n + 1) := by
    filter_upwards [hrTop.eventually (eventually_ge_atTop 1)] with n hn
    omega
  apply le_of_tendsto_of_tendsto
    (canonicalExpectedBlocks_tendstoUniformly_scalarIDS.tendsto_at E)
    ((acousticUpperEnvelope_div_tendsto E).comp
      (tendsto_add_atTop_nat 1))
  filter_upwards [hrpos] with n hn
  exact expectedCanonicalNormalizedHarmonicThresholdCount_le_upperRadius_div
    (n + 1) hE hE1 hn

/-- Two-sided acoustic square-root control on the canonical scalar IDS. -/
theorem canonicalScalarIDSValue_acoustic_sandwich
    {E : Real} (hE : 0 < E) (hE1 : E ≤ 1) :
    Real.sqrt E / 16 ≤ canonicalScalarIDSValue E ∧
      canonicalScalarIDSValue E ≤ Real.sqrt E :=
  ⟨canonicalScalarIDSValue_acoustic_lower hE hE1,
    canonicalScalarIDSValue_acoustic_upper hE hE1⟩

theorem canonicalScalarIDSValue_pos_of_pos_le_one
    {E : Real} (hE : 0 < E) (hE1 : E ≤ 1) :
    0 < canonicalScalarIDSValue E := by
  exact (div_pos (Real.sqrt_pos.2 hE) (by norm_num)).trans_le
    (canonicalScalarIDSValue_acoustic_lower hE hE1)

/-- The canonical scalar IDS is strictly positive at every positive energy. -/
theorem canonicalScalarIDSValue_pos_of_pos
    {E : Real} (hE : 0 < E) :
    0 < canonicalScalarIDSValue E := by
  by_cases hE1 : E ≤ 1
  · exact canonicalScalarIDSValue_pos_of_pos_le_one hE hE1
  · have hFone : 0 < canonicalScalarIDSValue 1 :=
      canonicalScalarIDSValue_pos_of_pos_le_one (by norm_num) le_rfl
    exact hFone.trans_le
      (monotone_canonicalScalarIDSValue (le_of_not_ge hE1))

end

end ArchonPhysics.CanonicalScalarIDSAcousticBounds
