import ArchonPhysics.DiagramRemainderCertificate
import ArchonPhysics.EqualMassPeriodicFPUTCanonicalTwoToTwoShell
import ArchonPhysics.EqualMassPeriodicFPUTFourWaveFGRDecomposition
import ArchonPhysics.PhyslibFPUTAfterSecondPicardEnergyEnvelope

/-!
# Explicit alpha-volume-time bounds for equal-mass four-wave remainders

The existing fixed-output enumeration has at most `32 N²` supported
two-vertex diagrams, while the complete degenerate `2 ↔ 2` sector has at
most `128 N` diagrams.  This file combines those exact counts with a concrete
single-diagram estimate.

Each unnormalized equal-mass quadratic Fourier vertex is bounded by
`8 |α|`.  Consequently a supported effective four-wave coefficient is
bounded by `64 |α|² / gap_N`, and its finite-time Duhamel coefficient by
`64 |α|² |T| / gap_N`.  Thus the complete and degenerate fixed-output
sums have explicit envelopes of orders

* `|α|² |T| N² / gap_N`, and
* `|α|² |T| N / gap_N`, respectively.

If `gap_N ≥ c N⁻s`, the sufficient power-law windows
`α_N = N⁻a`, `T_N = N^b` are `2a > b+s+2` for the full family and
`2a > b+s+1` for the degenerate family.

The exact post-second-Picard energy envelope presently has additional
volume-dependent factors for which no uniform polynomial estimate is proved
in the library.  The final section therefore records the minimal growing-time
remainder hypothesis `C |α|ᵖ |T|ʳ / Nʳ` and proves its exponent criterion
`ap+r > bq`.  It does not replace this condition by an empty `error → 0`
assumption and does not assume a kinetic equation.
-/

namespace ArchonPhysics.EqualMassPeriodicFPUTAlphaNTJointRemainder

open scoped BigOperators

open ArchonPhysics
open ArchonPhysics.EqualMassPeriodicFPUTCanonicalTwoToTwoShell
open ArchonPhysics.EqualMassPeriodicFPUTEffectiveFourWaveVertex
open ArchonPhysics.EqualMassPeriodicFPUTFourWaveFGRDecomposition
open ArchonPhysics.EqualMassPeriodicFPUTFourWaveRemainderCounting
open ArchonPhysics.EqualMassPeriodicFPUTFourierHamiltonian
open ArchonPhysics.EqualMassPeriodicFPUTFourierThreeWave
open ArchonPhysics.FinitePhaseMonomials
open ArchonPhysics.Lattice
open ArchonPhysics.NonresonantOscillatoryGain
open ArchonPhysics.PhyslibFPUTBinaryInteractionTreeCouples
open Filter Set Topology

noncomputable section

/-! ## Concrete one-diagram bound -/

/-- A Fourier character has unit complex norm. -/
theorem norm_fourierWave_eq_one
    (N : Nat) [NeZero N] (k x : Site N) :
    ‖fourierWave N k x‖ = 1 := by
  rw [fourierWave,
    ArchonPhysics.CleanCycleAcousticCountEnvelope.cleanCycleFourierBasis_apply]
  exact Circle.norm_coe _

/-- Every forward-bond multiplier has norm at most two. -/
theorem norm_bondFourierSymbol_le_two
    (N : Nat) [NeZero N] (k : Site N) :
    ‖bondFourierSymbol N k‖ ≤ 2 := by
  unfold bondFourierSymbol
  calc
    ‖fourierWave N k 1 - 1‖ ≤ ‖fourierWave N k 1‖ + ‖(1 : Complex)‖ :=
      norm_sub_le _ _
    _ = 2 := by rw [norm_fourierWave_eq_one]; norm_num

/-- Every outgoing-divergence multiplier has norm at most two. -/
theorem norm_outgoingFourierSymbol_le_two
    (N : Nat) [NeZero N] (k : Site N) :
    ‖outgoingFourierSymbol N k‖ ≤ 2 := by
  unfold outgoingFourierSymbol
  calc
    ‖(1 : Complex) - fourierWave N k (-1)‖ ≤
        ‖(1 : Complex)‖ + ‖fourierWave N k (-1)‖ := norm_sub_le _ _
    _ = 2 := by rw [norm_fourierWave_eq_one]; norm_num

/-- The literal unnormalized quadratic Fourier vertex is bounded by the
product of three bond/divergence symbols. -/
theorem norm_pureAlphaQuadraticFourierCoefficient_le
    (N : Nat) [NeZero N] (alpha : Real) (output left : Site N) :
    ‖pureAlphaQuadraticFourierCoefficient N alpha output left‖ ≤
      8 * |alpha| := by
  unfold pureAlphaQuadraticFourierCoefficient
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  calc
    |alpha| * ‖outgoingFourierSymbol N output‖ *
          ‖bondFourierSymbol N left‖ *
          ‖bondFourierSymbol N (output - left)‖ ≤
        |alpha| * 2 * 2 * 2 := by
      gcongr
      · exact norm_outgoingFourierSymbol_le_two N output
      · exact norm_bondFourierSymbol_le_two N left
      · exact norm_bondFourierSymbol_le_two N (output - left)
    _ = 8 * |alpha| := by ring

/-- Phase/conjugate branch action preserves complex norm. -/
theorem norm_phaseSignActComplex
    (sign : PhaseSign) (value : Complex) :
    ‖phaseSignActComplex sign value‖ = ‖value‖ := by
  cases sign <;> simp [phaseSignActComplex]

/-- The product of the two quadratic vertices is bounded by
`64 |α|²`. -/
theorem norm_twoVertexNumerator_le
    (N : Nat) [NeZero N] (alpha : Real)
    (diagram : EffectiveFourWaveDiagram N) :
    ‖twoVertexNumerator N alpha diagram‖ ≤ 64 * |alpha| ^ 2 := by
  unfold twoVertexNumerator outerQuadraticVertexCoefficient
    innerQuadraticVertexCoefficient
  rw [norm_mul, norm_phaseSignActComplex]
  calc
    ‖pureAlphaQuadraticFourierCoefficient N alpha
          (outputMomentum diagram) (outerVertexLeftMomentum diagram)‖ *
        ‖pureAlphaQuadraticFourierCoefficient N alpha
          (intermediateMomentum diagram)
          (phaseSignedMomentum (innerLeftBranch diagram)
            (innerLeftMomentum diagram))‖ ≤
        (8 * |alpha|) * (8 * |alpha|) :=
      mul_le_mul
        (norm_pureAlphaQuadraticFourierCoefficient_le N alpha _ _)
        (norm_pureAlphaQuadraticFourierCoefficient_le N alpha _ _)
        (norm_nonneg _) (by positivity)
    _ = 64 * |alpha| ^ 2 := by ring

/-- A supported diagram whose five diagram modes are not all active has zero
two-vertex numerator. -/
theorem twoVertexNumerator_eq_zero_of_not_active
    {N : Nat} [NeZero N] (alpha : Real)
    (diagram : EffectiveFourWaveDiagram N)
    (hsupported : IsTwoVertexMomentumSupported diagram)
    (hnotActive : ¬ IsActiveEffectiveFourWaveDiagram diagram) :
    twoVertexNumerator N alpha diagram = 0 := by
  have hzero : ∃ slot : Fin 5, diagramMode diagram slot = 0 := by
    by_contra hnozero
    apply hnotActive
    refine ⟨hsupported, ?_⟩
    intro slot hslot
    exact hnozero ⟨slot, hslot⟩
  obtain ⟨slot, hslot⟩ := hzero
  fin_cases slot
  · exact twoVertexNumerator_eq_zero_of_output_zero
      N alpha diagram hslot
  · exact twoVertexNumerator_eq_zero_of_intermediate_zero
      N alpha diagram hslot
  · exact twoVertexNumerator_eq_zero_of_spectator_zero
      N alpha diagram hsupported hslot
  · exact twoVertexNumerator_eq_zero_of_innerLeft_zero
      N alpha diagram hslot
  · exact twoVertexNumerator_eq_zero_of_innerRight_zero
      N alpha diagram hsupported hslot

/-- Concrete coefficient bound valid for every supported diagram.  Inactive
zero-mode diagrams vanish; active diagrams use the proved finite-volume
three-wave gap. -/
theorem norm_effectiveFourWaveCoefficient_le_alpha_sq_div_gap
    {N : Nat} [NeZero N] (alpha : Real)
    (diagram : EffectiveFourWaveDiagram N)
    (hsupported : IsTwoVertexMomentumSupported diagram) :
    ‖effectiveFourWaveCoefficient N alpha diagram‖ ≤
      64 * |alpha| ^ 2 / finiteNonzeroMomentumThreeWaveGap N := by
  by_cases hactive : IsActiveEffectiveFourWaveDiagram diagram
  · let activeDiagram : ActiveEffectiveFourWaveDiagram N :=
      ⟨diagram, hactive⟩
    have hgap : finiteNonzeroMomentumThreeWaveGap N ≤
        |innerHomologicalDivisor diagram| :=
      finiteThreeWaveGap_le_abs_innerHomologicalDivisor activeDiagram
    rw [effectiveFourWaveCoefficient, norm_div, norm_mul,
      Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
    calc
      ‖twoVertexNumerator N alpha diagram‖ /
          |innerHomologicalDivisor diagram| ≤
        (64 * |alpha| ^ 2) / |innerHomologicalDivisor diagram| :=
          div_le_div_of_nonneg_right
            (norm_twoVertexNumerator_le N alpha diagram) (abs_nonneg _)
      _ ≤ (64 * |alpha| ^ 2) /
          finiteNonzeroMomentumThreeWaveGap N :=
        div_le_div_of_nonneg_left (by positivity)
          (finiteNonzeroMomentumThreeWaveGap_pos N) hgap
  · rw [effectiveFourWaveCoefficient,
      twoVertexNumerator_eq_zero_of_not_active
        alpha diagram hsupported hactive,
      zero_div, norm_zero]
    exact div_nonneg (by positivity)
      (finiteNonzeroMomentumThreeWaveGap_pos N).le

/-- The existing oscillatory-integral bound turns the coefficient estimate
into the explicit single-diagram `α-N-T` envelope. -/
theorem norm_effectiveDiagramDuhamelCoefficient_le_alpha_sq_time_div_gap
    {N : Nat} [NeZero N] (alpha time : Real)
    (diagram : EffectiveFourWaveDiagram N)
    (hsupported : IsTwoVertexMomentumSupported diagram) :
    ‖effectiveDiagramDuhamelCoefficient N alpha diagram time‖ ≤
      (64 * |alpha| ^ 2 / finiteNonzeroMomentumThreeWaveGap N) * |time| := by
  rw [effectiveDiagramDuhamelCoefficient_eq, norm_mul]
  exact mul_le_mul
    (norm_effectiveFourWaveCoefficient_le_alpha_sq_div_gap
      alpha diagram hsupported)
    (norm_oscillatoryIntegral_le_abs_time
      (totalFourWaveMismatch diagram) time)
    (norm_nonneg _)
    (div_nonneg (by positivity)
      (finiteNonzeroMomentumThreeWaveGap_pos N).le)

/-! ## Exact counted sums -/

/-- Complete fixed-output supported two-vertex Duhamel sum. -/
def fixedOutputSupportedFourWaveDuhamelSum
    (N : Nat) [NeZero N] (alpha time : Real) (output : Site N) : Complex :=
  ∑ diagram : FixedOutputSupportedEffectiveFourWaveDiagram N output,
    effectiveDiagramDuhamelCoefficient N alpha diagram.1 time

/-- Complete fixed-output degenerate `2 ↔ 2` Duhamel sum. -/
def fixedOutputDegenerateTwoToTwoDuhamelRemainder
    (N : Nat) [NeZero N] (alpha time : Real) (output : Site N) : Complex :=
  ∑ diagram : FixedOutputDegenerateTwoToTwoDiagram N output,
    effectiveDiagramDuhamelCoefficient N alpha diagram.1.1 time

/-- The complete fixed-output family inherits the exact `32 N²` count. -/
theorem norm_fixedOutputSupportedFourWaveDuhamelSum_le
    (N : Nat) [NeZero N] (alpha time : Real) (output : Site N) :
    ‖fixedOutputSupportedFourWaveDuhamelSum N alpha time output‖ ≤
      (32 * (N : Real) ^ 2) *
        ((64 * |alpha| ^ 2 / finiteNonzeroMomentumThreeWaveGap N) *
          |time|) := by
  let single : Real :=
    (64 * |alpha| ^ 2 / finiteNonzeroMomentumThreeWaveGap N) * |time|
  have hsingle : 0 ≤ single := by
    dsimp [single]
    exact mul_nonneg
      (div_nonneg (by positivity)
        (finiteNonzeroMomentumThreeWaveGap_pos N).le)
      (abs_nonneg time)
  unfold fixedOutputSupportedFourWaveDuhamelSum
  calc
    ‖∑ diagram : FixedOutputSupportedEffectiveFourWaveDiagram N output,
        effectiveDiagramDuhamelCoefficient N alpha diagram.1 time‖ ≤
        ∑ diagram : FixedOutputSupportedEffectiveFourWaveDiagram N output,
          ‖effectiveDiagramDuhamelCoefficient
            N alpha diagram.1 time‖ := norm_sum_le _ _
    _ ≤ ∑ _diagram : FixedOutputSupportedEffectiveFourWaveDiagram N output,
          single := by
      apply Finset.sum_le_sum
      intro diagram _hdiagram
      exact norm_effectiveDiagramDuhamelCoefficient_le_alpha_sq_time_div_gap
        alpha time diagram.1 diagram.2.1
    _ = (Fintype.card
          (FixedOutputSupportedEffectiveFourWaveDiagram N output) : Real) *
          single := by simp
    _ ≤ ((32 * N ^ 2 : Nat) : Real) * single := by
      gcongr
      exact_mod_cast
        card_fixedOutputSupportedEffectiveFourWaveDiagram_le N output
    _ = (32 * (N : Real) ^ 2) *
        ((64 * |alpha| ^ 2 / finiteNonzeroMomentumThreeWaveGap N) *
          |time|) := by
      dsimp [single]
      push_cast
      ring

/-- The complete degenerate classification remainder inherits the stronger
`128 N` count. -/
theorem norm_fixedOutputDegenerateTwoToTwoDuhamelRemainder_le
    (N : Nat) [NeZero N] (alpha time : Real) (output : Site N) :
    ‖fixedOutputDegenerateTwoToTwoDuhamelRemainder
        N alpha time output‖ ≤
      (128 * (N : Real)) *
        ((64 * |alpha| ^ 2 / finiteNonzeroMomentumThreeWaveGap N) *
          |time|) := by
  let single : Real :=
    (64 * |alpha| ^ 2 / finiteNonzeroMomentumThreeWaveGap N) * |time|
  have hsingle : 0 ≤ single := by
    dsimp [single]
    exact mul_nonneg
      (div_nonneg (by positivity)
        (finiteNonzeroMomentumThreeWaveGap_pos N).le)
      (abs_nonneg time)
  unfold fixedOutputDegenerateTwoToTwoDuhamelRemainder
  calc
    ‖∑ diagram : FixedOutputDegenerateTwoToTwoDiagram N output,
        effectiveDiagramDuhamelCoefficient N alpha diagram.1.1 time‖ ≤
        ∑ diagram : FixedOutputDegenerateTwoToTwoDiagram N output,
          ‖effectiveDiagramDuhamelCoefficient
            N alpha diagram.1.1 time‖ := norm_sum_le _ _
    _ ≤ ∑ _diagram : FixedOutputDegenerateTwoToTwoDiagram N output,
          single := by
      apply Finset.sum_le_sum
      intro diagram _hdiagram
      exact norm_effectiveDiagramDuhamelCoefficient_le_alpha_sq_time_div_gap
        alpha time diagram.1.1 diagram.1.2.1
    _ = (Fintype.card
          (FixedOutputDegenerateTwoToTwoDiagram N output) : Real) *
          single := by simp
    _ ≤ ((128 * N : Nat) : Real) * single := by
      gcongr
      exact_mod_cast card_fixedOutputDegenerateTwoToTwoDiagram_le N output
    _ = (128 * (N : Real)) *
        ((64 * |alpha| ^ 2 / finiteNonzeroMomentumThreeWaveGap N) *
          |time|) := by
      dsimp [single]
      push_cast
      ring

/-! ## Polynomial gap hypotheses and explicit power schedules -/

/-- A transparent polynomial lower bound for the finite-volume three-wave
gap.  The present Fourier-three-wave library proves positivity at each fixed
`N`, but not this uniform exponent; hence it is kept explicit. -/
def PolynomialThreeWaveGapLowerBound (c : Real) (s : Nat) : Prop :=
  ∀ (N : Nat) [NeZero N],
    c / (N : Real) ^ s ≤ finiteNonzeroMomentumThreeWaveGap N

/-- Under `gap_N ≥ c N⁻s`, the complete fixed-output sum has the explicit
polynomial envelope `2048 c⁻¹ |α|² |T| N^(s+2)`. -/
theorem norm_fixedOutputSupportedFourWaveDuhamelSum_le_of_gapPolynomial
    {c : Real} (hc : 0 < c) (s : Nat)
    (hgap : PolynomialThreeWaveGapLowerBound c s)
    (N : Nat) [NeZero N] (alpha time : Real) (output : Site N) :
    ‖fixedOutputSupportedFourWaveDuhamelSum N alpha time output‖ ≤
      (2048 / c) * |alpha| ^ 2 * |time| * (N : Real) ^ (s + 2) := by
  have hN : (0 : Real) < (N : Real) := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have hlowerPos : 0 < c / (N : Real) ^ s :=
    div_pos hc (pow_pos hN s)
  have hinverse :
      1 / finiteNonzeroMomentumThreeWaveGap N ≤
        (N : Real) ^ s / c := by
    calc
      1 / finiteNonzeroMomentumThreeWaveGap N ≤
          1 / (c / (N : Real) ^ s) :=
        div_le_div_of_nonneg_left zero_le_one hlowerPos (hgap N)
      _ = (N : Real) ^ s / c := by
        field_simp [hc.ne', hN.ne']
  have hcoefficient :
      64 * |alpha| ^ 2 / finiteNonzeroMomentumThreeWaveGap N ≤
        (64 * |alpha| ^ 2) * ((N : Real) ^ s / c) := by
    calc
      64 * |alpha| ^ 2 / finiteNonzeroMomentumThreeWaveGap N =
          (64 * |alpha| ^ 2) *
            (1 / finiteNonzeroMomentumThreeWaveGap N) := by ring
      _ ≤ (64 * |alpha| ^ 2) * ((N : Real) ^ s / c) :=
        mul_le_mul_of_nonneg_left hinverse (by positivity)
  calc
    ‖fixedOutputSupportedFourWaveDuhamelSum N alpha time output‖ ≤
        (32 * (N : Real) ^ 2) *
          ((64 * |alpha| ^ 2 / finiteNonzeroMomentumThreeWaveGap N) *
            |time|) :=
      norm_fixedOutputSupportedFourWaveDuhamelSum_le N alpha time output
    _ ≤ (32 * (N : Real) ^ 2) *
          (((64 * |alpha| ^ 2) * ((N : Real) ^ s / c)) * |time|) := by
      gcongr
    _ = (2048 / c) * |alpha| ^ 2 * |time| *
          (N : Real) ^ (s + 2) := by
      rw [pow_add]
      norm_num
      field_simp [hc.ne']
      ring

/-- Under the same gap input, the degenerate sector gains one full power of
volume from its `128 N` count. -/
theorem norm_fixedOutputDegenerateTwoToTwoDuhamelRemainder_le_of_gapPolynomial
    {c : Real} (hc : 0 < c) (s : Nat)
    (hgap : PolynomialThreeWaveGapLowerBound c s)
    (N : Nat) [NeZero N] (alpha time : Real) (output : Site N) :
    ‖fixedOutputDegenerateTwoToTwoDuhamelRemainder
        N alpha time output‖ ≤
      (8192 / c) * |alpha| ^ 2 * |time| * (N : Real) ^ (s + 1) := by
  have hN : (0 : Real) < (N : Real) := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have hlowerPos : 0 < c / (N : Real) ^ s :=
    div_pos hc (pow_pos hN s)
  have hinverse :
      1 / finiteNonzeroMomentumThreeWaveGap N ≤
        (N : Real) ^ s / c := by
    calc
      1 / finiteNonzeroMomentumThreeWaveGap N ≤
          1 / (c / (N : Real) ^ s) :=
        div_le_div_of_nonneg_left zero_le_one hlowerPos (hgap N)
      _ = (N : Real) ^ s / c := by
        field_simp [hc.ne', hN.ne']
  have hcoefficient :
      64 * |alpha| ^ 2 / finiteNonzeroMomentumThreeWaveGap N ≤
        (64 * |alpha| ^ 2) * ((N : Real) ^ s / c) := by
    calc
      64 * |alpha| ^ 2 / finiteNonzeroMomentumThreeWaveGap N =
          (64 * |alpha| ^ 2) *
            (1 / finiteNonzeroMomentumThreeWaveGap N) := by ring
      _ ≤ (64 * |alpha| ^ 2) * ((N : Real) ^ s / c) :=
        mul_le_mul_of_nonneg_left hinverse (by positivity)
  calc
    ‖fixedOutputDegenerateTwoToTwoDuhamelRemainder
        N alpha time output‖ ≤
        (128 * (N : Real)) *
          ((64 * |alpha| ^ 2 / finiteNonzeroMomentumThreeWaveGap N) *
            |time|) :=
      norm_fixedOutputDegenerateTwoToTwoDuhamelRemainder_le
        N alpha time output
    _ ≤ (128 * (N : Real)) *
          (((64 * |alpha| ^ 2) * ((N : Real) ^ s / c)) * |time|) := by
      gcongr
    _ = (8192 / c) * |alpha| ^ 2 * |time| *
          (N : Real) ^ (s + 1) := by
      rw [pow_add]
      norm_num
      field_simp [hc.ne']
      ring

/-- Positive real volume parameter along the canonical schedule `N=n+1`. -/
def volumeScale (n : Nat) : Real := ((n + 1 : Nat) : Real)

/-- Coupling schedule `α_N = N⁻a`. -/
def inverseVolumePowerCoupling (a n : Nat) : Real :=
  1 / volumeScale n ^ a

/-- Time schedule `T_N = N^b`. -/
def volumePowerTime (b n : Nat) : Real :=
  volumeScale n ^ b

theorem volumeScale_pos (n : Nat) : 0 < volumeScale n := by
  dsimp [volumeScale]
  positivity

theorem volumeScale_tendsto_atTop : Tendsto volumeScale atTop atTop := by
  exact (tendsto_natCast_atTop_atTop (R := Real)).comp
    (tendsto_add_atTop_nat 1)

/-- Elementary exponent engine used below.  For `α_N=N⁻a` and
`T_N=N^b`, the monomial `|α_N|² |T_N| N^d` vanishes exactly under the
displayed strict sufficient inequality `b+d < 2a`. -/
theorem alpha_sq_time_volumePower_tendsto_zero
    {a b d : Nat} (hexponent : b + d < 2 * a) :
    Tendsto
      (fun n : Nat ↦
        |inverseVolumePowerCoupling a n| ^ 2 *
          |volumePowerTime b n| * volumeScale n ^ d)
      atTop (nhds 0) := by
  have hratio : Tendsto
      (fun x : Real ↦ x ^ (b + d) / x ^ (2 * a))
      atTop (nhds 0) :=
    tendsto_pow_div_pow_atTop_zero hexponent
  have hcomposed := hratio.comp volumeScale_tendsto_atTop
  convert hcomposed using 1
  funext n
  have hpos := volumeScale_pos n
  change
    |1 / volumeScale n ^ a| ^ 2 * |volumeScale n ^ b| *
        volumeScale n ^ d =
      volumeScale n ^ (b + d) / volumeScale n ^ (2 * a)
  rw [abs_of_pos (div_pos zero_lt_one (pow_pos hpos a)),
    abs_of_pos (pow_pos hpos b)]
  rw [pow_add, show 2 * a = a * 2 by omega, pow_mul]
  field_simp [hpos.ne']

/-! ## Joint limits for the counted families -/

/-- Explicit sufficient power window for the complete `O(N²)` diagram
family: `2a > b+s+2`. -/
theorem fixedOutputSupportedFourWaveDuhamelSum_tendsto_zero_powerSchedule
    {c : Real} (hc : 0 < c) (s a b : Nat)
    (hgap : PolynomialThreeWaveGapLowerBound c s)
    (hexponent : b + (s + 2) < 2 * a)
    (output : ∀ n, Site (n + 1)) :
    Tendsto
      (fun n : Nat ↦
        fixedOutputSupportedFourWaveDuhamelSum (n + 1)
          (inverseVolumePowerCoupling a n) (volumePowerTime b n)
          (output n))
      atTop (nhds 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  let upper : Nat → Real := fun n ↦
    (2048 / c) *
      (|inverseVolumePowerCoupling a n| ^ 2 *
        |volumePowerTime b n| * volumeScale n ^ (s + 2))
  have hupper : Tendsto upper atTop (nhds 0) := by
    dsimp [upper]
    simpa using tendsto_const_nhds.mul
      (alpha_sq_time_volumePower_tendsto_zero hexponent)
  apply squeeze_zero' (g := upper)
  · exact Eventually.of_forall fun _ ↦ norm_nonneg _
  · exact Eventually.of_forall fun n ↦ by
      have hbound :=
        norm_fixedOutputSupportedFourWaveDuhamelSum_le_of_gapPolynomial
          hc s hgap (n + 1) (inverseVolumePowerCoupling a n)
          (volumePowerTime b n) (output n)
      exact hbound.trans_eq (by
        dsimp [upper, volumeScale]
        ring)
  · exact hupper

/-- Explicit sufficient power window for the complete degenerate `O(N)`
classification remainder: `2a > b+s+1`. -/
theorem fixedOutputDegenerateTwoToTwoDuhamelRemainder_tendsto_zero_powerSchedule
    {c : Real} (hc : 0 < c) (s a b : Nat)
    (hgap : PolynomialThreeWaveGapLowerBound c s)
    (hexponent : b + (s + 1) < 2 * a)
    (output : ∀ n, Site (n + 1)) :
    Tendsto
      (fun n : Nat ↦
        fixedOutputDegenerateTwoToTwoDuhamelRemainder (n + 1)
          (inverseVolumePowerCoupling a n) (volumePowerTime b n)
          (output n))
      atTop (nhds 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  let upper : Nat → Real := fun n ↦
    (8192 / c) *
      (|inverseVolumePowerCoupling a n| ^ 2 *
        |volumePowerTime b n| * volumeScale n ^ (s + 1))
  have hupper : Tendsto upper atTop (nhds 0) := by
    dsimp [upper]
    simpa using tendsto_const_nhds.mul
      (alpha_sq_time_volumePower_tendsto_zero hexponent)
  apply squeeze_zero' (g := upper)
  · exact Eventually.of_forall fun _ ↦ norm_nonneg _
  · exact Eventually.of_forall fun n ↦ by
      have hbound :=
        norm_fixedOutputDegenerateTwoToTwoDuhamelRemainder_le_of_gapPolynomial
          hc s hgap (n + 1) (inverseVolumePowerCoupling a n)
          (volumePowerTime b n) (output n)
      exact hbound.trans_eq (by
        dsimp [upper, volumeScale]
        ring)
  · exact hupper

/-! ## Minimal structured input for the genuine Picard tail -/

/-- The minimal non-vacuous growing-window estimate needed for a Picard or
diagram tail whose current library envelope has not yet been reduced to
uniform powers of `N`.  Unlike `DiagramRemainderCertificate`, the time window
may grow with `n`, and no limit field is included: decay is proved below from
the displayed powers. -/
structure GrowingWindowAlphaNTRemainderBound
    (alpha horizon : Nat → Real)
    (remainder : Nat → Real → Complex) where
  /-- Uniform numerical prefactor. -/
  constant : Real
  constant_nonneg : 0 ≤ constant
  /-- Power of the weak coupling in the remainder. -/
  alphaPower : Nat
  /-- Power of the time horizon in the remainder. -/
  timePower : Nat
  /-- Explicit inverse-volume power. -/
  volumeDecay : Nat
  horizon_nonneg : ∀ n, 0 ≤ horizon n
  /-- The actual analytic content required from the model-specific Picard
  estimate. -/
  norm_remainder_le : ∀ n t, t ∈ Icc 0 (horizon n) →
    ‖remainder n t‖ ≤
      constant * |alpha n| ^ alphaPower * |horizon n| ^ timePower /
        volumeScale n ^ volumeDecay

/-- Uniform decay on the growing windows, analogous to the fixed-window
contract in `DiagramRemainderCertificate`. -/
def GrowingWindowRemainderVanishes
    (horizon : Nat → Real) (remainder : Nat → Real → Complex) : Prop :=
  ∀ epsilon, 0 < epsilon →
    ∀ᶠ n in atTop, ∀ t, t ∈ Icc 0 (horizon n) →
      ‖remainder n t‖ < epsilon

/-- General exponent engine for a structured remainder:
`C |α_N|ᵖ |T_N|ʳ / Nʳ → 0` under `bq < ap+r`. -/
theorem alpha_time_power_remainderEnvelope_tendsto_zero
    (C : Real) {a b p q r : Nat}
    (hexponent : b * q < a * p + r) :
    Tendsto
      (fun n : Nat ↦
        C * |inverseVolumePowerCoupling a n| ^ p *
          |volumePowerTime b n| ^ q / volumeScale n ^ r)
      atTop (nhds 0) := by
  have hratio : Tendsto
      (fun x : Real ↦
        C * (x ^ (b * q) / x ^ (a * p + r)))
      atTop (nhds 0) := by
    simpa using tendsto_const_nhds.mul
      (tendsto_pow_div_pow_atTop_zero hexponent :
        Tendsto (fun x : Real ↦ x ^ (b * q) / x ^ (a * p + r))
          atTop (nhds 0))
  have hcomposed := hratio.comp volumeScale_tendsto_atTop
  convert hcomposed using 1
  funext n
  have hpos := volumeScale_pos n
  change
    C * |1 / volumeScale n ^ a| ^ p * |volumeScale n ^ b| ^ q /
        volumeScale n ^ r =
      C * (volumeScale n ^ (b * q) /
        volumeScale n ^ (a * p + r))
  rw [abs_of_pos (div_pos zero_lt_one (pow_pos hpos a)),
    abs_of_pos (pow_pos hpos b), div_pow, one_pow,
    ← pow_mul, ← pow_mul, pow_add]
  field_simp [hpos.ne']

/-- The structured power bound implies uniform decay throughout the growing
time window.  There is no separate `remainder → 0` assumption. -/
theorem GrowingWindowAlphaNTRemainderBound.growingWindowRemainderVanishes
    {a b : Nat} {remainder : Nat → Real → Complex}
    (bound : GrowingWindowAlphaNTRemainderBound
      (inverseVolumePowerCoupling a) (volumePowerTime b) remainder)
    (hexponent : b * bound.timePower <
      a * bound.alphaPower + bound.volumeDecay) :
    GrowingWindowRemainderVanishes (volumePowerTime b) remainder := by
  intro epsilon hepsilon
  have henvelope := alpha_time_power_remainderEnvelope_tendsto_zero
    bound.constant hexponent
  have heventually : ∀ᶠ n in atTop,
      bound.constant * |inverseVolumePowerCoupling a n| ^ bound.alphaPower *
          |volumePowerTime b n| ^ bound.timePower /
            volumeScale n ^ bound.volumeDecay < epsilon :=
    henvelope.eventually (Iio_mem_nhds hepsilon)
  filter_upwards [heventually] with n hn
  intro t ht
  exact (bound.norm_remainder_le n t ht).trans_lt hn

/-- In particular the endpoint remainder at `T_N` tends to zero. -/
theorem GrowingWindowAlphaNTRemainderBound.endpoint_tendsto_zero
    {a b : Nat} {remainder : Nat → Real → Complex}
    (bound : GrowingWindowAlphaNTRemainderBound
      (inverseVolumePowerCoupling a) (volumePowerTime b) remainder)
    (hexponent : b * bound.timePower <
      a * bound.alphaPower + bound.volumeDecay) :
    Tendsto (fun n ↦ remainder n (volumePowerTime b n))
      atTop (nhds 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  let upper : Nat → Real := fun n ↦
    bound.constant *
      |inverseVolumePowerCoupling a n| ^ bound.alphaPower *
      |volumePowerTime b n| ^ bound.timePower /
      volumeScale n ^ bound.volumeDecay
  have hupper : Tendsto upper atTop (nhds 0) := by
    dsimp [upper]
    exact alpha_time_power_remainderEnvelope_tendsto_zero
      bound.constant hexponent
  apply squeeze_zero' (g := upper)
  · exact Eventually.of_forall fun _ ↦ norm_nonneg _
  · exact Eventually.of_forall fun n ↦ by
      apply bound.norm_remainder_le
      exact ⟨bound.horizon_nonneg n, le_rfl⟩
  · exact hupper

/-- Strongest combined statement available from the present library inputs:
the complete fixed-output degenerate four-wave remainder plus any genuine
Picard tail satisfying the minimal structured power bound vanishes jointly.
The two independent exponent conditions expose exactly the graph-counting
and Picard requirements. -/
theorem degenerateFourWave_add_picardRemainder_tendsto_zero_powerSchedule
    {c : Real} (hc : 0 < c) (s a b : Nat)
    (hgap : PolynomialThreeWaveGapLowerBound c s)
    (hdiagramExponent : b + (s + 1) < 2 * a)
    (output : ∀ n, Site (n + 1))
    (remainder : Nat → Real → Complex)
    (picardBound : GrowingWindowAlphaNTRemainderBound
      (inverseVolumePowerCoupling a) (volumePowerTime b) remainder)
    (hpicardExponent : b * picardBound.timePower <
      a * picardBound.alphaPower + picardBound.volumeDecay) :
    Tendsto
      (fun n : Nat ↦
        fixedOutputDegenerateTwoToTwoDuhamelRemainder (n + 1)
            (inverseVolumePowerCoupling a n) (volumePowerTime b n)
            (output n) +
          remainder n (volumePowerTime b n))
      atTop (nhds 0) := by
  have hdiagram :=
    fixedOutputDegenerateTwoToTwoDuhamelRemainder_tendsto_zero_powerSchedule
      hc s a b hgap hdiagramExponent output
  have hpicard := picardBound.endpoint_tendsto_zero hpicardExponent
  simpa using hdiagram.add hpicard

end

end ArchonPhysics.EqualMassPeriodicFPUTAlphaNTJointRemainder
