import ArchonPhysics.CleanCycleAcousticCountEnvelope
import ArchonPhysics.FreeFPUTCollisionMismatchBridge
import ArchonPhysics.NestedOscillatoryIntegral
import ArchonPhysics.PhyslibFPUTBinaryInteractionTreeCouples
import ArchonPhysics.QuadraticInteractionFirstNormalForm
import ArchonPhysics.FiniteNestedNormalFormExtraction

/-!
# Equal-mass periodic FPUT: Fourier momentum and the three-wave shell

This module specializes the finite binary-tree layer to the complex Fourier
labels of the one-dimensional equal-mass periodic chain.  Its normalized
acoustic dispersion is

`omega_N(k) = 2 sin (pi k.val / N)`.

The central finite-volume result is that a signed three-leg interaction which
conserves the exact `ZMod N` lattice momentum cannot also conserve this
frequency when all three modes are nonzero.  Thus the cubic on-shell sector
is a zero-mode sector, not a nonzero three-wave collision equation.

The last definitions expose the honest next object: the off-shell cubic
homological quotient and the resulting two-cubic-vertex effective quartic
coefficient.  They do not assume a kinetic equation and do not claim the
analytic diagram bounds needed for a scaling limit.
-/

namespace ArchonPhysics.EqualMassPeriodicFPUTFourierThreeWave

open scoped BigOperators ComplexConjugate

open ArchonPhysics
open ArchonPhysics.CleanCycleAcousticCountEnvelope
open ArchonPhysics.Lattice
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.QuadraticInteractionFirstNormalForm
open ArchonPhysics.FiniteNestedNormalFormExtraction

noncomputable section

/-! ## Normalized sine dispersion -/

/-- Positive-branch normalized acoustic frequency of the clean periodic
cycle.  Since `k.val < N`, its sine argument lies in `[0, pi)`. -/
def periodicSineFrequency (N : Nat) [NeZero N] (k : Site N) : Real :=
  2 * Real.sin (Real.pi * (k.val : Real) / (N : Real))

@[simp] theorem periodicSineFrequency_zero (N : Nat) [NeZero N] :
    periodicSineFrequency N (0 : Site N) = 0 := by
  simp [periodicSineFrequency]

theorem periodicSineAngle_pos_of_ne_zero
    {N : Nat} [NeZero N] {k : Site N} (hk : k ≠ 0) :
    0 < Real.pi * (k.val : Real) / (N : Real) := by
  have hN : 0 < (N : Real) := by exact_mod_cast NeZero.pos N
  have hkval : 0 < k.val := Nat.pos_of_ne_zero (by
    intro hzero
    apply hk
    apply ZMod.val_injective N
    simp [hzero])
  positivity

theorem periodicSineAngle_lt_pi
    (N : Nat) [NeZero N] (k : Site N) :
    Real.pi * (k.val : Real) / (N : Real) < Real.pi := by
  have hN : 0 < (N : Real) := by exact_mod_cast NeZero.pos N
  have hklt : (k.val : Real) < (N : Real) := by exact_mod_cast k.val_lt
  have hratio : (k.val : Real) / (N : Real) < 1 :=
    (div_lt_one hN).2 hklt
  calc
    Real.pi * (k.val : Real) / (N : Real) =
        Real.pi * ((k.val : Real) / (N : Real)) := by ring
    _ < Real.pi * 1 := mul_lt_mul_of_pos_left hratio Real.pi_pos
    _ = Real.pi := by ring

theorem periodicSineFrequency_pos_of_ne_zero
    {N : Nat} [NeZero N] {k : Site N} (hk : k ≠ 0) :
    0 < periodicSineFrequency N k := by
  unfold periodicSineFrequency
  exact mul_pos (by norm_num) (Real.sin_pos_of_pos_of_lt_pi
    (periodicSineAngle_pos_of_ne_zero hk)
    (periodicSineAngle_lt_pi N k))

theorem periodicSineFrequency_nonneg
    (N : Nat) [NeZero N] (k : Site N) :
    0 ≤ periodicSineFrequency N k := by
  by_cases hk : k = 0
  · subst k
    simp
  · exact (periodicSineFrequency_pos_of_ne_zero hk).le

theorem periodicSineFrequency_sq_eq_cleanCycleModeEnergy
    (N : Nat) [NeZero N] (k : Site N) :
    periodicSineFrequency N k ^ 2 = cleanCycleModeEnergy N k := by
  unfold periodicSineFrequency cleanCycleModeEnergy
  ring

theorem sqrt_cleanCycleModeEnergy_eq_periodicSineFrequency
    (N : Nat) [NeZero N] (k : Site N) :
    Real.sqrt (cleanCycleModeEnergy N k) = periodicSineFrequency N k := by
  rw [← periodicSineFrequency_sq_eq_cleanCycleModeEnergy]
  exact Real.sqrt_sq (periodicSineFrequency_nonneg N k)

/-! ## Strict trigonometric triangle inequalities -/

private theorem one_sub_cos_pos_of_pos_of_lt_pi
    {x : Real} (hx0 : 0 < x) (hxp : x < Real.pi) :
    0 < 1 - Real.cos x := by
  have hhalf0 : 0 < x / 2 := by linarith
  have hhalfp : x / 2 < Real.pi := by linarith [Real.pi_pos]
  have hsin : 0 < Real.sin (x / 2) :=
    Real.sin_pos_of_pos_of_lt_pi hhalf0 hhalfp
  have hcos : Real.cos x = 1 - 2 * Real.sin (x / 2) ^ 2 := by
    calc
      Real.cos x = Real.cos (2 * (x / 2)) := by ring_nf
      _ = 1 - 2 * Real.sin (x / 2) ^ 2 :=
        Real.cos_two_mul_eq_one_sub (x / 2)
  rw [hcos]
  nlinarith [sq_pos_of_pos hsin]

private theorem one_add_cos_pos_of_pos_of_lt_pi
    {x : Real} (hx0 : 0 < x) (hxp : x < Real.pi) :
    0 < 1 + Real.cos x := by
  have hhalf : x / 2 ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor <;> linarith [Real.pi_pos]
  have hcosHalf : 0 < Real.cos (x / 2) :=
    Real.cos_pos_of_mem_Ioo hhalf
  have hcos : Real.cos x = 2 * Real.cos (x / 2) ^ 2 - 1 := by
    calc
      Real.cos x = Real.cos (2 * (x / 2)) := by ring_nf
      _ = 2 * Real.cos (x / 2) ^ 2 - 1 := Real.cos_two_mul (x / 2)
  rw [hcos]
  nlinarith [sq_pos_of_pos hcosHalf]

theorem sin_add_lt_sum_of_pos_of_add_lt_pi
    {a b : Real} (ha0 : 0 < a) (hap : a < Real.pi)
    (hb0 : 0 < b) (hbp : b < Real.pi) :
    Real.sin (a + b) < Real.sin a + Real.sin b := by
  have hsinA : 0 < Real.sin a := Real.sin_pos_of_pos_of_lt_pi ha0 hap
  have hsinB : 0 < Real.sin b := Real.sin_pos_of_pos_of_lt_pi hb0 hbp
  have hA : 0 < 1 - Real.cos a :=
    one_sub_cos_pos_of_pos_of_lt_pi ha0 hap
  have hB : 0 < 1 - Real.cos b :=
    one_sub_cos_pos_of_pos_of_lt_pi hb0 hbp
  rw [Real.sin_add]
  nlinarith [mul_pos hsinA hB, mul_pos hsinB hA]

theorem neg_sin_add_lt_sum_of_pos_of_pi_le_add
    {a b : Real} (ha0 : 0 < a) (hap : a < Real.pi)
    (hb0 : 0 < b) (hbp : b < Real.pi) :
    -Real.sin (a + b) < Real.sin a + Real.sin b := by
  have hsinA : 0 < Real.sin a := Real.sin_pos_of_pos_of_lt_pi ha0 hap
  have hsinB : 0 < Real.sin b := Real.sin_pos_of_pos_of_lt_pi hb0 hbp
  have hA : 0 < 1 + Real.cos a :=
    one_add_cos_pos_of_pos_of_lt_pi ha0 hap
  have hB : 0 < 1 + Real.cos b :=
    one_add_cos_pos_of_pos_of_lt_pi hb0 hbp
  rw [Real.sin_add]
  nlinarith [mul_pos hsinA hB, mul_pos hsinB hA]

/-! ## Exact modular addition and strict acoustic subadditivity -/

private theorem periodicSineAngle_add_of_val_add_lt
    {N : Nat} [NeZero N] {k l : Site N}
    (hadd : k.val + l.val < N) :
    Real.pi * ((k + l).val : Real) / (N : Real) =
      Real.pi * (k.val : Real) / (N : Real) +
        Real.pi * (l.val : Real) / (N : Real) := by
  rw [ZMod.val_add_of_lt hadd]
  push_cast
  ring

private theorem periodicSineAngle_add_of_val_add_le
    {N : Nat} [NeZero N] {k l : Site N}
    (hadd : N ≤ k.val + l.val) :
    Real.pi * ((k + l).val : Real) / (N : Real) =
      (Real.pi * (k.val : Real) / (N : Real) +
        Real.pi * (l.val : Real) / (N : Real)) - Real.pi := by
  rw [ZMod.val_add_of_le hadd, Nat.cast_sub hadd]
  have hNne : (N : Real) ≠ 0 := by
    exact_mod_cast NeZero.ne N
  push_cast
  field_simp

/-- Strict subadditivity of the normalized acoustic dispersion on the
periodic group.  The conclusion is finite-volume and the gap is not uniform
in `N`. -/
theorem periodicSineFrequency_add_lt
    {N : Nat} [NeZero N] {k l : Site N}
    (hk : k ≠ 0) (hl : l ≠ 0) :
    periodicSineFrequency N (k + l) <
      periodicSineFrequency N k + periodicSineFrequency N l := by
  let a : Real := Real.pi * (k.val : Real) / (N : Real)
  let b : Real := Real.pi * (l.val : Real) / (N : Real)
  have ha0 : 0 < a := periodicSineAngle_pos_of_ne_zero hk
  have hap : a < Real.pi := periodicSineAngle_lt_pi N k
  have hb0 : 0 < b := periodicSineAngle_pos_of_ne_zero hl
  have hbp : b < Real.pi := periodicSineAngle_lt_pi N l
  by_cases hadd : k.val + l.val < N
  · have hangle := periodicSineAngle_add_of_val_add_lt hadd
    have htrig := sin_add_lt_sum_of_pos_of_add_lt_pi ha0 hap hb0 hbp
    unfold periodicSineFrequency
    change 2 * Real.sin
        (Real.pi * ((k + l).val : Real) / (N : Real)) <
      2 * Real.sin a + 2 * Real.sin b
    rw [hangle]
    linarith
  · have hle : N ≤ k.val + l.val := Nat.le_of_not_gt hadd
    have hangle := periodicSineAngle_add_of_val_add_le hle
    have htrig := neg_sin_add_lt_sum_of_pos_of_pi_le_add ha0 hap hb0 hbp
    unfold periodicSineFrequency
    change 2 * Real.sin
        (Real.pi * ((k + l).val : Real) / (N : Real)) <
      2 * Real.sin a + 2 * Real.sin b
    rw [hangle, Real.sin_sub_pi]
    linarith

/-! ## Signed Fourier momentum and absence of a nonzero three-wave shell -/

/-- The same interaction sign acts on a lattice momentum and on its positive
frequency. -/
def interactionSignMomentum {N : Nat} :
    InteractionSign → Site N → Site N
  | .plus, k => k
  | .minus, k => -k

/-- Exact periodic lattice momentum of a signed interaction. -/
def signedFourierMomentum {N n : Nat}
    (sign : Fin n → InteractionSign) (modes : Fin n → Site N) : Site N :=
  ∑ r, interactionSignMomentum (sign r) (modes r)

/-- Exact momentum selector for a complex Fourier vertex. -/
def FourierMomentumBalanced {N n : Nat}
    (sign : Fin n → InteractionSign) (modes : Fin n → Site N) : Prop :=
  signedFourierMomentum sign modes = 0

/-- Signed normalized sine-frequency mismatch using the same sign
decoration as `signedFourierMomentum`. -/
def periodicSinePhaseMismatch {N n : Nat} [NeZero N]
    (sign : Fin n → InteractionSign) (modes : Fin n → Site N) : Real :=
  ∑ r, (sign r).coefficient * periodicSineFrequency N (modes r)

private theorem decayFrequencyEquality_false
    {N : Nat} [NeZero N] {k l output : Site N}
    (hk : k ≠ 0) (hl : l ≠ 0)
    (hmomentum : output = k + l)
    (hfrequency : periodicSineFrequency N output =
      periodicSineFrequency N k + periodicSineFrequency N l) : False := by
  subst output
  linarith [periodicSineFrequency_add_lt hk hl]

/-- Every exact three-wave Fourier resonance has a translation leg.  This
covers all eight sign sectors.  Equivalently, the nonzero-mode three-wave
shell is empty at every finite volume. -/
theorem threeWave_fourier_resonance_has_zero_mode
    {N : Nat} [NeZero N]
    (sign : Fin 3 → InteractionSign) (modes : Fin 3 → Site N)
    (hmomentum : FourierMomentumBalanced sign modes)
    (hfrequency : periodicSinePhaseMismatch sign modes = 0) :
    ∃ r, modes r = 0 := by
  by_contra hzero
  push Not at hzero
  have hpos0 := periodicSineFrequency_pos_of_ne_zero (hzero 0)
  have hpos1 := periodicSineFrequency_pos_of_ne_zero (hzero 1)
  have hpos2 := periodicSineFrequency_pos_of_ne_zero (hzero 2)
  cases hs0 : sign 0 <;> cases hs1 : sign 1 <;> cases hs2 : sign 2
  all_goals
    unfold FourierMomentumBalanced signedFourierMomentum at hmomentum
    unfold periodicSinePhaseMismatch at hfrequency
    simp only [interactionSignMomentum, Fin.sum_univ_succ, Fin.isValue,
      hs0, Fin.succ_zero_eq_one, hs1, Finset.univ_unique,
      Fin.default_eq_zero, Finset.sum_singleton, Fin.succ_one_eq_two, hs2,
      InteractionSign.coefficient_plus, InteractionSign.coefficient_minus,
      one_mul, neg_mul] at hmomentum hfrequency
  case plus.plus.plus =>
    linarith
  case plus.plus.minus =>
    have hout : modes 2 = modes 0 + modes 1 := by
      linear_combination -hmomentum
    have hfreq : periodicSineFrequency N (modes 2) =
        periodicSineFrequency N (modes 0) +
          periodicSineFrequency N (modes 1) := by
      linarith
    exact decayFrequencyEquality_false (hzero 0) (hzero 1) hout hfreq
  case plus.minus.plus =>
    have hout : modes 1 = modes 0 + modes 2 := by
      linear_combination -hmomentum
    have hfreq : periodicSineFrequency N (modes 1) =
        periodicSineFrequency N (modes 0) +
          periodicSineFrequency N (modes 2) := by
      linarith
    exact decayFrequencyEquality_false (hzero 0) (hzero 2) hout hfreq
  case plus.minus.minus =>
    have hout : modes 0 = modes 1 + modes 2 := by
      linear_combination hmomentum
    have hfreq : periodicSineFrequency N (modes 0) =
        periodicSineFrequency N (modes 1) +
          periodicSineFrequency N (modes 2) := by
      linarith
    exact decayFrequencyEquality_false (hzero 1) (hzero 2) hout hfreq
  case minus.plus.plus =>
    have hout : modes 0 = modes 1 + modes 2 := by
      linear_combination -hmomentum
    have hfreq : periodicSineFrequency N (modes 0) =
        periodicSineFrequency N (modes 1) +
          periodicSineFrequency N (modes 2) := by
      linarith
    exact decayFrequencyEquality_false (hzero 1) (hzero 2) hout hfreq
  case minus.plus.minus =>
    have hout : modes 1 = modes 0 + modes 2 := by
      linear_combination hmomentum
    have hfreq : periodicSineFrequency N (modes 1) =
        periodicSineFrequency N (modes 0) +
          periodicSineFrequency N (modes 2) := by
      linarith
    exact decayFrequencyEquality_false (hzero 0) (hzero 2) hout hfreq
  case minus.minus.plus =>
    have hout : modes 2 = modes 0 + modes 1 := by
      linear_combination hmomentum
    have hfreq : periodicSineFrequency N (modes 2) =
        periodicSineFrequency N (modes 0) +
          periodicSineFrequency N (modes 1) := by
      linarith
    exact decayFrequencyEquality_false (hzero 0) (hzero 1) hout hfreq
  case minus.minus.minus =>
    linarith

/-! ## A finite-volume gap on the complete nonzero momentum shell -/

local instance interactionSignFintype : Fintype InteractionSign where
  elems := {.plus, .minus}
  complete := by
    intro sign
    cases sign <;> simp

local instance interactionSignInhabited : Inhabited InteractionSign :=
  ⟨.plus⟩

/-- A fully signed three-leg Fourier decoration. -/
abbrev SignedFourierTriple (N : Nat) :=
  (Fin 3 → InteractionSign) × (Fin 3 → Site N)

def signedFourierTripleMismatch
    {N : Nat} [NeZero N] (triple : SignedFourierTriple N) : Real :=
  periodicSinePhaseMismatch triple.1 triple.2

/-- The finite set on which the acoustic mismatch has a genuine pointwise
gap: every leg is nonzero and the signed modular momentum is balanced. -/
def IsNonzeroMomentumTriple
    {N : Nat} (triple : SignedFourierTriple N) : Prop :=
  (∀ r, triple.2 r ≠ 0) ∧ FourierMomentumBalanced triple.1 triple.2

instance instDecidableIsNonzeroMomentumTriple
    {N : Nat} [NeZero N] (triple : SignedFourierTriple N) :
    Decidable (IsNonzeroMomentumTriple triple) := by
  unfold IsNonzeroMomentumTriple FourierMomentumBalanced
  exact Classical.propDecidable _

theorem signedFourierTripleMismatch_ne_zero_of_nonzeroMomentum
    {N : Nat} [NeZero N] (triple : SignedFourierTriple N)
    (hactive : IsNonzeroMomentumTriple triple) :
    signedFourierTripleMismatch triple ≠ 0 := by
  intro hresonant
  obtain ⟨r, hr⟩ := threeWave_fourier_resonance_has_zero_mode
    triple.1 triple.2 hactive.2 hresonant
  exact hactive.1 r hr

/-- Existence of a single positive lower bound over all signed, nonzero,
momentum-balanced triples at fixed `N`.  Inactive triples are assigned the
harmless value one only for taking a minimum over the full finite type. -/
theorem exists_finite_nonzeroMomentumThreeWaveGap
    (N : Nat) [NeZero N] :
    ∃ gap : Real, 0 < gap ∧
      ∀ triple : SignedFourierTriple N,
        IsNonzeroMomentumTriple triple →
          gap ≤ |signedFourierTripleMismatch triple| := by
  let gapValue : SignedFourierTriple N → Real := fun triple ↦
    if IsNonzeroMomentumTriple triple then
      |signedFourierTripleMismatch triple|
    else 1
  obtain ⟨minimizer, hmin⟩ :=
    Finite.exists_min gapValue
  refine ⟨gapValue minimizer, ?_, ?_⟩
  · by_cases hactive : IsNonzeroMomentumTriple minimizer
    · rw [show gapValue minimizer =
          |signedFourierTripleMismatch minimizer| by
        simp [gapValue, hactive]]
      exact abs_pos.mpr
        (signedFourierTripleMismatch_ne_zero_of_nonzeroMomentum
          minimizer hactive)
    · simp [gapValue, hactive]
  · intro triple hactive
    have hbound := hmin triple
    simpa [gapValue, hactive] using hbound

/-- Canonical choice of the fixed-volume acoustic three-wave gap. -/
def finiteNonzeroMomentumThreeWaveGap
    (N : Nat) [NeZero N] : Real :=
  Classical.choose (exists_finite_nonzeroMomentumThreeWaveGap N)

theorem finiteNonzeroMomentumThreeWaveGap_pos
    (N : Nat) [NeZero N] :
    0 < finiteNonzeroMomentumThreeWaveGap N :=
  (Classical.choose_spec
    (exists_finite_nonzeroMomentumThreeWaveGap N)).1

theorem finiteNonzeroMomentumThreeWaveGap_le
    (N : Nat) [NeZero N] (triple : SignedFourierTriple N)
    (hactive : IsNonzeroMomentumTriple triple) :
    finiteNonzeroMomentumThreeWaveGap N ≤
      |signedFourierTripleMismatch triple| :=
  (Classical.choose_spec
    (exists_finite_nonzeroMomentumThreeWaveGap N)).2 triple hactive

/-! ## Adapter to the actual signed quadratic Picard terms -/

open ArchonPhysics.FreeFPUTCollisionMismatchBridge
open ArchonPhysics.FreeFPUTMismatchPhaseExpansion
open ArchonPhysics.FreeFPUTTensorPhaseExpansion

/-- Fourier sign/mode decoration carried by one actual free quadratic FPUT
Picard term. -/
def quadraticPhaseFourierTriple
    {N : Nat} [NeZero N] (observed : Site N)
    (term : QuadraticPhaseTerm N) : SignedFourierTriple N :=
  (quadraticCollisionSign term, quadraticCollisionModes observed term)

/-- The exact `ZMod N` momentum selector for one signed quadratic Picard
term. -/
def QuadraticPhaseFourierMomentumBalanced
    {N : Nat} [NeZero N] (observed : Site N)
    (term : QuadraticPhaseTerm N) : Prop :=
  FourierMomentumBalanced (quadraticCollisionSign term)
    (quadraticCollisionModes observed term)

theorem signedFourierTripleMismatch_quadraticPhaseFourierTriple
    {N : Nat} [NeZero N] (observed : Site N)
    (term : QuadraticPhaseTerm N) :
    signedFourierTripleMismatch
        (quadraticPhaseFourierTriple observed term) =
      quadraticPhaseMismatch (periodicSineFrequency N) observed term := by
  rw [quadraticPhaseMismatch_eq_signedCollisionSum]
  rfl

/-- If an actual signed quadratic Picard term is simultaneously on the
Fourier momentum shell and the sine-frequency shell, one of its observed or
input modes is the translation mode. -/
theorem quadraticPhase_fourier_resonance_has_zero_mode
    {N : Nat} [NeZero N] (observed : Site N)
    (term : QuadraticPhaseTerm N)
    (hmomentum : QuadraticPhaseFourierMomentumBalanced observed term)
    (hfrequency :
      quadraticPhaseMismatch (periodicSineFrequency N) observed term = 0) :
    ∃ r, quadraticCollisionModes observed term r = 0 := by
  apply threeWave_fourier_resonance_has_zero_mode
    (quadraticCollisionSign term) (quadraticCollisionModes observed term)
  · exact hmomentum
  · exact (signedFourierTripleMismatch_quadraticPhaseFourierTriple
      observed term).trans hfrequency

theorem finiteNonzeroMomentumThreeWaveGap_le_quadraticPhase
    {N : Nat} [NeZero N] (observed : Site N)
    (term : QuadraticPhaseTerm N)
    (hnonzero : ∀ r, quadraticCollisionModes observed term r ≠ 0)
    (hmomentum : QuadraticPhaseFourierMomentumBalanced observed term) :
    finiteNonzeroMomentumThreeWaveGap N ≤
      |quadraticPhaseMismatch (periodicSineFrequency N) observed term| := by
  rw [← signedFourierTripleMismatch_quadraticPhaseFourierTriple]
  exact finiteNonzeroMomentumThreeWaveGap_le N
    (quadraticPhaseFourierTriple observed term) ⟨hnonzero, hmomentum⟩

/-! ## Consumption by the first normal form and nested extraction -/

/-- Direct fixed-volume instantiation of the inverse-gap first-normal-form
bound for a family already restricted to nonzero, momentum-balanced Fourier
triples.  The supplied decoration is explicit: this theorem does not infer
momentum support from an arbitrary vertex. -/
theorem norm_quadraticPrimitiveCorrection_le_fixedFourierGap
    {N : Nat} [NeZero N]
    {Mode : Type*} [Fintype Mode]
    (vertex : Mode → Mode → Mode → Complex)
    (mismatch : Mode → Mode → Mode → Real)
    (decoration : Mode → Mode → Mode → SignedFourierTriple N)
    (amplitude : Mode → Complex) (time : Real) (out : Mode)
    (hmismatch : ∀ left right,
      mismatch out left right =
        signedFourierTripleMismatch (decoration out left right))
    (hactive : ∀ left right,
      IsNonzeroMomentumTriple (decoration out left right)) :
    ‖quadraticPrimitiveCorrection
        vertex mismatch amplitude time out‖ ≤
      (2 / finiteNonzeroMomentumThreeWaveGap N) *
        ∑ left, ∑ right,
          ‖vertex out left right‖ *
            ‖amplitude left‖ * ‖amplitude right‖ := by
  apply norm_quadraticPrimitiveCorrection_le
    vertex mismatch amplitude time out
    (finiteNonzeroMomentumThreeWaveGap N)
    (finiteNonzeroMomentumThreeWaveGap_pos N)
  intro left right
  rw [hmismatch left right]
  exact finiteNonzeroMomentumThreeWaveGap_le N
    (decoration out left right) (hactive left right)

/-- At fixed `N`, the exact first normal-form derivative identity and its
bounded primitive hold together on any explicitly decorated active Fourier
family.  The derivative premise is the microscopic interaction-picture
quadratic equation; no kinetic equation is assumed. -/
theorem finiteN_activeThreeWave_firstNormalForm
    {N : Nat} [NeZero N]
    {Mode : Type*} [Fintype Mode]
    (vertex : Mode → Mode → Mode → Complex)
    (mismatch : Mode → Mode → Mode → Real)
    (decoration : Mode → Mode → Mode → SignedFourierTriple N)
    (path : Real → Mode → Complex) (epsilon : Complex)
    (time : Real) (out : Mode)
    (hmismatch : ∀ left right,
      mismatch out left right =
        signedFourierTripleMismatch (decoration out left right))
    (hactive : ∀ left right,
      IsNonzeroMomentumTriple (decoration out left right))
    (hpath : ∀ mode, HasDerivAt (fun s ↦ path s mode)
      (epsilon * quadraticOscillatorySource
        vertex mismatch (path time) time mode) time) :
    HasDerivAt
        (fun s ↦ path s out - epsilon *
          quadraticPrimitiveCorrection vertex mismatch (path s) s out)
        (-(epsilon ^ 2) * quadraticCubicNormalFormSource
          vertex mismatch (path time) time out) time ∧
      ‖quadraticPrimitiveCorrection
          vertex mismatch (path time) time out‖ ≤
        (2 / finiteNonzeroMomentumThreeWaveGap N) *
          ∑ left, ∑ right,
            ‖vertex out left right‖ *
              ‖path time left‖ * ‖path time right‖ := by
  constructor
  · exact hasDerivAt_firstNormalForm
      vertex mismatch path epsilon time out hpath
  · exact norm_quadraticPrimitiveCorrection_le_fixedFourierGap
      vertex mismatch decoration (path time) time out hmismatch hactive

/-- One active actual quadratic Fourier term, packaged as an inner divisor
for the two-vertex (three-free-leaf/effective four-wave) Picard family. -/
abbrev ActiveQuadraticFourierTerm (N : Nat) [NeZero N] :=
  { data : Site N × QuadraticPhaseTerm N //
    IsNonzeroMomentumTriple
      (quadraticPhaseFourierTriple data.1 data.2) }

noncomputable instance activeQuadraticFourierTermFintype
    (N : Nat) [NeZero N] : Fintype (ActiveQuadraticFourierTerm N) :=
  Fintype.ofFinite _

def activeQuadraticFourierInnerMismatch
    {N : Nat} [NeZero N]
    (diagram : ActiveQuadraticFourierTerm N) : Real :=
  quadraticPhaseMismatch (periodicSineFrequency N)
    diagram.1.1 diagram.1.2

theorem activeQuadraticFourierInnerMismatch_ne_zero
    {N : Nat} [NeZero N]
    (diagram : ActiveQuadraticFourierTerm N) :
    activeQuadraticFourierInnerMismatch diagram ≠ 0 := by
  rw [activeQuadraticFourierInnerMismatch,
    ← signedFourierTripleMismatch_quadraticPhaseFourierTriple]
  exact signedFourierTripleMismatch_ne_zero_of_nonzeroMomentum
    (quadraticPhaseFourierTriple diagram.1.1 diagram.1.2) diagram.2

/-- Exact finite second-Picard extraction after the cubic shell has been
restricted to active off-shell Fourier diagrams.  The first term is the
effective higher-order (three-free-leaf, hence four-wave Hamiltonian)
interaction; the second is the normal-form boundary term. -/
theorem activeQuadraticFourierNestedPicard_eq_effective_sub_boundary
    {N : Nat} [NeZero N]
    (coefficient : ActiveQuadraticFourierTerm N → Complex)
    (outerMismatch : ActiveQuadraticFourierTerm N → Real)
    (time : Real) :
    finiteNestedPicardSum coefficient outerMismatch
        activeQuadraticFourierInnerMismatch time =
      finiteEffectiveInteractionSum coefficient outerMismatch
          activeQuadraticFourierInnerMismatch time -
        finiteNormalFormBoundarySum coefficient outerMismatch
          activeQuadraticFourierInnerMismatch time := by
  exact finiteNestedPicardSum_eq_effective_sub_boundary
    coefficient outerMismatch activeQuadraticFourierInnerMismatch time
    activeQuadraticFourierInnerMismatch_ne_zero

/-!
The next analytic batch, deliberately not asserted here, must bound binary
tree counts, nested time-simplex divisors, Fourier momentum-fibre
multiplicities, the effective four-wave kernel, and the Duhamel remainder in
a joint weak-nonlinearity/large-volume time window.  In particular the chosen
gap above may tend to zero with `N`.
-/

end

end ArchonPhysics.EqualMassPeriodicFPUTFourierThreeWave
