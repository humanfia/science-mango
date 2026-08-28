import ArchonPhysics.FreeFPUTCatalanPicardTailMajorant
import ArchonPhysics.NestedOscillatoryIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# Regular arbitrary-order oscillatory FPUT histories

This module isolates a genuine arbitrary-order analytic input for finite FPUT
Picard histories.  For a linear ordered history with local real phase
mismatches `delta_1, ..., delta_r`, it defines the actual nested Duhamel
integral

`integral_0^T exp(i delta_1 t_1) integral_0^{t_1} ... dt_r ... dt_1`.

Integration by parts merges the first two phases.  The recursively stated
fully-nonresonant condition below requires a gap `gamma` for every phase sum
that can occur in this merging procedure.  Under that explicit condition the
order-`r` integral is uniformly bounded by `(2 / gamma)^r`, independently of
time.  No kinetic equation, random-phase approximation, or probabilistic gap
claim is assumed.

The final section indexes the phase lists by the existing fixed-root binary
FPUT raw histories.  It turns uniform amplitude and gap hypotheses into the
single-history premise used by `FreeFPUTCatalanPicardTailMajorant`.  This is a
linear-order/spine interface: identifying a model's full branching Duhamel
coefficient with the supplied ordered integral remains an explicit adapter.
-/

namespace ArchonPhysics.FreeFPUTRegularArbitraryOrderOscillatoryHistory

open MeasureTheory
open ArchonPhysics
open ArchonPhysics.FreeFPUTBinaryTreeCatalanMomentumCounting
open ArchonPhysics.FreeFPUTCatalanPicardTailMajorant
open ArchonPhysics.Lattice
open ArchonPhysics.PhyslibFPUTBinaryInteractionTreeCouples
open Filter Topology
open scoped Interval

noncomputable section

/-! ## Linear ordered histories -/

/-- The genuine nested time-ordered oscillatory integral associated with a
list of local phase mismatches.  The empty history has coefficient one. -/
def linearOrderedOscillatoryIntegral : List Real -> Real -> Complex
  | [], _time => 1
  | delta :: phases, time =>
      ∫ t in (0 : Real)..time,
        Complex.exp ((Complex.I * delta) * t) *
          linearOrderedOscillatoryIntegral phases t

@[simp] theorem linearOrderedOscillatoryIntegral_nil (time : Real) :
    linearOrderedOscillatoryIntegral [] time = 1 := rfl

@[simp] theorem linearOrderedOscillatoryIntegral_cons
    (delta : Real) (phases : List Real) (time : Real) :
    linearOrderedOscillatoryIntegral (delta :: phases) time =
      ∫ t in (0 : Real)..time,
        Complex.exp ((Complex.I * delta) * t) *
          linearOrderedOscillatoryIntegral phases t := rfl

/-- Every ordered-history coefficient is continuous in its upper endpoint. -/
theorem continuous_linearOrderedOscillatoryIntegral
    (phases : List Real) :
    Continuous (linearOrderedOscillatoryIntegral phases) := by
  induction phases with
  | nil => exact continuous_const
  | cons delta phases ih =>
      change Continuous (fun endpoint : Real =>
        ∫ t in (0 : Real)..endpoint,
          Complex.exp ((Complex.I * delta) * t) *
            linearOrderedOscillatoryIntegral phases t)
      apply (intervalIntegral.differentiable_integral_of_continuous ?_).continuous
      exact (by fun_prop : Continuous (fun t : Real =>
        Complex.exp ((Complex.I * delta) * t))).mul ih

/-- FTC derivative of a nonempty ordered history. -/
theorem hasDerivAt_linearOrderedOscillatoryIntegral_cons
    (delta : Real) (phases : List Real) (time : Real) :
    HasDerivAt
      (linearOrderedOscillatoryIntegral (delta :: phases))
      (Complex.exp ((Complex.I * delta) * time) *
        linearOrderedOscillatoryIntegral phases time) time := by
  rw [show linearOrderedOscillatoryIntegral (delta :: phases) =
      fun endpoint => ∫ t in (0 : Real)..endpoint,
        Complex.exp ((Complex.I * delta) * t) *
          linearOrderedOscillatoryIntegral phases t by rfl]
  let integrand : Real -> Complex := fun t =>
    Complex.exp ((Complex.I * delta) * t) *
      linearOrderedOscillatoryIntegral phases t
  have hcontinuous : Continuous integrand :=
    (by fun_prop : Continuous (fun t : Real =>
      Complex.exp ((Complex.I * delta) * t))).mul
        (continuous_linearOrderedOscillatoryIntegral phases)
  exact intervalIntegral.integral_hasDerivAt_right
    (hcontinuous.intervalIntegrable (μ := volume) 0 time)
    hcontinuous.aestronglyMeasurable.stronglyMeasurableAtFilter
    hcontinuous.continuousAt

/-- Every nonempty ordered coefficient starts at zero. -/
@[simp] theorem linearOrderedOscillatoryIntegral_cons_zero
    (delta : Real) (phases : List Real) :
    linearOrderedOscillatoryIntegral (delta :: phases) 0 = 0 := by
  simp [linearOrderedOscillatoryIntegral]

/-- The one-vertex case agrees with the existing oscillatory integral. -/
theorem linearOrderedOscillatoryIntegral_singleton
    (delta time : Real) :
    linearOrderedOscillatoryIntegral [delta] time =
      NonresonantOscillatoryGain.oscillatoryIntegral delta time := by
  simp [linearOrderedOscillatoryIntegral,
    NonresonantOscillatoryGain.oscillatoryIntegral]

/-- At order two the arbitrary-order definition is exactly the previously
proved `NestedOscillatoryIntegral`, rather than a second competing notion. -/
theorem linearOrderedOscillatoryIntegral_pair_eq_nested
    (deltaOut deltaIn time : Real) :
    linearOrderedOscillatoryIntegral [deltaOut, deltaIn] time =
      NestedOscillatoryIntegral.nestedOscillatoryIntegral
        deltaOut deltaIn time := by
  unfold NestedOscillatoryIntegral.nestedOscillatoryIntegral
  rw [linearOrderedOscillatoryIntegral_cons]
  apply intervalIntegral.integral_congr
  intro t _ht
  dsimp
  simp [NonresonantOscillatoryGain.oscillatoryIntegral]

/-- A convenient antiderivative for a nonzero constant phase. -/
theorem hasDerivAt_expPhase_div
    {delta : Real} (hdelta : delta ≠ 0) (time : Real) :
    HasDerivAt
      (fun t : Real =>
        Complex.exp ((Complex.I * delta) * t) / (Complex.I * delta))
      (Complex.exp ((Complex.I * delta) * time)) time := by
  let c : Complex := Complex.I * delta
  have hc : c ≠ 0 :=
    mul_ne_zero Complex.I_ne_zero (Complex.ofReal_ne_zero.mpr hdelta)
  have hderiv : forall x : Real,
      HasDerivAt (fun y : Real => Complex.exp (c * y) / c)
        (Complex.exp (c * x)) x := by
    intro x
    have hlinear : HasDerivAt (fun y : Real => c * y) c x := by
      simpa only [mul_one] using!
        (((hasDerivAt_id (x : Complex)).const_mul c).comp_ofReal)
    simpa [Function.comp_def, hc] using
      ((Complex.hasDerivAt_exp _).comp x hlinear).div_const c
  simpa [c] using hderiv time

/-- Exact integration-by-parts recurrence.  It exhibits precisely why the
merged cumulative mismatch `deltaOne + deltaTwo` must also be controlled. -/
theorem linearOrderedOscillatoryIntegral_cons_cons_eq
    {deltaOne : Real} (hdeltaOne : deltaOne ≠ 0)
    (deltaTwo : Real) (tail : List Real) (time : Real) :
    linearOrderedOscillatoryIntegral
        (deltaOne :: deltaTwo :: tail) time =
      (Complex.exp ((Complex.I * deltaOne) * time) *
          linearOrderedOscillatoryIntegral (deltaTwo :: tail) time -
        linearOrderedOscillatoryIntegral
          ((deltaOne + deltaTwo) :: tail) time) /
        (Complex.I * deltaOne) := by
  let inner : Real -> Complex :=
    linearOrderedOscillatoryIntegral (deltaTwo :: tail)
  let innerDeriv : Real -> Complex := fun t =>
    Complex.exp ((Complex.I * deltaTwo) * t) *
      linearOrderedOscillatoryIntegral tail t
  let primitive : Real -> Complex := fun t =>
    Complex.exp ((Complex.I * deltaOne) * t) /
      (Complex.I * deltaOne)
  let phase : Real -> Complex := fun t =>
    Complex.exp ((Complex.I * deltaOne) * t)
  have hinner : forall t : Real,
      HasDerivAt inner (innerDeriv t) t := by
    intro t
    exact hasDerivAt_linearOrderedOscillatoryIntegral_cons
      deltaTwo tail t
  have hprimitive : forall t : Real,
      HasDerivAt primitive (phase t) t := by
    intro t
    exact hasDerivAt_expPhase_div hdeltaOne t
  have hinnerDerivContinuous : Continuous innerDeriv :=
    (by fun_prop : Continuous (fun t : Real =>
      Complex.exp ((Complex.I * deltaTwo) * t))).mul
        (continuous_linearOrderedOscillatoryIntegral tail)
  have hphaseContinuous : Continuous phase := by
    fun_prop
  have hibp :
      (∫ t in (0 : Real)..time, inner t * phase t) =
        inner time * primitive time - inner 0 * primitive 0 -
          ∫ t in (0 : Real)..time, innerDeriv t * primitive t := by
    exact intervalIntegral.integral_mul_deriv_eq_deriv_mul
      (fun t _ht => hinner t) (fun t _ht => hprimitive t)
      (hinnerDerivContinuous.intervalIntegrable (μ := volume) 0 time)
      (hphaseContinuous.intervalIntegrable (μ := volume) 0 time)
  have hmergedIntegral :
      (∫ t in (0 : Real)..time, innerDeriv t * primitive t) =
        linearOrderedOscillatoryIntegral
            ((deltaOne + deltaTwo) :: tail) time /
          (Complex.I * deltaOne) := by
    calc
      (∫ t in (0 : Real)..time, innerDeriv t * primitive t) =
          ∫ t in (0 : Real)..time,
            (Complex.exp ((Complex.I * (deltaOne + deltaTwo)) * t) *
              linearOrderedOscillatoryIntegral tail t) /
                (Complex.I * deltaOne) := by
        apply intervalIntegral.integral_congr
        intro t _ht
        dsimp [innerDeriv, primitive]
        rw [← NestedOscillatoryIntegral.exp_phase_mul_exp_phase
          deltaOne deltaTwo t]
        ring
      _ = (∫ t in (0 : Real)..time,
            Complex.exp ((Complex.I * (deltaOne + deltaTwo)) * t) *
              linearOrderedOscillatoryIntegral tail t) /
                (Complex.I * deltaOne) := by
        rw [intervalIntegral.integral_div]
      _ = linearOrderedOscillatoryIntegral
            ((deltaOne + deltaTwo) :: tail) time /
              (Complex.I * deltaOne) := by
        congr 1
        apply intervalIntegral.integral_congr
        intro t _ht
        push_cast
        rfl
  calc
    linearOrderedOscillatoryIntegral
        (deltaOne :: deltaTwo :: tail) time =
        ∫ t in (0 : Real)..time, inner t * phase t := by
      apply intervalIntegral.integral_congr
      intro t _ht
      dsimp [inner, phase]
      ring
    _ = inner time * primitive time - inner 0 * primitive 0 -
          ∫ t in (0 : Real)..time, innerDeriv t * primitive t := hibp
    _ = _ := by
      rw [hmergedIntegral]
      simp only [inner, primitive,
        linearOrderedOscillatoryIntegral_cons_zero, zero_mul, sub_zero]
      ring

/-! ## Fully nonresonant cumulative phase condition -/

/-- Recursive gap certificate for exactly the phase sums generated by
repeated integration by parts.  At a two-or-more vertex history it records
regularity both after deleting the outer vertex and after merging the first
two local phases.  Thus every denominator appearing anywhere in the complete
IBP tree is explicitly certified to have absolute value at least `gamma`. -/
inductive FullyNonresonantOrderedHistory (gamma : Real) :
    List Real -> Prop
  | nil : FullyNonresonantOrderedHistory gamma []
  | singleton (delta : Real) (gap : gamma <= |delta|) :
      FullyNonresonantOrderedHistory gamma [delta]
  | cons (deltaOne deltaTwo : Real) (tail : List Real)
      (firstGap : gamma <= |deltaOne|)
      (dropRegular : FullyNonresonantOrderedHistory gamma (deltaTwo :: tail))
      (mergeRegular : FullyNonresonantOrderedHistory gamma
        ((deltaOne + deltaTwo) :: tail)) :
      FullyNonresonantOrderedHistory gamma
        (deltaOne :: deltaTwo :: tail)

/-- A positive fully-nonresonant gap makes the outermost phase nonzero. -/
theorem FullyNonresonantOrderedHistory.head_ne_zero
    {gamma delta : Real} {tail : List Real}
    (hgamma : 0 < gamma)
    (hregular : FullyNonresonantOrderedHistory gamma (delta :: tail)) :
    delta ≠ 0 := by
  cases tail with
  | nil =>
      cases hregular with
      | singleton _ hgap =>
          exact (abs_pos.mp (hgamma.trans_le hgap))
  | cons deltaTwo tail =>
      cases hregular with
      | cons _ _ _ hgap _ _ =>
          exact (abs_pos.mp (hgamma.trans_le hgap))

/-- Arbitrary-order resolvent/IBP majorant.  Every integration by parts
creates two histories and one inverse phase; the complete bound is therefore
`(2/gamma)^r`.  It is uniform in the oriented endpoint `time`. -/
theorem norm_linearOrderedOscillatoryIntegral_le_resolvent
    {gamma : Real} (hgamma : 0 < gamma)
    {phases : List Real}
    (hregular : FullyNonresonantOrderedHistory gamma phases)
    (time : Real) :
    ‖linearOrderedOscillatoryIntegral phases time‖ <=
      (2 / gamma) ^ phases.length := by
  induction hregular generalizing time with
  | nil =>
      norm_num [linearOrderedOscillatoryIntegral]
  | singleton delta hgap =>
      have habsPos : 0 < |delta| := hgamma.trans_le hgap
      have hdelta : delta ≠ 0 := abs_pos.mp habsPos
      rw [linearOrderedOscillatoryIntegral_singleton]
      calc
        ‖NonresonantOscillatoryGain.oscillatoryIntegral delta time‖ <=
            2 / |delta| :=
          NonresonantOscillatoryGain.norm_oscillatoryIntegral_le_two_div_abs
            hdelta
        _ <= 2 / gamma :=
          (div_le_div_iff_of_pos_left (by norm_num) habsPos hgamma).2 hgap
        _ = (2 / gamma) ^ [delta].length := by simp
  | cons deltaOne deltaTwo tail firstGap _dropRegular _mergeRegular
      dropBound mergeBound =>
      have habsPos : 0 < |deltaOne| := hgamma.trans_le firstGap
      have hdeltaOne : deltaOne ≠ 0 := abs_pos.mp habsPos
      have hphaseNorm :
          ‖Complex.exp ((Complex.I * deltaOne) * time)‖ = 1 := by
        rw [show (Complex.I * (deltaOne : Complex)) * (time : Complex) =
          Complex.I * ((deltaOne * time : Real) : Complex) by
            push_cast
            ring]
        exact Complex.norm_exp_I_mul_ofReal (deltaOne * time)
      have hbasePos : 0 < 2 / gamma := div_pos (by norm_num) hgamma
      have hsubPos :
          0 < (2 / gamma) ^ (deltaTwo :: tail).length :=
        pow_pos hbasePos _
      rw [linearOrderedOscillatoryIntegral_cons_cons_eq
        hdeltaOne deltaTwo tail time, norm_div]
      calc
        ‖Complex.exp ((Complex.I * deltaOne) * time) *
                linearOrderedOscillatoryIntegral (deltaTwo :: tail) time -
              linearOrderedOscillatoryIntegral
                ((deltaOne + deltaTwo) :: tail) time‖ /
            ‖Complex.I * (deltaOne : Complex)‖ <=
            (‖Complex.exp ((Complex.I * deltaOne) * time) *
                linearOrderedOscillatoryIntegral (deltaTwo :: tail) time‖ +
              ‖linearOrderedOscillatoryIntegral
                ((deltaOne + deltaTwo) :: tail) time‖) /
              |deltaOne| := by
          rw [norm_mul, Complex.norm_I, one_mul,
            Complex.norm_real, Real.norm_eq_abs]
          exact div_le_div_of_nonneg_right
            (norm_sub_le _ _) (abs_nonneg deltaOne)
        _ = (‖linearOrderedOscillatoryIntegral
                (deltaTwo :: tail) time‖ +
              ‖linearOrderedOscillatoryIntegral
                ((deltaOne + deltaTwo) :: tail) time‖) /
              |deltaOne| := by rw [norm_mul, hphaseNorm, one_mul]
        _ <= (((2 / gamma) ^ (deltaTwo :: tail).length) +
              ((2 / gamma) ^ ((deltaOne + deltaTwo) :: tail).length)) /
              |deltaOne| := by
          exact div_le_div_of_nonneg_right
            (add_le_add (dropBound time) (mergeBound time))
            (abs_nonneg deltaOne)
        _ = (((2 / gamma) ^ (deltaTwo :: tail).length) +
              ((2 / gamma) ^ (deltaTwo :: tail).length)) /
              |deltaOne| := by simp
        _ <= (((2 / gamma) ^ (deltaTwo :: tail).length) +
              ((2 / gamma) ^ (deltaTwo :: tail).length)) /
              gamma := by
          exact (div_le_div_iff_of_pos_left
            (add_pos hsubPos hsubPos) habsPos hgamma).2 firstGap
        _ = (2 / gamma) ^
              (deltaOne :: deltaTwo :: tail).length := by
          simp only [List.length_cons]
          rw [show tail.length + 2 = (tail.length + 1) + 1 by omega,
            pow_succ]
          ring

/-! ## Fixed-root FPUT history adapter -/

/-- Multiply a supplied fixed-root FPUT raw-history amplitude by its genuine
linear ordered oscillatory integral. -/
def fixedRootOrderedOscillatoryHistoryCoefficient
    (N : Nat) [NeZero N] (rootMomentum : Site N)
    (amplitude :
      (r : Nat) -> FixedRootRawHistoryIndex N r rootMomentum -> Complex)
    (phaseHistory :
      (r : Nat) -> FixedRootRawHistoryIndex N r rootMomentum -> List Real)
    (time : Real) (r : Nat)
    (history : FixedRootRawHistoryIndex N r rootMomentum) : Complex :=
  amplitude r history *
    linearOrderedOscillatoryIntegral (phaseHistory r history) time

/-- The analytic per-vertex ratio left after combining amplitude growth
`rho^r` with the arbitrary-order inverse-gap gain. -/
def regularOrderedHistoryAnalyticRatio (rho gamma : Real) : Real :=
  2 * rho / gamma

theorem regularOrderedHistoryAnalyticRatio_nonneg
    {rho gamma : Real} (hrho : 0 <= rho) (hgamma : 0 < gamma) :
    0 <= regularOrderedHistoryAnalyticRatio rho gamma := by
  unfold regularOrderedHistoryAnalyticRatio
  positivity

/-- A uniform amplitude majorant and a fully nonresonant phase certificate
give a true single-history arbitrary-order bound. -/
theorem norm_fixedRootOrderedOscillatoryHistoryCoefficient_le
    (N : Nat) [NeZero N] (rootMomentum : Site N)
    (amplitude :
      (r : Nat) -> FixedRootRawHistoryIndex N r rootMomentum -> Complex)
    (phaseHistory :
      (r : Nat) -> FixedRootRawHistoryIndex N r rootMomentum -> List Real)
    {A rho gamma : Real} (hA : 0 <= A) (hrho : 0 <= rho)
    (hgamma : 0 < gamma)
    (hlength : forall r history, (phaseHistory r history).length = r)
    (hregular : forall r history,
      FullyNonresonantOrderedHistory gamma (phaseHistory r history))
    (hamplitude : forall r history,
      ‖amplitude r history‖ <= A * rho ^ r)
    (time : Real) (r : Nat)
    (history : FixedRootRawHistoryIndex N r rootMomentum) :
    ‖fixedRootOrderedOscillatoryHistoryCoefficient
        N rootMomentum amplitude phaseHistory time r history‖ <=
      A * regularOrderedHistoryAnalyticRatio rho gamma ^ r := by
  have hosc := norm_linearOrderedOscillatoryIntegral_le_resolvent
    hgamma (hregular r history) time
  unfold fixedRootOrderedOscillatoryHistoryCoefficient
  rw [norm_mul]
  calc
    ‖amplitude r history‖ *
          ‖linearOrderedOscillatoryIntegral
            (phaseHistory r history) time‖ <=
        (A * rho ^ r) *
          (2 / gamma) ^ (phaseHistory r history).length := by
      exact mul_le_mul (hamplitude r history) hosc
        (norm_nonneg _)
        (mul_nonneg hA (pow_nonneg hrho r))
    _ = A * regularOrderedHistoryAnalyticRatio rho gamma ^ r := by
      rw [hlength r history]
      unfold regularOrderedHistoryAnalyticRatio
      rw [show 2 * rho / gamma = rho * (2 / gamma) by ring, mul_pow]
      ring

/-- Explicit sufficient condition for the `q/(16N)` single-history premise
of the Catalan majorant.  This theorem is the analytic handoff to the
arbitrary-order summation module. -/
theorem norm_fixedRootOrderedOscillatoryHistoryCoefficient_le_catalanScale
    (N : Nat) [NeZero N] (rootMomentum : Site N)
    (amplitude :
      (r : Nat) -> FixedRootRawHistoryIndex N r rootMomentum -> Complex)
    (phaseHistory :
      (r : Nat) -> FixedRootRawHistoryIndex N r rootMomentum -> List Real)
    {A rho gamma q : Real} (hA : 0 <= A) (hrho : 0 <= rho)
    (hgamma : 0 < gamma) (hq : 0 <= q)
    (hratio : regularOrderedHistoryAnalyticRatio rho gamma <=
      q / (16 * (N : Real)))
    (hlength : forall r history, (phaseHistory r history).length = r)
    (hregular : forall r history,
      FullyNonresonantOrderedHistory gamma (phaseHistory r history))
    (hamplitude : forall r history,
      ‖amplitude r history‖ <= A * rho ^ r)
    (time : Real) (r : Nat)
    (history : FixedRootRawHistoryIndex N r rootMomentum) :
    ‖fixedRootOrderedOscillatoryHistoryCoefficient
        N rootMomentum amplitude phaseHistory time r history‖ <=
      A * singleHistoryCatalanScale N q r := by
  have hratio0 : 0 <= regularOrderedHistoryAnalyticRatio rho gamma :=
    regularOrderedHistoryAnalyticRatio_nonneg hrho hgamma
  have htarget0 : 0 <= q / (16 * (N : Real)) := by positivity
  calc
    ‖fixedRootOrderedOscillatoryHistoryCoefficient
        N rootMomentum amplitude phaseHistory time r history‖ <=
        A * regularOrderedHistoryAnalyticRatio rho gamma ^ r :=
      norm_fixedRootOrderedOscillatoryHistoryCoefficient_le
        N rootMomentum amplitude phaseHistory hA hrho hgamma
          hlength hregular hamplitude time r history
    _ <= A * (q / (16 * (N : Real))) ^ r := by
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ hratio0 hratio r) hA
    _ = A * singleHistoryCatalanScale N q r := rfl

/-- Under the explicit gap and smallness conditions, the complete fixed-root
order sum inherits the geometric Catalan bound. -/
theorem norm_fixedRootOrderedOscillatoryHistoryOrderSum_le_geometric
    (N : Nat) [NeZero N] (rootMomentum : Site N)
    (amplitude :
      (r : Nat) -> FixedRootRawHistoryIndex N r rootMomentum -> Complex)
    (phaseHistory :
      (r : Nat) -> FixedRootRawHistoryIndex N r rootMomentum -> List Real)
    {A rho gamma q : Real} (hA : 0 <= A) (hrho : 0 <= rho)
    (hgamma : 0 < gamma) (hq : 0 <= q)
    (hratio : regularOrderedHistoryAnalyticRatio rho gamma <=
      q / (16 * (N : Real)))
    (hlength : forall r history, (phaseHistory r history).length = r)
    (hregular : forall r history,
      FullyNonresonantOrderedHistory gamma (phaseHistory r history))
    (hamplitude : forall r history,
      ‖amplitude r history‖ <= A * rho ^ r)
    (time : Real) (r : Nat) :
    ‖fixedRootRawHistoryOrderSum N rootMomentum
        (fixedRootOrderedOscillatoryHistoryCoefficient
          N rootMomentum amplitude phaseHistory time) r‖ <=
      A * q ^ r := by
  apply norm_fixedRootRawHistoryOrderSum_le_geometric
    N rootMomentum _ hA hq
  intro order history
  exact norm_fixedRootOrderedOscillatoryHistoryCoefficient_le_catalanScale
    N rootMomentum amplitude phaseHistory hA hrho hgamma hq hratio
      hlength hregular hamplitude time order history

/-- The same concrete analytic hypotheses give the all-orders tail estimate
and its convergence to zero. -/
theorem fixedRootOrderedOscillatoryHistory_tail_certificate
    (N : Nat) [NeZero N] (rootMomentum : Site N)
    (amplitude :
      (r : Nat) -> FixedRootRawHistoryIndex N r rootMomentum -> Complex)
    (phaseHistory :
      (r : Nat) -> FixedRootRawHistoryIndex N r rootMomentum -> List Real)
    {A rho gamma q : Real} (hA : 0 <= A) (hrho : 0 <= rho)
    (hgamma : 0 < gamma) (hq0 : 0 <= q) (hq1 : q < 1)
    (hratio : regularOrderedHistoryAnalyticRatio rho gamma <=
      q / (16 * (N : Real)))
    (hlength : forall r history, (phaseHistory r history).length = r)
    (hregular : forall r history,
      FullyNonresonantOrderedHistory gamma (phaseHistory r history))
    (hamplitude : forall r history,
      ‖amplitude r history‖ <= A * rho ^ r)
    (time : Real) :
    (forall r,
      ‖fixedRootRawHistoryOrderSum N rootMomentum
          (fixedRootOrderedOscillatoryHistoryCoefficient
            N rootMomentum amplitude phaseHistory time) r‖ <=
        A * q ^ r) ∧
    (forall R,
      ‖fixedRootRawHistoryTail N rootMomentum
          (fixedRootOrderedOscillatoryHistoryCoefficient
            N rootMomentum amplitude phaseHistory time) R‖ <=
        A * q ^ R / (1 - q)) ∧
    Tendsto (fun R : Nat =>
      ‖fixedRootRawHistoryTail N rootMomentum
          (fixedRootOrderedOscillatoryHistoryCoefficient
            N rootMomentum amplitude phaseHistory time) R‖)
      atTop (nhds 0) := by
  have hsingle : forall r history,
      ‖fixedRootOrderedOscillatoryHistoryCoefficient
          N rootMomentum amplitude phaseHistory time r history‖ <=
        A * singleHistoryCatalanScale N q r := by
    intro r history
    exact norm_fixedRootOrderedOscillatoryHistoryCoefficient_le_catalanScale
      N rootMomentum amplitude phaseHistory hA hrho hgamma hq0 hratio
        hlength hregular hamplitude time r history
  refine ⟨?_, ?_, ?_⟩
  · intro r
    exact norm_fixedRootRawHistoryOrderSum_le_geometric
      N rootMomentum _ hA hq0 hsingle r
  · intro R
    exact norm_fixedRootRawHistoryTail_le_geometric
      N rootMomentum _ hA hq0 hq1 hsingle R
  · exact norm_fixedRootRawHistoryTail_tendsto_zero
      N rootMomentum _ hA hq0 hq1 hsingle

/-! ## Existing recursive Physlib coefficient specialization -/

/-- The existing recursive Physlib coefficient supplies the amplitude premise
with per-vertex ratio `leafBound * branchBound`. -/
theorem norm_realizedBinaryTreeAmplitude_le_geometric
    {Mode : Type*} {kernel : BinaryTreeCoefficientKernel Mode}
    (bound : BinaryTreeCoefficientKernelMajorant kernel)
    (N : Nat) [NeZero N] (rootMomentum : Site N)
    (realize : (r : Nat) ->
      FixedRootRawHistoryIndex N r rootMomentum ->
        RandomEigenmodeBinaryTree Mode)
    (horder : forall r history, (realize r history).shape.order = r)
    {A : Real} (_hA : 0 <= A) (hleafA : bound.leafBound <= A)
    (r : Nat) (history : FixedRootRawHistoryIndex N r rootMomentum) :
    ‖binaryTreeCoefficient kernel (realize r history)‖ <=
      A * (bound.leafBound * bound.branchBound) ^ r := by
  have hbranch0 : 0 <= bound.branchBound := bound.branchBound_nonneg
  calc
    ‖binaryTreeCoefficient kernel (realize r history)‖ <=
        bound.leafBound ^ ((realize r history).shape.order + 1) *
          bound.branchBound ^ (realize r history).shape.order :=
      bound.norm_binaryTreeCoefficient_le (realize r history)
    _ = bound.leafBound *
          (bound.leafBound * bound.branchBound) ^ r := by
      rw [horder r history, pow_succ, mul_pow]
      ring
    _ <= A * (bound.leafBound * bound.branchBound) ^ r := by
      exact mul_le_mul_of_nonneg_right hleafA
        (pow_nonneg
          (mul_nonneg bound.leafBound_nonneg hbranch0) r)

/-- Fully explicit arbitrary-order tail certificate for the existing Physlib
recursive tree coefficient multiplied by a supplied regular ordered phase
history.  The model-specific obligations are precisely the order-preserving
realization, the phase-list identification, and the cumulative-gap proof. -/
theorem fixedRootRealizedKernelOrderedOscillatoryHistory_tail_certificate
    {Mode : Type*} {kernel : BinaryTreeCoefficientKernel Mode}
    (bound : BinaryTreeCoefficientKernelMajorant kernel)
    (N : Nat) [NeZero N] (rootMomentum : Site N)
    (realize : (r : Nat) ->
      FixedRootRawHistoryIndex N r rootMomentum ->
        RandomEigenmodeBinaryTree Mode)
    (horder : forall r history, (realize r history).shape.order = r)
    (phaseHistory :
      (r : Nat) -> FixedRootRawHistoryIndex N r rootMomentum -> List Real)
    {A gamma q : Real} (hA : 0 <= A)
    (hleafA : bound.leafBound <= A)
    (hgamma : 0 < gamma) (hq0 : 0 <= q) (hq1 : q < 1)
    (hratio : regularOrderedHistoryAnalyticRatio
        (bound.leafBound * bound.branchBound) gamma <=
      q / (16 * (N : Real)))
    (hlength : forall r history, (phaseHistory r history).length = r)
    (hregular : forall r history,
      FullyNonresonantOrderedHistory gamma (phaseHistory r history))
    (time : Real) :
    (forall r,
      ‖fixedRootRawHistoryOrderSum N rootMomentum
          (fixedRootOrderedOscillatoryHistoryCoefficient N rootMomentum
            (fun order history =>
              binaryTreeCoefficient kernel (realize order history))
            phaseHistory time) r‖ <= A * q ^ r) ∧
    (forall R,
      ‖fixedRootRawHistoryTail N rootMomentum
          (fixedRootOrderedOscillatoryHistoryCoefficient N rootMomentum
            (fun order history =>
              binaryTreeCoefficient kernel (realize order history))
            phaseHistory time) R‖ <= A * q ^ R / (1 - q)) ∧
    Tendsto (fun R : Nat =>
      ‖fixedRootRawHistoryTail N rootMomentum
          (fixedRootOrderedOscillatoryHistoryCoefficient N rootMomentum
            (fun order history =>
              binaryTreeCoefficient kernel (realize order history))
            phaseHistory time) R‖) atTop (nhds 0) := by
  have hrho : 0 <= bound.leafBound * bound.branchBound :=
    mul_nonneg bound.leafBound_nonneg bound.branchBound_nonneg
  exact fixedRootOrderedOscillatoryHistory_tail_certificate
    N rootMomentum
      (fun order history =>
        binaryTreeCoefficient kernel (realize order history))
      phaseHistory hA hrho hgamma hq0 hq1 hratio hlength hregular
      (fun r history =>
        norm_realizedBinaryTreeAmplitude_le_geometric bound
          N rootMomentum realize horder hA hleafA r history)
      time

end

end ArchonPhysics.FreeFPUTRegularArbitraryOrderOscillatoryHistory
