import Family8Grounding.Family8FixedJohnAutomaticRepetitionUpperV1
import Family8Grounding.Family8FiniteRandomRigidMotionPaperFixedJohnGreedyLossSourceExponentV4
import FamilyStickyGrounding.FamilyStickyScaleChainSmallDeltaExponentBudgetProducerV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5000000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8FixedJohnTransportScalarPowerCapV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Family8KatzTaoFrostmanPropertiesV1
open Family8FiniteRandomRigidMotionPaperFixedJohnAutomaticConflictCapV2
open Family8FiniteRandomRigidMotionPaperFixedJohnAutomaticDensityRepetitionsV2
open Family8FiniteRandomRigidMotionPaperFixedJohnFrostmanCWAConnectorV2
open Family8FiniteRandomRigidMotionPaperFixedJohnGreedyLossSourceExponentV4
open Family8FrostmanRHSScaleVolumeAlgebraV4
open Family8FixedJohnAutomaticRepetitionUpperV1
open FamilyStickyScaleChainSmallDeltaExponentBudgetProducerV1

noncomputable section

/-!
# Datum-uniform power cap for the fixed-John transport scalar

The automatic copy count contributes only two inverse powers of the
normalized radius.  Combining that bound with the existing automatic greedy
loss envelope leaves a finite coefficient and one explicit exponent.  A
standard finite-constant threshold absorbs the coefficient.  The harmless
comparison `delta^2 <= delta/8` below `delta <= 1/8` returns the final bound
to the original scale without any datum-dependent premise.
-/

def fixedJohnTransportNormalizedExponent
    (tailEta sourceEta gamma : Real) : Real :=
  (17 + tailEta + sourceEta) + 2 * (1 - gamma / 2)

def fixedJohnTransportPowerConstant
    (tailEta sourceEpsilon gamma : Real) : ENNReal :=
  ENNReal.ofReal (fixedJohnGreedyLossSourcePowerConstant tailEta) *
    ((8 : ENNReal) ^ sourceEpsilon * (8 : ENNReal) ^ (2 * gamma)) *
      (2 : ENNReal) ^ (1 - gamma / 2)

def fixedJohnTransportScalarThreshold
    (tailEta sourceEta sourceEpsilon gamma kappa : Real) : NNReal :=
  min (1 / 8 : NNReal)
    (finiteConstantSmallDeltaThreshold
      (fixedJohnTransportPowerConstant tailEta sourceEpsilon gamma)
      (kappa - 2 *
        fixedJohnTransportNormalizedExponent tailEta sourceEta gamma))

theorem fixedJohnTransportScalarThreshold_pos
    (tailEta sourceEta sourceEpsilon gamma kappa : Real) :
    0 < fixedJohnTransportScalarThreshold
      tailEta sourceEta sourceEpsilon gamma kappa := by
  apply lt_min
  · norm_num
  · exact finiteConstantSmallDeltaThreshold_pos _ _

theorem fixedJohnTransportNormalizedExponent_pos
    {tailEta sourceEta gamma : Real}
    (htailEta : 0 < tailEta) (hsourceEta : 0 <= sourceEta)
    (hgamma : gamma <= 2) :
    0 < fixedJohnTransportNormalizedExponent tailEta sourceEta gamma := by
  unfold fixedJohnTransportNormalizedExponent
  nlinarith

theorem fixedJohnTransportPowerConstant_ne_top
    (tailEta sourceEpsilon gamma : Real) :
    fixedJohnTransportPowerConstant tailEta sourceEpsilon gamma ≠ ∞ := by
  unfold fixedJohnTransportPowerConstant
  apply ENNReal.mul_ne_top
  · apply ENNReal.mul_ne_top
    · exact ENNReal.ofReal_ne_top
    · apply ENNReal.mul_ne_top
      · exact ENNReal.rpow_ne_top_of_ne_zero (by norm_num) (by norm_num)
      · exact ENNReal.rpow_ne_top_of_ne_zero (by norm_num) (by norm_num)
  · exact ENNReal.rpow_ne_top_of_ne_zero (by norm_num) (by norm_num)

theorem fixedJohnFrostmanTransportScalar_le_normalizedPower
    {sourceEpsilon gamma sourceEta tailEta : Real}
    {delta : NNReal} {iota : Type}
    [Fintype iota] [Nonempty iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible)
    {C : ENNReal}
    (hsourceEta : 0 <= sourceEta) (htailEta : 0 < tailEta)
    (hgamma : gamma <= 2)
    (hKT : IsKatzTao C D.family.bodyFamily)
    (hC : C <= (delta : ENNReal) ^ (-sourceEta)) :
    fixedJohnFrostmanTransportScalar
        (fixedJohnAutomaticGreedyLoss D hD : ENNReal)
        ((fixedJohnAutomaticDensityRepetitions D hD : ENNReal) *
          (1 / 4 : ENNReal)) sourceEpsilon gamma <=
      fixedJohnTransportPowerConstant tailEta sourceEpsilon gamma *
        (((delta / 8 : NNReal) : ENNReal) ^
          (-fixedJohnTransportNormalizedExponent
            tailEta sourceEta gamma)) := by
  let rho : ENNReal := ((delta / 8 : NNReal) : ENNReal)
  let p : Real := 17 + tailEta + sourceEta
  let q : Real := 1 - gamma / 2
  let K : ENNReal :=
    ENNReal.ofReal (fixedJohnGreedyLossSourcePowerConstant tailEta)
  have hrho0 : rho ≠ 0 := by
    dsimp only [rho]
    exact ENNReal.coe_ne_zero.mpr (admissibleNormalizedRadiusPos hD).ne'
  have hrhoTop : rho ≠ ∞ := by
    dsimp only [rho]
    exact ENNReal.coe_ne_top
  have hq : 0 <= q := by dsimp only [q]; linarith
  have hloss : (fixedJohnAutomaticGreedyLoss D hD : ENNReal) <=
      K * rho ^ (-p) := by
    simpa only [K, rho, p] using
      fixedJohnAutomaticGreedyLoss_le_sourceExponentPower
        D hD hsourceEta htailEta hKT hC
  have hcopy :
      (fixedJohnAutomaticDensityRepetitions D hD : ENNReal) *
          (1 / 4 : ENNReal) <=
        2 * rho ^ (-2 : Real) := by
    calc
      (fixedJohnAutomaticDensityRepetitions D hD : ENNReal) *
            (1 / 4 : ENNReal) <=
          (fixedJohnAutomaticDensityRepetitions D hD : ENNReal) * 1 := by
        gcongr
        norm_num
      _ = (fixedJohnAutomaticDensityRepetitions D hD : ENNReal) := by simp
      _ <= 2 * rho ^ (-2 : Real) := by
        simpa only [rho] using
          fixedJohnAutomaticDensityRepetitions_le_two_mul_rho_neg_two D hD
  have hcopyPow :
      ((fixedJohnAutomaticDensityRepetitions D hD : ENNReal) *
          (1 / 4 : ENNReal)) ^ q <=
        (2 * rho ^ (-2 : Real)) ^ q :=
    ENNReal.rpow_le_rpow hcopy hq
  unfold fixedJohnFrostmanTransportScalar
  calc
    (fixedJohnAutomaticGreedyLoss D hD : ENNReal) *
          ((8 : ENNReal) ^ sourceEpsilon *
            (8 : ENNReal) ^ (2 * gamma)) *
          (((fixedJohnAutomaticDensityRepetitions D hD : ENNReal) *
            (1 / 4 : ENNReal)) ^ q) <=
        (K * rho ^ (-p)) *
          ((8 : ENNReal) ^ sourceEpsilon *
            (8 : ENNReal) ^ (2 * gamma)) *
          ((2 * rho ^ (-2 : Real)) ^ q) := by
      exact mul_le_mul' (mul_le_mul' hloss le_rfl) hcopyPow
    _ = (K *
          ((8 : ENNReal) ^ sourceEpsilon *
            (8 : ENNReal) ^ (2 * gamma)) *
          (2 : ENNReal) ^ q) *
        (rho ^ (-p) * rho ^ ((-2 : Real) * q)) := by
      rw [ENNReal.mul_rpow_of_nonneg _ _ hq]
      have hrhoPower :
          (rho ^ (-2 : Real)) ^ q = rho ^ ((-2 : Real) * q) := by
        rw [← ENNReal.rpow_mul]
      rw [hrhoPower]
      ac_rfl
    _ = (K *
          ((8 : ENNReal) ^ sourceEpsilon *
            (8 : ENNReal) ^ (2 * gamma)) *
          (2 : ENNReal) ^ q) *
        rho ^ ((-p) + ((-2 : Real) * q)) := by
      rw [ENNReal.rpow_add _ _ hrho0 hrhoTop]
    _ = fixedJohnTransportPowerConstant tailEta sourceEpsilon gamma *
        rho ^ (-fixedJohnTransportNormalizedExponent
          tailEta sourceEta gamma) := by
      have hexponent :
          (-p) + ((-2 : Real) * q) =
            -fixedJohnTransportNormalizedExponent
              tailEta sourceEta gamma := by
        dsimp only [p, q, fixedJohnTransportNormalizedExponent]
        ring
      rw [hexponent]
      rfl

theorem fixedJohnFrostmanTransportScalar_le_deltaPower
    {sourceEpsilon gamma sourceEta tailEta kappa : Real}
    {delta : NNReal} {iota : Type}
    [Fintype iota] [Nonempty iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible)
    {C : ENNReal}
    (hsourceEta : 0 <= sourceEta) (htailEta : 0 < tailEta)
    (hgamma : gamma <= 2)
    (hgap : 2 * fixedJohnTransportNormalizedExponent
        tailEta sourceEta gamma < kappa)
    (hKT : IsKatzTao C D.family.bodyFamily)
    (hC : C <= (delta : ENNReal) ^ (-sourceEta))
    (hsmall : delta <= fixedJohnTransportScalarThreshold
      tailEta sourceEta sourceEpsilon gamma kappa) :
    fixedJohnFrostmanTransportScalar
        (fixedJohnAutomaticGreedyLoss D hD : ENNReal)
        ((fixedJohnAutomaticDensityRepetitions D hD : ENNReal) *
          (1 / 4 : ENNReal)) sourceEpsilon gamma <=
      (delta : ENNReal) ^ (-kappa) := by
  let d : ENNReal := (delta : ENNReal)
  let rho : ENNReal := ((delta / 8 : NNReal) : ENNReal)
  let r : Real := fixedJohnTransportNormalizedExponent
    tailEta sourceEta gamma
  let a : Real := kappa - 2 * r
  let K : ENNReal :=
    fixedJohnTransportPowerConstant tailEta sourceEpsilon gamma
  have hr : 0 < r := by
    exact fixedJohnTransportNormalizedExponent_pos
      htailEta hsourceEta hgamma
  have ha : 0 < a := by dsimp only [a, r]; linarith
  have hd0 : d ≠ 0 := by
    dsimp only [d]
    exact ENNReal.coe_ne_zero.mpr hD.delta_pos.ne'
  have hdTop : d ≠ ∞ := by
    dsimp only [d]
    exact ENNReal.coe_ne_top
  have hrho0 : rho ≠ 0 := by
    dsimp only [rho]
    exact ENNReal.coe_ne_zero.mpr (admissibleNormalizedRadiusPos hD).ne'
  have hrhoTop : rho ≠ ∞ := by
    dsimp only [rho]
    exact ENNReal.coe_ne_top
  have hdeltaEight : delta <= (1 / 8 : NNReal) :=
    hsmall.trans (min_le_left _ _)
  have hquadNN : delta ^ 2 <= delta / 8 := by
    calc
      delta ^ 2 = delta * delta := by ring
      _ <= delta * (1 / 8 : NNReal) := by gcongr
      _ = delta / 8 := by ring
  have hquad : d ^ 2 <= rho := by
    dsimp only [d, rho]
    exact_mod_cast hquadNN
  have hquadPow : (d ^ 2) ^ r <= rho ^ r :=
    ENNReal.rpow_le_rpow hquad hr.le
  have hrhoNeg : rho ^ (-r) <= d ^ (-2 * r) := by
    calc
      rho ^ (-r) = (rho ^ r)⁻¹ := ENNReal.rpow_neg rho r
      _ <= ((d ^ 2) ^ r)⁻¹ := ENNReal.inv_le_inv' hquadPow
      _ = (d ^ 2) ^ (-r) := (ENNReal.rpow_neg (d ^ 2) r).symm
      _ = (d ^ (2 : Real)) ^ (-r) := by
        exact congrArg (fun x : ENNReal => x ^ (-r))
          (ENNReal.rpow_natCast d 2).symm
      _ = d ^ ((2 : Real) * (-r)) := by
        rw [← ENNReal.rpow_mul]
      _ = d ^ (-2 * r) := by
        congr 1
        ring
  have hK : K <= d ^ (-a) := by
    apply finiteConstant_le_delta_negativePower
      (fixedJohnTransportPowerConstant_ne_top
        tailEta sourceEpsilon gamma) ha hD.delta_pos
    simpa only [fixedJohnTransportScalarThreshold, K, a, r] using
      hsmall.trans (min_le_right _ _)
  have hnormalized :=
    fixedJohnFrostmanTransportScalar_le_normalizedPower
      (sourceEpsilon := sourceEpsilon)
      D hD hsourceEta htailEta hgamma hKT hC
  calc
    fixedJohnFrostmanTransportScalar
          (fixedJohnAutomaticGreedyLoss D hD : ENNReal)
          ((fixedJohnAutomaticDensityRepetitions D hD : ENNReal) *
            (1 / 4 : ENNReal)) sourceEpsilon gamma <=
        K * rho ^ (-r) := by
      simpa only [K, rho, r] using hnormalized
    _ <= d ^ (-a) * d ^ (-2 * r) :=
      mul_le_mul' hK hrhoNeg
    _ = d ^ ((-a) + (-2 * r)) := by
      rw [ENNReal.rpow_add _ _ hd0 hdTop]
    _ = d ^ (-kappa) := by
      congr 1
      dsimp only [a]
      ring

/-! The exact identity `(delta / 8)^(-r) = 8^r * delta^(-r)` avoids the
quadratic scale comparison used above.  The resulting sharp successor only
spends `r`, rather than `2 * r`, units of the exponent budget. -/

def fixedJohnTransportSharpPowerConstant
    (tailEta sourceEta sourceEpsilon gamma : Real) : ENNReal :=
  fixedJohnTransportPowerConstant tailEta sourceEpsilon gamma *
    (8 : ENNReal) ^
      fixedJohnTransportNormalizedExponent tailEta sourceEta gamma

def fixedJohnTransportSharpScalarThreshold
    (tailEta sourceEta sourceEpsilon gamma kappa : Real) : NNReal :=
  finiteConstantSmallDeltaThreshold
    (fixedJohnTransportSharpPowerConstant
      tailEta sourceEta sourceEpsilon gamma)
    (kappa - fixedJohnTransportNormalizedExponent
      tailEta sourceEta gamma)

theorem fixedJohnTransportSharpScalarThreshold_pos
    (tailEta sourceEta sourceEpsilon gamma kappa : Real) :
    0 < fixedJohnTransportSharpScalarThreshold
      tailEta sourceEta sourceEpsilon gamma kappa := by
  exact finiteConstantSmallDeltaThreshold_pos _ _

theorem fixedJohnTransportSharpPowerConstant_ne_top
    (tailEta sourceEta sourceEpsilon gamma : Real) :
    fixedJohnTransportSharpPowerConstant
      tailEta sourceEta sourceEpsilon gamma ≠ ∞ := by
  unfold fixedJohnTransportSharpPowerConstant
  apply ENNReal.mul_ne_top
  · exact fixedJohnTransportPowerConstant_ne_top
      tailEta sourceEpsilon gamma
  · exact ENNReal.rpow_ne_top_of_ne_zero (by norm_num) (by norm_num)

theorem fixedJohnFrostmanTransportScalar_le_deltaPower_sharp
    {sourceEpsilon gamma sourceEta tailEta kappa : Real}
    {delta : NNReal} {iota : Type}
    [Fintype iota] [Nonempty iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible)
    {C : ENNReal}
    (hsourceEta : 0 <= sourceEta) (htailEta : 0 < tailEta)
    (hgamma : gamma <= 2)
    (hgap : fixedJohnTransportNormalizedExponent
        tailEta sourceEta gamma < kappa)
    (hKT : IsKatzTao C D.family.bodyFamily)
    (hC : C <= (delta : ENNReal) ^ (-sourceEta))
    (hsmall : delta <= fixedJohnTransportSharpScalarThreshold
      tailEta sourceEta sourceEpsilon gamma kappa) :
    fixedJohnFrostmanTransportScalar
        (fixedJohnAutomaticGreedyLoss D hD : ENNReal)
        ((fixedJohnAutomaticDensityRepetitions D hD : ENNReal) *
          (1 / 4 : ENNReal)) sourceEpsilon gamma <=
      (delta : ENNReal) ^ (-kappa) := by
  let d : ENNReal := (delta : ENNReal)
  let rho : ENNReal := ((delta / 8 : NNReal) : ENNReal)
  let r : Real := fixedJohnTransportNormalizedExponent
    tailEta sourceEta gamma
  let a : Real := kappa - r
  let K0 : ENNReal :=
    fixedJohnTransportPowerConstant tailEta sourceEpsilon gamma
  let K : ENNReal :=
    fixedJohnTransportSharpPowerConstant
      tailEta sourceEta sourceEpsilon gamma
  have hr : 0 < r := by
    exact fixedJohnTransportNormalizedExponent_pos
      htailEta hsourceEta hgamma
  have ha : 0 < a := by dsimp only [a, r]; linarith
  have hd0 : d ≠ 0 := by
    dsimp only [d]
    exact ENNReal.coe_ne_zero.mpr hD.delta_pos.ne'
  have hdTop : d ≠ ∞ := by
    dsimp only [d]
    exact ENNReal.coe_ne_top
  have hscale : rho ^ (-r) =
      (8 : ENNReal) ^ r * d ^ (-r) := by
    dsimp only [rho, d]
    rw [ENNReal.coe_div (by norm_num)]
    norm_num only [ENNReal.coe_ofNat]
    rw [ENNReal.rpow_neg, ENNReal.rpow_neg]
    rw [ENNReal.div_rpow_of_nonneg _ _ hr.le]
    rw [ENNReal.inv_div
      (Or.inl (ENNReal.rpow_ne_top_of_ne_zero
        (by norm_num) (by norm_num)))
      (Or.inl (by simp [ENNReal.rpow_eq_zero_iff]))]
    rw [ENNReal.div_eq_inv_mul]
    ac_rfl
  have hK : K <= d ^ (-a) := by
    apply finiteConstant_le_delta_negativePower
      (fixedJohnTransportSharpPowerConstant_ne_top
        tailEta sourceEta sourceEpsilon gamma) ha hD.delta_pos
    simpa only [fixedJohnTransportSharpScalarThreshold, K, a, r] using
      hsmall
  have hnormalized :=
    fixedJohnFrostmanTransportScalar_le_normalizedPower
      (sourceEpsilon := sourceEpsilon)
      D hD hsourceEta htailEta hgamma hKT hC
  calc
    fixedJohnFrostmanTransportScalar
          (fixedJohnAutomaticGreedyLoss D hD : ENNReal)
          ((fixedJohnAutomaticDensityRepetitions D hD : ENNReal) *
            (1 / 4 : ENNReal)) sourceEpsilon gamma <=
        K0 * rho ^ (-r) := by
      simpa only [K0, rho, r] using hnormalized
    _ = K * d ^ (-r) := by
      rw [hscale]
      dsimp only [K, K0, r, fixedJohnTransportSharpPowerConstant]
      ac_rfl
    _ <= d ^ (-a) * d ^ (-r) :=
      mul_le_mul' hK le_rfl
    _ = d ^ ((-a) + (-r)) := by
      rw [ENNReal.rpow_add _ _ hd0 hdTop]
    _ = d ^ (-kappa) := by
      congr 1
      dsimp only [a]
      ring

#print axioms fixedJohnTransportSharpScalarThreshold_pos
#print axioms fixedJohnTransportSharpPowerConstant_ne_top
#print axioms fixedJohnFrostmanTransportScalar_le_deltaPower_sharp

#print axioms fixedJohnTransportScalarThreshold_pos
#print axioms fixedJohnTransportNormalizedExponent_pos
#print axioms fixedJohnTransportPowerConstant_ne_top
#print axioms fixedJohnFrostmanTransportScalar_le_normalizedPower
#print axioms fixedJohnFrostmanTransportScalar_le_deltaPower

end
end Family8FixedJohnTransportScalarPowerCapV1
