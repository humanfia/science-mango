import ArchonPhysics.CanonicalIIDCoerciveIteratedA2TwistDifferenceOscillatoryBound
import ArchonPhysics.FiniteSecondOrderChargeFiberExpansion
import ArchonPhysics.FiniteHaarChargeFiberConcentration

/-!
# Finite paired-numerator bridge for the iterated-A2 Haar remainder

The twist-difference estimate isolates one quantitative input:

`norm cancellationNumerator <= C * gamma`.

This module turns a finite history pairing into precisely such an aggregate
bound, then carries it through the two inner denominators and the coherent
Haar charge fibers.  A certificate supplies an invariant finite history
set, a fixed-point-free involutive partner, a main/residual decomposition,
exact cancellation of paired main numerators, an `O(gamma)` paired residual,
and a partner-invariant denominator of norm at least `gamma^2`.

The resulting coherent quotient sum is `O(1 / gamma)`.  Applying the
certificate separately on every Haar charge fiber gives an explicit
loss-two bound for the complete physical iterated/iterated remainder, hence
the existing `alpha = 5/4` cutoff is available.

The final audit is important: the actual inner-branch flip is already a
charge-preserving fixed-point-free involution, and its denominator product
is invariant.  However, the raw cancellation numerator is odd while the
physical static coefficient is also odd.  Their product is therefore even,
not cancelling.  Thus the available flip is not the missing partner for the
weighted numerator except on its zero locus.  No additional actual partner
or residual estimate is asserted.
-/

namespace ArchonPhysics.CanonicalIIDCoerciveIteratedA2PairedNumeratorHaarBridge

open scoped BigOperators

open ArchonPhysics
open ArchonPhysics.CanonicalIIDCoerciveCorrectedStructuralRankRPAAdapter
open ArchonPhysics.CanonicalIIDCoerciveIteratedA2TwistDifferenceOscillatoryBound
open ArchonPhysics.CanonicalIIDCoerciveIteratedA2TwistRenormalizedRemainder
open ArchonPhysics.CanonicalIIDCoerciveRegularGoodCutoffExponentBalance
open ArchonPhysics.FiniteHaarChargeFiberConcentration
open ArchonPhysics.FiniteSecondOrderChargeFiberExpansion
open ArchonPhysics.FiniteSecondOrderCharacterFamilyExpansion
open ArchonPhysics.FreeFPUTTadpoleFeedbackCancellation
open ArchonPhysics.FreeFPUTChargeFiberAggregation
open ArchonPhysics.NestedOscillatoryIntegral
open ArchonPhysics.PhyslibFPUTIteratedQuadraticSecondPicardCharacterFamily

noncomputable section

local instance iteratedA2TermDecidableEq (N : Nat) :
    DecidableEq (IteratedQuadraticSecondPicardCharacterTerm N) :=
  Classical.decEq _

/-! ## A model-independent finite pairing estimate -/

/-- If a finite set is invariant under a partner permutation and every
oriented pair sum is bounded by `2 * cost * scale`, then the full sum is
bounded by `(sum cost) * scale`.  The factor two disappears because every
unoriented pair occurs in both orientations. -/
theorem norm_finset_sum_le_cost_mul_scale_of_pairing
    {H : Type*} [DecidableEq H]
    (histories : Finset H) (partner : H ≃ H)
    (hmem : ∀ h, h ∈ histories ↔ partner h ∈ histories)
    (f : H → Complex) (cost : H → Real) (scale : Real)
    (hpair : ∀ h ∈ histories,
      ‖f h + f (partner h)‖ ≤ 2 * cost h * scale) :
    ‖∑ h ∈ histories, f h‖ ≤
      (∑ h ∈ histories, cost h) * scale := by
  have hreindex :
      (∑ h ∈ histories, f (partner h)) =
        ∑ h ∈ histories, f h := by
    exact Finset.sum_equiv partner hmem (fun h hh => rfl)
  have hhalf :
      (∑ h ∈ histories, f h) =
        (1 / 2 : Complex) *
          ∑ h ∈ histories, (f h + f (partner h)) := by
    rw [Finset.sum_add_distrib, hreindex]
    ring
  rw [hhalf, norm_mul]
  have hnormHalf : ‖(1 / 2 : Complex)‖ = (1 / 2 : Real) := by
    norm_num
  rw [hnormHalf]
  calc
    (1 / 2 : Real) *
        ‖∑ h ∈ histories, (f h + f (partner h))‖ ≤
      (1 / 2 : Real) *
        ∑ h ∈ histories, ‖f h + f (partner h)‖ := by
      gcongr
      exact norm_sum_le _ _
    _ ≤ (1 / 2 : Real) *
        ∑ h ∈ histories, (2 * cost h * scale) := by
      exact mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum (fun h hh => hpair h hh)) (by norm_num)
    _ = (∑ h ∈ histories, cost h) * scale := by
      simp_rw [show 2 * cost _ * scale = 2 * (cost _ * scale) by ring]
      rw [← Finset.mul_sum, ← Finset.sum_mul]
      ring

/-- Exact user-facing normalization: if every oriented pair is bounded by
`cost h * scale`, then the aggregate is bounded by `(sum cost) * scale`.
The estimate is stated without absorbing a factor two into `cost`. -/
theorem norm_finset_sum_le_cost_mul_scale_of_pairing_exact
    {H : Type*} [DecidableEq H]
    (histories : Finset H) (partner : H ≃ H)
    (hmem : ∀ h, h ∈ histories ↔ partner h ∈ histories)
    (f : H → Complex) (cost : H → Real) (scale : Real)
    (hcost : ∀ h ∈ histories, 0 ≤ cost h) (hscale : 0 ≤ scale)
    (hpair : ∀ h ∈ histories,
      ‖f h + f (partner h)‖ ≤ cost h * scale) :
    ‖∑ h ∈ histories, f h‖ ≤
      (∑ h ∈ histories, cost h) * scale := by
  apply norm_finset_sum_le_cost_mul_scale_of_pairing
    histories partner hmem f cost scale
  intro h hh
  calc
    ‖f h + f (partner h)‖ ≤ cost h * scale := hpair h hh
    _ ≤ 2 * cost h * scale := by
      nlinarith [mul_nonneg (hcost h hh) hscale]

/-! ## Paired main/residual numerator certificate -/

/-- Complete finite certificate for passing from paired numerator
cancellation to a one-gap coherent quotient estimate. -/
structure FinitePairedQuotientNumeratorCertificate
    {H : Type*} [DecidableEq H]
    (histories : Finset H)
    (numerator denominator : H → Complex) (gamma : Real) where
  partner : H ≃ H
  partner_involutive : ∀ h, partner (partner h) = h
  partner_mem_iff : ∀ h, h ∈ histories ↔ partner h ∈ histories
  partner_ne : ∀ h ∈ histories, partner h ≠ h
  mainNumerator : H → Complex
  residualNumerator : H → Complex
  cost : H → Real
  gamma_pos : 0 < gamma
  cost_nonneg : ∀ h ∈ histories, 0 ≤ cost h
  numerator_eq : ∀ h ∈ histories,
    numerator h = mainNumerator h + residualNumerator h
  main_pair_cancel : ∀ h ∈ histories,
    mainNumerator h + mainNumerator (partner h) = 0
  residual_pair_bound : ∀ h ∈ histories,
    ‖residualNumerator h + residualNumerator (partner h)‖ ≤
      cost h * gamma
  denominator_partner : ∀ h ∈ histories,
    denominator (partner h) = denominator h
  denominator_gap : ∀ h ∈ histories,
    gamma ^ 2 ≤ ‖denominator h‖

namespace FinitePairedQuotientNumeratorCertificate

variable {H : Type*} [DecidableEq H]
variable {histories : Finset H}
variable {numerator denominator : H → Complex} {gamma : Real}

/-- The paired main numerator sums to zero exactly. -/
theorem sum_mainNumerator_eq_zero
    (certificate : FinitePairedQuotientNumeratorCertificate
      histories numerator denominator gamma) :
    (∑ h ∈ histories, certificate.mainNumerator h) = 0 := by
  apply Finset.sum_involution
    (fun h _hh => certificate.partner h)
  · intro h hh
    exact certificate.main_pair_cancel h hh
  · intro h hh _hmain
    exact certificate.partner_ne h hh
  · intro h hh
    exact (certificate.partner_mem_iff h).mp hh
  · intro h hh
    exact certificate.partner_involutive h

/-- Exact reduction of the aggregate numerator to its paired residual. -/
theorem sum_numerator_eq_sum_residual
    (certificate : FinitePairedQuotientNumeratorCertificate
      histories numerator denominator gamma) :
    (∑ h ∈ histories, numerator h) =
      ∑ h ∈ histories, certificate.residualNumerator h := by
  calc
    (∑ h ∈ histories, numerator h) =
      ∑ h ∈ histories,
        (certificate.mainNumerator h + certificate.residualNumerator h) := by
          apply Finset.sum_congr rfl
          intro h hh
          exact certificate.numerator_eq h hh
    _ = (∑ h ∈ histories, certificate.mainNumerator h) +
        ∑ h ∈ histories, certificate.residualNumerator h := by
          rw [Finset.sum_add_distrib]
    _ = ∑ h ∈ histories, certificate.residualNumerator h := by
      rw [certificate.sum_mainNumerator_eq_zero, zero_add]

/-- Paired `O(gamma)` residuals give the requested aggregate numerator
bound. -/
theorem norm_sum_numerator_le_cost_mul_gamma
    (certificate : FinitePairedQuotientNumeratorCertificate
      histories numerator denominator gamma) :
    ‖∑ h ∈ histories, numerator h‖ ≤
      (∑ h ∈ histories, certificate.cost h) * gamma := by
  rw [certificate.sum_numerator_eq_sum_residual]
  exact norm_finset_sum_le_cost_mul_scale_of_pairing_exact
    histories certificate.partner certificate.partner_mem_iff
    certificate.residualNumerator certificate.cost gamma
    certificate.cost_nonneg (le_of_lt certificate.gamma_pos)
    certificate.residual_pair_bound

/-- The normalized paired main terms still cancel because the denominator
is partner-invariant. -/
theorem mainQuotient_pair_cancel
    (certificate : FinitePairedQuotientNumeratorCertificate
      histories numerator denominator gamma)
    (h : H) (hh : h ∈ histories) :
    certificate.mainNumerator h / denominator h +
        certificate.mainNumerator (certificate.partner h) /
          denominator (certificate.partner h) = 0 := by
  rw [certificate.denominator_partner h hh]
  rw [← add_div, certificate.main_pair_cancel h hh, zero_div]

/-- Dividing an `O(gamma)` pair residual by a partner-invariant denominator
of size at least `gamma^2` gives an `O(1/gamma)` pair residual. -/
theorem residualQuotient_pair_bound
    (certificate : FinitePairedQuotientNumeratorCertificate
      histories numerator denominator gamma)
    (h : H) (hh : h ∈ histories) :
    ‖certificate.residualNumerator h / denominator h +
        certificate.residualNumerator (certificate.partner h) /
          denominator (certificate.partner h)‖ ≤
      certificate.cost h * (1 / gamma) := by
  rw [certificate.denominator_partner h hh, ← add_div, norm_div]
  have hnumerator0 :
      0 ≤ certificate.cost h * gamma :=
    mul_nonneg (certificate.cost_nonneg h hh)
      (le_of_lt certificate.gamma_pos)
  calc
    ‖certificate.residualNumerator h +
          certificate.residualNumerator (certificate.partner h)‖ /
        ‖denominator h‖ ≤
      (certificate.cost h * gamma) / (gamma ^ 2) :=
        div_le_div₀ hnumerator0
          (certificate.residual_pair_bound h hh)
          (sq_pos_of_pos certificate.gamma_pos)
          (certificate.denominator_gap h hh)
    _ = certificate.cost h * (1 / gamma) := by
      field_simp [ne_of_gt certificate.gamma_pos]

/-- Exact reduction of the quotient aggregate to the normalized paired
residual. -/
theorem sum_quotient_eq_sum_residualQuotient
    (certificate : FinitePairedQuotientNumeratorCertificate
      histories numerator denominator gamma) :
    (∑ h ∈ histories, numerator h / denominator h) =
      ∑ h ∈ histories,
        certificate.residualNumerator h / denominator h := by
  have hmain :
      (∑ h ∈ histories,
          certificate.mainNumerator h / denominator h) = 0 := by
    apply Finset.sum_involution
      (fun h _hh => certificate.partner h)
    · intro h hh
      exact certificate.mainQuotient_pair_cancel h hh
    · intro h hh _hmain
      exact certificate.partner_ne h hh
    · intro h hh
      exact (certificate.partner_mem_iff h).mp hh
    · intro h hh
      exact certificate.partner_involutive h
  calc
    (∑ h ∈ histories, numerator h / denominator h) =
      ∑ h ∈ histories,
        (certificate.mainNumerator h / denominator h +
          certificate.residualNumerator h / denominator h) := by
            apply Finset.sum_congr rfl
            intro h hh
            rw [certificate.numerator_eq h hh, add_div]
    _ = (∑ h ∈ histories,
          certificate.mainNumerator h / denominator h) +
        ∑ h ∈ histories,
          certificate.residualNumerator h / denominator h := by
            rw [Finset.sum_add_distrib]
    _ = ∑ h ∈ histories,
          certificate.residualNumerator h / denominator h := by
            rw [hmain, zero_add]

/-- Main theorem: finite paired numerator cancellation and a two-gap
denominator produce a coherent one-gap quotient bound. -/
theorem norm_sum_quotient_le_cost_div_gamma
    (certificate : FinitePairedQuotientNumeratorCertificate
      histories numerator denominator gamma) :
    ‖∑ h ∈ histories, numerator h / denominator h‖ ≤
      (∑ h ∈ histories, certificate.cost h) / gamma := by
  rw [certificate.sum_quotient_eq_sum_residualQuotient]
  have hraw := norm_finset_sum_le_cost_mul_scale_of_pairing_exact
    histories certificate.partner certificate.partner_mem_iff
    (fun h => certificate.residualNumerator h / denominator h)
    certificate.cost (1 / gamma)
    certificate.cost_nonneg
    (one_div_nonneg.mpr (le_of_lt certificate.gamma_pos))
    certificate.residualQuotient_pair_bound
  simpa [div_eq_mul_inv] using hraw

end FinitePairedQuotientNumeratorCertificate

/-! ## Coherent Haar charge-fiber aggregation -/

/-- Total pairing cost in one charge fiber. -/
def pairedChargeFiberCost
    {d J : Type*} [Fintype d] [Fintype J] [DecidableEq J]
    {numerator denominator : J → Complex} {gamma : Real}
    (charge : J → d → Int)
    (certificate : ∀ q : d → Int,
      FinitePairedQuotientNumeratorCertificate
        (chargeFiber charge q) numerator denominator gamma)
    (q : d → Int) : Real :=
  ∑ j ∈ chargeFiber charge q, (certificate q).cost j

/-- Applying a paired certificate on every charge fiber bounds the complete
coherent Haar square by the squared one-gap fiber costs. -/
theorem sameChargeFamilySquare_quotient_le_pairedFiberCosts
    {d J : Type*} [Fintype d] [Fintype J] [DecidableEq J]
    (numerator denominator : J → Complex) (charge : J → d → Int)
    (gamma : Real)
    (certificate : ∀ q : d → Int,
      FinitePairedQuotientNumeratorCertificate
        (chargeFiber charge q) numerator denominator gamma) :
    sameChargeFamilySquare
        (fun j => numerator j / denominator j) charge ≤
      ∑ q ∈ realizedCharges charge,
        (pairedChargeFiberCost charge certificate q / gamma) ^ 2 := by
  rw [sameChargeFamilySquare_eq_chargeFiberNormSqSum]
  unfold sameChargeFiberNormSqSum
  apply Finset.sum_le_sum
  intro q hq
  rw [Complex.normSq_eq_norm_sq,
    coherentFiberCoefficient_eq_sum_chargeFiber]
  exact pow_le_pow_left₀ (norm_nonneg _)
    ((certificate q).norm_sum_quotient_le_cost_div_gamma) 2

/-! ## Actual physical numerator, denominator, and coefficient identity -/

/-- Actual common-denominator cancellation numerator of one physical twist
orbit. -/
def physicalIteratedA2TwistCancellationNumerator
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (observed : Lattice.Site N)
    (time : Real)
    (term : IteratedQuadraticSecondPicardCharacterTerm N) : Complex :=
  nestedTwistCancellationNumerator
    (iteratedQuadraticOuterMismatch m observed term)
    (iteratedQuadraticInnerMismatch m term)
    (iteratedQuadraticOuterMismatch m observed
      (flipIteratedQuadraticInnerBranch term))
    (iteratedQuadraticInnerMismatch m
      (flipIteratedQuadraticInnerBranch term)) time

/-- Product of the two inner mismatch denominators. -/
def physicalIteratedA2TwistDenominator
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N) : Complex :=
  (Complex.I * iteratedQuadraticInnerMismatch m term) *
    (Complex.I * iteratedQuadraticInnerMismatch m
      (flipIteratedQuadraticInnerBranch term))

/-- Numerator after including the actual static tree coefficient. -/
def physicalIteratedA2WeightedTwistNumerator
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa : Real)
    (radius : Lattice.Site N → Real) (observed : Lattice.Site N)
    (time : Real)
    (term : IteratedQuadraticSecondPicardCharacterTerm N) : Complex :=
  iteratedQuadraticSecondPicardStaticCoefficient
      m kappa radius observed term *
    physicalIteratedA2TwistCancellationNumerator m observed time term

/-- Away from the two inner resonances, the phase-renormalized physical
coefficient is exactly weighted numerator divided by the two-gap
denominator. -/
theorem phaseRenormalizedPhysicalIteratedA2Coefficient_eq_weightedNumerator_div
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa : Real)
    (radius : Lattice.Site N → Real) (observed : Lattice.Site N)
    (time : Real) (term : IteratedQuadraticSecondPicardCharacterTerm N)
    (hinner : iteratedQuadraticInnerMismatch m term ≠ 0)
    (hinnerFlip : iteratedQuadraticInnerMismatch m
      (flipIteratedQuadraticInnerBranch term) ≠ 0) :
    phaseRenormalizedPhysicalIteratedA2Coefficient
        m kappa radius observed time term =
      physicalIteratedA2WeightedTwistNumerator
          m kappa radius observed time term /
        physicalIteratedA2TwistDenominator m term := by
  rw [phaseRenormalizedPhysicalIteratedA2Coefficient_eq_nestedDifference]
  change
    iteratedQuadraticSecondPicardStaticCoefficient
        m kappa radius observed term *
      nestedTwistDifference
        (iteratedQuadraticOuterMismatch m observed term)
        (iteratedQuadraticInnerMismatch m term)
        (iteratedQuadraticOuterMismatch m observed
          (flipIteratedQuadraticInnerBranch term))
        (iteratedQuadraticInnerMismatch m
          (flipIteratedQuadraticInnerBranch term)) time =
      physicalIteratedA2WeightedTwistNumerator
          m kappa radius observed time term /
        physicalIteratedA2TwistDenominator m term
  rw [nestedTwistDifference_eq_numerator_div hinner hinnerFlip
    (physicalIteratedA2_totalMismatch_flip_eq m observed term)]
  unfold physicalIteratedA2WeightedTwistNumerator
    physicalIteratedA2TwistCancellationNumerator
    physicalIteratedA2TwistDenominator
  ring

/-! ## Charge-fiber certificate to the actual loss-two remainder -/

/-- The denominator-gap field of the charge-fiber certificate already
forces both inner mismatches to be nonzero; no separate nonresonance premise
is needed. -/
theorem physicalIteratedA2_innerMismatches_ne_zero_of_pairedFiberCertificate
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa : Real)
    (radius : Lattice.Site N → Real) (observed : Lattice.Site N)
    (time gamma : Real)
    (certificate : ∀ q : Lattice.Site N → Int,
      FinitePairedQuotientNumeratorCertificate
        (chargeFiber iteratedQuadraticSecondPicardCharge q)
        (physicalIteratedA2WeightedTwistNumerator
          m kappa radius observed time)
        (physicalIteratedA2TwistDenominator m) gamma)
    (term : IteratedQuadraticSecondPicardCharacterTerm N) :
    iteratedQuadraticInnerMismatch m term ≠ 0 ∧
      iteratedQuadraticInnerMismatch m
        (flipIteratedQuadraticInnerBranch term) ≠ 0 := by
  have hmem : term ∈ chargeFiber iteratedQuadraticSecondPicardCharge
      (iteratedQuadraticSecondPicardCharge term) := by
    simp [chargeFiber]
  have hnormPos :
      0 < ‖physicalIteratedA2TwistDenominator m term‖ :=
    (sq_pos_of_pos
      (certificate (iteratedQuadraticSecondPicardCharge term)).gamma_pos).trans_le
        ((certificate
          (iteratedQuadraticSecondPicardCharge term)).denominator_gap term hmem)
  have hdenom : physicalIteratedA2TwistDenominator m term ≠ 0 :=
    norm_pos_iff.mp hnormPos
  unfold physicalIteratedA2TwistDenominator at hdenom
  have hfactors := mul_ne_zero_iff.mp hdenom
  constructor
  · exact Complex.ofReal_ne_zero.mp (mul_ne_zero_iff.mp hfactors.1).2
  · exact Complex.ofReal_ne_zero.mp (mul_ne_zero_iff.mp hfactors.2).2

/-- If every actual charge fiber carries the explicit finite pairing
certificate, the complete phase-renormalized Haar square has the advertised
loss-two bound. -/
theorem sameChargeFamilySquare_phaseRenormalized_le_pairedFiberCosts
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa : Real)
    (radius : Lattice.Site N → Real) (observed : Lattice.Site N)
    (time gamma : Real)
    (certificate : ∀ q : Lattice.Site N → Int,
      FinitePairedQuotientNumeratorCertificate
        (chargeFiber iteratedQuadraticSecondPicardCharge q)
        (physicalIteratedA2WeightedTwistNumerator
          m kappa radius observed time)
        (physicalIteratedA2TwistDenominator m) gamma) :
    sameChargeFamilySquare
        (phaseRenormalizedPhysicalIteratedA2Coefficient
          m kappa radius observed time)
        iteratedQuadraticSecondPicardCharge ≤
      ∑ q ∈ realizedCharges iteratedQuadraticSecondPicardCharge,
        (pairedChargeFiberCost
          iteratedQuadraticSecondPicardCharge certificate q / gamma) ^ 2 := by
  have hcoefficient :
      phaseRenormalizedPhysicalIteratedA2Coefficient
          m kappa radius observed time =
        fun term =>
          physicalIteratedA2WeightedTwistNumerator
              m kappa radius observed time term /
            physicalIteratedA2TwistDenominator m term := by
    funext term
    have hnonzero :=
      physicalIteratedA2_innerMismatches_ne_zero_of_pairedFiberCertificate
        m kappa radius observed time gamma certificate term
    exact phaseRenormalizedPhysicalIteratedA2Coefficient_eq_weightedNumerator_div
      m kappa radius observed time term hnonzero.1 hnonzero.2
  rw [hcoefficient]
  exact sameChargeFamilySquare_quotient_le_pairedFiberCosts
    _ _ _ gamma certificate

/-- Corresponding complete actual iterated/iterated remainder bound. -/
theorem completeA2IteratedIteratedRemainder_le_quarter_pairedFiberCosts
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa : Real)
    (radius : Lattice.Site N → Real) (observed : Lattice.Site N)
    (time gamma : Real)
    (certificate : ∀ q : Lattice.Site N → Int,
      FinitePairedQuotientNumeratorCertificate
        (chargeFiber iteratedQuadraticSecondPicardCharge q)
        (physicalIteratedA2WeightedTwistNumerator
          m kappa radius observed time)
        (physicalIteratedA2TwistDenominator m) gamma) :
    completeA2IteratedIteratedRemainder
        m kappa radius observed time ≤
      (1 / 4 : Real) *
        ∑ q ∈ realizedCharges iteratedQuadraticSecondPicardCharge,
          (pairedChargeFiberCost
            iteratedQuadraticSecondPicardCharge certificate q / gamma) ^ 2 := by
  rw [completeA2IteratedIteratedRemainder_eq_quarter_phaseRenormalizedSquare]
  exact mul_le_mul_of_nonneg_left
    (sameChargeFamilySquare_phaseRenormalized_le_pairedFiberCosts
      m kappa radius observed time gamma certificate) (by norm_num)

/-- The preceding paired-fiber remainder is an effective loss-two object,
so the existing explicit `alpha = 5/4` cutoff is admissible. -/
theorem pairedNumeratorHaarBridge_lossTwo_cutoff_admissible :
    CutoffExponentAdmissible 4 2 quadraticKineticDeficit
      correctedSecondPicardG4CutoffExponent :=
  numeratorGain_lossTwo_cutoff_admissible

/-! ## Audit of the actual available inner flip -/

/-- Swapping the two local histories negates the common-denominator raw
numerator whenever their total mismatch agrees. -/
theorem nestedTwistCancellationNumerator_swap_eq_neg
    {outer inner outerTwist innerTwist time : Real}
    (htotal : outer + inner = outerTwist + innerTwist) :
    nestedTwistCancellationNumerator
        outerTwist innerTwist outer inner time =
      -nestedTwistCancellationNumerator
        outer inner outerTwist innerTwist time := by
  unfold nestedTwistCancellationNumerator
  rw [← htotal]
  ring

/-- The actual raw numerator is odd under the existing inner flip. -/
theorem physicalIteratedA2TwistCancellationNumerator_flip_eq_neg
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (observed : Lattice.Site N)
    (time : Real) (term : IteratedQuadraticSecondPicardCharacterTerm N) :
    physicalIteratedA2TwistCancellationNumerator m observed time
        (flipIteratedQuadraticInnerBranch term) =
      -physicalIteratedA2TwistCancellationNumerator
        m observed time term := by
  unfold physicalIteratedA2TwistCancellationNumerator
  simp only [flipIteratedQuadraticInnerBranch_involutive]
  exact nestedTwistCancellationNumerator_swap_eq_neg
    (physicalIteratedA2_totalMismatch_flip_eq m observed term)

/-- The two-gap denominator product is invariant under the existing flip. -/
theorem physicalIteratedA2TwistDenominator_flip_eq
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N) :
    physicalIteratedA2TwistDenominator m
        (flipIteratedQuadraticInnerBranch term) =
      physicalIteratedA2TwistDenominator m term := by
  unfold physicalIteratedA2TwistDenominator
  simp only [flipIteratedQuadraticInnerBranch_involutive]
  ring

/-- Because both the static factor and raw numerator are odd, the weighted
physical numerator is even under the only currently available full-history
involution. -/
theorem physicalIteratedA2WeightedTwistNumerator_flip_eq
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa : Real)
    (radius : Lattice.Site N → Real) (observed : Lattice.Site N)
    (time : Real) (term : IteratedQuadraticSecondPicardCharacterTerm N) :
    physicalIteratedA2WeightedTwistNumerator
        m kappa radius observed time
        (flipIteratedQuadraticInnerBranch term) =
      physicalIteratedA2WeightedTwistNumerator
        m kappa radius observed time term := by
  unfold physicalIteratedA2WeightedTwistNumerator
  rw [iteratedQuadraticSecondPicardStaticCoefficient_flip_eq_neg,
    physicalIteratedA2TwistCancellationNumerator_flip_eq_neg]
  ring

/-- Explicit obstruction: if the weighted numerator is nonzero, pairing a
term with the existing inner flip doubles it instead of cancelling it. -/
theorem physicalWeightedNumerator_pair_nonzero_of_nonzero
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa : Real)
    (radius : Lattice.Site N → Real) (observed : Lattice.Site N)
    (time : Real) (term : IteratedQuadraticSecondPicardCharacterTerm N)
    (hnonzero : physicalIteratedA2WeightedTwistNumerator
      m kappa radius observed time term ≠ 0) :
    physicalIteratedA2WeightedTwistNumerator
          m kappa radius observed time term +
        physicalIteratedA2WeightedTwistNumerator
          m kappa radius observed time
          (flipIteratedQuadraticInnerBranch term) ≠ 0 := by
  rw [physicalIteratedA2WeightedTwistNumerator_flip_eq]
  intro hsum
  apply hnonzero
  apply mul_left_cancel₀ (show (2 : Complex) ≠ 0 by norm_num)
  simpa only [two_mul, mul_zero] using hsum

/-- The repository does contain a fixed-point-free, charge-preserving
involutive partner on the full actual iterated history type. -/
theorem actualInnerFlip_partner_audit
    {N : Nat} [NeZero N] :
    (∀ term : IteratedQuadraticSecondPicardCharacterTerm N,
      iteratedA2InnerFlipEquiv (iteratedA2InnerFlipEquiv term) = term) ∧
    (∀ term : IteratedQuadraticSecondPicardCharacterTerm N,
      iteratedA2InnerFlipEquiv term ≠ term) ∧
    (∀ term : IteratedQuadraticSecondPicardCharacterTerm N,
      iteratedQuadraticSecondPicardCharge (iteratedA2InnerFlipEquiv term) =
        iteratedQuadraticSecondPicardCharge term) := by
  constructor
  · intro term
    exact flipIteratedQuadraticInnerBranch_involutive term
  constructor
  · intro term
    exact flipIteratedQuadraticInnerBranch_ne term
  · intro term
    exact iteratedQuadraticSecondPicardCharge_flipIteratedQuadraticInnerBranch
      term

end

end ArchonPhysics.CanonicalIIDCoerciveIteratedA2PairedNumeratorHaarBridge
