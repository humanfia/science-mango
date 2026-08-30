import ArchonPhysics.CanonicalIIDCoerciveIteratedA2PairedNumeratorHaarBridge

/-!
Consumer for the finite paired-numerator, quotient, Haar-fiber, and actual
iterated-A2 obstruction bridge.
-/

namespace ArchonPhysicsConsumers.Thermalization

open scoped BigOperators

open ArchonPhysics
open ArchonPhysics.CanonicalIIDCoerciveCorrectedStructuralRankRPAAdapter
open ArchonPhysics.CanonicalIIDCoerciveIteratedA2PairedNumeratorHaarBridge
open ArchonPhysics.CanonicalIIDCoerciveIteratedA2TwistRenormalizedRemainder
open ArchonPhysics.CanonicalIIDCoerciveRegularGoodCutoffExponentBalance
open ArchonPhysics.FiniteHaarChargeFiberConcentration
open ArchonPhysics.FiniteSecondOrderCharacterFamilyExpansion
open ArchonPhysics.FreeFPUTChargeFiberAggregation
open ArchonPhysics.FreeFPUTTadpoleFeedbackCancellation
open ArchonPhysics.PhyslibFPUTIteratedQuadraticSecondPicardCharacterFamily

noncomputable section

local instance iteratedA2TermDecidableEq (N : Nat) :
    DecidableEq (IteratedQuadraticSecondPicardCharacterTerm N) :=
  Classical.decEq _

example {H : Type*} [DecidableEq H]
    (histories : Finset H) (partner : H ≃ H)
    (hmem : ∀ h, h ∈ histories ↔ partner h ∈ histories)
    (f : H → Complex) (cost : H → Real) (scale : Real)
    (hcost : ∀ h ∈ histories, 0 ≤ cost h) (hscale : 0 ≤ scale)
    (hpair : ∀ h ∈ histories,
      ‖f h + f (partner h)‖ ≤ cost h * scale) :
    ‖∑ h ∈ histories, f h‖ ≤
      (∑ h ∈ histories, cost h) * scale :=
  norm_finset_sum_le_cost_mul_scale_of_pairing_exact
    histories partner hmem f cost scale hcost hscale hpair

example {H : Type*} [DecidableEq H]
    {histories : Finset H} {numerator denominator : H → Complex}
    {gamma : Real}
    (certificate : FinitePairedQuotientNumeratorCertificate
      histories numerator denominator gamma) :
    ‖∑ h ∈ histories, numerator h‖ ≤
      (∑ h ∈ histories, certificate.cost h) * gamma :=
  certificate.norm_sum_numerator_le_cost_mul_gamma

example {H : Type*} [DecidableEq H]
    {histories : Finset H} {numerator denominator : H → Complex}
    {gamma : Real}
    (certificate : FinitePairedQuotientNumeratorCertificate
      histories numerator denominator gamma) :
    ‖∑ h ∈ histories, numerator h / denominator h‖ ≤
      (∑ h ∈ histories, certificate.cost h) / gamma :=
  certificate.norm_sum_quotient_le_cost_div_gamma

example {d J : Type*} [Fintype d] [Fintype J] [DecidableEq J]
    (numerator denominator : J → Complex) (charge : J → d → Int)
    (gamma : Real)
    (certificate : ∀ q : d → Int,
      FinitePairedQuotientNumeratorCertificate
        (chargeFiber charge q) numerator denominator gamma) :
    sameChargeFamilySquare
        (fun j => numerator j / denominator j) charge ≤
      ∑ q ∈ realizedCharges charge,
        (pairedChargeFiberCost charge certificate q / gamma) ^ 2 :=
  sameChargeFamilySquare_quotient_le_pairedFiberCosts
    numerator denominator charge gamma certificate

example {N : Nat} [NeZero N]
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
        physicalIteratedA2TwistDenominator m term :=
  phaseRenormalizedPhysicalIteratedA2Coefficient_eq_weightedNumerator_div
    m kappa radius observed time term hinner hinnerFlip

example {N : Nat} [NeZero N]
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
            iteratedQuadraticSecondPicardCharge certificate q / gamma) ^ 2 :=
  completeA2IteratedIteratedRemainder_le_quarter_pairedFiberCosts
    m kappa radius observed time gamma certificate

example :
    CutoffExponentAdmissible 4 2 quadraticKineticDeficit
      correctedSecondPicardG4CutoffExponent :=
  pairedNumeratorHaarBridge_lossTwo_cutoff_admissible

example {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa : Real)
    (radius : Lattice.Site N → Real) (observed : Lattice.Site N)
    (time : Real) (term : IteratedQuadraticSecondPicardCharacterTerm N) :
    physicalIteratedA2WeightedTwistNumerator
        m kappa radius observed time
        (flipIteratedQuadraticInnerBranch term) =
      physicalIteratedA2WeightedTwistNumerator
        m kappa radius observed time term :=
  physicalIteratedA2WeightedTwistNumerator_flip_eq
    m kappa radius observed time term

example {N : Nat} [NeZero N] :
    (∀ term : IteratedQuadraticSecondPicardCharacterTerm N,
      iteratedA2InnerFlipEquiv (iteratedA2InnerFlipEquiv term) = term) ∧
    (∀ term : IteratedQuadraticSecondPicardCharacterTerm N,
      iteratedA2InnerFlipEquiv term ≠ term) ∧
    (∀ term : IteratedQuadraticSecondPicardCharacterTerm N,
      iteratedQuadraticSecondPicardCharge (iteratedA2InnerFlipEquiv term) =
        iteratedQuadraticSecondPicardCharge term) :=
  actualInnerFlip_partner_audit

end

end ArchonPhysicsConsumers.Thermalization
