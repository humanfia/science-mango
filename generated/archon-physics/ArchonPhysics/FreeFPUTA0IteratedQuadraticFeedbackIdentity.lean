import ArchonPhysics.PhyslibFPUTCompleteSecondPicardCharacterFamily
import ArchonPhysics.NestedOscillatoryEnergyIdentity
import ArchonPhysics.FiniteSecondOrderCharacterFamilyExpansion

/-!
# Charge-matched A0/iterated-quadratic feedback identity

The singleton free initial character can interfere after Haar averaging only
with second-Picard terms carrying the same initial-phase charge.  On the
iterated-quadratic branch, equality of those charges forces the outer and
inner mismatches of the nested time integral to be exact negatives.  The
nested shuffle identity then turns the real return contribution into the
squared modulus of its one-step oscillatory integral.

The statements retain repeated modes, both ordered placements of the
first-Picard coordinate, and both conjugation branches.  The resulting
norm-square factor is an exact finite-time feedback identity; no assertion
that it already equals a complete macroscopic gain term is made.
-/

namespace ArchonPhysics.FreeFPUTA0IteratedQuadraticFeedbackIdentity

open UnitAddTorus
open ArchonPhysics
open ArchonPhysics.FiniteHaarOscillatorySecondMoment
open ArchonPhysics.FinitePhaseMonomials
open ArchonPhysics.FiniteSecondOrderCharacterFamilyExpansion
open ArchonPhysics.ForcedComplexModeDuhamel
open ArchonPhysics.FreeFPUTA0DirectCubicBridge
open ArchonPhysics.FreeFPUTDuhamelResonanceBridge
open ArchonPhysics.FreeFPUTMismatchPhaseExpansion
open ArchonPhysics.FreeFPUTTensorPhaseExpansion
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.ModeCoupling
open ArchonPhysics.NestedOscillatoryEnergyIdentity
open ArchonPhysics.NestedOscillatoryIntegral
open ArchonPhysics.NonresonantOscillatoryGain
open ArchonPhysics.PhyslibFPUTCompleteSecondPicardCharacterFamily
open ArchonPhysics.PhyslibFPUTFirstPicardCoordinateCharacterFamily
open ArchonPhysics.PhyslibFPUTFirstPicardDecomposition
open ArchonPhysics.PhyslibFPUTIteratedQuadraticSecondPicardCharacterFamily

noncomputable section

/-! ## Charge/frequency pairing -/

/-- The charge/frequency pairing is additive in the charge. -/
theorem chargeFrequency_add
    {d : Type*} [Fintype d]
    (left right : d → Int) (frequency : d → Real) :
    chargeFrequency (left + right) frequency =
      chargeFrequency left frequency + chargeFrequency right frequency := by
  classical
  unfold chargeFrequency
  simp only [Pi.add_apply, Int.cast_add, add_mul, Finset.sum_add_distrib]

/-- Negating a charge negates its paired frequency. -/
theorem chargeFrequency_neg
    {d : Type*} [Fintype d]
    (charge : d → Int) (frequency : d → Real) :
    chargeFrequency (-charge) frequency =
      -chargeFrequency charge frequency := by
  classical
  unfold chargeFrequency
  simp only [Pi.neg_apply, Int.cast_neg, neg_mul, Finset.sum_neg_distrib]

/-- The singleton free initial charge pairs to the observed frequency. -/
@[simp] theorem chargeFrequency_freeInitialPhaseCharge
    {N : Nat} [NeZero N]
    (observed : Lattice.Site N) (frequency : Lattice.Site N → Real) :
    chargeFrequency (freeInitialPhaseCharge observed 0) frequency =
      frequency observed := by
  classical
  unfold chargeFrequency freeInitialPhaseCharge binarySignedMode
    binaryPhaseSign SignedMode.charge
  simp only [if_pos, PhaseSign.exponent_phase]
  rw [Fintype.sum_eq_single observed]
  · simp
  · intro other hne
    simp [hne]

/-- Pairing the positive/conjugate coordinate charge is multiplication by
the corresponding real branch sign. -/
theorem chargeFrequency_firstPicardCoordinateCharge
    {N : Nat} [NeZero N]
    (entry : QuadraticFirstPicardCoordinateCharacterTerm N)
    (frequency : Lattice.Site N → Real) :
    chargeFrequency
        (physlibQuadraticFirstPicardCoordinateCharacterCharge entry)
        frequency =
      firstPicardCoordinateBranchSign entry.2 *
        chargeFrequency (quadraticPhaseCharge entry.1) frequency := by
  rcases entry with ⟨term, branch⟩
  fin_cases branch
  · simp
  · simp [chargeFrequency_neg]

/-- Pairing the complete iterated-quadratic charge separates into the free
outer leg and the signed inner first-Picard charge. -/
theorem chargeFrequency_iteratedQuadraticSecondPicardCharge
    {N : Nat} [NeZero N]
    (term : IteratedQuadraticSecondPicardCharacterTerm N)
    (frequency : Lattice.Site N → Real) :
    chargeFrequency (iteratedQuadraticSecondPicardCharge term) frequency =
      chargeFrequency (iteratedQuadraticFreeCharge term) frequency +
        firstPicardCoordinateBranchSign
            (iteratedQuadraticInnerEntry term).2 *
          chargeFrequency
            (quadraticPhaseCharge (iteratedQuadraticInnerEntry term).1)
            frequency := by
  unfold iteratedQuadraticSecondPicardCharge
  rw [chargeFrequency_add,
    chargeFrequency_firstPicardCoordinateCharge]

/-! ## Charge-matched return mismatches -/

/-- Equality with the singleton `A0` charge forces the outer mismatch of an
iterated tree to be the negative of its inner mismatch. -/
theorem iteratedQuadraticOuterMismatch_eq_neg_inner_of_charge_eq_freeInitial
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N)
    (hcharge : freeInitialPhaseCharge observed 0 =
      iteratedQuadraticSecondPicardCharge term) :
    iteratedQuadraticOuterMismatch m observed term =
      -iteratedQuadraticInnerMismatch m term := by
  have hfrequency := congrArg
    (fun charge : Lattice.Site N → Int ↦
      chargeFrequency charge (modeFrequency m)) hcharge
  rw [chargeFrequency_freeInitialPhaseCharge,
    chargeFrequency_iteratedQuadraticSecondPicardCharge] at hfrequency
  unfold iteratedQuadraticOuterMismatch iteratedQuadraticInnerMismatch
    firstPicardCoordinateBranchMismatch
  rw [quadraticPhaseMismatch_eq_output_sub_chargeFrequency]
  rw [hfrequency]
  ring

/-- The complete `Sum.inl` charge condition is the same return condition. -/
theorem iteratedQuadraticOuterMismatch_eq_neg_inner_of_completeCharge
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N)
    (hcharge : freeInitialPhaseCharge observed 0 =
      completeSecondPicardCharge (Sum.inl term)) :
    iteratedQuadraticOuterMismatch m observed term =
      -iteratedQuadraticInnerMismatch m term := by
  apply iteratedQuadraticOuterMismatch_eq_neg_inner_of_charge_eq_freeInitial
    m observed term
  simpa using hcharge

/-! ## Reality of the deterministic feedback prefactor -/

/-- A real force produces a purely imaginary forced-mode source. -/
@[simp] theorem forcedModeSource_re (omega force : Real) :
    (forcedModeSource omega force).re = 0 := by
  unfold forcedModeSource
  rw [Complex.div_re]
  simp

/-- The unsigned quadratic tensor coefficient is real. -/
@[simp] theorem quadraticPhaseCoefficient_im
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (observed : Lattice.Site N)
    (radius : Lattice.Site N → Real) (term : QuadraticPhaseTerm N) :
    (quadraticPhaseCoefficient m observed radius term).im = 0 := by
  simp [quadraticPhaseCoefficient]

/-- A physical quadratic Duhamel coefficient is purely imaginary. -/
@[simp] theorem physlibFreeQuadraticDuhamelCoefficient_re
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa : Real)
    (radius : Lattice.Site N → Real) (observed : Lattice.Site N)
    (term : QuadraticPhaseTerm N) :
    (freeQuadraticDuhamelCoefficient
      (physlibQuadraticCoupling m kappa 1 observed)
      m observed radius term).re = 0 := by
  unfold freeQuadraticDuhamelCoefficient physlibQuadraticCoupling
  rw [Complex.mul_re, forcedModeSource_re, quadraticPhaseCoefficient_im]
  ring

/-- Either coordinate branch has a purely imaginary static first-Picard
coefficient. -/
theorem firstPicardCoordinateBranchStaticCoefficient_re
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa : Real)
    (radius : Lattice.Site N → Real)
    (innerObserved : Lattice.Site N)
    (entry : QuadraticFirstPicardCoordinateCharacterTerm N) :
    (firstPicardCoordinateBranchStaticCoefficient
      m kappa radius innerObserved entry).re = 0 := by
  by_cases hpositive : 0 < modeFrequency m innerObserved
  · rcases entry with ⟨term, branch⟩
    by_cases hbranch : branch = 0
    · subst branch
      unfold firstPicardCoordinateBranchStaticCoefficient
      rw [if_pos hpositive]
      simp only [Fin.isValue, if_true, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, zero_mul, sub_zero,
        physlibFreeQuadraticDuhamelCoefficient_re, mul_zero]
    · have hbranchOne : branch = 1 := Fin.eq_one_of_ne_zero branch hbranch
      subst branch
      unfold firstPicardCoordinateBranchStaticCoefficient
      rw [if_pos hpositive]
      simp only [Fin.isValue, one_ne_zero, if_false, Complex.mul_re,
        Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
      have hcoefficient := physlibFreeQuadraticDuhamelCoefficient_re
        m kappa radius innerObserved term
      have hstarCoefficient :
          (starRingEnd Complex
            (freeQuadraticDuhamelCoefficient
              (physlibQuadraticCoupling m kappa 1 innerObserved)
              m innerObserved radius term)).re = 0 := by
        simp [hcoefficient]
      rw [hstarCoefficient, mul_zero]
  · unfold firstPicardCoordinateBranchStaticCoefficient
    rw [if_neg hpositive]
    rfl

/-- The complete deterministic coefficient of an iterated tree is real: it
contains the product of the imaginary outer and inner quadratic couplings. -/
theorem iteratedQuadraticSecondPicardStaticCoefficient_im
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa : Real)
    (radius : Lattice.Site N → Real) (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N) :
    (iteratedQuadraticSecondPicardStaticCoefficient
      m kappa radius observed term).im = 0 := by
  by_cases hpositive : 0 < modeFrequency m observed
  · have houterRe :
        (physlibIteratedQuadraticOuterCoupling m kappa observed *
          (interactionTensor m 3
            (Fin.cons observed (iteratedQuadraticOuterModes term)) : Complex) *
          ((radius (iteratedQuadraticFreeMode term) / 2 : Real) : Complex)).re =
            0 := by
      simp [physlibIteratedQuadraticOuterCoupling, Complex.mul_re,
        Complex.mul_im]
    unfold iteratedQuadraticSecondPicardStaticCoefficient
    rw [if_pos hpositive]
    rw [show
      physlibIteratedQuadraticOuterCoupling m kappa observed *
            (interactionTensor m 3
              (Fin.cons observed (iteratedQuadraticOuterModes term)) : Complex) *
            ((radius (iteratedQuadraticFreeMode term) / 2 : Real) : Complex) *
          firstPicardCoordinateBranchStaticCoefficient
            m kappa radius (iteratedQuadraticFirstPicardMode term)
              (iteratedQuadraticInnerEntry term) =
        (physlibIteratedQuadraticOuterCoupling m kappa observed *
            (interactionTensor m 3
              (Fin.cons observed (iteratedQuadraticOuterModes term)) : Complex) *
            ((radius (iteratedQuadraticFreeMode term) / 2 : Real) : Complex)) *
          firstPicardCoordinateBranchStaticCoefficient
            m kappa radius (iteratedQuadraticFirstPicardMode term)
              (iteratedQuadraticInnerEntry term) by ring]
    rw [Complex.mul_im, houterRe,
      firstPicardCoordinateBranchStaticCoefficient_re]
    ring
  · unfold iteratedQuadraticSecondPicardStaticCoefficient
    rw [if_neg hpositive]
    rfl

/-! ## Exact charge-matched feedback identity -/

/-- Termwise `A0`/iterated-`A2` interference on a matching charge is a real
static prefactor times the squared one-step oscillatory integral. -/
theorem two_mul_re_freeInitial_mul_star_iteratedNestedCoefficient_eq_normSq
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa time : Real)
    (radius : Lattice.Site N → Real) (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N)
    (hcharge : freeInitialPhaseCharge observed 0 =
      iteratedQuadraticSecondPicardCharge term) :
    2 * (freeInitialPhaseCoefficient radius (modeFrequency m) observed 0 *
        starRingEnd Complex
          (iteratedQuadraticSecondPicardNestedCoefficient
            m kappa radius observed time term)).re =
      (freeInitialPhaseCoefficient radius (modeFrequency m) observed 0 *
        starRingEnd Complex
          (iteratedQuadraticSecondPicardStaticCoefficient
            m kappa radius observed term)).re *
        Complex.normSq
          (oscillatoryIntegral
            (iteratedQuadraticInnerMismatch m term) time) := by
  have hmismatch :=
    iteratedQuadraticOuterMismatch_eq_neg_inner_of_charge_eq_freeInitial
      m observed term hcharge
  have henergy := two_mul_re_nestedOscillatoryIntegral_neg_self
    (iteratedQuadraticInnerMismatch m term) time
  have hfreeIm :
      (freeInitialPhaseCoefficient radius (modeFrequency m) observed 0).im = 0 :=
    rfl
  have hstaticIm := iteratedQuadraticSecondPicardStaticCoefficient_im
    m kappa radius observed term
  unfold iteratedQuadraticSecondPicardNestedCoefficient
  rw [hmismatch, map_mul]
  have hprefactorIm :
      (freeInitialPhaseCoefficient radius (modeFrequency m) observed 0 *
        starRingEnd Complex
          (iteratedQuadraticSecondPicardStaticCoefficient
            m kappa radius observed term)).im = 0 := by
    rw [Complex.mul_im]
    simp [hfreeIm, hstaticIm]
  rw [show
    freeInitialPhaseCoefficient radius (modeFrequency m) observed 0 *
        (starRingEnd Complex
            (iteratedQuadraticSecondPicardStaticCoefficient
              m kappa radius observed term) *
          starRingEnd Complex
            (nestedOscillatoryIntegral
              (-iteratedQuadraticInnerMismatch m term)
              (iteratedQuadraticInnerMismatch m term) time)) =
      (freeInitialPhaseCoefficient radius (modeFrequency m) observed 0 *
        starRingEnd Complex
          (iteratedQuadraticSecondPicardStaticCoefficient
            m kappa radius observed term)) *
        starRingEnd Complex
          (nestedOscillatoryIntegral
            (-iteratedQuadraticInnerMismatch m term)
            (iteratedQuadraticInnerMismatch m term) time) by ring]
  rw [Complex.mul_re, hprefactorIm]
  simp only [zero_mul, sub_zero, Complex.conj_re]
  rw [← henergy]
  ring

/-- The real weight multiplying the one-step norm square for one
iterated-quadratic return tree. -/
def iteratedQuadraticFeedbackNormSqTerm
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa time : Real)
    (radius : Lattice.Site N → Real) (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N) : Real :=
  (freeInitialPhaseCoefficient radius (modeFrequency m) observed 0 *
    starRingEnd Complex
      (iteratedQuadraticSecondPicardStaticCoefficient
        m kappa radius observed term)).re *
    Complex.normSq
      (oscillatoryIntegral (iteratedQuadraticInnerMismatch m term) time)

/-- The same termwise identity stated directly for the `Sum.inl` branch of
the complete second-Picard family. -/
theorem two_mul_re_freeInitial_mul_star_completeInlCoefficient_eq_feedback
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa beta time : Real)
    (radius : Lattice.Site N → Real) (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N)
    (hcharge : freeInitialPhaseCharge observed 0 =
      completeSecondPicardCharge (Sum.inl term)) :
    2 * (freeInitialPhaseCoefficient radius (modeFrequency m) observed 0 *
        starRingEnd Complex
          (completeSecondPicardCoefficient
            m kappa beta radius observed time (Sum.inl term))).re =
      iteratedQuadraticFeedbackNormSqTerm
        m kappa time radius observed term := by
  apply two_mul_re_freeInitial_mul_star_iteratedNestedCoefficient_eq_normSq
    m kappa time radius observed term
  simpa using hcharge

/-- Exact finite sum of all charge-matched `Sum.inl` feedback terms.  The
index is unchanged, so repeated modes and both ordered outer placements are
retained with their original multiplicities. -/
theorem equalChargeFamilyInterference_freeInitial_completeInl_eq_feedbackSum
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa beta time : Real)
    (radius : Lattice.Site N → Real) (observed : Lattice.Site N) :
    equalChargeFamilyInterference
        (freeInitialPhaseCoefficient radius (modeFrequency m) observed)
        (freeInitialPhaseCharge observed)
        (fun term : IteratedQuadraticSecondPicardCharacterTerm N ↦
          completeSecondPicardCoefficient
            m kappa beta radius observed time (Sum.inl term))
        (fun term : IteratedQuadraticSecondPicardCharacterTerm N ↦
          completeSecondPicardCharge (Sum.inl term)) =
      ∑ term : IteratedQuadraticSecondPicardCharacterTerm N,
        if freeInitialPhaseCharge observed 0 =
            completeSecondPicardCharge (Sum.inl term) then
          iteratedQuadraticFeedbackNormSqTerm
            m kappa time radius observed term
        else 0 := by
  classical
  unfold equalChargeFamilyInterference equalChargeCrossPairSum
  rw [Fin.sum_univ_one]
  rw [Complex.re_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro term hterm
  by_cases hcharge : freeInitialPhaseCharge observed 0 =
      completeSecondPicardCharge (Sum.inl term)
  · rw [if_pos hcharge, if_pos hcharge]
    exact two_mul_re_freeInitial_mul_star_completeInlCoefficient_eq_feedback
      m kappa beta time radius observed term hcharge
  · rw [if_neg hcharge, if_neg hcharge]
    norm_num

/-- The exact finite subtype of iterated trees selected by the singleton
`A0` charge.  It is a subtype of the original ordered tree index rather than
a quotient, so no repeated or swapped term is identified. -/
abbrev FreeInitialMatchedIteratedQuadraticTerm
    (N : Nat) [NeZero N] (observed : Lattice.Site N) :=
  {term : IteratedQuadraticSecondPicardCharacterTerm N //
    freeInitialPhaseCharge observed 0 =
      completeSecondPicardCharge (Sum.inl term)}

/-- Subtype form of the complete charge-matched feedback sum. -/
theorem equalChargeFamilyInterference_freeInitial_completeInl_eq_matchedSum
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa beta time : Real)
    (radius : Lattice.Site N → Real) (observed : Lattice.Site N) :
    equalChargeFamilyInterference
        (freeInitialPhaseCoefficient radius (modeFrequency m) observed)
        (freeInitialPhaseCharge observed)
        (fun term : IteratedQuadraticSecondPicardCharacterTerm N ↦
          completeSecondPicardCoefficient
            m kappa beta radius observed time (Sum.inl term))
        (fun term : IteratedQuadraticSecondPicardCharacterTerm N ↦
          completeSecondPicardCharge (Sum.inl term)) =
      ∑ term : FreeInitialMatchedIteratedQuadraticTerm N observed,
        iteratedQuadraticFeedbackNormSqTerm
          m kappa time radius observed term.1 := by
  rw [equalChargeFamilyInterference_freeInitial_completeInl_eq_feedbackSum]
  classical
  rw [← Finset.sum_filter]
  exact Finset.sum_subtype _ (fun term ↦ by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]) _

end

end ArchonPhysics.FreeFPUTA0IteratedQuadraticFeedbackIdentity
