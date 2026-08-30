import ArchonPhysics.PhyslibFPUTCubicLipschitzEnvelopeMesoscopicScale
import ArchonPhysics.FreeFPUTRegularArbitraryOrderOscillatoryHistory

/-!
# Near/far nonresonant split for the physical FPUT A1 and A2 histories

The absolute-value endpoint envelope loses oscillatory cancellation by bounding
the first and second Picard coefficients by powers of the elapsed time.  This
module makes one genuine cancellation step.

For a threshold `delta > 0`, the A1 character family is split into
`|mismatch| < delta` and `delta <= |mismatch|`.  The far sector is uniformly
bounded by `2 / delta`, replacing its previous factor `|T|`.

For the iterated-quadratic A2 branch, the exact nested integral is identified
with a length-two ordered history from
`FreeFPUTRegularArbitraryOrderOscillatoryHistory`.  Its far sector is bounded
by `(2 / delta)^2`.  The complementary set is not hidden: it consists exactly
of histories for which the outer mismatch, inner mismatch, or cumulative
mismatch `outer + inner` lies below `delta`.  The cumulative alternative is
the explicit recollision obstruction.

The direct-cubic A2 branch receives the one-step `2 / delta` gain.  The final
theorems plug these splits into `finiteCharacterTwoStepAbsMass` and hence into
the existing cubic Lipschitz endpoint envelope.  All near-resonant and
recollision masses remain explicit.

## Scope relative to Deng--Hani-type kinetic derivations

This deterministic finite-volume lemma is only an oscillatory cancellation
adapter.  An FPUT adaptation of the Deng--Hani wave-kinetic program
(arXiv:2104.11204, arXiv:2110.04565, arXiv:2301.07063) would still have to
state and prove, separately, all of the following inputs:

1. an iid mass environment sampled once and then frozen for the entire orbit;
2. an initial-only Haar or Gaussian law, with no independent re-Haar draw at
   later blocks;
3. an explicit joint limit `g -> 0`, `N -> infinity` and its scaling law;
4. estimates uniform for macroscopic `tau in [0, deltaKin]` at physical time
   `T = tau * |g|^(-2)`;
5. a mismatch-counting, small-ball, or equidistribution theorem controlling
   the near-resonant sets defined below;
6. a proof that the memory/recollision remainder tends to zero.

Only after item 6, together with the preceding probabilistic and joint-limit
inputs, could one infer a Markovian kinetic closure.  This file assumes none
of items 1--6: `N` and `m` are fixed deterministic parameters, the only
analytic premise is the displayed deterministic gap `0 < delta`, and the
same initial orbit is used throughout.  In particular, no Markov property,
propagation of chaos, block independence, or re-Haar mechanism is encoded.
-/

namespace ArchonPhysics.PhyslibFPUTA1A2NonresonantHistorySplit

open scoped BigOperators
open ArchonPhysics
open ArchonPhysics.FiniteHaarOscillatorySecondMoment
open ArchonPhysics.FreeFPUTA0DirectCubicBridge
open ArchonPhysics.FreeFPUTCubicPhaseExpansion
open ArchonPhysics.FreeFPUTDuhamelResonanceBridge
open ArchonPhysics.FreeFPUTMismatchPhaseExpansion
open ArchonPhysics.FreeFPUTRegularArbitraryOrderOscillatoryHistory
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.NestedOscillatoryIntegral
open ArchonPhysics.NonresonantOscillatoryGain
open ArchonPhysics.PhyslibFPUTActualHaarPostSecondPicardDecomposition
open ArchonPhysics.PhyslibFPUTCompleteSecondPicardCharacterFamily
open ArchonPhysics.PhyslibFPUTCubicHistoryLipschitzRemainder
open ArchonPhysics.PhyslibFPUTCubicLipschitzEnvelopeMesoscopicScale
open ArchonPhysics.PhyslibFPUTFirstPicardDecomposition
open ArchonPhysics.PhyslibFPUTIteratedQuadraticSecondPicardCharacterFamily
open ArchonPhysics.PhyslibFPUTSecondOrderHaarCharacterExpansion

noncomputable section
open ArchonPhysics
open ArchonPhysics.FiniteHaarOscillatorySecondMoment
open ArchonPhysics.FreeFPUTDuhamelResonanceBridge
open ArchonPhysics.FreeFPUTMismatchPhaseExpansion
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.NonresonantOscillatoryGain
open ArchonPhysics.PhyslibFPUTActualHaarPostSecondPicardDecomposition
open ArchonPhysics.PhyslibFPUTSecondOrderHaarCharacterExpansion


def coefficientAbsMassOn
    {J : Type*} [Fintype J] (indices : Finset J)
    (coefficient : J -> Complex) : Real :=
  ∑ j ∈ indices, ‖coefficient j‖

def nearMismatchIndices
    {J : Type*} [Fintype J] (delta : Real)
    (mismatch : J -> Real) : Finset J := by
  classical
  exact Finset.univ.filter fun j => |mismatch j| < delta

def farMismatchIndices
    {J : Type*} [Fintype J] (delta : Real)
    (mismatch : J -> Real) : Finset J := by
  classical
  exact Finset.univ.filter fun j => delta <= |mismatch j|

theorem finiteCharacterCoefficientAbsMass_eq_near_add_far
    {J : Type*} [Fintype J] (delta : Real)
    (mismatch : J -> Real) (coefficient : J -> Complex) :
    finiteCharacterCoefficientAbsMass coefficient =
      coefficientAbsMassOn (nearMismatchIndices delta mismatch) coefficient +
        coefficientAbsMassOn (farMismatchIndices delta mismatch) coefficient := by
  classical
  unfold finiteCharacterCoefficientAbsMass coefficientAbsMassOn
    nearMismatchIndices farMismatchIndices
  simpa only [Finset.sum_filter, Finset.sum_const_zero, not_lt] using
    (Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun j => |mismatch j| < delta) (fun j => ‖coefficient j‖)).symm

theorem coefficientAbsMassOn_oscillatory_near_le_time
    {J : Type*} [Fintype J] (delta : Real)
    (mismatch : J -> Real) (coefficient : J -> Complex) (T : Real) :
    coefficientAbsMassOn (nearMismatchIndices delta mismatch)
        (oscillatoryCoefficient coefficient mismatch T) <=
      |T| * coefficientAbsMassOn
        (nearMismatchIndices delta mismatch) coefficient := by
  classical
  unfold coefficientAbsMassOn oscillatoryCoefficient
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j hj
  rw [norm_mul]
  calc
    ‖coefficient j‖ * ‖oscillatoryIntegral (mismatch j) T‖ <=
        ‖coefficient j‖ * |T| :=
      mul_le_mul_of_nonneg_left
        (norm_oscillatoryIntegral_le_abs_time (mismatch j) T)
        (norm_nonneg (coefficient j))
    _ = |T| * ‖coefficient j‖ := by ring

theorem coefficientAbsMassOn_oscillatory_far_le_inverse_gap
    {J : Type*} [Fintype J] {delta : Real} (hdelta : 0 < delta)
    (mismatch : J -> Real) (coefficient : J -> Complex) (T : Real) :
    coefficientAbsMassOn (farMismatchIndices delta mismatch)
        (oscillatoryCoefficient coefficient mismatch T) <=
      (2 / delta) * coefficientAbsMassOn
        (farMismatchIndices delta mismatch) coefficient := by
  classical
  unfold coefficientAbsMassOn oscillatoryCoefficient
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j hj
  have hgap : delta <= |mismatch j| := by
    simpa only [farMismatchIndices, Finset.mem_filter, Finset.mem_univ,
      true_and] using hj
  have habs : 0 < |mismatch j| := hdelta.trans_le hgap
  have hmismatch : mismatch j ≠ 0 := abs_pos.mp habs
  have hresolvent : 2 / |mismatch j| <= 2 / delta :=
    (div_le_div_iff_of_pos_left (by norm_num) habs hdelta).2 hgap
  rw [norm_mul]
  calc
    ‖coefficient j‖ * ‖oscillatoryIntegral (mismatch j) T‖ <=
        ‖coefficient j‖ * (2 / |mismatch j|) :=
      mul_le_mul_of_nonneg_left
        (norm_oscillatoryIntegral_le_two_div_abs hmismatch) (norm_nonneg (coefficient j))
    _ <= ‖coefficient j‖ * (2 / delta) :=
      mul_le_mul_of_nonneg_left hresolvent (norm_nonneg (coefficient j))
    _ = (2 / delta) * ‖coefficient j‖ := by ring

def physlibA1NearStaticAbsMass
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa delta : Real)
    (radius : Lattice.Site N -> Real) (observed : Lattice.Site N) : Real :=
  coefficientAbsMassOn
    (nearMismatchIndices delta
      (quadraticPhaseMismatch (modeFrequency m) observed))
    (freeQuadraticDuhamelCoefficient
      (physlibQuadraticCoupling m kappa 1 observed) m observed radius)

def physlibA1FarStaticAbsMass
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa delta : Real)
    (radius : Lattice.Site N -> Real) (observed : Lattice.Site N) : Real :=
  coefficientAbsMassOn
    (farMismatchIndices delta
      (quadraticPhaseMismatch (modeFrequency m) observed))
    (freeQuadraticDuhamelCoefficient
      (physlibQuadraticCoupling m kappa 1 observed) m observed radius)

/-- Deterministic fixed-volume A1 cancellation.  It uses only `0 < delta`;
the near sector remains explicit and no random law, joint limit, Markov
property, or re-Haar step is assumed. -/
theorem physlibA1CoefficientAbsMass_le_near_time_add_far_inverse_gap
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa : Real)
    {delta : Real} (hdelta : 0 < delta)
    (radius : Lattice.Site N -> Real) (T : Real)
    (observed : Lattice.Site N) :
    finiteCharacterCoefficientAbsMass
        (physlibQuadraticFirstPicardCharacterCoefficient
          m kappa radius T observed) <=
      |T| * physlibA1NearStaticAbsMass m kappa delta radius observed +
        (2 / delta) *
          physlibA1FarStaticAbsMass m kappa delta radius observed := by
  let mismatch := quadraticPhaseMismatch (modeFrequency m) observed
  let coefficient := freeQuadraticDuhamelCoefficient
    (physlibQuadraticCoupling m kappa 1 observed) m observed radius
  unfold physlibQuadraticFirstPicardCharacterCoefficient
  change finiteCharacterCoefficientAbsMass
    (oscillatoryCoefficient coefficient mismatch T) <= _
  calc
    finiteCharacterCoefficientAbsMass
        (oscillatoryCoefficient coefficient mismatch T) =
      coefficientAbsMassOn (nearMismatchIndices delta mismatch)
          (oscillatoryCoefficient coefficient mismatch T) +
        coefficientAbsMassOn (farMismatchIndices delta mismatch)
          (oscillatoryCoefficient coefficient mismatch T) :=
      finiteCharacterCoefficientAbsMass_eq_near_add_far
        delta mismatch (oscillatoryCoefficient coefficient mismatch T)
    _ <= |T| * coefficientAbsMassOn
          (nearMismatchIndices delta mismatch) coefficient +
        (2 / delta) * coefficientAbsMassOn
          (farMismatchIndices delta mismatch) coefficient :=
      add_le_add
        (coefficientAbsMassOn_oscillatory_near_le_time
          delta mismatch coefficient T)
        (coefficientAbsMassOn_oscillatory_far_le_inverse_gap
          hdelta mismatch coefficient T)
    _ = _ := rfl

open scoped BigOperators
open ArchonPhysics
open ArchonPhysics.FiniteHaarOscillatorySecondMoment
open ArchonPhysics.FreeFPUTA0DirectCubicBridge
open ArchonPhysics.FreeFPUTCubicPhaseExpansion
open ArchonPhysics.FreeFPUTRegularArbitraryOrderOscillatoryHistory
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.NestedOscillatoryIntegral
open ArchonPhysics.PhyslibFPUTActualHaarPostSecondPicardDecomposition
open ArchonPhysics.PhyslibFPUTCompleteSecondPicardCharacterFamily
open ArchonPhysics.PhyslibFPUTIteratedQuadraticSecondPicardCharacterFamily


theorem fullyNonresonant_pair_iff
    (delta deltaOut deltaIn : Real) :
    FullyNonresonantOrderedHistory delta [deltaOut, deltaIn] <->
      delta <= |deltaOut| /\ delta <= |deltaIn| /\
        delta <= |deltaOut + deltaIn| := by
  constructor
  · intro hregular
    cases hregular with
    | cons _ _ _ houter hdrop hmerge =>
        cases hdrop with
        | singleton _ hinner =>
            cases hmerge with
            | singleton _ htotal =>
                exact ⟨houter, hinner, htotal⟩
  · rintro ⟨houter, hinner, htotal⟩
    exact FullyNonresonantOrderedHistory.cons deltaOut deltaIn [] houter
      (FullyNonresonantOrderedHistory.singleton deltaIn hinner)
      (FullyNonresonantOrderedHistory.singleton (deltaOut + deltaIn) htotal)

def iteratedQuadraticPhaseHistory
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N) : List Real :=
  [iteratedQuadraticOuterMismatch m observed term,
    iteratedQuadraticInnerMismatch m term]

def iteratedQuadraticRegularTerms
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (observed : Lattice.Site N)
    (delta : Real) : Finset (IteratedQuadraticSecondPicardCharacterTerm N) := by
  classical
  exact Finset.univ.filter fun term =>
    FullyNonresonantOrderedHistory delta
      (iteratedQuadraticPhaseHistory m observed term)

def iteratedQuadraticNearRecollisionTerms
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (observed : Lattice.Site N)
    (delta : Real) : Finset (IteratedQuadraticSecondPicardCharacterTerm N) := by
  classical
  exact Finset.univ.filter fun term =>
    ¬ (FullyNonresonantOrderedHistory delta
      (iteratedQuadraticPhaseHistory m observed term))

theorem mem_iteratedQuadraticNearRecollisionTerms_iff
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (observed : Lattice.Site N)
    (delta : Real) (term : IteratedQuadraticSecondPicardCharacterTerm N) :
    term ∈ iteratedQuadraticNearRecollisionTerms m observed delta <->
      |iteratedQuadraticOuterMismatch m observed term| < delta \/
      |iteratedQuadraticInnerMismatch m term| < delta \/
      |iteratedQuadraticOuterMismatch m observed term +
        iteratedQuadraticInnerMismatch m term| < delta := by
  classical
  unfold iteratedQuadraticNearRecollisionTerms iteratedQuadraticPhaseHistory
  simp only [Finset.mem_filter, Finset.mem_univ, true_and,
    fullyNonresonant_pair_iff, not_and_or, not_le]

def physlibA2IteratedNearHistoryAbsMass
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa delta : Real)
    (radius : Lattice.Site N -> Real) (T : Real)
    (observed : Lattice.Site N) : Real :=
  coefficientAbsMassOn
    (iteratedQuadraticNearRecollisionTerms m observed delta)
    (iteratedQuadraticSecondPicardNestedCoefficient
      m kappa radius observed T)

def physlibA2IteratedRegularStaticAbsMass
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa delta : Real)
    (radius : Lattice.Site N -> Real)
    (observed : Lattice.Site N) : Real :=
  coefficientAbsMassOn
    (iteratedQuadraticRegularTerms m observed delta)
    (iteratedQuadraticSecondPicardStaticCoefficient
      m kappa radius observed)

theorem iteratedQuadraticNestedAbsMassOn_regular_le_inverse_gap_sq
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa : Real)
    {delta : Real} (hdelta : 0 < delta)
    (radius : Lattice.Site N -> Real) (T : Real)
    (observed : Lattice.Site N) :
    coefficientAbsMassOn
        (iteratedQuadraticRegularTerms m observed delta)
        (iteratedQuadraticSecondPicardNestedCoefficient
          m kappa radius observed T) <=
      (2 / delta) ^ 2 *
        physlibA2IteratedRegularStaticAbsMass
          m kappa delta radius observed := by
  classical
  unfold physlibA2IteratedRegularStaticAbsMass coefficientAbsMassOn
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro term hterm
  have hregular : FullyNonresonantOrderedHistory delta
      (iteratedQuadraticPhaseHistory m observed term) := by
    simpa only [iteratedQuadraticRegularTerms, Finset.mem_filter,
      Finset.mem_univ, true_and] using hterm
  have hosc :
      ‖nestedOscillatoryIntegral
        (iteratedQuadraticOuterMismatch m observed term)
        (iteratedQuadraticInnerMismatch m term) T‖ <=
        (2 / delta) ^ 2 := by
    rw [<- linearOrderedOscillatoryIntegral_pair_eq_nested]
    simpa only [iteratedQuadraticPhaseHistory, List.length_cons,
      List.length_nil, Nat.zero_add] using
      norm_linearOrderedOscillatoryIntegral_le_resolvent
        hdelta hregular T
  unfold iteratedQuadraticSecondPicardNestedCoefficient
  rw [norm_mul]
  calc
    ‖iteratedQuadraticSecondPicardStaticCoefficient
          m kappa radius observed term‖ *
        ‖nestedOscillatoryIntegral
          (iteratedQuadraticOuterMismatch m observed term)
          (iteratedQuadraticInnerMismatch m term) T‖ <=
      ‖iteratedQuadraticSecondPicardStaticCoefficient
          m kappa radius observed term‖ * (2 / delta) ^ 2 :=
        mul_le_mul_of_nonneg_left hosc (norm_nonneg _)
    _ = (2 / delta) ^ 2 *
        ‖iteratedQuadraticSecondPicardStaticCoefficient
          m kappa radius observed term‖ := by ring

theorem physlibA2IteratedCoefficientAbsMass_le_near_add_regular_inverse_gap_sq
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa : Real)
    {delta : Real} (hdelta : 0 < delta)
    (radius : Lattice.Site N -> Real) (T : Real)
    (observed : Lattice.Site N) :
    finiteCharacterCoefficientAbsMass
        (iteratedQuadraticSecondPicardNestedCoefficient
          m kappa radius observed T) <=
      physlibA2IteratedNearHistoryAbsMass
          m kappa delta radius T observed +
        (2 / delta) ^ 2 *
          physlibA2IteratedRegularStaticAbsMass
            m kappa delta radius observed := by
  classical
  let regular := fun term : IteratedQuadraticSecondPicardCharacterTerm N =>
    FullyNonresonantOrderedHistory delta
      (iteratedQuadraticPhaseHistory m observed term)
  let coefficient := iteratedQuadraticSecondPicardNestedCoefficient
    m kappa radius observed T
  have hsplit : finiteCharacterCoefficientAbsMass coefficient =
      coefficientAbsMassOn
          (iteratedQuadraticNearRecollisionTerms m observed delta) coefficient +
        coefficientAbsMassOn
          (iteratedQuadraticRegularTerms m observed delta) coefficient := by
    unfold finiteCharacterCoefficientAbsMass coefficientAbsMassOn
      iteratedQuadraticNearRecollisionTerms iteratedQuadraticRegularTerms
    simpa only [Finset.sum_filter, add_comm, regular] using
      (Finset.sum_filter_add_sum_filter_not Finset.univ regular
        (fun term => ‖coefficient term‖)).symm
  calc
    finiteCharacterCoefficientAbsMass coefficient =
        coefficientAbsMassOn
          (iteratedQuadraticNearRecollisionTerms m observed delta) coefficient +
        coefficientAbsMassOn
          (iteratedQuadraticRegularTerms m observed delta) coefficient := hsplit
    _ <= physlibA2IteratedNearHistoryAbsMass
          m kappa delta radius T observed +
        (2 / delta) ^ 2 *
          physlibA2IteratedRegularStaticAbsMass
            m kappa delta radius observed :=
      add_le_add le_rfl
        (iteratedQuadraticNestedAbsMassOn_regular_le_inverse_gap_sq
          m kappa hdelta radius T observed)

open scoped BigOperators
open ArchonPhysics
open ArchonPhysics.FiniteHaarOscillatorySecondMoment
open ArchonPhysics.FreeFPUTA0DirectCubicBridge
open ArchonPhysics.FreeFPUTCubicPhaseExpansion
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.PhyslibFPUTActualHaarPostSecondPicardDecomposition
open ArchonPhysics.PhyslibFPUTCompleteSecondPicardCharacterFamily
open ArchonPhysics.PhyslibFPUTIteratedQuadraticSecondPicardCharacterFamily


def physlibA2CubicNearHistoryAbsMass
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (beta delta : Real)
    (radius : Lattice.Site N -> Real) (T : Real)
    (observed : Lattice.Site N) : Real :=
  coefficientAbsMassOn
    (nearMismatchIndices delta
      (cubicPhaseMismatch (modeFrequency m) observed))
    (oscillatoryCoefficient
      (cubicDuhamelCoefficient
        (physicalCubicUnitCoupling (modeFrequency m observed) beta)
        m observed radius)
      (cubicPhaseMismatch (modeFrequency m) observed) T)

def physlibA2CubicFarStaticAbsMass
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (beta delta : Real)
    (radius : Lattice.Site N -> Real)
    (observed : Lattice.Site N) : Real :=
  coefficientAbsMassOn
    (farMismatchIndices delta
      (cubicPhaseMismatch (modeFrequency m) observed))
    (cubicDuhamelCoefficient
      (physicalCubicUnitCoupling (modeFrequency m observed) beta)
      m observed radius)

theorem mem_physlibA2CubicNearTerms_iff
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (delta : Real)
    (observed : Lattice.Site N) (term : CubicPhaseTerm N) :
    term ∈ nearMismatchIndices delta
        (cubicPhaseMismatch (modeFrequency m) observed) <->
      |cubicPhaseMismatch (modeFrequency m) observed term| < delta := by
  classical
  simp [nearMismatchIndices]

theorem physlibA2CubicCoefficientAbsMass_le_near_add_far_inverse_gap
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (beta : Real)
    {delta : Real} (hdelta : 0 < delta)
    (radius : Lattice.Site N -> Real) (T : Real)
    (observed : Lattice.Site N) :
    finiteCharacterCoefficientAbsMass
        (oscillatoryCoefficient
          (cubicDuhamelCoefficient
            (physicalCubicUnitCoupling (modeFrequency m observed) beta)
            m observed radius)
          (cubicPhaseMismatch (modeFrequency m) observed) T) <=
      physlibA2CubicNearHistoryAbsMass
          m beta delta radius T observed +
        (2 / delta) *
          physlibA2CubicFarStaticAbsMass
            m beta delta radius observed := by
  let mismatch := cubicPhaseMismatch (modeFrequency m) observed
  let coefficient := cubicDuhamelCoefficient
    (physicalCubicUnitCoupling (modeFrequency m observed) beta)
    m observed radius
  calc
    finiteCharacterCoefficientAbsMass
        (oscillatoryCoefficient coefficient mismatch T) =
      coefficientAbsMassOn (nearMismatchIndices delta mismatch)
          (oscillatoryCoefficient coefficient mismatch T) +
        coefficientAbsMassOn (farMismatchIndices delta mismatch)
          (oscillatoryCoefficient coefficient mismatch T) :=
      finiteCharacterCoefficientAbsMass_eq_near_add_far
        delta mismatch (oscillatoryCoefficient coefficient mismatch T)
    _ <= coefficientAbsMassOn (nearMismatchIndices delta mismatch)
          (oscillatoryCoefficient coefficient mismatch T) +
        (2 / delta) * coefficientAbsMassOn
          (farMismatchIndices delta mismatch) coefficient :=
      add_le_add le_rfl
        (coefficientAbsMassOn_oscillatory_far_le_inverse_gap
          hdelta mismatch coefficient T)
    _ = _ := rfl

def physlibA2NearHistoryAbsMass
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa beta delta : Real)
    (radius : Lattice.Site N -> Real) (T : Real)
    (observed : Lattice.Site N) : Real :=
  physlibA2IteratedNearHistoryAbsMass
      m kappa delta radius T observed +
    physlibA2CubicNearHistoryAbsMass
      m beta delta radius T observed

def physlibA2FarResolventAbsMass
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa beta delta : Real)
    (radius : Lattice.Site N -> Real)
    (observed : Lattice.Site N) : Real :=
  (2 / delta) ^ 2 *
      physlibA2IteratedRegularStaticAbsMass
        m kappa delta radius observed +
    (2 / delta) *
      physlibA2CubicFarStaticAbsMass
        m beta delta radius observed

theorem completeSecondPicardCoefficientAbsMass_eq_iterated_add_cubic
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa beta : Real)
    (radius : Lattice.Site N -> Real) (T : Real)
    (observed : Lattice.Site N) :
    finiteCharacterCoefficientAbsMass
        (completeSecondPicardCoefficient
          m kappa beta radius observed T) =
      finiteCharacterCoefficientAbsMass
          (iteratedQuadraticSecondPicardNestedCoefficient
            m kappa radius observed T) +
        finiteCharacterCoefficientAbsMass
          (oscillatoryCoefficient
            (cubicDuhamelCoefficient
              (physicalCubicUnitCoupling (modeFrequency m observed) beta)
              m observed radius)
            (cubicPhaseMismatch (modeFrequency m) observed) T) := by
  classical
  unfold finiteCharacterCoefficientAbsMass
  rw [Fintype.sum_sum_type]
  rfl

/-- Complete deterministic A2 split.  The unresolved term is the literal
near-history mass, including cumulative recollisions; this theorem supplies
no equidistribution estimate and does not Markovize the dynamics. -/
theorem completeSecondPicardCoefficientAbsMass_le_near_history_add_far_resolvent
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa beta : Real)
    {delta : Real} (hdelta : 0 < delta)
    (radius : Lattice.Site N -> Real) (T : Real)
    (observed : Lattice.Site N) :
    finiteCharacterCoefficientAbsMass
        (completeSecondPicardCoefficient
          m kappa beta radius observed T) <=
      physlibA2NearHistoryAbsMass
          m kappa beta delta radius T observed +
        physlibA2FarResolventAbsMass
          m kappa beta delta radius observed := by
  rw [completeSecondPicardCoefficientAbsMass_eq_iterated_add_cubic]
  have hiter :=
    physlibA2IteratedCoefficientAbsMass_le_near_add_regular_inverse_gap_sq
      m kappa hdelta radius T observed
  have hcubic :=
    physlibA2CubicCoefficientAbsMass_le_near_add_far_inverse_gap
      m beta hdelta radius T observed
  unfold physlibA2NearHistoryAbsMass physlibA2FarResolventAbsMass
  linarith

open ArchonPhysics
open ArchonPhysics.FiniteHaarOscillatorySecondMoment
open ArchonPhysics.FreeFPUTA0DirectCubicBridge
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.PhyslibFPUTActualHaarPostSecondPicardDecomposition
open ArchonPhysics.PhyslibFPUTCompleteSecondPicardCharacterFamily
open ArchonPhysics.PhyslibFPUTCubicHistoryLipschitzRemainder
open ArchonPhysics.PhyslibFPUTCubicLipschitzEnvelopeMesoscopicScale
open ArchonPhysics.PhyslibFPUTSecondOrderHaarCharacterExpansion


def physlibReferenceNearFarAbsMassEnvelope
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa beta g delta : Real)
    (radius : Lattice.Site N -> Real) (T : Real)
    (observed : Lattice.Site N) : Real :=
  finiteCharacterCoefficientAbsMass
      (freeInitialPhaseCoefficient radius (modeFrequency m) observed) +
    |g| *
      (|T| * physlibA1NearStaticAbsMass
          m kappa delta radius observed +
        (2 / delta) * physlibA1FarStaticAbsMass
          m kappa delta radius observed) +
    g ^ 2 *
      (physlibA2NearHistoryAbsMass
          m kappa beta delta radius T observed +
        physlibA2FarResolventAbsMass
          m kappa beta delta radius observed)

theorem finiteCharacterTwoStepAbsMass_le_near_far_envelope
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa beta g : Real)
    {delta : Real} (hdelta : 0 < delta)
    (radius : Lattice.Site N -> Real) (T : Real)
    (observed : Lattice.Site N) :
    finiteCharacterTwoStepAbsMass g
        (freeInitialPhaseCoefficient radius (modeFrequency m) observed)
        (physlibQuadraticFirstPicardCharacterCoefficient
          m kappa radius T observed)
        (completeSecondPicardCoefficient
          m kappa beta radius observed T) <=
      physlibReferenceNearFarAbsMassEnvelope
        m kappa beta g delta radius T observed := by
  have hA1 :=
    physlibA1CoefficientAbsMass_le_near_time_add_far_inverse_gap
      m kappa hdelta radius T observed
  have hA2 :=
    completeSecondPicardCoefficientAbsMass_le_near_history_add_far_resolvent
      m kappa beta hdelta radius T observed
  unfold finiteCharacterTwoStepAbsMass
    physlibReferenceNearFarAbsMassEnvelope
  exact add_le_add
    (add_le_add le_rfl
      (mul_le_mul_of_nonneg_left hA1 (abs_nonneg g)))
    (mul_le_mul_of_nonneg_left hA2 (sq_nonneg g))

def physlibHaarCubicLipschitzNearFarUnitEnvelope
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N)
    (mUpper kappa beta g H delta : Real)
    (radius : Lattice.Site N -> Real) (T : Real)
    (observed : Lattice.Site N) : Real :=
  2 * physlibReferenceNearFarAbsMassEnvelope
      m kappa beta g delta radius T observed *
      cubicLipschitzAfterSecondPicardCoefficientUnitEnergyWindowEnvelope
        m mUpper kappa beta g H radius T observed +
    |g| ^ 3 *
      cubicLipschitzAfterSecondPicardCoefficientUnitEnergyWindowEnvelope
        m mUpper kappa beta g H radius T observed ^ 2

/-- Endpoint-envelope handoff for a single unchanged initial orbit.  The
near/recollision mass is not discarded or restarted with an independent Haar
phase.  A kinetic/Markov conclusion additionally requires all six inputs
listed in the module scope note. -/
theorem physlibHaarCubicLipschitzUnitEnvelope_le_near_far_envelope
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N)
    (mUpper kappa beta g H : Real) {delta : Real} (hdelta : 0 < delta)
    (radius : Lattice.Site N -> Real) (T : Real)
    (observed : Lattice.Site N)
    (hmUpper : 0 <= mUpper) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (hH : 0 <= H) (hT : 0 <= T) :
    physlibHaarCubicLipschitzEnergyCorrectionUnitEnvelope
        m mUpper kappa beta g H radius T observed <=
      physlibHaarCubicLipschitzNearFarUnitEnvelope
        m mUpper kappa beta g H delta radius T observed := by
  have hmass := finiteCharacterTwoStepAbsMass_le_near_far_envelope
    m kappa beta g hdelta radius T observed
  have hcoefficient : 0 <=
      cubicLipschitzAfterSecondPicardCoefficientUnitEnergyWindowEnvelope
        m mUpper kappa beta g H radius T observed :=
    coefficientUnitEnergyWindow_nonneg
      m mUpper kappa beta g H radius T observed hmUpper hbeta hH hT
  unfold physlibHaarCubicLipschitzEnergyCorrectionUnitEnvelope
    physlibHaarCubicLipschitzNearFarUnitEnvelope
  have hleading := mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right hmass hcoefficient)
    (show (0 : Real) <= 2 by norm_num)
  exact add_le_add (by simpa only [mul_assoc] using hleading) le_rfl
end
end ArchonPhysics.PhyslibFPUTA1A2NonresonantHistorySplit
