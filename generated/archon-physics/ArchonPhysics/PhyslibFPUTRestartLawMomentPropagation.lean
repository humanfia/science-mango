import ArchonPhysics.PhyslibFPUTMultiblockRPAMomentPropagation

/-!
# Probability-law sufficient conditions for multiblock RPA restart

The preceding multiblock module deliberately exposes a recurrence hypothesis.
This module gives a more concrete sufficient condition for that recurrence:
the restarted law is close to the reference law in the dual metric generated
by measurable tests bounded by one, the moment observable is uniformly
bounded, and the deterministic moment propagation is Lipschitz.

For second and fourth amplitude moments the law defects are respectively
`M^2 * eta_j` and `M^4 * eta_j`.  Adding the actual one-block Physlib defects
gives `M^2 * eta_j + 2 M epsilon_block` and
`M^4 * eta_j + 4 M^3 epsilon_block`.

This file does **not** prove that a Hamiltonian block pushforward is close to
Haar.  That law-closeness statement, as well as the deterministic moment-map
Lipschitz estimate, remains an explicit hypothesis.
-/

namespace ArchonPhysics.PhyslibFPUTRestartLawMomentPropagation

open MeasureTheory
open UnitAddTorus
open ArchonPhysics
open ArchonPhysics.CoerciveHamiltonianPhyslib
open ArchonPhysics.Lattice
open ArchonPhysics.PhyslibFPUTMultiblockRPAMomentPropagation
open ArchonPhysics.PhyslibFPUTShortTimeRPAMomentStability
open ArchonPhysics.RandomPhaseMoments

noncomputable section

/-! ## A normalized bounded-test law metric -/

/-- `BoundedTestLawDistanceAtMost mu nu eta` is the dual bounded-test
condition

`|E_mu f - E_nu f| <= eta`

for every measurable real test with `|f| <= 1`.  On probability measures this
is a standard total-variation-strength condition (up to the convention used
for the factor `2`).  We use the dual condition directly to avoid hiding a TV
normalization convention. -/
def BoundedTestLawDistanceAtMost
    {Omega : Type*} [MeasurableSpace Omega]
    (mu nu : Measure Omega) (eta : Real) : Prop :=
  ∀ f : Omega → Real, Measurable f → (∀ omega, |f omega| ≤ 1) →
    |∫ omega, f omega ∂mu - ∫ omega, f omega ∂nu| ≤ eta

theorem boundedTestLawDistanceAtMost_nonneg
    {Omega : Type*} [MeasurableSpace Omega]
    {mu nu : Measure Omega} {eta : Real}
    (hclose : BoundedTestLawDistanceAtMost mu nu eta) :
    0 ≤ eta := by
  simpa using hclose (fun _ ↦ 0) measurable_const (fun _ ↦ by simp)

/-- Scaling the normalized bounded-test estimate to a test bounded by `B`
costs exactly the factor `B`. -/
theorem abs_integral_sub_integral_le_of_boundedTestLawDistanceAtMost
    {Omega : Type*} [MeasurableSpace Omega]
    {mu nu : Measure Omega} {eta B : Real}
    (hclose : BoundedTestLawDistanceAtMost mu nu eta)
    (hB : 0 ≤ B)
    (f : Omega → Real) (hf : Measurable f)
    (hbound : ∀ omega, |f omega| ≤ B) :
    |∫ omega, f omega ∂mu - ∫ omega, f omega ∂nu| ≤ B * eta := by
  rcases hB.eq_or_lt with hBzero | hBpos
  · subst B
    have hfzero : f = 0 := by
      funext omega
      have habs : |f omega| = 0 :=
        le_antisymm (by simpa using hbound omega) (abs_nonneg _)
      exact abs_eq_zero.mp habs
    simp [hfzero]
  · let normalized : Omega → Real := fun omega ↦ f omega / B
    have hnormalizedMeasurable : Measurable normalized :=
      hf.div_const B
    have hnormalizedBound : ∀ omega, |normalized omega| ≤ 1 := by
      intro omega
      rw [show |normalized omega| = |f omega| / B by
        simp [normalized, abs_div, abs_of_pos hBpos]]
      exact (div_le_one hBpos).mpr (hbound omega)
    have hnormalized := hclose normalized hnormalizedMeasurable
      hnormalizedBound
    calc
      |∫ omega, f omega ∂mu - ∫ omega, f omega ∂nu| =
          B * |∫ omega, normalized omega ∂mu -
            ∫ omega, normalized omega ∂nu| := by
        simp only [normalized, integral_div, ← sub_div, abs_div,
          abs_of_pos hBpos]
        rw [mul_comm B, div_mul_cancel₀ _ hBpos.ne']
      _ ≤ B * eta := mul_le_mul_of_nonneg_left hnormalized hB

/-- Pushforward version: a bounded-test estimate for `map phi source` controls
expectations of `f ∘ phi` under the source law. -/
theorem abs_pushforward_integral_sub_integral_le
    {Xi Omega : Type*} [MeasurableSpace Xi] [MeasurableSpace Omega]
    (source : Measure Xi) (nu : Measure Omega)
    (phi : Xi → Omega) (hphi : Measurable phi)
    {eta B : Real}
    (hclose : BoundedTestLawDistanceAtMost
      (Measure.map phi source) nu eta)
    (hB : 0 ≤ B)
    (f : Omega → Real) (hf : Measurable f)
    (hbound : ∀ omega, |f omega| ≤ B) :
    |∫ xi, f (phi xi) ∂source - ∫ omega, f omega ∂nu| ≤
      B * eta := by
  have h := abs_integral_sub_integral_le_of_boundedTestLawDistanceAtMost
    hclose hB f hf hbound
  rw [integral_map_of_stronglyMeasurable hphi hf.stronglyMeasurable] at h
  exact h

/-! ## Canonical Haar restart law -/

/-- A named, transparent statement that one restarted phase law is within
`eta` of the canonical finite product Haar law. -/
def IsCanonicalHaarRestartLawClose
    {d : Type*} [Fintype d]
    (restartLaw : Measure (UnitAddTorus d)) (eta : Real) : Prop :=
  BoundedTestLawDistanceAtMost restartLaw (finitePhaseHaarLaw d) eta

/-! ## Bounded amplitude-moment tests -/

/-- The real second-moment test associated to a complex amplitude. -/
def amplitudeSecondMomentObservable
    {Omega : Type*} (amplitude : Omega → Complex) (omega : Omega) : Real :=
  Complex.normSq (amplitude omega)

/-- The real fourth-moment test associated to a complex amplitude. -/
def amplitudeFourthMomentObservable
    {Omega : Type*} (amplitude : Omega → Complex) (omega : Omega) : Real :=
  Complex.normSq (amplitude omega) ^ 2

theorem measurable_amplitudeSecondMomentObservable
    {Omega : Type*} [MeasurableSpace Omega]
    {amplitude : Omega → Complex} (hamplitude : Measurable amplitude) :
    Measurable (amplitudeSecondMomentObservable amplitude) :=
  Complex.continuous_normSq.measurable.comp hamplitude

theorem measurable_amplitudeFourthMomentObservable
    {Omega : Type*} [MeasurableSpace Omega]
    {amplitude : Omega → Complex} (hamplitude : Measurable amplitude) :
    Measurable (amplitudeFourthMomentObservable amplitude) :=
  (Complex.continuous_normSq.measurable.comp hamplitude).pow_const 2

theorem abs_amplitudeSecondMomentObservable_le
    {Omega : Type*} {amplitude : Omega → Complex}
    {M : Real} (_hM : 0 ≤ M)
    (hbound : ∀ omega, ‖amplitude omega‖ ≤ M) (omega : Omega) :
    |amplitudeSecondMomentObservable amplitude omega| ≤ M ^ 2 := by
  unfold amplitudeSecondMomentObservable
  rw [abs_of_nonneg (Complex.normSq_nonneg _),
    Complex.normSq_eq_norm_sq]
  exact pow_le_pow_left₀ (norm_nonneg _) (hbound omega) 2

theorem abs_amplitudeFourthMomentObservable_le
    {Omega : Type*} {amplitude : Omega → Complex}
    {M : Real} (_hM : 0 ≤ M)
    (hbound : ∀ omega, ‖amplitude omega‖ ≤ M) (omega : Omega) :
    |amplitudeFourthMomentObservable amplitude omega| ≤ M ^ 4 := by
  unfold amplitudeFourthMomentObservable
  rw [abs_of_nonneg (sq_nonneg _), Complex.normSq_eq_norm_sq]
  have hpow := pow_le_pow_left₀ (norm_nonneg (amplitude omega))
    (hbound omega) 4
  calc
    (‖amplitude omega‖ ^ 2) ^ 2 = ‖amplitude omega‖ ^ 4 := by ring
    _ ≤ M ^ 4 := hpow

/-- A single bounded-test law estimate simultaneously gives the natural
`M^2 eta` and `M^4 eta` errors for amplitude moments. -/
theorem amplitude_second_fourth_law_discrepancy
    {Omega : Type*} [MeasurableSpace Omega]
    {mu nu : Measure Omega} {eta M : Real}
    (hclose : BoundedTestLawDistanceAtMost mu nu eta)
    (hM : 0 ≤ M)
    (amplitude : Omega → Complex) (hamplitude : Measurable amplitude)
    (hbound : ∀ omega, ‖amplitude omega‖ ≤ M) :
    |∫ omega, amplitudeSecondMomentObservable amplitude omega ∂mu -
        ∫ omega, amplitudeSecondMomentObservable amplitude omega ∂nu| ≤
        M ^ 2 * eta ∧
    |∫ omega, amplitudeFourthMomentObservable amplitude omega ∂mu -
        ∫ omega, amplitudeFourthMomentObservable amplitude omega ∂nu| ≤
        M ^ 4 * eta := by
  constructor
  · exact abs_integral_sub_integral_le_of_boundedTestLawDistanceAtMost
      hclose (sq_nonneg M) _
        (measurable_amplitudeSecondMomentObservable hamplitude)
        (abs_amplitudeSecondMomentObservable_le hM hbound)
  · exact abs_integral_sub_integral_le_of_boundedTestLawDistanceAtMost
      hclose (by positivity : 0 ≤ M ^ 4) _
        (measurable_amplitudeFourthMomentObservable hamplitude)
        (abs_amplitudeFourthMomentObservable_le hM hbound)

/-! ## From law closeness and Lipschitz propagation to a restart recurrence -/

/-- Generic sufficient condition for one affine restart recurrence.

`propagatedError` is the part controlled by the deterministic moment-map
Lipschitz estimate.  `localDefect` is the one-block approximation error.  The
remaining middle term in `hdecomposition` is an actual expectation difference
under the restarted and reference laws, and is bounded here using the
bounded-test metric. -/
theorem restart_recurrence_of_boundedTestLawDistance
    {Omega : Type*} [MeasurableSpace Omega]
    (restartLaw referenceLaw : Nat → Measure Omega)
    (observable : Nat → Omega → Real)
    (error propagatedError localDefect eta observableBound : Nat → Real)
    {L h : Real}
    (hobservableBound0 : ∀ j, 0 ≤ observableBound j)
    (hlaw : ∀ j, BoundedTestLawDistanceAtMost
      (restartLaw j) (referenceLaw j) (eta j))
    (hmeasurable : ∀ j, Measurable (observable j))
    (hobservableBound : ∀ j omega,
      |observable j omega| ≤ observableBound j)
    (hLipschitz : ∀ j,
      propagatedError j ≤ (1 + L * h) * error j)
    (hdecomposition : ∀ j,
      error (j + 1) ≤ propagatedError j +
        |∫ omega, observable j omega ∂restartLaw j -
          ∫ omega, observable j omega ∂referenceLaw j| +
        localDefect j) :
    ∀ j, error (j + 1) ≤ (1 + L * h) * error j +
      (observableBound j * eta j + localDefect j) := by
  intro j
  have hlawError :=
    abs_integral_sub_integral_le_of_boundedTestLawDistanceAtMost
      (hlaw j) (hobservableBound0 j) (observable j) (hmeasurable j)
        (hobservableBound j)
  calc
    error (j + 1) ≤ propagatedError j +
        |∫ omega, observable j omega ∂restartLaw j -
          ∫ omega, observable j omega ∂referenceLaw j| +
        localDefect j := hdecomposition j
    _ ≤ (1 + L * h) * error j +
        observableBound j * eta j + localDefect j :=
      add_le_add (add_le_add (hLipschitz j) hlawError) le_rfl
    _ = (1 + L * h) * error j +
        (observableBound j * eta j + localDefect j) := by ring

/-- Simultaneous second/fourth restart recurrences for phase laws close to the
canonical Haar law.  The displayed decomposition and Lipschitz hypotheses are
the exact additional dynamical inputs. -/
theorem canonicalHaar_amplitude_restart_recurrences
    {d : Type*} [Fintype d]
    (restartLaw : Nat → Measure (UnitAddTorus d))
    (amplitude : Nat → UnitAddTorus d → Complex)
    (secondError fourthError : Nat → Real)
    (propagatedSecondError propagatedFourthError : Nat → Real)
    (localSecondDefect localFourthDefect eta : Nat → Real)
    {M L h : Real}
    (hM : 0 ≤ M)
    (hlaw : ∀ j, IsCanonicalHaarRestartLawClose
      (restartLaw j) (eta j))
    (hamplitudeMeasurable : ∀ j, Measurable (amplitude j))
    (hamplitudeBound : ∀ j phase, ‖amplitude j phase‖ ≤ M)
    (hsecondLipschitz : ∀ j,
      propagatedSecondError j ≤ (1 + L * h) * secondError j)
    (hfourthLipschitz : ∀ j,
      propagatedFourthError j ≤ (1 + L * h) * fourthError j)
    (hsecondDecomposition : ∀ j,
      secondError (j + 1) ≤ propagatedSecondError j +
        |∫ phase, amplitudeSecondMomentObservable (amplitude j) phase
              ∂restartLaw j -
          ∫ phase, amplitudeSecondMomentObservable (amplitude j) phase
              ∂finitePhaseHaarLaw d| +
        localSecondDefect j)
    (hfourthDecomposition : ∀ j,
      fourthError (j + 1) ≤ propagatedFourthError j +
        |∫ phase, amplitudeFourthMomentObservable (amplitude j) phase
              ∂restartLaw j -
          ∫ phase, amplitudeFourthMomentObservable (amplitude j) phase
              ∂finitePhaseHaarLaw d| +
        localFourthDefect j) :
    (∀ j, secondError (j + 1) ≤ (1 + L * h) * secondError j +
      (M ^ 2 * eta j + localSecondDefect j)) ∧
    (∀ j, fourthError (j + 1) ≤ (1 + L * h) * fourthError j +
      (M ^ 4 * eta j + localFourthDefect j)) := by
  constructor
  · exact restart_recurrence_of_boundedTestLawDistance
      restartLaw (fun _ ↦ finitePhaseHaarLaw d)
      (fun j ↦ amplitudeSecondMomentObservable (amplitude j))
      secondError propagatedSecondError localSecondDefect eta (fun _ ↦ M ^ 2)
      (fun _ ↦ sq_nonneg M) hlaw
      (fun j ↦ measurable_amplitudeSecondMomentObservable
        (hamplitudeMeasurable j))
      (fun j ↦ abs_amplitudeSecondMomentObservable_le hM
        (hamplitudeBound j))
      hsecondLipschitz hsecondDecomposition
  · exact restart_recurrence_of_boundedTestLawDistance
      restartLaw (fun _ ↦ finitePhaseHaarLaw d)
      (fun j ↦ amplitudeFourthMomentObservable (amplitude j))
      fourthError propagatedFourthError localFourthDefect eta (fun _ ↦ M ^ 4)
      (fun _ ↦ by positivity) hlaw
      (fun j ↦ measurable_amplitudeFourthMomentObservable
        (hamplitudeMeasurable j))
      (fun j ↦ abs_amplitudeFourthMomentObservable_le hM
        (hamplitudeBound j))
      hfourthLipschitz hfourthDecomposition

/-- Explicit pushforward-law form for one canonical-Haar comparison.  The
source space may encode a conditional block history; only measurability of
the restart map and its bounded-test closeness to Haar are used. -/
theorem canonicalHaar_pushforward_amplitude_moment_discrepancy
    {Xi d : Type*} [MeasurableSpace Xi] [Fintype d]
    (source : Measure Xi)
    (restartMap : Xi → UnitAddTorus d) (hrestartMap : Measurable restartMap)
    {eta M : Real}
    (hclose : IsCanonicalHaarRestartLawClose
      (Measure.map restartMap source) eta)
    (hM : 0 ≤ M)
    (amplitude : UnitAddTorus d → Complex)
    (hamplitude : Measurable amplitude)
    (hbound : ∀ phase, ‖amplitude phase‖ ≤ M) :
    |∫ xi, amplitudeSecondMomentObservable amplitude (restartMap xi)
          ∂source -
        ∫ phase, amplitudeSecondMomentObservable amplitude phase
          ∂finitePhaseHaarLaw d| ≤ M ^ 2 * eta ∧
    |∫ xi, amplitudeFourthMomentObservable amplitude (restartMap xi)
          ∂source -
        ∫ phase, amplitudeFourthMomentObservable amplitude phase
          ∂finitePhaseHaarLaw d| ≤ M ^ 4 * eta := by
  constructor
  · exact abs_pushforward_integral_sub_integral_le source
      (finitePhaseHaarLaw d) restartMap hrestartMap hclose (sq_nonneg M)
      (amplitudeSecondMomentObservable amplitude)
      (measurable_amplitudeSecondMomentObservable hamplitude)
      (abs_amplitudeSecondMomentObservable_le hM hbound)
  · exact abs_pushforward_integral_sub_integral_le source
      (finitePhaseHaarLaw d) restartMap hrestartMap hclose
      (by positivity : 0 ≤ M ^ 4)
      (amplitudeFourthMomentObservable amplitude)
      (measurable_amplitudeFourthMomentObservable hamplitude)
      (abs_amplitudeFourthMomentObservable_le hM hbound)

/-! ## Physlib law-corrected restart defects -/

/-- Total second-moment defect: law mismatch plus the actual one-block
first-Duhamel moment defect. -/
def physlibLawCorrectedSecondMomentBlockDefect
    {N : Nat} [NeZero N]
    (m : PositiveMassConfig N) (mUpper kappa beta g H M : Real)
    (observed : Site N) (h eta : Real) : Real :=
  M ^ 2 * eta +
    physlibSecondMomentBlockDefect
      m mUpper kappa beta g H M observed h

/-- Total fourth-moment defect: law mismatch plus the actual one-block
first-Duhamel moment defect. -/
def physlibLawCorrectedFourthMomentBlockDefect
    {N : Nat} [NeZero N]
    (m : PositiveMassConfig N) (mUpper kappa beta g H M : Real)
    (observed : Site N) (h eta : Real) : Real :=
  M ^ 4 * eta +
    physlibFourthMomentBlockDefect
      m mUpper kappa beta g H M observed h

/-- Concrete sufficient conditions for the two restart recurrences used by
the multiblock layer.  `hlaw` is the unproved Hamiltonian-to-Haar input;
`hsecondLipschitz` and `hfourthLipschitz` are the unproved dynamical moment-map
stability inputs.  All remaining terms are explicit integrals or the already
proved one-block Physlib error. -/
theorem physlib_canonicalHaar_restart_recurrences
    {N : Nat} [NeZero N]
    (m : PositiveMassConfig N)
    {mUpper kappa beta g H M L h : Real}
    (observed : Site N)
    (restartLaw : Nat → Measure (UnitAddTorus (Site N)))
    (amplitude : Nat → UnitAddTorus (Site N) → Complex)
    (secondError fourthError : Nat → Real)
    (propagatedSecondError propagatedFourthError eta : Nat → Real)
    (hM : 0 ≤ M)
    (hlaw : ∀ j, IsCanonicalHaarRestartLawClose
      (restartLaw j) (eta j))
    (hamplitudeMeasurable : ∀ j, Measurable (amplitude j))
    (hamplitudeBound : ∀ j phase, ‖amplitude j phase‖ ≤ M)
    (hsecondLipschitz : ∀ j,
      propagatedSecondError j ≤ (1 + L * h) * secondError j)
    (hfourthLipschitz : ∀ j,
      propagatedFourthError j ≤ (1 + L * h) * fourthError j)
    (hsecondDecomposition : ∀ j,
      secondError (j + 1) ≤ propagatedSecondError j +
        |∫ phase, amplitudeSecondMomentObservable (amplitude j) phase
              ∂restartLaw j -
          ∫ phase, amplitudeSecondMomentObservable (amplitude j) phase
              ∂finitePhaseHaarLaw (Site N)| +
        physlibSecondMomentBlockDefect
          m mUpper kappa beta g H M observed h)
    (hfourthDecomposition : ∀ j,
      fourthError (j + 1) ≤ propagatedFourthError j +
        |∫ phase, amplitudeFourthMomentObservable (amplitude j) phase
              ∂restartLaw j -
          ∫ phase, amplitudeFourthMomentObservable (amplitude j) phase
              ∂finitePhaseHaarLaw (Site N)| +
        physlibFourthMomentBlockDefect
          m mUpper kappa beta g H M observed h) :
    (∀ j, secondError (j + 1) ≤ (1 + L * h) * secondError j +
      physlibLawCorrectedSecondMomentBlockDefect
        m mUpper kappa beta g H M observed h (eta j)) ∧
    (∀ j, fourthError (j + 1) ≤ (1 + L * h) * fourthError j +
      physlibLawCorrectedFourthMomentBlockDefect
        m mUpper kappa beta g H M observed h (eta j)) := by
  have hrecurrences := canonicalHaar_amplitude_restart_recurrences
    restartLaw amplitude secondError fourthError
      propagatedSecondError propagatedFourthError
      (fun _ ↦ physlibSecondMomentBlockDefect
        m mUpper kappa beta g H M observed h)
      (fun _ ↦ physlibFourthMomentBlockDefect
        m mUpper kappa beta g H M observed h)
      eta hM hlaw hamplitudeMeasurable hamplitudeBound
      hsecondLipschitz hfourthLipschitz
      hsecondDecomposition hfourthDecomposition
  simpa [physlibLawCorrectedSecondMomentBlockDefect,
    physlibLawCorrectedFourthMomentBlockDefect] using hrecurrences

/-- Multiblock consequence with the law defects kept nonuniform and visible
inside the exact accumulated sum. -/
theorem physlib_canonicalHaar_restart_multiblock_bounds
    {N : Nat} [NeZero N]
    (m : PositiveMassConfig N)
    {mUpper kappa beta g H M L h : Real}
    (observed : Site N)
    (restartLaw : Nat → Measure (UnitAddTorus (Site N)))
    (amplitude : Nat → UnitAddTorus (Site N) → Complex)
    (secondError fourthError : Nat → Real)
    (propagatedSecondError propagatedFourthError eta : Nat → Real)
    (hsecond0 : 0 ≤ secondError 0)
    (hfourth0 : 0 ≤ fourthError 0)
    (hM : 0 ≤ M) (hL : 0 ≤ L) (hh : 0 ≤ h)
    (heta0 : ∀ j, 0 ≤ eta j)
    (hblockError : 0 ≤
      shortTimeRPABlockError m mUpper kappa beta g H observed h)
    (hlaw : ∀ j, IsCanonicalHaarRestartLawClose
      (restartLaw j) (eta j))
    (hamplitudeMeasurable : ∀ j, Measurable (amplitude j))
    (hamplitudeBound : ∀ j phase, ‖amplitude j phase‖ ≤ M)
    (hsecondLipschitz : ∀ j,
      propagatedSecondError j ≤ (1 + L * h) * secondError j)
    (hfourthLipschitz : ∀ j,
      propagatedFourthError j ≤ (1 + L * h) * fourthError j)
    (hsecondDecomposition : ∀ j,
      secondError (j + 1) ≤ propagatedSecondError j +
        |∫ phase, amplitudeSecondMomentObservable (amplitude j) phase
              ∂restartLaw j -
          ∫ phase, amplitudeSecondMomentObservable (amplitude j) phase
              ∂finitePhaseHaarLaw (Site N)| +
        physlibSecondMomentBlockDefect
          m mUpper kappa beta g H M observed h)
    (hfourthDecomposition : ∀ j,
      fourthError (j + 1) ≤ propagatedFourthError j +
        |∫ phase, amplitudeFourthMomentObservable (amplitude j) phase
              ∂restartLaw j -
          ∫ phase, amplitudeFourthMomentObservable (amplitude j) phase
              ∂finitePhaseHaarLaw (Site N)| +
        physlibFourthMomentBlockDefect
          m mUpper kappa beta g H M observed h)
    (K : Nat) :
    secondError K ≤
        (secondError 0 +
          ∑ j ∈ Finset.range K,
            physlibLawCorrectedSecondMomentBlockDefect
              m mUpper kappa beta g H M observed h (eta j)) *
          Real.exp (L * h * (K : Real)) ∧
    fourthError K ≤
        (fourthError 0 +
          ∑ j ∈ Finset.range K,
            physlibLawCorrectedFourthMomentBlockDefect
              m mUpper kappa beta g H M observed h (eta j)) *
          Real.exp (L * h * (K : Real)) := by
  have hrecurrences := physlib_canonicalHaar_restart_recurrences
    m observed restartLaw amplitude secondError fourthError
      propagatedSecondError propagatedFourthError eta hM hlaw
      hamplitudeMeasurable hamplitudeBound hsecondLipschitz
      hfourthLipschitz hsecondDecomposition hfourthDecomposition
  have hsecondDefect0 : ∀ j, 0 ≤
      physlibLawCorrectedSecondMomentBlockDefect
        m mUpper kappa beta g H M observed h (eta j) := by
    intro j
    have hlocal : 0 ≤ physlibSecondMomentBlockDefect
        m mUpper kappa beta g H M observed h := by
      unfold physlibSecondMomentBlockDefect secondMomentBlockDefect
      exact mul_nonneg (mul_nonneg (by norm_num) hM) hblockError
    exact add_nonneg (mul_nonneg (sq_nonneg M) (heta0 j)) hlocal
  have hfourthDefect0 : ∀ j, 0 ≤
      physlibLawCorrectedFourthMomentBlockDefect
        m mUpper kappa beta g H M observed h (eta j) := by
    intro j
    have hlocal : 0 ≤ physlibFourthMomentBlockDefect
        m mUpper kappa beta g H M observed h := by
      unfold physlibFourthMomentBlockDefect fourthMomentBlockDefect
      exact mul_nonneg
        (mul_nonneg (by norm_num) (pow_nonneg hM 3)) hblockError
    exact add_nonneg (mul_nonneg (pow_nonneg hM 4) (heta0 j)) hlocal
  constructor
  · exact discrete_affine_error_exp_bound
      hsecond0 hL hh hsecondDefect0 hrecurrences.1 K
  · exact discrete_affine_error_exp_bound
      hfourth0 hL hh hfourthDefect0 hrecurrences.2 K

end

end ArchonPhysics.PhyslibFPUTRestartLawMomentPropagation
