import ArchonPhysics.PhyslibFPUTCouplingLawMomentControl
import ArchonPhysics.PhyslibFPUTRestartLawMomentPropagation

/-!
# Coupling-based multiblock Physlib RPA restart

This module replaces the strong total-variation/Haar restart assumption by an
explicit, blockwise coupling certificate.  On one common probability space,
the actual and reference amplitudes are within `delta_j` outside a measurable
bad set of probability at most `p_j`, and both amplitudes are bounded by `M`.

The resulting restart defects are

* `2 M delta_j + 2 M^2 p_j + oneBlockSecondDefect`, and
* `4 M^3 delta_j + 2 M^4 p_j + oneBlockFourthDefect`.

They are then accumulated by the nonuniform discrete Grönwall theorem.  The
certificate's existence and the displayed moment-map Lipschitz/decomposition
hypotheses are not derived from the Hamiltonian flow here.
-/

namespace ArchonPhysics.PhyslibFPUTCouplingMultiblockRestart

open MeasureTheory
open ArchonPhysics
open ArchonPhysics.CoerciveHamiltonianPhyslib
open ArchonPhysics.Lattice
open ArchonPhysics.PhyslibFPUTCouplingLawMomentControl
open ArchonPhysics.PhyslibFPUTMultiblockRPAMomentPropagation
open ArchonPhysics.PhyslibFPUTShortTimeRPAMomentStability

noncomputable section

/-! ## Minimal blockwise coupling certificate -/

/-- A common-source coupling certificate for every restart block.  No field
asserts that such a certificate exists for an actual Hamiltonian flow. -/
structure AmplitudeCouplingRestartCertificate
    {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) (M : Real) where
  actual : Nat → Omega → Complex
  reference : Nat → Omega → Complex
  bad : Nat → Set Omega
  delta : Nat → Real
  failureProbability : Nat → Real
  actual_measurable : ∀ j, Measurable (actual j)
  reference_measurable : ∀ j, Measurable (reference j)
  bad_measurable : ∀ j, MeasurableSet (bad j)
  delta_nonneg : ∀ j, 0 ≤ delta j
  bad_probability : ∀ j, mu.real (bad j) ≤ failureProbability j
  near_on_good : ∀ j omega, omega ∉ bad j →
    ‖actual j omega - reference j omega‖ ≤ delta j
  actual_bound : ∀ j omega, ‖actual j omega‖ ≤ M
  reference_bound : ∀ j omega, ‖reference j omega‖ ≤ M

namespace AmplitudeCouplingRestartCertificate

variable {Omega : Type*} [MeasurableSpace Omega]
  {mu : Measure Omega} {M : Real}

/-- Pushforward law of the actual amplitude at block `j`. -/
def actualLaw (certificate : AmplitudeCouplingRestartCertificate mu M)
    (j : Nat) : Measure Complex :=
  Measure.map (certificate.actual j) mu

/-- Pushforward law of the reference amplitude at block `j`. -/
def referenceLaw (certificate : AmplitudeCouplingRestartCertificate mu M)
    (j : Nat) : Measure Complex :=
  Measure.map (certificate.reference j) mu

theorem failureProbability_nonneg
    (certificate : AmplitudeCouplingRestartCertificate mu M) (j : Nat) :
    0 ≤ certificate.failureProbability j :=
  measureReal_nonneg.trans (certificate.bad_probability j)

end AmplitudeCouplingRestartCertificate

/-! ## Coupling defects -/

/-- Pure coupling contribution to a second-moment restart defect. -/
def couplingSecondMomentDefect (M delta p : Real) : Real :=
  2 * M * delta + 2 * M ^ 2 * p

/-- Pure coupling contribution to a fourth-moment restart defect. -/
def couplingFourthMomentDefect (M delta p : Real) : Real :=
  4 * M ^ 3 * delta + 2 * M ^ 4 * p

theorem couplingSecondMomentDefect_nonneg
    {M delta p : Real} (hM : 0 ≤ M) (hdelta : 0 ≤ delta)
    (hp : 0 ≤ p) :
    0 ≤ couplingSecondMomentDefect M delta p := by
  unfold couplingSecondMomentDefect
  positivity

theorem couplingFourthMomentDefect_nonneg
    {M delta p : Real} (hM : 0 ≤ M) (hdelta : 0 ≤ delta)
    (hp : 0 ≤ p) :
    0 ≤ couplingFourthMomentDefect M delta p := by
  unfold couplingFourthMomentDefect
  positivity

/-- Coupling contribution plus the actual Physlib one-block second-moment
defect. -/
def physlibCouplingSecondMomentRestartDefect
    {N : Nat} [NeZero N]
    (m : PositiveMassConfig N) (mUpper kappa beta g H M : Real)
    (observed : Site N) (h delta p : Real) : Real :=
  couplingSecondMomentDefect M delta p +
    physlibSecondMomentBlockDefect
      m mUpper kappa beta g H M observed h

/-- Coupling contribution plus the actual Physlib one-block fourth-moment
defect. -/
def physlibCouplingFourthMomentRestartDefect
    {N : Nat} [NeZero N]
    (m : PositiveMassConfig N) (mUpper kappa beta g H M : Real)
    (observed : Site N) (h delta p : Real) : Real :=
  couplingFourthMomentDefect M delta p +
    physlibFourthMomentBlockDefect
      m mUpper kappa beta g H M observed h

/-! ## Certificate-to-moment law control -/

/-- Every block certificate gives the advertised second/fourth pushforward-law
moment errors. -/
theorem certificate_pushforward_second_fourth_moment_errors
    {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    {M : Real} (hM : 0 ≤ M)
    (certificate : AmplitudeCouplingRestartCertificate mu M)
    (j : Nat) :
    |∫ z, Complex.normSq z ∂certificate.actualLaw j -
        ∫ z, Complex.normSq z ∂certificate.referenceLaw j| ≤
      couplingSecondMomentDefect M
        (certificate.delta j) (certificate.failureProbability j) ∧
    |∫ z, Complex.normSq z ^ 2 ∂certificate.actualLaw j -
        ∫ z, Complex.normSq z ^ 2 ∂certificate.referenceLaw j| ≤
      couplingFourthMomentDefect M
        (certificate.delta j) (certificate.failureProbability j) := by
  simpa [AmplitudeCouplingRestartCertificate.actualLaw,
    AmplitudeCouplingRestartCertificate.referenceLaw,
    couplingSecondMomentDefect, couplingFourthMomentDefect] using
    pushforward_second_fourth_moment_errors
      mu (certificate.actual j) (certificate.reference j)
      (certificate.actual_measurable j) (certificate.reference_measurable j)
      (certificate.bad j) (certificate.bad_measurable j)
      (certificate.delta_nonneg j) hM (certificate.bad_probability j)
      (certificate.near_on_good j) (certificate.actual_bound j)
      (certificate.reference_bound j)

/-! ## Coupling certificate to restart recurrence -/

/-- The coupling certificate, moment-map Lipschitz bounds, and an explicit
triangle decomposition imply the two affine restart recurrences with the
advertised total defects. -/
theorem physlib_restart_recurrences_of_coupling_certificate
    {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    {N : Nat} [NeZero N]
    (m : PositiveMassConfig N)
    {mUpper kappa beta g H M L h : Real}
    (observed : Site N)
    (certificate : AmplitudeCouplingRestartCertificate mu M)
    (secondError fourthError : Nat → Real)
    (propagatedSecondError propagatedFourthError : Nat → Real)
    (hM : 0 ≤ M)
    (hsecondLipschitz : ∀ j,
      propagatedSecondError j ≤ (1 + L * h) * secondError j)
    (hfourthLipschitz : ∀ j,
      propagatedFourthError j ≤ (1 + L * h) * fourthError j)
    (hsecondDecomposition : ∀ j,
      secondError (j + 1) ≤ propagatedSecondError j +
        |∫ z, Complex.normSq z ∂certificate.actualLaw j -
          ∫ z, Complex.normSq z ∂certificate.referenceLaw j| +
        physlibSecondMomentBlockDefect
          m mUpper kappa beta g H M observed h)
    (hfourthDecomposition : ∀ j,
      fourthError (j + 1) ≤ propagatedFourthError j +
        |∫ z, Complex.normSq z ^ 2 ∂certificate.actualLaw j -
          ∫ z, Complex.normSq z ^ 2 ∂certificate.referenceLaw j| +
        physlibFourthMomentBlockDefect
          m mUpper kappa beta g H M observed h) :
    (∀ j, secondError (j + 1) ≤ (1 + L * h) * secondError j +
      physlibCouplingSecondMomentRestartDefect
        m mUpper kappa beta g H M observed h
          (certificate.delta j) (certificate.failureProbability j)) ∧
    (∀ j, fourthError (j + 1) ≤ (1 + L * h) * fourthError j +
      physlibCouplingFourthMomentRestartDefect
        m mUpper kappa beta g H M observed h
          (certificate.delta j) (certificate.failureProbability j)) := by
  constructor
  · intro j
    have hmoment :=
      (certificate_pushforward_second_fourth_moment_errors
        mu hM certificate j).1
    calc
      secondError (j + 1) ≤ propagatedSecondError j +
          |∫ z, Complex.normSq z ∂certificate.actualLaw j -
            ∫ z, Complex.normSq z ∂certificate.referenceLaw j| +
          physlibSecondMomentBlockDefect
            m mUpper kappa beta g H M observed h := hsecondDecomposition j
      _ ≤ (1 + L * h) * secondError j +
          couplingSecondMomentDefect M
            (certificate.delta j) (certificate.failureProbability j) +
          physlibSecondMomentBlockDefect
            m mUpper kappa beta g H M observed h :=
        add_le_add (add_le_add (hsecondLipschitz j) hmoment) le_rfl
      _ = (1 + L * h) * secondError j +
          physlibCouplingSecondMomentRestartDefect
            m mUpper kappa beta g H M observed h
              (certificate.delta j) (certificate.failureProbability j) := by
        rw [physlibCouplingSecondMomentRestartDefect]
        ring
  · intro j
    have hmoment :=
      (certificate_pushforward_second_fourth_moment_errors
        mu hM certificate j).2
    calc
      fourthError (j + 1) ≤ propagatedFourthError j +
          |∫ z, Complex.normSq z ^ 2 ∂certificate.actualLaw j -
            ∫ z, Complex.normSq z ^ 2 ∂certificate.referenceLaw j| +
          physlibFourthMomentBlockDefect
            m mUpper kappa beta g H M observed h := hfourthDecomposition j
      _ ≤ (1 + L * h) * fourthError j +
          couplingFourthMomentDefect M
            (certificate.delta j) (certificate.failureProbability j) +
          physlibFourthMomentBlockDefect
            m mUpper kappa beta g H M observed h :=
        add_le_add (add_le_add (hfourthLipschitz j) hmoment) le_rfl
      _ = (1 + L * h) * fourthError j +
          physlibCouplingFourthMomentRestartDefect
            m mUpper kappa beta g H M observed h
              (certificate.delta j) (certificate.failureProbability j) := by
        rw [physlibCouplingFourthMomentRestartDefect]
        ring

/-! ## Nonuniform multiblock accumulation -/

/-- Nonuniform discrete Grönwall accumulation of the coupling-corrected
Physlib defects. -/
theorem physlib_coupling_restart_multiblock_bounds
    {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    {N : Nat} [NeZero N]
    (m : PositiveMassConfig N)
    {mUpper kappa beta g H M L h : Real}
    (observed : Site N)
    (certificate : AmplitudeCouplingRestartCertificate mu M)
    (secondError fourthError : Nat → Real)
    (propagatedSecondError propagatedFourthError : Nat → Real)
    (hsecond0 : 0 ≤ secondError 0)
    (hfourth0 : 0 ≤ fourthError 0)
    (hM : 0 ≤ M) (hL : 0 ≤ L) (hh : 0 ≤ h)
    (hblockError : 0 ≤
      shortTimeRPABlockError m mUpper kappa beta g H observed h)
    (hsecondLipschitz : ∀ j,
      propagatedSecondError j ≤ (1 + L * h) * secondError j)
    (hfourthLipschitz : ∀ j,
      propagatedFourthError j ≤ (1 + L * h) * fourthError j)
    (hsecondDecomposition : ∀ j,
      secondError (j + 1) ≤ propagatedSecondError j +
        |∫ z, Complex.normSq z ∂certificate.actualLaw j -
          ∫ z, Complex.normSq z ∂certificate.referenceLaw j| +
        physlibSecondMomentBlockDefect
          m mUpper kappa beta g H M observed h)
    (hfourthDecomposition : ∀ j,
      fourthError (j + 1) ≤ propagatedFourthError j +
        |∫ z, Complex.normSq z ^ 2 ∂certificate.actualLaw j -
          ∫ z, Complex.normSq z ^ 2 ∂certificate.referenceLaw j| +
        physlibFourthMomentBlockDefect
          m mUpper kappa beta g H M observed h)
    (K : Nat) :
    secondError K ≤
        (secondError 0 +
          ∑ j ∈ Finset.range K,
            physlibCouplingSecondMomentRestartDefect
              m mUpper kappa beta g H M observed h
                (certificate.delta j) (certificate.failureProbability j)) *
          Real.exp (L * h * (K : Real)) ∧
    fourthError K ≤
        (fourthError 0 +
          ∑ j ∈ Finset.range K,
            physlibCouplingFourthMomentRestartDefect
              m mUpper kappa beta g H M observed h
                (certificate.delta j) (certificate.failureProbability j)) *
          Real.exp (L * h * (K : Real)) := by
  have hrecurrences := physlib_restart_recurrences_of_coupling_certificate
    mu m observed certificate secondError fourthError
      propagatedSecondError propagatedFourthError hM
      hsecondLipschitz hfourthLipschitz
      hsecondDecomposition hfourthDecomposition
  have hlocalSecond : 0 ≤ physlibSecondMomentBlockDefect
      m mUpper kappa beta g H M observed h := by
    unfold physlibSecondMomentBlockDefect secondMomentBlockDefect
    exact mul_nonneg (mul_nonneg (by norm_num) hM) hblockError
  have hlocalFourth : 0 ≤ physlibFourthMomentBlockDefect
      m mUpper kappa beta g H M observed h := by
    unfold physlibFourthMomentBlockDefect fourthMomentBlockDefect
    exact mul_nonneg
      (mul_nonneg (by norm_num) (pow_nonneg hM 3)) hblockError
  have hsecondDefect0 : ∀ j, 0 ≤
      physlibCouplingSecondMomentRestartDefect
        m mUpper kappa beta g H M observed h
          (certificate.delta j) (certificate.failureProbability j) := by
    intro j
    exact add_nonneg
      (couplingSecondMomentDefect_nonneg hM (certificate.delta_nonneg j)
        (certificate.failureProbability_nonneg j))
      hlocalSecond
  have hfourthDefect0 : ∀ j, 0 ≤
      physlibCouplingFourthMomentRestartDefect
        m mUpper kappa beta g H M observed h
          (certificate.delta j) (certificate.failureProbability j) := by
    intro j
    exact add_nonneg
      (couplingFourthMomentDefect_nonneg hM (certificate.delta_nonneg j)
        (certificate.failureProbability_nonneg j))
      hlocalFourth
  constructor
  · exact discrete_affine_error_exp_bound
      hsecond0 hL hh hsecondDefect0 hrecurrences.1 K
  · exact discrete_affine_error_exp_bound
      hfourth0 hL hh hfourthDefect0 hrecurrences.2 K

end

end ArchonPhysics.PhyslibFPUTCouplingMultiblockRestart
