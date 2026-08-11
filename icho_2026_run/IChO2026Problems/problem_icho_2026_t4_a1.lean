import Mathlib
import IChO2026Chem

/-!
# IChO 2026 T4-A1: atomic abundance of uranium-235

Atomic masses below are numerical values in atomic mass units (a.u.) and
atomic abundances are dimensionless fractions.  The named isotope constructors
retain the chemical identity of the two uranium isotopes, while their masses
and abundances are scalar readouts.

The printed question lists the isotope masses.  The average atomic mass
`238.03 a.u.` used in the official calculation is represented as empirical
periodic-table data, rather than as a value of the abundance to be calculated.
-/

namespace IChO2026Problems.T4A1

/-- The two uranium isotopes admitted by the T4-A1 approximation. -/
private inductive UraniumIsotope where
  | uranium235
  | uranium238
  deriving DecidableEq, Fintype, Repr

/-- Numerical atomic mass, expressed in atomic mass units. -/
private abbrev AtomicMass := ℝ

/-- Dimensionless atomic fraction of an isotope in one natural-uranium sample. -/
private abbrev AtomicFraction := ℝ

/--
The assumed two-isotope composition of natural uranium.  Since
`UraniumIsotope` has exactly the two stated constructors, the exhaustive
equation explicitly records the question's assumption that no other isotope
contributes to the sample.
-/
private structure NaturalUraniumSample where
  atomicFraction : UraniumIsotope → AtomicFraction
  atomicFraction_nonnegative : ∀ isotope, 0 ≤ atomicFraction isotope
  atomicFractions_exhaustive :
    atomicFraction .uranium235 + atomicFraction .uranium238 = 1

/--
Atomic-mass data for uranium.  The average is a separate empirical readout;
the requested abundance is deliberately not a field of this structure.
-/
private structure UraniumAtomicMassData where
  isotopeAtomicMass : UraniumIsotope → AtomicMass
  averageAtomicMass : AtomicMass

/--
The isotope masses stated in T4-A1 and the periodic-table average atomic mass
used by the official calculation.  Decimal data are retained as their exact
printed rational values in `ℝ`.
-/
private def UraniumAtomicMassData.matchesOfficialCalculation
    (data : UraniumAtomicMassData) : Prop :=
  data.isotopeAtomicMass .uranium235 = 235.04 ∧
    data.isotopeAtomicMass .uranium238 = 238.05 ∧
      data.averageAtomicMass = 238.03

/-- The abundance-weighted atomic mass in the two-isotope approximation. -/
private def weightedAtomicMass (sample : NaturalUraniumSample)
    (data : UraniumAtomicMassData) : AtomicMass :=
  sample.atomicFraction .uranium235 * data.isotopeAtomicMass .uranium235 +
    sample.atomicFraction .uranium238 * data.isotopeAtomicMass .uranium238

/--
The governing mass-balance law for the sample.  It is an explicit hypothesis
because the law, not an opaque assertion of the requested numerical answer,
bridges the isotope data to the abundance.
-/
private def NaturalUraniumSample.obeysAtomicMassBalance
    (sample : NaturalUraniumSample) (data : UraniumAtomicMassData) : Prop :=
  data.averageAtomicMass = weightedAtomicMass sample data

/--
A fraction agrees with a percentage displayed to two decimal places when the
percentage is within half a last displayed digit.  This records the
approximate presentation `0.66 %` without identifying it with the exact
fraction.
-/
private def ReportsPercentageToTwoDecimalPlaces
    (fraction reportedPercent : ℝ) : Prop :=
  |100 * fraction - reportedPercent| < 1 / 200

/--
Solving the two-isotope weighted-average equation first expresses the
uranium-235 atomic fraction in terms of the supplied masses.  The denominator
is nonzero for the two distinct isotope masses stated in the problem.
-/
private theorem uranium235_atomic_fraction_formula
    (sample : NaturalUraniumSample)
    (data : UraniumAtomicMassData)
    (hdata : data.matchesOfficialCalculation)
    (hbalance : sample.obeysAtomicMassBalance data) :
    sample.atomicFraction .uranium235 =
      (data.averageAtomicMass - data.isotopeAtomicMass .uranium238) /
        (data.isotopeAtomicMass .uranium235 -
          data.isotopeAtomicMass .uranium238) := by
  rcases hdata with ⟨hmass235, hmass238, havg⟩
  unfold NaturalUraniumSample.obeysAtomicMassBalance weightedAtomicMass at hbalance
  rw [hmass235, hmass238, havg] at hbalance ⊢
  norm_num at hbalance ⊢
  nlinarith [sample.atomicFractions_exhaustive]

/--
T4-A1: the supplied isotope masses, the periodic-table average, and the
two-isotope mass balance determine the atomic abundance of `²³⁵U` as
`2 / 301`.  Its percentage agrees with the reported `0.66 %` at the printed
two-decimal precision.
-/
theorem uranium235_atomic_abundance
    (sample : NaturalUraniumSample)
    (data : UraniumAtomicMassData)
    (hdata : data.matchesOfficialCalculation)
    (hbalance : sample.obeysAtomicMassBalance data) :
    sample.atomicFraction .uranium235 = (2 : ℝ) / 301 ∧
      ReportsPercentageToTwoDecimalPlaces
        (sample.atomicFraction .uranium235) 0.66 := by
  have hfraction : sample.atomicFraction .uranium235 = (2 : ℝ) / 301 := by
    calc
      sample.atomicFraction .uranium235 =
          (data.averageAtomicMass - data.isotopeAtomicMass .uranium238) /
            (data.isotopeAtomicMass .uranium235 -
              data.isotopeAtomicMass .uranium238) :=
        uranium235_atomic_fraction_formula sample data hdata hbalance
      _ = (2 : ℝ) / 301 := by
        rcases hdata with ⟨hmass235, hmass238, havg⟩
        rw [hmass235, hmass238, havg]
        norm_num
  constructor
  · exact hfraction
  · rw [hfraction]
    norm_num [ReportsPercentageToTwoDecimalPlaces]

end IChO2026Problems.T4A1
