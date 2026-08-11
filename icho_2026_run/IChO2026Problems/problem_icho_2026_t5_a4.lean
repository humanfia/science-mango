import Mathlib
import IChO2026Chem

/-!
# IChO 2026, Theory Problem T5 (Cardiolipins) — Subquestion 5.4

**Source.** 58th International Chemistry Olympiad, Tashkent, Uzbekistan, 2026,
Theory Problem T5, printed page Q5-3 (`T5_page-3.png`); page Q5-2
(`T5_page-2.png`) inspected and contains only subquestion 5.2 (structure
drawing), hence no data for 5.4.

**Statement (5.4).** 100 g of the fatty acid RCOOH (the fatty-acid residue of
the cardiolipin PL1) reacts with 181.0 g of iodine.  RCOOH also reacts in a
similar way with an unknown reagent X and forms an adduct whose iodine mass
fraction is 36.57 %.  **Determine the molecular formula of X.**

## Assumption / target split

Assumptions (source data plus explicit chemical bridges):

* `ArI` — standard atomic mass of iodine, 126.9 g·mol⁻¹, as printed on the
  exam periodic table and used throughout the official marking scheme (so the
  molar mass of I₂ is `2 · ArI = 253.8` g·mol⁻¹).
* `Halogen.atomicMass` — tabulated standard atomic masses of the four
  candidate halogen partners of iodine in a diatomic interhalogen (exam
  periodic-table data).
* `hI2` — the iodine-number experiment: each C=C double bond of RCOOH adds
  exactly one molecule of I₂ (the addition reaction recorded in the marking
  scheme), so a 100 g sample of an acid of molar mass `M` with `N` double
  bonds consumes `N · (100 / M) · (2 · ArI) = 181.0` grams of iodine.
* `hX` — the "reacts in a similar way" bridge: X is a diatomic interhalogen
  `I–Hal`, one iodine atom plus one halogen atom, adding one molecule per
  C=C bond.  This is carried by the explicit composition
  `x.formula = MolecularFormula.IHal h` for some halogen `h`; the branch
  `h = iodine` is exactly the molecular-iodine (I₂) alternative that the
  marking scheme checks and rejects.
* `hω` — the adduct mass-fraction measurement, expressed through the
  formula-derived mass laws `MolecularFormula.iodineMass` and
  `MolecularFormula.molarMass`: one mole of adduct contains
  `N · x.formula.iodineMass` grams of iodine and has molar mass
  `M + N · x.formula.molarMass`.  Because 36.57 % is a rounded readout, the
  hypothesis pins the true fraction to the printed value within half a unit
  of the last printed digit: `|ω − 0.3657| ≤ 0.00005`.  This tolerance is
  ~10³–10⁴ times smaller than the gap to any wrong branch (fluorine 0.4435,
  chlorine 0.4194, iodine 0.6441), so it does not preselect the answer.
* `hN : N = 2` — the number of C=C double bonds of RCOOH, the reusable
  conclusion of subquestion 5.3 (T5-A3).  Per the dependency policy
  `natural_language_prerequisite_only` it is restated here as an explicit
  hypothesis; the T5-A3 target file is not imported.
* Positivity side condition `0 < M` (a molar mass is positive); it also
  keeps every denominator nonzero.

Targets (what subquestion 5.4 asks to determine and support with
calculations):

1. `molarMass_of_iodine_experiment` — the marking scheme's intermediate
   value `M / N ≈ 140.2` g·mol⁻¹ per double bond (exact: 25380/181).
2. `experimental_halogen_mass_exact` and `experimental_halogen_mass_approx` —
   the marking-scheme calculation of the second halogen's atomic mass:
   `A = ArI / 0.3657 − ArI − 2 · ArI · 100 / 181.0 = 79.885…`, i.e.
   79.9 g·mol⁻¹ to the printed precision.
3. `X_formula_eq_IBr` — the requested public conclusion: the molecular
   formula of X is `MolecularFormula.IBr`, iodine monobromide.
4. `diiodine_adduct_fraction` — the marking scheme's consistency check: had
   X been molecular iodine I₂, the adduct's iodine mass fraction would have
   been exactly 181/281 = 0.6441… ≠ 0.3657, so that branch is excluded.

All scalar quantities are real numerical readouts in the source's units
(masses in grams, molar masses in g·mol⁻¹), following the convention of the
shared module `IChO2026Chem.Kinetics.BelousovZhabotinsky`.
-/

namespace IChO2026T5A4

/-- Standard atomic mass of iodine in g·mol⁻¹, as printed on the IChO 2026
periodic table and used by the official marking scheme (hence the molar mass
of I₂ is `2 · ArI = 253.8` g·mol⁻¹). -/
def ArI : ℝ := 126.9

/-- The candidate halogen partners of iodine in the unknown diatomic
interhalogen X = I–Hal.  (X reacts with RCOOH "in a similar way" to iodine,
so X adds across each C=C bond; the alternatives considered by the marking
scheme are the interhalogens and, via `Halogen.iodine`, molecular iodine
itself.) -/
inductive Halogen where
  | fluorine
  | chlorine
  | bromine
  | iodine
  deriving DecidableEq, Repr

/-- Standard atomic masses of the halogens in g·mol⁻¹ (exam periodic-table
data; 79.90 for bromine is the value the marking scheme matches against the
computed 79.9). -/
def Halogen.atomicMass : Halogen → ℝ
  | .fluorine => 19.00
  | .chlorine => 35.45
  | .bromine  => 79.90
  | .iodine   => ArI

/-- A molecular formula as an explicit composition: the atom count of each
candidate halogen element. -/
structure MolecularFormula where
  /-- Number of atoms of the given element in one molecule. -/
  count : Halogen → ℕ

namespace MolecularFormula

/-- The formula I–Hal: one iodine atom and one atom of the halogen `h`
(two iodine atoms when `h = iodine`, i.e. molecular iodine I₂). -/
def IHal (h : Halogen) : MolecularFormula where
  count e := (if e = h then 1 else 0) + (if e = .iodine then 1 else 0)

/-- The molecular formula IBr, iodine monobromide. -/
def IBr : MolecularFormula := IHal .bromine

/-- The molar-mass law of a formula: the sum over all elements of the atom
count times the standard atomic mass, in g·mol⁻¹. -/
def molarMass (f : MolecularFormula) : ℝ :=
  (f.count .fluorine : ℝ) * Halogen.atomicMass .fluorine +
  (f.count .chlorine : ℝ) * Halogen.atomicMass .chlorine +
  (f.count .bromine  : ℝ) * Halogen.atomicMass .bromine +
  (f.count .iodine   : ℝ) * Halogen.atomicMass .iodine

/-- The iodine-content law of a formula: the mass of iodine, in grams,
carried by one mole of a substance with that formula. -/
def iodineMass (f : MolecularFormula) : ℝ := (f.count .iodine : ℝ) * ArI

/-- The formula-derived molar-mass law for an interhalogen I–Hal:
`M(I–Hal) = ArI + Ar(Hal)` (in particular `M(I₂) = 2 · ArI`). -/
theorem molarMass_IHal (h : Halogen) :
    (IHal h).molarMass = ArI + Halogen.atomicMass h := by
  cases h <;> simp [IHal, molarMass, Halogen.atomicMass] <;> ring

/-- The formula-derived iodine-content law for an interhalogen I–Hal:
one mole of I–Hal contains one mole of iodine atoms (two for I₂). -/
theorem iodineMass_IHal (h : Halogen) :
    (IHal h).iodineMass = (if h = .iodine then 2 else 1) * ArI := by
  cases h <;> simp [IHal, iodineMass]

end MolecularFormula

/-- The unknown reagent X, carried by its explicit molecular formula. -/
structure ReagentX where
  /-- The molecular formula (elemental composition) of X. -/
  formula : MolecularFormula

/-- **Marking-scheme step 1.** The iodine-number experiment fixes the molar
mass of RCOOH per C=C double bond: `M = N · (2 · ArI) · 100 / 181.0`, i.e.
`M / N ≈ 140.2` g·mol⁻¹ (exact value 25380/181 = 140.221…, within 0.03 of
the marking scheme's rounded 140.2). -/
theorem molarMass_of_iodine_experiment
    (N : ℕ) (M : ℝ) (hM : 0 < M) (hN : N = 2)
    (hI2 : (N : ℝ) * (100 / M) * (2 * ArI) = 181.0) :
    M = (N : ℝ) * (2 * ArI) * 100 / 181.0 ∧
    |M / (N : ℝ) - 140.2| ≤ 0.03 := by
  subst hN
  have hM' : M ≠ 0 := hM.ne'
  have hMval : M = 50760 / 181 := by
    field_simp at hI2
    norm_num [ArI] at hI2
    linarith
  refine ⟨?_, ?_⟩
  · rw [hMval]
    norm_num [ArI]
  · rw [hMval, abs_le]
    constructor <;> norm_num

/-- **Marking-scheme step 2 (exact).**  Solving the adduct mass-fraction
equation `0.3657 = N · ArI / (M + N · (ArI + A))` together with the
iodine-number relation gives the experimental atomic mass `A` of the second
halogen of X in closed form (numerically 79.885 g·mol⁻¹). -/
theorem experimental_halogen_mass_exact
    (N : ℕ) (M A : ℝ) (hM : 0 < M) (hA : 0 < A) (hN : N = 2)
    (hI2 : (N : ℝ) * (100 / M) * (2 * ArI) = 181.0)
    (hω : (N : ℝ) * ArI / (M + (N : ℝ) * (ArI + A)) = 0.3657) :
    A = ArI / 0.3657 - ArI - (2 * ArI) * 100 / 181.0 := by
  subst hN
  push_cast at hI2 hω
  have hM' : M ≠ 0 := hM.ne'
  have hArI : (0 : ℝ) < ArI := by norm_num [ArI]
  have hD : (M + (2 : ℝ) * (ArI + A)) ≠ 0 := by
    have hpos : (0 : ℝ) < M + (2 : ℝ) * (ArI + A) := by positivity
    exact hpos.ne'
  have e1 : (2 : ℝ) * ArI = 0.3657 * (M + (2 : ℝ) * (ArI + A)) := by
    rwa [div_eq_iff hD] at hω
  have hMval : M = 50760 / 181 := by
    field_simp at hI2
    norm_num [ArI] at hI2
    linarith
  have eA : A = ArI / 0.3657 - ArI - M / 2 := by
    field_simp
    linarith [e1]
  rw [eA, hMval]
  norm_num [ArI]

/-- **Marking-scheme step 2 (printed value).**  The experimental atomic mass
of the second halogen rounds to the marking scheme's `A_Hal = 79.9` g·mol⁻¹. -/
theorem experimental_halogen_mass_approx
    (N : ℕ) (M A : ℝ) (hM : 0 < M) (hA : 0 < A) (hN : N = 2)
    (hI2 : (N : ℝ) * (100 / M) * (2 * ArI) = 181.0)
    (hω : (N : ℝ) * ArI / (M + (N : ℝ) * (ArI + A)) = 0.3657) :
    |A - 79.9| ≤ 0.02 := by
  have eA := experimental_halogen_mass_exact N M A hM hA hN hI2 hω
  rw [eA, abs_le]
  constructor <;> norm_num [ArI]

/-- **Requested conclusion (public).**  The molecular formula of X is IBr,
iodine monobromide.  Among the four compositions I–F, I–Cl, I–Br and I₂,
only IBr makes the formula-derived iodine mass fraction of the adduct
consistent with the measured (rounded) value 36.57 %: the fractions for the
other branches are 0.4435, 0.4194 and 0.6441 respectively, each wildly
outside the rounding tolerance, while IBr gives 0.36568…, within
`0.00005` of the readout. -/
theorem X_formula_eq_IBr
    (x : ReagentX) (N : ℕ) (M : ℝ)
    (hM : 0 < M) (hN : N = 2)
    (hI2 : (N : ℝ) * (100 / M) * (2 * ArI) = 181.0)
    (hX : ∃ h : Halogen, x.formula = MolecularFormula.IHal h)
    (hω : |(N : ℝ) * x.formula.iodineMass /
        (M + (N : ℝ) * x.formula.molarMass) - 0.3657| ≤ 0.00005) :
    x.formula = MolecularFormula.IBr := by
  obtain ⟨h, hh⟩ := hX
  rw [hh] at hω ⊢
  subst hN
  push_cast at hI2 hω
  have hM' : M ≠ 0 := hM.ne'
  have hMval : M = 50760 / 181 := by
    field_simp at hI2
    norm_num [ArI] at hI2
    linarith
  cases h with
  | fluorine =>
      have h1 : (MolecularFormula.IHal .fluorine).iodineMass = 126.9 := by
        norm_num [MolecularFormula.iodineMass, MolecularFormula.IHal, ArI]
      have h2 : (MolecularFormula.IHal .fluorine).molarMass = 145.9 := by
        norm_num [MolecularFormula.molarMass, MolecularFormula.IHal,
          Halogen.atomicMass, ArI]
      rw [h1, h2, hMval, abs_le] at hω
      norm_num at hω
  | chlorine =>
      have h1 : (MolecularFormula.IHal .chlorine).iodineMass = 126.9 := by
        norm_num [MolecularFormula.iodineMass, MolecularFormula.IHal, ArI]
      have h2 : (MolecularFormula.IHal .chlorine).molarMass = 162.35 := by
        norm_num [MolecularFormula.molarMass, MolecularFormula.IHal,
          Halogen.atomicMass, ArI]
      rw [h1, h2, hMval, abs_le] at hω
      norm_num at hω
  | bromine => rfl
  | iodine =>
      have h1 : (MolecularFormula.IHal .iodine).iodineMass = 253.8 := by
        norm_num [MolecularFormula.iodineMass, MolecularFormula.IHal, ArI]
      have h2 : (MolecularFormula.IHal .iodine).molarMass = 253.8 := by
        norm_num [MolecularFormula.molarMass, MolecularFormula.IHal,
          Halogen.atomicMass, ArI]
      rw [h1, h2, hMval, abs_le] at hω
      norm_num at hω

/-- **Consistency check (excluded branch).**  Had X been molecular iodine
I₂, each C=C bond would add `2 · ArI` grams of pure iodine and the adduct's
iodine mass fraction would be exactly 181/281 = 0.6441…, which differs from
the measured 0.3657; the I₂ alternative is therefore refuted by the data. -/
theorem diiodine_adduct_fraction
    (N : ℕ) (M : ℝ) (hM : 0 < M) (hN : N = 2)
    (hI2 : (N : ℝ) * (100 / M) * (2 * ArI) = 181.0) :
    (N : ℝ) * (2 * ArI) / (M + (N : ℝ) * (2 * ArI)) = (181 : ℝ) / 281 ∧
    (181 : ℝ) / 281 ≠ (0.3657 : ℝ) := by
  subst hN
  push_cast at hI2 ⊢
  have hM' : M ≠ 0 := hM.ne'
  have hMval : M = 50760 / 181 := by
    field_simp at hI2
    norm_num [ArI] at hI2
    linarith
  refine ⟨?_, ?_⟩
  · rw [hMval]
    norm_num [ArI]
  · norm_num

end IChO2026T5A4
