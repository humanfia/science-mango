import Mathlib

/-!
# IChO 2026, Theory Problem T4 ("The nuclear past of Uzbekistan"), subquestion 4.1

## Source contract

58th International Chemistry Olympiad, Tashkent, Uzbekistan, 2026.
Subquestion 4.1 (2.0 pt) asks:

> **Calculate** the atomic abundance of ²³⁵U in natural uranium, assuming it
> consists only of isotopes ²³⁵U (235.04 a.u.) and ²³⁸U (238.05 a.u.).

The shared problem context (page image `T4_page-1.png`) states that natural
uranium consists primarily of the two isotopes ²³⁵U and ²³⁸U and that ²³⁵U is
responsible for sustaining nuclear fission reactions.  The official marking
scheme additionally substitutes the average atomic mass of uranium from the
periodic table supplied with the examination, 238.03 a.u., into the mixing
equation

> `238.03 = x * 235.04 + (1 - x) * 238.05`   (equation (1) of the rubric),

and solves it to `x = 0.02 / 3.01 ≈ 0.00664`, quoting the atomic abundance of
²³⁵U as `0.66 %` (a slightly lower estimate than the commonly accepted
`0.72 %`, influenced by the rounded input data).  One rubric point is awarded
for equation (1) and one for the final answer.

## Assumption / target split

* Assumptions (all sourced): the two-isotope species type `UraniumIsotope`;
  the printed isotope mass readouts `UraniumIsotope.mass`; the periodic-table
  average atomic mass `naturalUraniumAverageMass = 238.03` a.u.; and an
  isotopic composition whose atom fractions are nonnegative, normalized (the
  sample consists only of the two isotopes), and compatible with the
  abundance-weighted average-mass law `averageAtomicMass`.
* Target (conclusion only): the ²³⁵U atom fraction equals `0.02 / 3.01`, and
  expressed as a percentage it is `0.66 %` to the precision quoted in the
  official answer (`|100 * x - 0.66| ≤ 0.005`).

All quantities are real numerical readouts in the source's units (atomic mass
units for masses, dimensionless atom fractions for abundances), following the
project convention used in `IChO2026Chem.Kinetics.BelousovZhabotinsky`.
-/

namespace IChO2026Problems.T4.A1

/-- The isotopes that natural uranium is assumed to consist of in subquestion
4.1: uranium-235 and uranium-238. -/
inductive UraniumIsotope where
  | u235
  | u238
  deriving DecidableEq, Repr

/-- The isotope mass readout in atomic mass units (a.u.), as printed in the
statement of subquestion 4.1: 235.04 a.u. for ²³⁵U and 238.05 a.u. for ²³⁸U. -/
def UraniumIsotope.mass : UraniumIsotope → ℝ
  | .u235 => 235.04
  | .u238 => 238.05

/-- An isotopic composition of a uranium sample: the atom fraction (atomic
abundance) of each uranium isotope in the sample. -/
abbrev IsotopicComposition := UraniumIsotope → ℝ

/-- The average atomic mass of natural uranium, 238.03 a.u.: the
periodic-table readout that the official marking scheme substitutes into the
mixing equation. -/
def naturalUraniumAverageMass : ℝ := 238.03

/-- The average-mass (mixing) law for a two-isotope uranium sample: the
average atomic mass is the atom-fraction-weighted sum of the isotope masses.
Under the normalization `comp .u235 + comp .u238 = 1` this is equation (1) of
the official rubric, `238.03 = x * 235.04 + (1 - x) * 238.05` with
`x = comp .u235`. -/
def averageAtomicMass (comp : IsotopicComposition) : ℝ :=
  comp .u235 * UraniumIsotope.mass .u235 + comp .u238 * UraniumIsotope.mass .u238

/-- **IChO 2026, T4, subquestion 4.1.**  The atomic abundance of ²³⁵U in
natural uranium.

If an isotopic composition of natural uranium

* assigns a nonnegative atom fraction to each of the two isotopes
  (`hnonneg`),
* is normalized, because the sample is assumed to consist only of ²³⁵U and
  ²³⁸U (`hnormalized`), and
* reproduces the periodic-table average atomic mass 238.03 a.u. under the
  average-mass law (`hmixing`),

then the atomic abundance of ²³⁵U is exactly `0.02 / 3.01 ≈ 0.00664`, i.e.
`0.66 %` at the precision quoted by the official answer. -/
theorem atomic_abundance_u235 (comp : IsotopicComposition)
    (hnonneg : ∀ i, 0 ≤ comp i)
    (hnormalized : comp .u235 + comp .u238 = 1)
    (hmixing : averageAtomicMass comp = naturalUraniumAverageMass) :
    comp .u235 = 0.02 / 3.01 ∧ |100 * comp .u235 - 0.66| ≤ 0.005 := by
  -- Unfold the average-mass law and the periodic-table readout to the
  -- rubric's mixing equation: `comp .u235 * 235.04 + comp .u238 * 238.05 = 238.03`.
  have hmix : comp .u235 * 235.04 + comp .u238 * 238.05 = 238.03 := hmixing
  -- Normalization rewrites the ²³⁸U fraction as `1 - comp .u235`, giving
  -- equation (1) of the rubric in the single unknown `comp .u235`.
  have h238 : comp .u238 = 1 - comp .u235 := by linarith
  rw [h238] at hmix
  -- The linear equation `comp .u235 * (235.04 - 238.05) = 238.03 - 238.05`
  -- solves to `comp .u235 = 0.02 / 3.01`.
  have hx : comp .u235 = 0.02 / 3.01 := by linarith
  refine ⟨hx, ?_⟩
  -- As a percentage, `100 * (0.02 / 3.01) = 200 / 301 ≈ 0.6645`, which is
  -- within `0.005` of the official `0.66 %` readout.
  rw [hx, abs_le]
  constructor <;> norm_num

end IChO2026Problems.T4.A1
