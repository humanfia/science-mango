import Mathlib

/-!
# IChO 2026, Theory Problem T4, subquestion 4.9

**The Nuclear Past of Uzbekistan — fission count and fuel mass of the
Urtabulak device**

The Urtabulak gas leak was ended by detonating a 30-kiloton (TNT equivalent)
underground nuclear explosion; the problem text (page Q4-3) states that
1 ton of TNT equivalent is 4.184 GJ of energy.  Subquestion 4.9 asks, using
the energy per fission ΔE found in subquestion 4.4, for

* `TN`, the total number of fissions during the nuclear explosion, and
* `m`, the mass (in kg) of the enriched uranium used in the explosion,
  assuming it contained 90 % by mass of the ²³⁵U isotope and that 33 % of
  the ²³⁵U underwent fission.

The problem also states a fallback branch: a contestant without an answer for
4.4 should use ΔE = 200 MeV.

## Modelling conventions

Following the project convention (see
`IChO2026Chem.Kinetics.BelousovZhabotinsky`), every quantity is modelled as a
real numerical readout in a fixed source unit, documented at each definition:
energies in joules (J) or MeV, amounts of substance in moles, masses in grams
or kilograms, and the Avogadro constant in mol⁻¹.

The energy per fission from subquestion 4.4 enters as an explicit hypothesis
(`ΔE_MeV = 185.2`), in line with the `natural_language_prerequisite_only`
dependency policy; no conclusion of the present subquestion is assumed.
The marking scheme's derivation chain

  E = 30.0 × 10³ ton × 4.184 GJ ton⁻¹ = 1.2552 × 10¹⁴ J,
  E_fission = 185.2 MeV × 1.602 × 10⁻¹³ J MeV⁻¹ = 2.967 × 10⁻¹¹ J,
  TN = E / E_fission = 4.23 × 10²⁴,
  n(²³⁵U) = TN / N_A = 7.03 mol,
  m(²³⁵U) = n × 235.04 g mol⁻¹ = 1.65 × 10³ g,
  m = m(²³⁵U) / (0.90 × 0.33) = 5.56 kg

is carried by transparent definitions (`explosionEnergyJ`, `fissionEnergyJ`,
`totalFissions`, `u235AmountFissionedMol`, `u235MassFissionedG`,
`enrichedUraniumMassKg`), and the recorded answers appear only as theorem
conclusions, each certified to the precision at which the marking scheme
records it: the absolute tolerance is half a unit of the last recorded digit
(three significant figures for `TN` and `m`).

No physical constants are taken from Mathlib/Physlib/CRNT: none of the pinned
packages exposes an Avogadro constant, an MeV–joule conversion, or a TNT
equivalence (checked 2026-08-11), so every empirical constant below is sourced
from the official problem text or the official marking scheme, as flagged in
its docstring.
-/

namespace IChO2026Problems.T4.A9

/-! ## Sourced empirical data

Every constant in this section is taken from the official problem text or
from the numerical conventions of the official marking scheme; none is
invented, and no recorded answer of subquestion 4.9 appears here. -/

/-- Explosion yield in tons of TNT equivalent: the Urtabulak charge was a
"30-kiloton in TNT equivalent" device (problem text, page Q4-3). -/
def explosionYieldTonsTNT : ℝ := 30.0e3

/-- Energy of one ton of TNT equivalent, in joules: the problem text states
"1 ton of TNT equivalent is 4.184 GJ of energy", i.e. 4.184 × 10⁹ J. -/
def joulesPerTonTNT : ℝ := 4.184e9

/-- Joules per MeV, as used by the official marking scheme:
1 MeV = 1.602 × 10⁻¹³ J. -/
def joulesPerMeV : ℝ := 1.602e-13

/-- Avogadro constant, in mol⁻¹, as used by the official marking scheme:
N_A = 6.022 × 10²³ mol⁻¹. -/
def avogadroConstant : ℝ := 6.022e23

/-- Molar mass of the ²³⁵U isotope, in g mol⁻¹.  Subquestion 4.1 gives the
atomic mass 235.04 a.u.; the marking scheme uses 235.04 g mol⁻¹. -/
def u235MolarMass : ℝ := 235.04

/-- Mass fraction of ²³⁵U in the enriched uranium: "it contained 90 % by mass
of the ²³⁵U isotope" (subquestion 4.9). -/
def enrichmentMassFraction : ℝ := 0.90

/-- Fraction of the ²³⁵U that underwent fission: "33 % of the ²³⁵U underwent
fission" (subquestion 4.9). -/
def fissionedFraction : ℝ := 0.33

/-! ## Governing relations (the marking-scheme derivation chain) -/

/-- Total energy released by the explosion, in joules:
E = 30.0 × 10³ ton × 4.184 GJ ton⁻¹ = 1.2552 × 10¹⁴ J. -/
noncomputable def explosionEnergyJ : ℝ := explosionYieldTonsTNT * joulesPerTonTNT

/-- Energy released by a single ²³⁵U fission, in joules, when the per-fission
energy is `ΔE_MeV` MeV: E_fission = ΔE × 1.602 × 10⁻¹³ J. -/
noncomputable def fissionEnergyJ (ΔE_MeV : ℝ) : ℝ := ΔE_MeV * joulesPerMeV

/-- Total number of fissions during the explosion: TN = E / E_fission. -/
noncomputable def totalFissions (ΔE_MeV : ℝ) : ℝ := explosionEnergyJ / fissionEnergyJ ΔE_MeV

/-- Amount of ²³⁵U that underwent fission, in moles: n = TN / N_A. -/
noncomputable def u235AmountFissionedMol (ΔE_MeV : ℝ) : ℝ :=
  totalFissions ΔE_MeV / avogadroConstant

/-- Mass of ²³⁵U that underwent fission, in grams: m = n × 235.04 g mol⁻¹. -/
noncomputable def u235MassFissionedG (ΔE_MeV : ℝ) : ℝ :=
  u235AmountFissionedMol ΔE_MeV * u235MolarMass

/-- Mass of enriched uranium used in the explosion, in kilograms: the
fissioned ²³⁵U mass divided by the enrichment mass fraction and by the
fissioned fraction, m = m(²³⁵U) / (0.90 × 0.33), converted from grams to
kilograms. -/
noncomputable def enrichedUraniumMassKg (ΔE_MeV : ℝ) : ℝ :=
  u235MassFissionedG ΔE_MeV / (enrichmentMassFraction * fissionedFraction) / 1000

/-! ## Marking-scheme waypoints

Intermediate readouts of the official solution, stated so the prover stage
can certify the derivation chain step by step. -/

/-- The explosion energy is exactly 1.2552 × 10¹⁴ J
(30.0 × 10³ ton × 4.184 × 10⁹ J ton⁻¹). -/
theorem explosion_energy_value : explosionEnergyJ = 1.2552e14 := by
  norm_num [explosionEnergyJ, explosionYieldTonsTNT, joulesPerTonTNT]

/-- With ΔE = 185.2 MeV (the answer of subquestion 4.4), one fission releases
exactly 2.966904 × 10⁻¹¹ J, which the marking scheme rounds to
2.967 × 10⁻¹¹ J. -/
theorem fission_energy_value (ΔE_MeV : ℝ) (hΔE : ΔE_MeV = 185.2) :
    fissionEnergyJ ΔE_MeV = 2.966904e-11 := by
  subst hΔE; norm_num [fissionEnergyJ, joulesPerMeV]

/-- The amount of ²³⁵U that fissioned is 7.03 mol to the three significant
figures of the marking scheme (tolerance: half a unit of the last recorded
digit). -/
theorem u235_amount_fissioned_approx (ΔE_MeV : ℝ) (hΔE : ΔE_MeV = 185.2) :
    |u235AmountFissionedMol ΔE_MeV - 7.03| ≤ 5e-3 := by
  subst hΔE; rw [abs_le]; constructor <;>
    norm_num [u235AmountFissionedMol, totalFissions, explosionEnergyJ,
      explosionYieldTonsTNT, joulesPerTonTNT, fissionEnergyJ, joulesPerMeV,
      avogadroConstant]

/-- The mass of ²³⁵U that fissioned is 1.65 × 10³ g to the three significant
figures of the marking scheme (tolerance: half a unit of the last recorded
digit). -/
theorem u235_mass_fissioned_approx (ΔE_MeV : ℝ) (hΔE : ΔE_MeV = 185.2) :
    |u235MassFissionedG ΔE_MeV - 1.65e3| ≤ 5 := by
  subst hΔE; rw [abs_le]; constructor <;>
    norm_num [u235MassFissionedG, u235AmountFissionedMol, totalFissions,
      explosionEnergyJ, explosionYieldTonsTNT, joulesPerTonTNT, fissionEnergyJ,
      joulesPerMeV, avogadroConstant, u235MolarMass]

/-! ## Requested conclusions of subquestion 4.9

Using ΔE = 185.2 MeV from subquestion 4.4
(`natural_language_prerequisite_only`, restated here as the hypothesis
`hΔE`).  Each recorded answer is certified to three significant figures, the
precision of the marking scheme. -/

/-- **Requested output 1 (2 points).** The total number of fissions during
the nuclear explosion is TN = 4.23 × 10²⁴ to the three significant figures of
the marking scheme (tolerance: half a unit of the last recorded digit). -/
theorem total_fissions_approx (ΔE_MeV : ℝ) (hΔE : ΔE_MeV = 185.2) :
    |totalFissions ΔE_MeV - 4.23e24| ≤ 5e21 := by
  subst hΔE; rw [abs_le]; constructor <;>
    norm_num [totalFissions, explosionEnergyJ, explosionYieldTonsTNT,
      joulesPerTonTNT, fissionEnergyJ, joulesPerMeV]

/-- **Requested output 2 (2 points).** The mass of enriched uranium used in
the explosion is m = 5.56 kg to the three significant figures of the marking
scheme (tolerance: half a unit of the last recorded digit). -/
theorem enriched_uranium_mass_approx (ΔE_MeV : ℝ) (hΔE : ΔE_MeV = 185.2) :
    |enrichedUraniumMassKg ΔE_MeV - 5.56| ≤ 5e-3 := by
  subst hΔE; rw [abs_le]; constructor <;>
    norm_num [enrichedUraniumMassKg, u235MassFissionedG,
      u235AmountFissionedMol, totalFissions, explosionEnergyJ,
      explosionYieldTonsTNT, joulesPerTonTNT, fissionEnergyJ, joulesPerMeV,
      avogadroConstant, u235MolarMass, enrichmentMassFraction,
      fissionedFraction]

/-- **Subquestion 4.9 target.** Using the energy per fission from 4.4, the
total number of fissions is 4.23 × 10²⁴ and the mass of enriched uranium
(90 % ²³⁵U by mass, 33 % of the ²³⁵U fissioned) is 5.56 kg, each to the three
significant figures of the marking scheme. -/
theorem target (ΔE_MeV : ℝ) (hΔE : ΔE_MeV = 185.2) :
    |totalFissions ΔE_MeV - 4.23e24| ≤ 5e21 ∧
      |enrichedUraniumMassKg ΔE_MeV - 5.56| ≤ 5e-3 :=
  ⟨total_fissions_approx ΔE_MeV hΔE, enriched_uranium_mass_approx ΔE_MeV hΔE⟩

/-! ## Fallback branch

The problem instructs a contestant without an answer for 4.4 to use
ΔE = 200 MeV.  The marking scheme does not record the resulting values, so
the readouts below are this formalization's own three-significant-figure
evaluation of the same governing relations at ΔE = 200 MeV, stated with the
same half-last-digit tolerances. -/

/-- **Fallback branch (ΔE = 200 MeV).** The same governing relations give
TN = 3.92 × 10²⁴ fissions and m = 5.15 kg of enriched uranium, each to three
significant figures. -/
theorem target_fallback (ΔE_MeV : ℝ) (hΔE : ΔE_MeV = 200) :
    |totalFissions ΔE_MeV - 3.92e24| ≤ 5e21 ∧
      |enrichedUraniumMassKg ΔE_MeV - 5.15| ≤ 5e-3 := by
  subst hΔE; rw [abs_le, abs_le]; constructor <;> constructor <;>
    norm_num [totalFissions, enrichedUraniumMassKg, u235MassFissionedG,
      u235AmountFissionedMol, explosionEnergyJ, explosionYieldTonsTNT,
      joulesPerTonTNT, fissionEnergyJ, joulesPerMeV, avogadroConstant,
      u235MolarMass, enrichmentMassFraction, fissionedFraction]

end IChO2026Problems.T4.A9
