import IChO2026Chem

/-!
# IChO 2026, Problem T6 (Carbon Nanorings), Subquestion 6.3

**Source.** 58th International Chemistry Olympiad, Tashkent 2026, theory
problem T6, subquestion 6.3 (problem PDF page 53; rubric in the official
solution PDF, 2 points).

**Question.** The voltages applied during the AFM-mediated synthesis of
cyclo[n]carbons Cₙ may vary. Using the given C–X bond dissociation energies,
choose the possible halogen(s) in the halogenated reagent for C18 synthesis via
a retro-Bergman reaction with a voltage of 2.5 V acting on the electrons.

| Bond  | BDE / kJ mol⁻¹ |
|-------|----------------|
| C–F   | 467            |
| C–Cl  | 346            |
| C–Br  | 290            |
| C–I   | 228            |

**Marking-scheme reasoning (source of the governing relation).** The energy
delivered per mole of electrons accelerated through a potential difference
U is E = U · e · N_A / 1000 kJ mol⁻¹. With the exam data values
e = 1.602 × 10⁻¹⁹ C and N_A = 6.022 × 10²³ mol⁻¹ at U = 2.5 V this gives
E_given = 2.5 × 96.485 ≈ 241.2 kJ mol⁻¹ (the exact evaluation with the exam
constants is 241.1811 kJ mol⁻¹). A halogen X is a possible candidate iff
BDE(C–X) ≤ E_given; the only tabulated bond meeting the criterion is C–I, so
X = I. The rubric awards 1 point for the unit transformation and 1 point for
the correct halogen choice, and 0 points if any other or more than one halogen
is chosen — so uniqueness of the answer is part of the source contract.

## Assumption / target split

Assumptions (all sourced from the problem statement or the exam data values
used by the official marking scheme; none of them mentions the answer):

* `Halogen`: the four candidate halogen species F, Cl, Br, I of the C–X table.
* `carbonHalogenBondBDE`: the tabulated C–X bond dissociation energies, in
  kJ mol⁻¹ (empirical data supplied by the problem).
* `elementaryCharge`, `avogadroConstant`: the exam data values
  e = 1.602 × 10⁻¹⁹ C and N_A = 6.022 × 10²³ mol⁻¹ explicitly used in the
  marking scheme's conversion. (Physlib exposes an `elementaryCharge` only as
  a dimensionful `ChargeUnit` carrying the exact SI value 1.602176634e-19 C,
  and has no Avogadro constant; the rounded exam values are therefore kept as
  local real constants with documented provenance.)
* `molarElectronEnergyKJmol`: the governing physical law
  E(U) = U · e · N_A / 1000 kJ mol⁻¹, i.e. one mole of electrons accelerated
  through U volts carries U · F kJ mol⁻¹.
* `biasVoltage`: the condition of the subquestion, U = 2.5 V.
* `IsPossibleHalogenAt`: the selection criterion from the marking scheme,
  X possible at voltage U iff BDE(C–X) ≤ E(U). This inequality is the strong
  bridge: the classification below is derivable from it by numeric comparison
  and is not true by definition.

Targets (the requested conclusions; the recorded answer X = I appears only
here, never in a premise or definition):

* `molarElectronEnergy_at_bias`: the unit-transformation component,
  E(2.5 V) = 241.1811 kJ mol⁻¹.
* `molarElectronEnergy_at_bias_approx`: the marking scheme's rounded value
  E_given = 241.2 kJ mol⁻¹ agrees with the exact evaluation to within
  0.1 kJ mol⁻¹.
* `isPossibleHalogenAt_bias_iff`: the classification — at 2.5 V a halogen
  meets the criterion iff it is iodine.
* `possibleHalogens_at_bias`: set form, the possible halogens are exactly
  {I}.
* `existsUnique_possibleHalogen_at_bias`: uniqueness form, exactly one
  halogen qualifies (the rubric's "0 pts for more than one halogen").

All declarations below are proved against these source-faithful statements.
-/

namespace IChO2026.T6.A3

/-- The four candidate halogens of the problem's C–X bond-energy table.
Species identity is preserved (rather than collapsing to bare numbers) because
the requested conclusion is a statement about which species qualifies. -/
inductive Halogen where
  | fluorine
  | chlorine
  | bromine
  | iodine
  deriving DecidableEq, Repr, Fintype

/-- Tabulated C–X bond dissociation energies from the problem statement,
in kJ mol⁻¹: C–F 467, C–Cl 346, C–Br 290, C–I 228. -/
noncomputable def carbonHalogenBondBDE : Halogen → ℝ
  | .fluorine => 467
  | .chlorine => 346
  | .bromine  => 290
  | .iodine   => 228

/-- Elementary charge, exam data value used by the official marking scheme:
e = 1.602 × 10⁻¹⁹ C. -/
noncomputable def elementaryCharge : ℝ := 1.602 / 10^19

/-- Avogadro constant, exam data value used by the official marking scheme:
N_A = 6.022 × 10²³ mol⁻¹. -/
noncomputable def avogadroConstant : ℝ := 6.022 * 10^23

/-- Molar energy delivered to electrons accelerated through a potential
difference `U` (in volts), in kJ mol⁻¹:

E(U) = U · e · N_A / 1000.

This is the governing conversion law of the subquestion: one electron through
one volt gains one electronvolt (e joules), so one mole of electrons gains
U · e · N_A joules per mole, i.e. U · F joules per mole with
F = e · N_A the Faraday constant; division by 1000 converts J to kJ. -/
noncomputable def molarElectronEnergyKJmol (U : ℝ) : ℝ :=
  U * elementaryCharge * avogadroConstant / 1000

/-- The AFM bias voltage specified in subquestion 6.3: 2.5 V. -/
noncomputable def biasVoltage : ℝ := 2.5

/-- Selection criterion from the official marking scheme: at bias voltage `U`
(in volts), halogen `X` is a possible constituent of the halogenated reagent
iff the molar electron energy suffices to break the C–X bond, i.e.
BDE(C–X) ≤ E(U). -/
def IsPossibleHalogenAt (U : ℝ) (X : Halogen) : Prop :=
  carbonHalogenBondBDE X ≤ molarElectronEnergyKJmol U

/-- Every tabulated C–X bond dissociation energy is positive. -/
theorem carbonHalogenBondBDE_pos (X : Halogen) :
    0 < carbonHalogenBondBDE X := by
  cases X <;> norm_num [carbonHalogenBondBDE]

/-- Unit transformation (first rubric point): with the exam constants, the
molar electron energy at the 2.5 V bias evaluates exactly to
241.1811 kJ mol⁻¹, since 2.5 · (1.602 × 10⁻¹⁹) · (6.022 × 10²³) / 1000
= 241.1811. -/
theorem molarElectronEnergy_at_bias :
    molarElectronEnergyKJmol biasVoltage = 241.1811 := by
  norm_num [molarElectronEnergyKJmol, biasVoltage, elementaryCharge,
    avogadroConstant]

/-- The marking scheme's rounded value E_given = 2.5 · 96.485 ≈ 241.2 kJ mol⁻¹
agrees with the exact evaluation `molarElectronEnergy_at_bias` to within
0.1 kJ mol⁻¹. -/
theorem molarElectronEnergy_at_bias_approx :
    |molarElectronEnergyKJmol biasVoltage - 241.2| ≤ 0.1 := by
  rw [molarElectronEnergy_at_bias, abs_le]
  constructor <;> norm_num

/-- Main classification (second rubric point): at the 2.5 V bias, a halogen
satisfies the bond-energy criterion if and only if it is iodine.
Numerically this is the content of
228 ≤ 241.1811 < 290 < 346 < 467. -/
theorem isPossibleHalogenAt_bias_iff (X : Halogen) :
    IsPossibleHalogenAt biasVoltage X ↔ X = Halogen.iodine := by
  cases X <;>
    simp only [IsPossibleHalogenAt, carbonHalogenBondBDE,
      molarElectronEnergy_at_bias, reduceCtorEq, iff_true, iff_false] <;>
    norm_num

/-- Set form of the classification: the halogens that can serve in the
halogenated reagent for the 2.5 V retro-Bergman synthesis of C18 are exactly
{iodine}. -/
theorem possibleHalogens_at_bias :
    {X : Halogen | IsPossibleHalogenAt biasVoltage X} = {Halogen.iodine} := by
  ext X
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  exact isPossibleHalogenAt_bias_iff X

/-- Uniqueness form: exactly one halogen meets the criterion at 2.5 V —
the rubric's "0 pts for more than one halogen chosen". -/
theorem existsUnique_possibleHalogen_at_bias :
    ∃! X : Halogen, IsPossibleHalogenAt biasVoltage X :=
  ⟨Halogen.iodine, (isPossibleHalogenAt_bias_iff _).mpr rfl,
    fun Y hY => (isPossibleHalogenAt_bias_iff Y).mp hY⟩

end IChO2026.T6.A3
