import IChO2026Chem

/-!
# IChO 2026 T1-A3: identifying W from a ferric-ion test and isotope peaks

The formulae below are atom counts and the mass-spectrum ratio is
dimensionless.  The source and rubric use the displayed ratio `9 : 1`
directly.  At the same time, their printed calculation
`0.989 / (0.011 * n) = 9` gives the real scratch value
`n = 989 / 99`, not the literal real number `10`.  We therefore keep the
source-reported ratio equal to `9` and separate the rubric's unrounded real
calculation from its final whole-number carbon report.  The rounding locus is
the reported carbon count, never the input ratio.
-/

namespace IChO2026Problems.T1A3

/-- The four plants listed as possible sources of the blue elixir. -/
private inductive Plant where
  | zingiber
  | hypericum
  | chamomilla
  | artemisia
  deriving DecidableEq, Fintype

/-- The ten labelled compounds in the source table. -/
private inductive PlantCompound where
  | c1 | c2 | c3 | c4 | c5 | c6 | c7 | c8 | c9 | c10
  deriving DecidableEq, Fintype

/-- Atom counts in the molecular formulae printed in the plant table. -/
private structure MolecularFormula where
  carbon : ℕ
  hydrogen : ℕ
  oxygen : ℕ
  deriving DecidableEq

/-- The molecular formula printed beside each labelled compound. -/
private def molecularFormula : PlantCompound → MolecularFormula
  | .c1 => ⟨11, 14, 3⟩
  | .c2 => ⟨10, 18, 1⟩
  | .c3 => ⟨10, 18, 1⟩
  | .c4 => ⟨6, 12, 1⟩
  | .c5 => ⟨10, 12, 2⟩
  | .c6 => ⟨10, 18, 1⟩
  | .c7 => ⟨14, 16, 0⟩
  | .c8 => ⟨15, 24, 0⟩
  | .c9 => ⟨10, 16, 1⟩
  | .c10 => ⟨10, 18, 1⟩

/-- The source-table extraction relation between each plant and its compounds. -/
private def extractableCompounds : Plant → Finset PlantCompound
  | .zingiber => {.c1, .c2, .c3}
  | .hypericum => {.c4, .c5, .c6}
  | .chamomilla => {.c7, .c8, .c3}
  | .artemisia => {.c9, .c10, .c3}

/-- Compound 1, named zingerone in the solution. -/
private def zingerone : PlantCompound := .c1

/-- Compound 5, named eugenol in the solution. -/
private def eugenol : PlantCompound := .c5

/-- The number of carbon atoms in a compound's supplied molecular formula. -/
private def carbonAtomCount (compound : PlantCompound) : ℕ :=
  (molecularFormula compound).carbon

/-- Structural information visible in the source table: precisely zingerone
and eugenol among the relevant candidates contain a phenolic hydroxy group. -/
private def hasPhenolicHydroxy (compound : PlantCompound) : Prop :=
  compound = zingerone ∨ compound = eugenol

/-- A qualitative observation from adding a compound to aqueous `Fe³⁺`. -/
private inductive FerricTestOutcome where
  | noCharacteristicChange
  | characteristicColourChange
  deriving DecidableEq

/-- The blue elixir has the four different chromatographic substances `X`,
`Y`, `Z`, and `W`; their identities are deliberately not selected here. -/
private structure BlueElixir where
  X : PlantCompound
  Y : PlantCompound
  Z : PlantCompound
  W : PlantCompound
  X_ne_Y : X ≠ Y
  X_ne_Z : X ≠ Z
  X_ne_W : X ≠ W
  Y_ne_Z : Y ≠ Z
  Y_ne_W : Y ≠ W
  Z_ne_W : Z ≠ W

/-- Empirical bridge used by the ferric-ion test in this question: a
characteristic positive outcome establishes the presence of a phenolic group.
It is a hypothesis rather than a definition of the experimental outcome. -/
private def FerricTestOutcome.establishesPhenolicHydroxy
    (test : PlantCompound → FerricTestOutcome) : Prop :=
  ∀ compound, test compound = .characteristicColourChange →
    hasPhenolicHydroxy compound

/-- The natural-abundance model supplied in the question.  Its two fractions
exhaust carbon, since carbon is assumed to consist exclusively of `¹²C` and
`¹³C`; other elements are monoisotopic in the peak model below. -/
private structure CarbonIsotopeAbundances where
  carbon12Fraction : ℝ
  carbon13Fraction : ℝ
  carbon12_nonneg : 0 ≤ carbon12Fraction
  carbon13_nonneg : 0 ≤ carbon13Fraction
  exhaustive : carbon12Fraction + carbon13Fraction = 1

/-- The supplied natural abundance of `¹²C` is `98.9 %`; exclusivity of the
two carbon isotopes consequently fixes the `¹³C` fraction to `1.1 %`. -/
private def CarbonIsotopeAbundances.matchesSuppliedData
    (abundances : CarbonIsotopeAbundances) : Prop :=
  abundances.carbon12Fraction = 989 / 1000

/-- The reported dimensionless ratio of the molecular-ion peak to the
`[M+1]⁺` peak.  The source supplies the ratio, not absolute peak heights. -/
private structure MassSpectrumReport where
  molecularIonToPlusOneRatio : ℝ

/-- The source datum is retained literally as the ratio `9 : 1`; no tolerance
is attached to this input. -/
private def MassSpectrumReport.matchesSuppliedData
    (spectrum : MassSpectrumReport) : Prop :=
  spectrum.molecularIonToPlusOneRatio = 9

/-- The real-valued scratch result of the official rubric's isotope
calculation, before it is reported as a whole number of carbon atoms.  It is
deliberately distinct from the molecular formula's natural-number count. -/
private structure SourceReportedCarbonCalculation where
  unroundedCarbonCount : ℝ

/-- Reporting a real calculation as the nearest whole carbon count.  This is
the only rounding convention required to reconcile the rubric's exact printed
inputs with its reported integer output. -/
private def reportsNearestWholeCarbonCount
    (calculated : ℝ) (reported : ℕ) : Prop :=
  |calculated - (reported : ℝ)| < 1 / 2

/-- The official calculation/reporting contract.  The first equality is the
rubric's Equation (1) after cancelling the common `0.989^(n-1)` factor:
`0.989 / (0.011 * n) = 9`.  Carbon exclusivity supplies the `¹³C` abundance,
and the assumption that all other elements are monoisotopic is exactly what
permits this carbon-only ratio calculation.  `unroundedCarbonCount` is the
real arithmetic scratch value; `reportedCarbonCount` is the molecule's
integer count. -/
private def SourceReportedCarbonCalculation.matchesOfficialRubric
    (calculation : SourceReportedCarbonCalculation)
    (abundances : CarbonIsotopeAbundances)
    (spectrum : MassSpectrumReport)
    (reportedCarbonCount : ℕ) : Prop :=
  0 < calculation.unroundedCarbonCount ∧
    abundances.carbon12Fraction /
        (abundances.carbon13Fraction * calculation.unroundedCarbonCount) =
      spectrum.molecularIonToPlusOneRatio ∧
    reportsNearestWholeCarbonCount calculation.unroundedCarbonCount
      reportedCarbonCount

/-- A characteristic ferric-ion colour change restricts `W` to the two
phenolic structures visible in the supplied table. -/
private theorem ferric_test_restricts_W_to_phenolic_candidates
    (elixir : BlueElixir)
    (test : PlantCompound → FerricTestOutcome)
    (hobserved : test elixir.W = .characteristicColourChange)
    (htest : FerricTestOutcome.establishesPhenolicHydroxy test) :
    hasPhenolicHydroxy elixir.W := by
  exact htest elixir.W hobserved

/-- The official exact `9 : 1` input and its whole-number reporting contract
force the reported carbon count to be ten.  In particular, the proof first
derives the satisfiable real scratch value `989 / 99`; it does not assume the
false equality `0.989 / (0.011 * 10) = 9`. -/
private theorem carbon_count_from_source_reported_calculation
    (compound : PlantCompound)
    (abundances : CarbonIsotopeAbundances)
    (spectrum : MassSpectrumReport)
    (calculation : SourceReportedCarbonCalculation)
    (habundances : abundances.matchesSuppliedData)
    (hratio : spectrum.matchesSuppliedData)
    (hcalculation : calculation.matchesOfficialRubric abundances spectrum
      (carbonAtomCount compound)) :
    carbonAtomCount compound = 10 := by
  have h12 : abundances.carbon12Fraction = (989 : ℝ) / 1000 := habundances
  have h13 : abundances.carbon13Fraction = (11 : ℝ) / 1000 := by
    nlinarith [abundances.exhaustive]
  rcases hcalculation with ⟨hcalculated_pos, hequation, hreported⟩
  have hcalculated_ne : calculation.unroundedCarbonCount ≠ 0 :=
    ne_of_gt hcalculated_pos
  have hcalculated :
      calculation.unroundedCarbonCount = (989 : ℝ) / 99 := by
    rw [h12, h13, hratio] at hequation
    field_simp [hcalculated_ne] at hequation
    nlinarith
  unfold reportsNearestWholeCarbonCount at hreported
  rw [hcalculated, abs_lt] at hreported
  have hnine_real : (9 : ℝ) < (carbonAtomCount compound : ℝ) := by
    nlinarith [hreported.2]
  have heleven_real : (carbonAtomCount compound : ℝ) < 11 := by
    nlinarith [hreported.1]
  have hnine : 9 < carbonAtomCount compound := by
    exact_mod_cast hnine_real
  have heleven : carbonAtomCount compound < 11 := by
    exact_mod_cast heleven_real
  omega

/-- T1-A3 asks for both the number of carbon atoms and the identity of `W`.
The conclusion identifies `W` only after the ferric-test and source-reported
isotope-calculation assumptions have supplied those two independent
constraints. -/
theorem identify_W
    (elixir : BlueElixir)
    (test : PlantCompound → FerricTestOutcome)
    (abundances : CarbonIsotopeAbundances)
    (spectrum : MassSpectrumReport)
    (calculation : SourceReportedCarbonCalculation)
    (hobserved : test elixir.W = .characteristicColourChange)
    (htest : FerricTestOutcome.establishesPhenolicHydroxy test)
    (habundances : abundances.matchesSuppliedData)
    (hratio : spectrum.matchesSuppliedData)
    (hcalculation : calculation.matchesOfficialRubric abundances spectrum
      (carbonAtomCount elixir.W)) :
    elixir.W = eugenol ∧ carbonAtomCount elixir.W = 10 := by
  have hphenolic : hasPhenolicHydroxy elixir.W :=
    ferric_test_restricts_W_to_phenolic_candidates elixir test hobserved htest
  have hcarbon : carbonAtomCount elixir.W = 10 :=
    carbon_count_from_source_reported_calculation elixir.W abundances spectrum
      calculation habundances hratio hcalculation
  constructor
  · rcases hphenolic with hW | hW
    · rw [hW] at hcarbon
      norm_num [carbonAtomCount, zingerone, molecularFormula] at hcarbon
    · exact hW
  · exact hcarbon

end IChO2026Problems.T1A3
